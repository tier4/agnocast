#include "agnocast.h"

#include <linux/device.h>
#include <linux/hashtable.h>
#include <linux/kprobes.h>
#include <linux/slab.h>  // kmalloc, kfree
#include <linux/version.h>

MODULE_LICENSE("Dual BSD/GPL");

static int major;
static struct class * agnocast_class;
static struct device * agnocast_device;
static DEFINE_MUTEX(global_mutex);

// =========================================
// data structure

#define TOPIC_HASH_BITS 10  // hash table size : 2^TOPIC_HASH_BITS
#define PUB_INFO_HASH_BITS 1
#define SUB_INFO_HASH_BITS 3
#define PROC_INFO_HASH_BITS 10

struct process_info
{
  uint32_t pid;
  uint64_t shm_addr;
  uint64_t shm_size;
  struct hlist_node node;
};

DEFINE_HASHTABLE(proc_info_htable, PROC_INFO_HASH_BITS);

struct publisher_info
{
  uint32_t pid;
  uint32_t entries_num;
  bool exited;
  struct hlist_node node;
};

struct subscriber_info
{
  uint32_t pid;
  uint64_t latest_received_timestamp;
  bool is_take_sub;
  struct hlist_node node;
};

struct topic_struct
{
  struct rb_root entries;
  DECLARE_HASHTABLE(pub_info_htable, PUB_INFO_HASH_BITS);
  DECLARE_HASHTABLE(sub_info_htable, SUB_INFO_HASH_BITS);
};

struct topic_wrapper
{
  char * key;
  struct topic_struct topic;
  struct hlist_node node;
};

struct entry_node
{
  struct rb_node node;
  uint64_t timestamp;  // rbtree key
  uint32_t publisher_pid;
  uint64_t msg_virtual_address;
  uint32_t referencing_subscriber_pids[MAX_SUBSCRIBER_NUM];
  uint8_t subscriber_reference_count[MAX_SUBSCRIBER_NUM];
  bool published;
};

DEFINE_HASHTABLE(topic_hashtable, TOPIC_HASH_BITS);

static unsigned long get_topic_hash(const char * str)
{
  unsigned long hash = full_name_hash(NULL /*namespace*/, str, strlen(str));
  return hash_min(hash, TOPIC_HASH_BITS);
}

static struct topic_wrapper * insert_topic(const char * topic_name)
{
  struct topic_wrapper * wrapper = kmalloc(sizeof(struct topic_wrapper), GFP_KERNEL);
  if (!wrapper) {
    dev_warn(agnocast_device, "kmalloc failed. (insert_topic)\n");
    return NULL;
  }

  wrapper->key = kstrdup(topic_name, GFP_KERNEL);
  if (!wrapper->key) {
    dev_warn(agnocast_device, "kstrdup failed. (insert_topic)\n");
    kfree(wrapper);
    return NULL;
  }

  wrapper->topic.entries = RB_ROOT;
  hash_init(wrapper->topic.pub_info_htable);
  hash_init(wrapper->topic.sub_info_htable);

  hash_add(topic_hashtable, &wrapper->node, get_topic_hash(topic_name));
  return wrapper;
}

static struct topic_wrapper * find_topic(const char * topic_name)
{
  struct topic_wrapper * entry;
  unsigned long hash_val = get_topic_hash(topic_name);

  hash_for_each_possible(topic_hashtable, entry, node, hash_val)
  {
    if (strcmp(entry->key, topic_name) == 0) return entry;
  }

  return NULL;
}

static int get_size_sub_info_htable(struct topic_wrapper * wrapper)
{
  int count = 0;
  struct subscriber_info * sub_info;
  int bkt_sub_info;
  hash_for_each(wrapper->topic.sub_info_htable, bkt_sub_info, sub_info, node)
  {
    count++;
  }
  return count;
}

static struct subscriber_info * find_subscriber_info(
  const struct topic_wrapper * wrapper, uint32_t subscriber_pid)
{
  struct subscriber_info * info;
  uint32_t hash_val = hash_min(subscriber_pid, SUB_INFO_HASH_BITS);
  hash_for_each_possible(wrapper->topic.sub_info_htable, info, node, hash_val)
  {
    if (info->pid == subscriber_pid) {
      return info;
    }
  }

  return NULL;
}

static struct subscriber_info * insert_subscriber_info(
  struct topic_wrapper * wrapper, uint32_t subscriber_pid, bool is_take_sub)
{
  int count = get_size_sub_info_htable(wrapper);
  if (count == MAX_SUBSCRIBER_NUM) {
    dev_warn(
      agnocast_device,
      "The number of subscribers for the topic (topic_name=%s) reached the upper "
      "bound (MAX_SUBSCRIBER_NUM=%d), so no new subscriber can be "
      "added. (insert_subscriber_info)\n",
      wrapper->key, MAX_SUBSCRIBER_NUM);
    return NULL;
  }

  struct subscriber_info * info = find_subscriber_info(wrapper, subscriber_pid);
  if (info) {
    dev_warn(
      agnocast_device,
      "Subscriber (pid=%d) already exists in the topic (topic_name=%s). "
      "(insert_subscriber_info)\n",
      subscriber_pid, wrapper->key);
    return NULL;
  }

  struct subscriber_info * new_info = kmalloc(sizeof(struct subscriber_info), GFP_KERNEL);
  if (!new_info) {
    dev_warn(agnocast_device, "kmalloc failed. (insert_subscriber_info)\n");
    return NULL;
  }

  new_info->pid = subscriber_pid;
  new_info->latest_received_timestamp = 0;
  new_info->is_take_sub = is_take_sub;
  INIT_HLIST_NODE(&new_info->node);
  uint32_t hash_val = hash_min(subscriber_pid, SUB_INFO_HASH_BITS);
  hash_add(wrapper->topic.sub_info_htable, &new_info->node, hash_val);

  dev_info(
    agnocast_device,
    "Subscriber (pid=%d) is added to the topic (topic_name=%s). (insert_subscriber_info)\n",
    subscriber_pid, wrapper->key);
  return new_info;
}

static int get_size_pub_info_htable(struct topic_wrapper * wrapper)
{
  int count = 0;
  struct publisher_info * pub_info;
  int bkt_pub_info;
  hash_for_each(wrapper->topic.pub_info_htable, bkt_pub_info, pub_info, node)
  {
    count++;
  }
  return count;
}

static struct publisher_info * find_publisher_info(
  const struct topic_wrapper * wrapper, uint32_t publisher_pid)
{
  struct publisher_info * info;
  uint32_t hash_val = hash_min(publisher_pid, PUB_INFO_HASH_BITS);
  hash_for_each_possible(wrapper->topic.pub_info_htable, info, node, hash_val)
  {
    if (info->pid == publisher_pid) {
      return info;
    }
  }

  return NULL;
}

static struct publisher_info * insert_publisher_info(
  struct topic_wrapper * wrapper, uint32_t publisher_pid)
{
  int count = get_size_pub_info_htable(wrapper);

  if (count == MAX_PUBLISHER_NUM) {
    dev_warn(
      agnocast_device,
      "The number of publishers for the topic (topic_name=%s) reached the upper "
      "bound (MAX_PUBLISHER_NUM=%d), so no new publisher can be "
      "added. (insert_publisher_info)\n",
      wrapper->key, MAX_PUBLISHER_NUM);
    return NULL;
  }

  struct publisher_info * info = find_publisher_info(wrapper, publisher_pid);
  if (info) {
    dev_warn(
      agnocast_device,
      "Publisher (pid=%d) already exists in the topic (topic_name=%s). "
      "(insert_publisher_info)\n",
      publisher_pid, wrapper->key);
    return NULL;
  }

  struct publisher_info * new_info = kmalloc(sizeof(struct publisher_info), GFP_KERNEL);
  if (!new_info) {
    dev_warn(agnocast_device, "kmalloc failed. (insert_publisher_info)\n");
    return NULL;
  }

  new_info->pid = publisher_pid;
  new_info->entries_num = 0;
  new_info->exited = false;
  INIT_HLIST_NODE(&new_info->node);
  uint32_t hash_val = hash_min(publisher_pid, PUB_INFO_HASH_BITS);
  hash_add(wrapper->topic.pub_info_htable, &new_info->node, hash_val);

  return new_info;
}

static int increment_entries_num(struct topic_wrapper * wrapper, uint32_t publisher_pid)
{
  struct publisher_info * info = find_publisher_info(wrapper, publisher_pid);
  if (!info) {
    dev_warn(
      agnocast_device,
      "Publisher (pid=%d) doesn't exist in the topic (topic_name=%s). "
      "(increment_entries_num)\n",
      publisher_pid, wrapper->key);
    return -1;
  }
  info->entries_num++;

  return 0;
}

static int decrement_entries_num(struct topic_wrapper * wrapper, uint32_t publisher_pid)
{
  struct publisher_info * info = find_publisher_info(wrapper, publisher_pid);
  if (!info) {
    dev_warn(
      agnocast_device,
      "Publisher (pid=%d) doesn't exist in the topic (topic_name=%s). "
      "(decrement_entries_num)\n",
      publisher_pid, wrapper->key);
    return -1;
  }
  info->entries_num--;

  return 0;
}

static bool is_subscriber_referencing(struct entry_node * en)
{
  // Since referencing_subscriber_pids always stores entries in order from the lowest index,
  // if there's nothing at index 0, it means it doesn't exist.
  return (en->referencing_subscriber_pids[0] > 0);
}

static int get_referencing_subscriber_index(struct entry_node * en, uint32_t subscriber_pid)
{
  for (int i = 0; i < MAX_SUBSCRIBER_NUM; i++) {
    if (en->referencing_subscriber_pids[i] == subscriber_pid) {
      return i;
    }
  }
  return -1;
}

static void remove_referencing_subscriber_by_index(struct entry_node * en, int index)
{
  for (int i = index; i < MAX_SUBSCRIBER_NUM - 1; i++) {
    en->referencing_subscriber_pids[i] = en->referencing_subscriber_pids[i + 1];
    en->subscriber_reference_count[i] = en->subscriber_reference_count[i + 1];
  }

  en->referencing_subscriber_pids[MAX_SUBSCRIBER_NUM - 1] = 0;
  en->subscriber_reference_count[MAX_SUBSCRIBER_NUM - 1] = 0;
  return;
}

static int increment_sub_rc(struct entry_node * en, uint32_t subscriber_pid)
{
  int index = get_referencing_subscriber_index(en, subscriber_pid);
  if (index == -1) {
    for (int i = 0; i < MAX_SUBSCRIBER_NUM; i++) {
      if (en->referencing_subscriber_pids[i] == 0) {
        en->referencing_subscriber_pids[i] = subscriber_pid;
        index = i;
        break;
      }
    }
    if (index == -1) return -1;
  }
  en->subscriber_reference_count[index]++;
  return 0;
}

static int decrement_sub_rc(struct entry_node * en, uint32_t subscriber_pid)
{
  int index = get_referencing_subscriber_index(en, subscriber_pid);
  if (index == -1) return -1;

  en->subscriber_reference_count[index]--;
  if (en->subscriber_reference_count[index] == 0) {
    remove_referencing_subscriber_by_index(en, index);
  }
  return 0;
}

static struct entry_node * find_message_entry(
  struct topic_wrapper * wrapper, uint32_t publisher_pid, uint64_t msg_timestamp)
{
  struct rb_root * root = &wrapper->topic.entries;
  struct rb_node ** new = &(root->rb_node);

  while (*new) {
    struct entry_node * this = container_of(*new, struct entry_node, node);

    if (msg_timestamp < this->timestamp) {
      new = &((*new)->rb_left);
    } else if (msg_timestamp > this->timestamp) {
      new = &((*new)->rb_right);
    } else {
      // TODO: Previously, each publisher had its own tree, so timestamps did not overlap. However,
      // with unification, there is a slight possibility of timestamp conflict. This could be
      // resolved by using a timestamp and PID pair, but it is not implemented yet.
      return this;
    }
  }

  return NULL;
}

static int increment_message_entry_rc(
  const char * topic_name, uint32_t subscriber_pid, uint32_t publisher_pid, uint64_t msg_timestamp)
{
  struct topic_wrapper * wrapper = find_topic(topic_name);
  if (!wrapper) {
    dev_warn(
      agnocast_device, "Topic (topic_name=%s) not found. (increment_message_entry_rc)\n",
      topic_name);
    return -1;
  }

  struct entry_node * en = find_message_entry(wrapper, publisher_pid, msg_timestamp);
  if (!en) {
    dev_warn(
      agnocast_device,
      "Message entry (topic_name=%s publisher_pid=%d timestamp=%lld) not found. "
      "(increment_message_entry_rc)\n",
      topic_name, publisher_pid, msg_timestamp);
    return -1;
  }

  if (increment_sub_rc(en, subscriber_pid) == -1) {
    dev_warn(
      agnocast_device,
      "The number of subscribers for the entry_node (timestamp=%lld) reached the upper "
      "bound (MAX_SUBSCRIBER_NUM=%d), so no new subscriber can reference."
      " (increment_message_entry_rc)\n",
      en->timestamp, MAX_SUBSCRIBER_NUM);
    return -1;
  }

  return 0;
}

static int decrement_message_entry_rc(
  const char * topic_name, uint32_t subscriber_pid, uint32_t publisher_pid, uint64_t msg_timestamp)
{
  struct topic_wrapper * wrapper = find_topic(topic_name);
  if (!wrapper) {
    dev_warn(
      agnocast_device, "Topic (topic_name=%s) not found. (decrement_message_entry_rc)\n",
      topic_name);
    return -1;
  }

  struct entry_node * en = find_message_entry(wrapper, publisher_pid, msg_timestamp);
  if (!en) {
    dev_warn(
      agnocast_device,
      "Message entry (topic_name=%s publisher_pid=%d timestamp=%lld) not found. "
      "(decrement_message_entry_rc)\n",
      topic_name, publisher_pid, msg_timestamp);
    return -1;
  }

  if (decrement_sub_rc(en, subscriber_pid) == -1) {
    dev_warn(
      agnocast_device,
      "Subscriber (pid=%d) is not referencing (topic_name=%s publisher_pid=%d "
      "timestamp=%lld). (decrement_message_entry_rc)\n",
      subscriber_pid, topic_name, publisher_pid, msg_timestamp);
    return -1;
  }

  return 0;
}

static int insert_message_entry(
  const char * topic_name, uint32_t publisher_pid, uint64_t msg_virtual_address, uint64_t timestamp)
{
  struct topic_wrapper * wrapper = find_topic(topic_name);
  if (!wrapper) {
    dev_warn(
      agnocast_device, "Topic (topic_name=%s) not found. (insert_message_entry)\n", topic_name);
    return -1;
  }

  struct rb_root * root = &wrapper->topic.entries;
  struct rb_node ** new = &(root->rb_node);
  struct rb_node * parent = NULL;

  while (*new) {
    struct entry_node * this = container_of(*new, struct entry_node, node);
    parent = *new;

    if (timestamp < this->timestamp) {
      new = &((*new)->rb_left);
    } else if (timestamp > this->timestamp) {
      new = &((*new)->rb_right);
    } else {
      dev_warn(
        agnocast_device,
        "Message entry (timestamp=%lld) already exists in the publisher (pid=%d) queue in the "
        "topic (topic_name=%s). "
        "(insert_message_entry)\n",
        timestamp, publisher_pid, topic_name);
      return -1;
    }
  }

  struct entry_node * new_node = kmalloc(sizeof(struct entry_node), GFP_KERNEL);
  if (!new_node) {
    dev_warn(agnocast_device, "kmalloc failed. (insert_message_entry)\n");
    return -1;
  }

  new_node->timestamp = timestamp;
  new_node->publisher_pid = publisher_pid;
  new_node->msg_virtual_address = msg_virtual_address;
  for (int i = 0; i < MAX_SUBSCRIBER_NUM; i++) {
    new_node->referencing_subscriber_pids[i] = 0;
    new_node->subscriber_reference_count[i] = 0;
  }
  new_node->published = false;

  rb_link_node(&new_node->node, parent, new);
  rb_insert_color(&new_node->node, root);

  if (increment_entries_num(wrapper, publisher_pid) == -1) return -1;

  dev_dbg(
    agnocast_device,
    "Insert a message entry (topic_name=%s publisher_pid=%d msg_virtual_address=%lld "
    "timestamp=%lld). "
    "(insert_message_entry)",
    topic_name, publisher_pid, msg_virtual_address, timestamp);
  return 0;
}

// =========================================
// "/sys/module/agnocast/status/*"

// Example
//
// $ sudo cat /sys/module/agnocast/status/process
// process: id=123, addr=4398046511104, size=67108864
//  publisher
//   /my_dynamic_topic
//   /my_static_topic
//  subscription
//
// process: id=456, addr=4398180728832, size=16777216
//  publisher
//  subscription
//   /my_dynamic_topic
//   /my_static_topic
//
// process: id=789, addr=4398113619968, size=67108864
//  publisher
//   /my_dynamic_topic
//  subscription
//   /my_static_topic
static ssize_t show_processes(struct kobject * kobj, struct kobj_attribute * attr, char * buf)
{
  mutex_lock(&global_mutex);

  int used_size = 0;
  int ret;

  struct process_info * proc_info;
  int bkt_proc_info;
  hash_for_each(proc_info_htable, bkt_proc_info, proc_info, node)
  {
    ret = scnprintf(
      buf + used_size, PAGE_SIZE - used_size, "process: id=%u, addr=%llu, size=%llu\n",
      proc_info->pid, proc_info->shm_addr, proc_info->shm_size);
    used_size += ret;

    ret = scnprintf(buf + used_size, PAGE_SIZE - used_size, " publisher\n");
    used_size += ret;

    struct topic_wrapper * wrapper;
    int bkt_topic;
    hash_for_each(topic_hashtable, bkt_topic, wrapper, node)
    {
      struct publisher_info * pub_info;
      int bkt_pub_info;
      hash_for_each(wrapper->topic.pub_info_htable, bkt_pub_info, pub_info, node)
      {
        if (proc_info->pid == pub_info->pid) {
          ret = scnprintf(buf + used_size, PAGE_SIZE - used_size, "  %s\n", wrapper->key);
          used_size += ret;
        }
      }
    }

    ret = scnprintf(buf + used_size, PAGE_SIZE - used_size, " subscription\n");
    used_size += ret;

    hash_for_each(topic_hashtable, bkt_topic, wrapper, node)
    {
      struct subscriber_info * sub_info;
      int bkt_sub_info;
      hash_for_each(wrapper->topic.sub_info_htable, bkt_sub_info, sub_info, node)
      {
        if (proc_info->pid == sub_info->pid) {
          ret = scnprintf(buf + used_size, PAGE_SIZE - used_size, "  %s\n", wrapper->key);
          used_size += ret;
        }
      }
    }

    ret = scnprintf(buf + used_size, PAGE_SIZE - used_size, "\n");
    used_size += ret;
  }

  if (used_size >= PAGE_SIZE) {
    dev_warn(agnocast_device, "Exceeding PAGE_SIZE. Truncating output...\n");
    mutex_unlock(&global_mutex);
    return -ENOSPC;
  }

  mutex_unlock(&global_mutex);
  return used_size;
}

// Example
//
// $ sudo cat /sys/module/agnocast/status/topic_list
// topic: /my_dynamic_topic
//  publisher: 15198, 15171,
//  subscription: 15237,
//
// topic: /my_static_topic
//  publisher: 15171,
//  subscription: 15237, 15198,
static ssize_t show_topics(struct kobject * kobj, struct kobj_attribute * attr, char * buf)
{
  mutex_lock(&global_mutex);

  int used_size = 0;
  int ret;

  struct topic_wrapper * wrapper;
  int bkt_topic;
  hash_for_each(topic_hashtable, bkt_topic, wrapper, node)
  {
    ret = scnprintf(buf + used_size, PAGE_SIZE - used_size, "topic: %s\n", wrapper->key);
    used_size += ret;

    ret = scnprintf(buf + used_size, PAGE_SIZE - used_size, " publisher:");
    used_size += ret;

    struct publisher_info * pub_info;
    int bkt_pub_info;
    hash_for_each(wrapper->topic.pub_info_htable, bkt_pub_info, pub_info, node)
    {
      ret = scnprintf(buf + used_size, PAGE_SIZE - used_size, " %d,", pub_info->pid);
      used_size += ret;
    }

    ret = scnprintf(buf + used_size, PAGE_SIZE - used_size, "\n");
    used_size += ret;

    ret = scnprintf(buf + used_size, PAGE_SIZE - used_size, " subscription:");
    used_size += ret;

    struct subscriber_info * sub_info;
    int bkt_sub_info;
    hash_for_each(wrapper->topic.sub_info_htable, bkt_sub_info, sub_info, node)
    {
      ret = scnprintf(buf + used_size, PAGE_SIZE - used_size, " %d,", sub_info->pid);
      used_size += ret;
    }

    ret = scnprintf(buf + used_size, PAGE_SIZE - used_size, "\n\n");
    used_size += ret;
  }

  if (used_size >= PAGE_SIZE) {
    dev_warn(agnocast_device, "Exceeding PAGE_SIZE. Truncating output...\n");
    mutex_unlock(&global_mutex);
    return -ENOSPC;
  }

  mutex_unlock(&global_mutex);
  return used_size;
}

static char * debug_topic_name;

// Example
// $ echo "/my_dynamic_topic" | sudo tee /sys/module/agnocast/status/topic_info
static ssize_t store_topic_name(
  struct kobject * kobj, struct kobj_attribute * attr, const char * buf, size_t count)
{
  mutex_lock(&global_mutex);

  if (debug_topic_name) {
    kfree(debug_topic_name);
  }

  debug_topic_name = kstrdup(buf, GFP_KERNEL);
  if (!debug_topic_name) {
    dev_warn(agnocast_device, "kstrdup failed\n");
  }

  mutex_unlock(&global_mutex);
  return count;
}

// Example
//
// $ sudo cat /sys/module/agnocast/status/topic_info
// topic: /my_dynamic_topic
//  publisher: 9495, 9468,
//  subscription: 9534,
//  entries:
//   time=1731287511550597936, pid=9495, addr=4398118383424, published=1, referencing=[9534,]
//   time=1731287511651085986, pid=9468, addr=4398051231552, published=1, referencing=[]
//   time=1731287511651972687, pid=9495, addr=4398118368832, published=1, referencing=[]
//   time=1731287511752437732, pid=9468, addr=4398050770944, published=1, referencing=[]
static ssize_t show_topic_info(struct kobject * kobj, struct kobj_attribute * attr, char * buf)
{
  mutex_lock(&global_mutex);

  int used_size = 0;
  int ret;

  ret = scnprintf(buf + used_size, PAGE_SIZE - used_size, "topic: %s", debug_topic_name);
  used_size += ret;

  if (!debug_topic_name) {
    mutex_unlock(&global_mutex);
    return ret;
  }

  struct topic_wrapper * wrapper;
  int bkt_topic;
  hash_for_each(topic_hashtable, bkt_topic, wrapper, node)
  {
    if (strncmp(debug_topic_name, wrapper->key, strlen(wrapper->key)) != 0) continue;

    ret = scnprintf(buf + used_size, PAGE_SIZE - used_size, " publisher:");
    used_size += ret;

    struct publisher_info * pub_info;
    int bkt_pub_info;
    hash_for_each(wrapper->topic.pub_info_htable, bkt_pub_info, pub_info, node)
    {
      ret = scnprintf(buf + used_size, PAGE_SIZE - used_size, " %d,", pub_info->pid);
      used_size += ret;
    }

    ret = scnprintf(buf + used_size, PAGE_SIZE - used_size, "\n subscription:");
    used_size += ret;

    struct subscriber_info * sub_info;
    int bkt_sub_info;
    hash_for_each(wrapper->topic.sub_info_htable, bkt_sub_info, sub_info, node)
    {
      ret = scnprintf(buf + used_size, PAGE_SIZE - used_size, " %d,", sub_info->pid);
      used_size += ret;
    }

    ret = scnprintf(buf + used_size, PAGE_SIZE - used_size, "\n entries:\n");
    used_size += ret;

    struct rb_root * root = &wrapper->topic.entries;
    struct rb_node * node;
    for (node = rb_first(root); node; node = rb_next(node)) {
      struct entry_node * en = container_of(node, struct entry_node, node);

      ret = scnprintf(
        buf + used_size, PAGE_SIZE - used_size,
        "  time=%lld, pid=%u, addr=%lld, published=%d, referencing=[", en->timestamp,
        en->publisher_pid, en->msg_virtual_address, en->published);
      used_size += ret;

      for (int i = 0; i < MAX_SUBSCRIBER_NUM; i++) {
        if (en->referencing_subscriber_pids[i] > 0) {
          ret = scnprintf(
            buf + used_size, PAGE_SIZE - used_size, "%u,", en->referencing_subscriber_pids[i]);
          used_size += ret;
        }
      }

      ret = scnprintf(buf + used_size, PAGE_SIZE - used_size, "]\n");
      used_size += ret;
    }
  }

  if (used_size >= PAGE_SIZE) {
    dev_warn(agnocast_device, "Exceeding PAGE_SIZE. Truncating output...\n");
    mutex_unlock(&global_mutex);
    return -ENOSPC;
  }

  mutex_unlock(&global_mutex);
  return used_size;
}

static struct kobject * status_kobj;
static struct kobj_attribute process_attribute = __ATTR(process_list, 0444, show_processes, NULL);
static struct kobj_attribute topics_attribute = __ATTR(topic_list, 0444, show_topics, NULL);
static struct kobj_attribute topic_info_attribute =
  __ATTR(topic_info, 0644, show_topic_info, store_topic_name);

static struct attribute * attrs[] = {
  &process_attribute.attr,
  &topics_attribute.attr,
  &topic_info_attribute.attr,
  NULL,
};

static struct attribute_group attribute_group = {
  .attrs = attrs,
};

// =========================================
// /dev/agnocast
static int get_shm(char * topic_name, union ioctl_subscriber_args * ioctl_ret)
{
  struct topic_wrapper * wrapper = find_topic(topic_name);
  if (!wrapper) {
    dev_warn(agnocast_device, "Topic (topic_name=%s) not found. (get_shm)\n", topic_name);
    return -1;
  }

  int count = get_size_pub_info_htable(wrapper);
  if (count > MAX_PUBLISHER_NUM) {
    dev_warn(
      agnocast_device,
      "The number of publishers for the topic (topic_name=%s) reached the "
      "upper bound (MAX_PUBLISHER_NUM=%d), so no new subscriber can be "
      "added. (get_shm)\n",
      topic_name, MAX_PUBLISHER_NUM);
    return -1;
  }

  int index = 0;
  struct publisher_info * pub_info;
  int bkt;
  hash_for_each(wrapper->topic.pub_info_htable, bkt, pub_info, node)
  {
    if (pub_info->exited) {
      continue;
    }
    ioctl_ret->ret_pids[index] = pub_info->pid;

    struct process_info * proc_info;
    uint32_t hash_val = hash_min(pub_info->pid, PROC_INFO_HASH_BITS);
    hash_for_each_possible(proc_info_htable, proc_info, node, hash_val)
    {
      if (proc_info->pid == pub_info->pid) {
        ioctl_ret->ret_shm_addrs[index] = proc_info->shm_addr;
        ioctl_ret->ret_shm_sizes[index] = proc_info->shm_size;
        index++;
        break;
      }
    }
  }

  ioctl_ret->ret_publisher_num = index;

  return 0;
}

static int subscriber_add(
  char * topic_name, uint32_t qos_depth, uint32_t subscriber_pid, uint64_t init_timestamp,
  bool is_take_sub, union ioctl_subscriber_args * ioctl_ret)
{
  struct topic_wrapper * wrapper = find_topic(topic_name);
  if (!wrapper) {
    wrapper = insert_topic(topic_name);
    if (!wrapper) {
      dev_warn(
        agnocast_device, "Failed to add a new topic (topic_name=%s). (subscriber_add)\n",
        topic_name);
      return -1;
    }
    dev_info(agnocast_device, "Topic (topic_name=%s) added. (subscriber_add)\n", topic_name);
  } else {
    dev_info(
      agnocast_device, "Topic (topic_name=%s) already exists. (subscriber_add)\n", topic_name);
  }

  struct subscriber_info * sub_info = insert_subscriber_info(wrapper, subscriber_pid, is_take_sub);
  if (!sub_info) {
    return -1;
  }
  sub_info->latest_received_timestamp = init_timestamp;

  // Return qos_depth messages in order from newest to oldest for transient local
  ioctl_ret->ret_transient_local_num = 0;
  bool sub_info_updated = false;
  for (struct rb_node * node = rb_last(&wrapper->topic.entries); node; node = rb_prev(node)) {
    // A qos_depth of 0 indicates that transient_local is disabled.
    if (qos_depth <= ioctl_ret->ret_transient_local_num) break;

    struct entry_node * en = container_of(node, struct entry_node, node);
    /*
     * TODO: In the current implementation, the timestamp of the most recently received item is
     * stored in sub_info->latest_received_timestamp. If there are older items that haven't been
     * published yet, they will be ignored, even on the next RECEIVE. To fix this, the
     * implementation should be changed so that items are inserted into the rb_tree only after they
     * are published.
     */
    if (!en->published) {
      continue;
    }

    if (increment_sub_rc(en, subscriber_pid) == -1) {
      dev_warn(
        agnocast_device,
        "The number of subscribers for the entry_node (timestamp=%lld) reached the upper "
        "bound (MAX_SUBSCRIBER_NUM=%d), so no new subscriber can reference."
        " (subscriber_add)\n",
        en->timestamp, MAX_SUBSCRIBER_NUM);
      return -1;
    }

    ioctl_ret->ret_publisher_pids[ioctl_ret->ret_transient_local_num] = en->publisher_pid;
    ioctl_ret->ret_timestamps[ioctl_ret->ret_transient_local_num] = en->timestamp;
    ioctl_ret->ret_last_msg_addrs[ioctl_ret->ret_transient_local_num] = en->msg_virtual_address;
    ioctl_ret->ret_transient_local_num++;

    if (!sub_info_updated) {
      sub_info->latest_received_timestamp = en->timestamp;
      sub_info_updated = true;
    }
  }

  return get_shm(topic_name, ioctl_ret);
}

static int publisher_add(
  const char * topic_name, uint32_t pid, union ioctl_publisher_args * ioctl_ret)
{
  struct topic_wrapper * wrapper = find_topic(topic_name);
  if (!wrapper) {
    wrapper = insert_topic(topic_name);
    if (!wrapper) {
      dev_warn(
        agnocast_device, "Failed to add a new topic (topic_name=%s). (publisher_add)\n",
        topic_name);
      return -1;
    }
    dev_info(agnocast_device, "Topic (topic_name=%s) added. (publisher_add)\n", topic_name);
  } else {
    dev_info(
      agnocast_device, "Topic (topic_name=%s) already exists. (publisher_add)\n", topic_name);
  }

  if (!insert_publisher_info(wrapper, pid)) {
    return -1;
  }

  // set shm addr to ioctl_ret
  struct process_info * proc_info;
  uint32_t hash_val = hash_min(pid, PROC_INFO_HASH_BITS);
  bool proc_info_found = false;
  hash_for_each_possible(proc_info_htable, proc_info, node, hash_val)
  {
    if (proc_info->pid == pid) {
      ioctl_ret->ret_shm_addr = proc_info->shm_addr;
      ioctl_ret->ret_shm_size = proc_info->shm_size;
      proc_info_found = true;
      break;
    }
  }

  if (!proc_info_found) {
    dev_warn(agnocast_device, "Process (pid=%d) not found. (publisher_add)\n", pid);
    return -1;
  }

  // set subscriber info to ioctl_ret
  int index = 0;
  struct subscriber_info * sub_info;
  int bkt_sub_info;
  hash_for_each(wrapper->topic.sub_info_htable, bkt_sub_info, sub_info, node)
  {
    ioctl_ret->ret_subscriber_pids[index] = sub_info->pid;
    index++;
  }
  ioctl_ret->ret_subscriber_len = index;

  dev_info(
    agnocast_device, "Publisher (pid=%d) is added to the topic (topic_name=%s)\n", pid, topic_name);
  return 0;
}

static uint64_t release_msgs_to_meet_depth(
  const char * topic_name, const uint32_t publisher_pid, const uint32_t qos_depth,
  union ioctl_enqueue_and_release_args * ioctl_ret)
{
  ioctl_ret->ret_len = 0;

  struct topic_wrapper * wrapper = find_topic(topic_name);
  if (!wrapper) {
    dev_warn(
      agnocast_device, "Topic (topic_name=%s) not found. (release_msgs_to_meet_depth)\n",
      topic_name);
    return -1;
  }

  struct publisher_info * pub_info = find_publisher_info(wrapper, publisher_pid);
  if (!pub_info) {
    dev_warn(
      agnocast_device,
      "Publisher (pid=%d) not found in the topic (topic_name=%s). (release_msgs_to_meet_depth)\n",
      publisher_pid, topic_name);
    return -1;
  }

  if (pub_info->entries_num <= qos_depth) {
    return 0;
  }

  const uint32_t leak_warn_threshold =
    (qos_depth <= 100) ? 100 + qos_depth : qos_depth * 2;  // This is rough value.
  if (pub_info->entries_num > leak_warn_threshold) {
    dev_warn(
      agnocast_device,
      "For some reason, the reference count hasn't been decremented, causing the number of "
      "messages for this publisher to increase. (publisher_pid=%d, topic_name=%s, entries_num=%d)."
      "(release_msgs_to_meet_depth)\n",
      publisher_pid, topic_name, pub_info->entries_num);
    return -1;
  }

  struct rb_node * node = rb_first(&wrapper->topic.entries);
  if (!node) {
    dev_warn(
      agnocast_device,
      "Failed to get message entries in publisher (pid=%d). (release_msgs_to_meet_depth)\n",
      publisher_pid);
    return -1;
  }

  // Number of entries exceeding qos_depth
  uint32_t num_search_entries = pub_info->entries_num - qos_depth;

  // NOTE:
  //   The searched message is either deleted or, if a reference count remains, is not deleted.
  //   In both cases, this number of searches is sufficient, as it does not affect the Queue size of
  //   QoS.
  //
  // HACK:
  //   The current implementation only releases a maximum of MAX_RELEASE_NUM messages at a time, and
  //   if there are more messages to release, qos_depth is temporarily not met.
  //   However, it is rare for the subscriber_reference_count of more than MAX_RELEASE_NUM messages
  //   that are out of qos_depth to be zero at a specific time. If this happens, as long as the
  //   publisher's qos_depth is greater than the subscriber's qos_depth, this has little effect on
  //   system behavior.
  while (num_search_entries > 0 && ioctl_ret->ret_len < MAX_RELEASE_NUM) {
    struct entry_node * en = container_of(node, struct entry_node, node);
    node = rb_next(node);
    if (!node) {
      dev_warn(
        agnocast_device,
        "entries_num is inconsistent with actual message entry num. "
        "(release_msgs_to_meet_depth)\n");
      return -1;
    }

    if (en->publisher_pid != publisher_pid) continue;

    num_search_entries--;

    // This is not counted in a Queue size of QoS.
    if (is_subscriber_referencing(en)) continue;

    ioctl_ret->ret_released_addrs[ioctl_ret->ret_len] = en->msg_virtual_address;
    ioctl_ret->ret_len++;
    if (decrement_entries_num(wrapper, publisher_pid) == -1) return -1;
    rb_erase(&en->node, &wrapper->topic.entries);
    kfree(en);

    dev_dbg(
      agnocast_device,
      "Release oldest message in the publisher_info (publisher_pid=%d) of the topic "
      "(topic_name=%s) with qos_depth %d. "
      "(release_msgs_to_meet_depth)\n",
      publisher_pid, topic_name, qos_depth);
  }

  return 0;
}

static uint64_t enqueue_and_release(
  const char * topic_name, const uint32_t publisher_pid, const uint32_t qos_depth,
  const uint64_t msg_virtual_address, const uint64_t timestamp,
  union ioctl_enqueue_and_release_args * ioctl_ret)
{
  if (insert_message_entry(topic_name, publisher_pid, msg_virtual_address, timestamp) == -1) {
    return -1;
  }
  return release_msgs_to_meet_depth(topic_name, publisher_pid, qos_depth, ioctl_ret);
}

static int receive_and_update(
  char * topic_name, uint32_t subscriber_pid, uint32_t qos_depth,
  union ioctl_receive_msg_args * ioctl_ret)
{
  struct topic_wrapper * wrapper = find_topic(topic_name);
  if (!wrapper) {
    dev_warn(
      agnocast_device, "Topic (topic_name=%s) not found. (receive_and_update)\n", topic_name);
    return -1;
  }

  struct subscriber_info * sub_info = find_subscriber_info(wrapper, subscriber_pid);

  ioctl_ret->ret_len = 0;
  bool sub_info_updated = false;
  uint64_t prev_latest_received_timestamp = sub_info->latest_received_timestamp;
  for (struct rb_node * node = rb_last(&wrapper->topic.entries); node; node = rb_prev(node)) {
    struct entry_node * en = container_of(node, struct entry_node, node);
    if ((en->timestamp <= prev_latest_received_timestamp) || (qos_depth == ioctl_ret->ret_len)) {
      break;
    }

    /*
     * TODO: In the current implementation, the timestamp of the most recently received item is
     * stored in sub_info->latest_received_timestamp. If there are older items that haven't been
     * published yet, they will be ignored, even on the next RECEIVE. To fix this, the
     * implementation should be changed so that items are inserted into the rb_tree only after they
     * are published.
     */
    if (!en->published) {
      continue;
    }

    if (increment_sub_rc(en, subscriber_pid) == -1) {
      dev_warn(
        agnocast_device,
        "The number of subscribers for the entry_node (timestamp=%lld) reached the upper "
        "bound (MAX_SUBSCRIBER_NUM=%d), so no new subscriber can reference."
        " (receive_and_update)\n",
        en->timestamp, MAX_SUBSCRIBER_NUM);
      return -1;
    }

    ioctl_ret->ret_publisher_pids[ioctl_ret->ret_len] = en->publisher_pid;
    ioctl_ret->ret_timestamps[ioctl_ret->ret_len] = en->timestamp;
    ioctl_ret->ret_last_msg_addrs[ioctl_ret->ret_len] = en->msg_virtual_address;
    ioctl_ret->ret_len++;

    if (!sub_info_updated) {
      sub_info->latest_received_timestamp = en->timestamp;
      sub_info_updated = true;
    }
  }

  return 0;
}

static int publish_msg(
  char * topic_name, uint32_t publisher_pid, uint64_t msg_timestamp,
  union ioctl_publish_args * ioctl_ret)
{
  struct topic_wrapper * wrapper = find_topic(topic_name);
  if (!wrapper) {
    dev_warn(agnocast_device, "Topic (topic_name=%s) not found. (publish_msg)\n", topic_name);
    return -1;
  }

  struct entry_node * en = find_message_entry(wrapper, publisher_pid, msg_timestamp);
  if (!en) {
    dev_warn(
      agnocast_device,
      "Message entry (topic_name=%s publisher_pid=%d timestamp=%lld) not found. "
      "(publish_msg)\n",
      topic_name, publisher_pid, msg_timestamp);
    return -1;
  }

  if (en->published) {
    dev_warn(
      agnocast_device,
      "Tried to publish a message that has already been published. (topic_name=%s publisher_pid=%d "
      "timestamp=%lld). (publish_msg)\n",
      topic_name, publisher_pid, msg_timestamp);
    return -1;
  }

  int index = 0;
  struct subscriber_info * sub_info;
  int bkt_sub_info;
  hash_for_each(wrapper->topic.sub_info_htable, bkt_sub_info, sub_info, node)
  {
    if (sub_info->is_take_sub) continue;
    ioctl_ret->ret_pids[index] = sub_info->pid;
    index++;
  }
  ioctl_ret->ret_len = index;

  en->published = true;

  return 0;
}

static int take_msg(
  char * topic_name, uint32_t subscriber_pid, uint32_t qos_depth,
  union ioctl_take_msg_args * ioctl_ret)
{
  struct topic_wrapper * wrapper = find_topic(topic_name);
  if (!wrapper) {
    dev_warn(agnocast_device, "Topic (topic_name=%s) not found. (take_msg)\n", topic_name);
    return -1;
  }
  struct subscriber_info * sub_info = find_subscriber_info(wrapper, subscriber_pid);

  // These remains 0 if no message is found to take.
  ioctl_ret->ret_addr = 0;
  ioctl_ret->ret_timestamp = 0;
  ioctl_ret->ret_publisher_pid = 0;

  uint32_t searched_count = 0;
  struct entry_node * candidate_en = NULL;
  struct rb_node * node = rb_last(&wrapper->topic.entries);
  while (node && searched_count < qos_depth) {
    struct entry_node * en = container_of(node, struct entry_node, node);
    if (en->timestamp <= sub_info->latest_received_timestamp) {
      break;  // Never take any messages that are older than the most recently received
    }
    if (en->published) candidate_en = en;
    searched_count++;
    node = rb_prev(node);
  }

  if (!candidate_en) return 0;

  if (increment_sub_rc(candidate_en, subscriber_pid) == -1) {
    dev_warn(
      agnocast_device,
      "The number of subscribers for the entry_node (timestamp=%lld) reached the upper "
      "bound (MAX_SUBSCRIBER_NUM=%d), so no new subscriber can reference."
      " (take_msg)\n",
      candidate_en->timestamp, MAX_SUBSCRIBER_NUM);
    return -1;
  }

  ioctl_ret->ret_addr = candidate_en->msg_virtual_address;
  ioctl_ret->ret_timestamp = candidate_en->timestamp;
  ioctl_ret->ret_publisher_pid = candidate_en->publisher_pid;

  sub_info->latest_received_timestamp = ioctl_ret->ret_timestamp;

  return 0;
}

static int new_shm_addr(uint32_t pid, uint64_t shm_size, union ioctl_new_shm_args * ioctl_ret)
{
  // TODO: assume 0x40000000000~ (4398046511104) is allocatable
  static uint64_t allocatable_addr = 0x40000000000;

  struct process_info * new_proc_info = kmalloc(sizeof(struct process_info), GFP_KERNEL);
  new_proc_info->pid = pid;
  new_proc_info->shm_addr = allocatable_addr;
  new_proc_info->shm_size = shm_size;

  INIT_HLIST_NODE(&new_proc_info->node);
  uint32_t hash_val = hash_min(new_proc_info->pid, PROC_INFO_HASH_BITS);
  hash_add(proc_info_htable, &new_proc_info->node, hash_val);

  allocatable_addr += shm_size;

  ioctl_ret->ret_addr = new_proc_info->shm_addr;
  return 0;
}

static int get_subscriber_num(char * topic_name, union ioctl_get_subscriber_num_args * ioctl_ret)
{
  struct topic_wrapper * wrapper = find_topic(topic_name);
  if (!wrapper) {
    dev_warn(
      agnocast_device, "Topic (topic_name=%s) not found. (get_subscription_num)\n", topic_name);
    return -1;
  }

  ioctl_ret->ret_subscriber_num = get_size_sub_info_htable(wrapper);

  return 0;
}

static long agnocast_ioctl(struct file * file, unsigned int cmd, unsigned long arg)
{
  mutex_lock(&global_mutex);
  int ret = 0;
  char topic_name_buf[256];
  union ioctl_subscriber_args sub_args;
  union ioctl_publisher_args pub_args;
  union ioctl_enqueue_and_release_args enqueue_release_args;
  union ioctl_update_entry_args entry_args;
  union ioctl_receive_msg_args receive_msg_args;
  union ioctl_publish_args publish_args;
  union ioctl_take_msg_args take_args;
  union ioctl_new_shm_args new_shm_args;
  union ioctl_get_subscriber_num_args get_subscriber_num_args;

  switch (cmd) {
    case AGNOCAST_SUBSCRIBER_ADD_CMD:
      if (copy_from_user(&sub_args, (union ioctl_subscriber_args __user *)arg, sizeof(sub_args)))
        goto unlock_mutex_and_return;
      if (copy_from_user(
            topic_name_buf, (char __user *)sub_args.topic_name, sizeof(topic_name_buf)))
        goto unlock_mutex_and_return;
      ret = subscriber_add(
        topic_name_buf, sub_args.qos_depth, sub_args.subscriber_pid, sub_args.init_timestamp,
        sub_args.is_take_sub, &sub_args);
      if (copy_to_user((union ioctl_subscriber_args __user *)arg, &sub_args, sizeof(sub_args)))
        goto unlock_mutex_and_return;
      break;
    case AGNOCAST_PUBLISHER_ADD_CMD:
      if (copy_from_user(&pub_args, (union ioctl_publisher_args __user *)arg, sizeof(pub_args)))
        goto unlock_mutex_and_return;
      if (copy_from_user(
            topic_name_buf, (char __user *)pub_args.topic_name, sizeof(topic_name_buf)))
        goto unlock_mutex_and_return;
      ret = publisher_add(topic_name_buf, pub_args.publisher_pid, &pub_args);
      if (copy_to_user((union ioctl_publisher_args __user *)arg, &pub_args, sizeof(pub_args)))
        goto unlock_mutex_and_return;
      break;
    case AGNOCAST_ENQUEUE_AND_RELEASE_CMD:
      if (copy_from_user(
            &enqueue_release_args, (union ioctl_enqueue_and_release_args __user *)arg,
            sizeof(enqueue_release_args)))
        goto unlock_mutex_and_return;
      if (copy_from_user(
            topic_name_buf, (char __user *)enqueue_release_args.topic_name, sizeof(topic_name_buf)))
        goto unlock_mutex_and_return;
      ret = enqueue_and_release(
        topic_name_buf, enqueue_release_args.publisher_pid, enqueue_release_args.qos_depth,
        enqueue_release_args.msg_virtual_address, enqueue_release_args.timestamp,
        &enqueue_release_args);
      if (copy_to_user((uint64_t __user *)arg, &enqueue_release_args, sizeof(enqueue_release_args)))
        goto unlock_mutex_and_return;
      break;
    case AGNOCAST_INCREMENT_RC_CMD:
      if (copy_from_user(
            &entry_args, (union ioctl_update_entry_args __user *)arg, sizeof(entry_args)))
        goto unlock_mutex_and_return;
      if (copy_from_user(
            topic_name_buf, (char __user *)entry_args.topic_name, sizeof(topic_name_buf)))
        goto unlock_mutex_and_return;
      ret = increment_message_entry_rc(
        topic_name_buf, entry_args.subscriber_pid, entry_args.publisher_pid,
        entry_args.msg_timestamp);
      break;
    case AGNOCAST_DECREMENT_RC_CMD:
      if (copy_from_user(
            &entry_args, (union ioctl_update_entry_args __user *)arg, sizeof(entry_args)))
        goto unlock_mutex_and_return;
      if (copy_from_user(
            topic_name_buf, (char __user *)entry_args.topic_name, sizeof(topic_name_buf)))
        goto unlock_mutex_and_return;
      ret = decrement_message_entry_rc(
        topic_name_buf, entry_args.subscriber_pid, entry_args.publisher_pid,
        entry_args.msg_timestamp);
      break;
    case AGNOCAST_RECEIVE_MSG_CMD:
      if (copy_from_user(
            &receive_msg_args, (union ioctl_receive_msg_args __user *)arg,
            sizeof(receive_msg_args)))
        goto unlock_mutex_and_return;
      if (copy_from_user(
            topic_name_buf, (char __user *)receive_msg_args.topic_name, sizeof(topic_name_buf)))
        goto unlock_mutex_and_return;
      ret = receive_and_update(
        topic_name_buf, receive_msg_args.subscriber_pid, receive_msg_args.qos_depth,
        &receive_msg_args);
      if (copy_to_user(
            (union ioctl_receive_msg_args __user *)arg, &receive_msg_args,
            sizeof(receive_msg_args)))
        goto unlock_mutex_and_return;
      break;
    case AGNOCAST_PUBLISH_MSG_CMD:
      if (copy_from_user(
            &publish_args, (union ioctl_publish_args __user *)arg, sizeof(publish_args)))
        goto unlock_mutex_and_return;
      if (copy_from_user(
            topic_name_buf, (char __user *)publish_args.topic_name, sizeof(topic_name_buf)))
        goto unlock_mutex_and_return;
      ret = publish_msg(
        topic_name_buf, publish_args.publisher_pid, publish_args.msg_timestamp, &publish_args);
      if (copy_to_user((union ioctl_publish_args __user *)arg, &publish_args, sizeof(publish_args)))
        goto unlock_mutex_and_return;
      break;
    case AGNOCAST_TAKE_MSG_CMD:
      if (copy_from_user(&take_args, (union ioctl_take_msg_args __user *)arg, sizeof(take_args)))
        goto unlock_mutex_and_return;
      if (copy_from_user(
            topic_name_buf, (char __user *)take_args.topic_name, sizeof(topic_name_buf)))
        goto unlock_mutex_and_return;
      ret = take_msg(topic_name_buf, take_args.subscriber_pid, take_args.qos_depth, &take_args);
      if (copy_to_user((union ioctl_take_msg_args __user *)arg, &take_args, sizeof(take_args)))
        goto unlock_mutex_and_return;
      break;
    case AGNOCAST_NEW_SHM_CMD:
      if (copy_from_user(
            &new_shm_args, (union ioctl_new_shm_args __user *)arg, sizeof(new_shm_args)))
        goto unlock_mutex_and_return;
      ret = new_shm_addr(new_shm_args.pid, new_shm_args.shm_size, &new_shm_args);
      if (copy_to_user((union ioctl_new_shm_args __user *)arg, &new_shm_args, sizeof(new_shm_args)))
        goto unlock_mutex_and_return;
      break;
    case AGNOCAST_GET_SUBSCRIBER_NUM_CMD:
      if (copy_from_user(
            &get_subscriber_num_args, (union ioctl_get_subscriber_num_args __user *)arg,
            sizeof(get_subscriber_num_args)))
        goto unlock_mutex_and_return;
      if (copy_from_user(
            topic_name_buf, (char __user *)get_subscriber_num_args.topic_name,
            sizeof(topic_name_buf)))
        goto unlock_mutex_and_return;
      ret = get_subscriber_num(topic_name_buf, &get_subscriber_num_args);
      if (copy_to_user(
            (union ioctl_get_subscriber_num_args __user *)arg, &get_subscriber_num_args,
            sizeof(get_subscriber_num_args)))
        goto unlock_mutex_and_return;
      break;
    default:
      mutex_unlock(&global_mutex);
      return -EINVAL;
  }

  mutex_unlock(&global_mutex);
  return ret;

unlock_mutex_and_return:
  mutex_unlock(&global_mutex);
  return -EFAULT;
}

#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 2, 0)
static char * agnocast_devnode(const struct device * dev, umode_t * mode)
#else
static char * agnocast_devnode(struct device * dev, umode_t * mode)
#endif
{
  if (mode) {
    *mode = 0666;
  }
  return NULL;
}

static struct file_operations fops = {
  .unlocked_ioctl = agnocast_ioctl,
};

// =========================================
// Handler for publisher process exit
static void remove_entry_node(struct topic_wrapper * wrapper, struct entry_node * en)
{
  rb_erase(&en->node, &wrapper->topic.entries);
  kfree(en);
}

static struct publisher_info * set_exited_if_publisher(struct topic_wrapper * wrapper)
{
  struct publisher_info * pub_info;
  uint32_t hash_val = hash_min(current->pid, PUB_INFO_HASH_BITS);
  hash_for_each_possible(wrapper->topic.pub_info_htable, pub_info, node, hash_val)
  {
    if (pub_info->pid != current->pid) {
      continue;
    }
    pub_info->exited = true;
    return pub_info;
  }
  return NULL;
}

static void remove_publisher_info(struct topic_wrapper * wrapper, uint32_t publisher_pid)
{
  struct publisher_info * pub_info;
  struct hlist_node * tmp;
  uint32_t hash_val = hash_min(publisher_pid, PUB_INFO_HASH_BITS);
  hash_for_each_possible_safe(wrapper->topic.pub_info_htable, pub_info, tmp, node, hash_val)
  {
    if (pub_info->pid != publisher_pid) {
      continue;
    }

    hash_del(&pub_info->node);
    kfree(pub_info);
    break;
  }
}

static void pre_handler_publisher_exit(struct topic_wrapper * wrapper)
{
  struct publisher_info * pub_info = set_exited_if_publisher(wrapper);
  if (!pub_info) return;

  struct rb_root * root = &wrapper->topic.entries;
  struct rb_node * node = rb_first(root);
  while (node) {
    struct entry_node * en = rb_entry(node, struct entry_node, node);
    node = rb_next(node);
    if (en->publisher_pid == current->pid && !is_subscriber_referencing(en)) {
      pub_info->entries_num--;
      remove_entry_node(wrapper, en);
    }
  }

  if (pub_info->entries_num == 0) {
    remove_publisher_info(wrapper, current->pid);
  }

  dev_info(
    agnocast_device,
    "Publisher exit handler (pid=%d) on topic (topic_name=%s) has finished executing. "
    "(pre_handler_publisher)\n",
    current->pid, wrapper->key);
}

static bool remove_if_subscriber(struct topic_wrapper * wrapper)
{
  struct subscriber_info * sub_info;
  struct hlist_node * tmp;
  uint32_t hash_val = hash_min(current->pid, SUB_INFO_HASH_BITS);
  bool is_subscriber = false;
  hash_for_each_possible_safe(wrapper->topic.sub_info_htable, sub_info, tmp, node, hash_val)
  {
    if (sub_info->pid != current->pid) {
      continue;
    }

    hash_del(&sub_info->node);
    kfree(sub_info);
    is_subscriber = true;
    break;
  }

  return is_subscriber;
}

static bool remove_if_referencing_subscriber(struct entry_node * en)
{
  int index = get_referencing_subscriber_index(en, current->pid);
  if (index == -1) return false;

  remove_referencing_subscriber_by_index(en, index);
  return true;
}

static void pre_handler_subscriber_exit(struct topic_wrapper * wrapper)
{
  if (!remove_if_subscriber(wrapper)) return;

  // Decrement the reference count, then free the entry node if it reaches zero and publisher has
  // already exited.
  struct rb_root * root = &wrapper->topic.entries;
  struct rb_node * node = rb_first(root);
  while (node) {
    struct entry_node * en = rb_entry(node, struct entry_node, node);
    node = rb_next(node);
    if (!remove_if_referencing_subscriber(en)) continue;

    if (is_subscriber_referencing(en)) continue;

    bool publisher_exited = false;
    struct publisher_info * pub_info;
    uint32_t hash_val = hash_min(en->publisher_pid, PUB_INFO_HASH_BITS);
    hash_for_each_possible(wrapper->topic.pub_info_htable, pub_info, node, hash_val)
    {
      if (pub_info->pid == en->publisher_pid) {
        if (pub_info->exited) publisher_exited = true;
        break;
      }
    }
    if (!publisher_exited) continue;

    pub_info->entries_num--;
    remove_entry_node(wrapper, en);
    if (pub_info->entries_num == 0) {
      remove_publisher_info(wrapper, pub_info->pid);
    }
  }

  dev_info(
    agnocast_device,
    "Subscriber exit handler (pid=%d) on topic (topic_name=%s) has finished executing. "
    "(pre_handler_subscriber)\n",
    current->pid, wrapper->key);
}

static int pre_handler_do_exit(struct kprobe * p, struct pt_regs * regs)
{
  mutex_lock(&global_mutex);

  // Quickly determine if it is an Agnocast-related process.
  struct process_info * proc_info;
  struct hlist_node * tmp;
  uint32_t hash_val = hash_min(current->pid, PROC_INFO_HASH_BITS);
  bool agnocast_related = false;
  hash_for_each_possible_safe(proc_info_htable, proc_info, tmp, node, hash_val)
  {
    if (proc_info->pid == current->pid) {
      hash_del(&proc_info->node);
      kfree(proc_info);
      agnocast_related = true;
      break;
    }
  }

  if (!agnocast_related) {
    mutex_unlock(&global_mutex);
    return 0;
  }

  struct topic_wrapper * wrapper;
  struct hlist_node * node;
  int bkt;
  hash_for_each_safe(topic_hashtable, bkt, node, wrapper, node)
  {
    pre_handler_publisher_exit(wrapper);

    pre_handler_subscriber_exit(wrapper);

    // Check if we can release the topic_wrapper
    if (get_size_pub_info_htable(wrapper) == 0 && get_size_sub_info_htable(wrapper) == 0) {
      hash_del(&wrapper->node);
      if (wrapper->key) {
        kfree(wrapper->key);
      }
      kfree(wrapper);
    }
  }

  mutex_unlock(&global_mutex);
  return 0;
}

static struct kprobe kp = {
  .symbol_name = "do_exit",
  .pre_handler = pre_handler_do_exit,
};

// =========================================

static int agnocast_init(void)
{
  mutex_init(&global_mutex);

  status_kobj = kobject_create_and_add("status", &THIS_MODULE->mkobj.kobj);
  if (!status_kobj) {
    return -ENOMEM;
  }

  int ret = sysfs_create_group(status_kobj, &attribute_group);
  if (ret) {
    // Decrement reference count
    kobject_put(status_kobj);
  }

  major = register_chrdev(0, "agnocast" /*device driver name*/, &fops);

#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 3, 0)
  agnocast_class = class_create("agnocast_class");
#else
  agnocast_class = class_create(THIS_MODULE, "agnocast_class");
#endif

  agnocast_class->devnode = agnocast_devnode;
  agnocast_device =
    device_create(agnocast_class, NULL, MKDEV(major, 0), NULL, "agnocast" /*file name*/);

  ret = register_kprobe(&kp);
  if (ret < 0) {
    dev_warn(agnocast_device, "register_kprobe failed, returned %d. (agnocast_init)\n", ret);
    return ret;
  }

  dev_info(agnocast_device, "Agnocast installed!\n");

  return 0;
}

static void remove_all_topics(void)
{
  struct topic_wrapper * wrapper;
  struct hlist_node * tmp;
  int bkt;

  hash_for_each_safe(topic_hashtable, bkt, tmp, wrapper, node)
  {
    struct rb_root * root = &wrapper->topic.entries;
    struct rb_node * node = rb_first(root);
    while (node) {
      struct entry_node * en = rb_entry(node, struct entry_node, node);
      node = rb_next(node);
      remove_entry_node(wrapper, en);
    }

    struct publisher_info * pub_info;
    int bkt_pub_info;
    struct hlist_node * tmp_pub_info;
    hash_for_each_safe(wrapper->topic.pub_info_htable, bkt_pub_info, tmp_pub_info, pub_info, node)
    {
      hash_del(&pub_info->node);
      kfree(pub_info);
    }

    hash_del(&wrapper->node);
    kfree(wrapper->key);
    kfree(wrapper);
  }
}

static void remove_all_process_info(void)
{
  struct process_info * proc_info;
  int bkt;
  struct hlist_node * tmp;
  hash_for_each_safe(proc_info_htable, bkt, tmp, proc_info, node)
  {
    hash_del(&proc_info->node);
    kfree(proc_info);
  }
}

static void agnocast_exit(void)
{
  mutex_lock(&global_mutex);
  remove_all_topics();
  remove_all_process_info();
  mutex_unlock(&global_mutex);

  dev_info(agnocast_device, "Agnocast removed!\n");

  // Decrement reference count
  kobject_put(status_kobj);

  device_destroy(agnocast_class, MKDEV(major, 0));
  class_destroy(agnocast_class);
  unregister_chrdev(major, "agnocast");

  unregister_kprobe(&kp);
}

module_init(agnocast_init) module_exit(agnocast_exit)
