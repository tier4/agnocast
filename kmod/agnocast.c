#include <linux/device.h>
#include <linux/fs.h>
#include <linux/hash.h>       // hash_64
#include <linux/hashtable.h>  // hash table utilities
#include <linux/init.h>
#include <linux/kernel.h>
#include <linux/kobject.h>
#include <linux/kprobes.h>
#include <linux/module.h>
#include <linux/rbtree.h>
#include <linux/slab.h>    // kmalloc, kfree
#include <linux/string.h>  // strcmp, strdup
#include <linux/sysfs.h>
#include <linux/uaccess.h>
#include <linux/version.h>

MODULE_LICENSE("Dual BSD/GPL");

static int major;
static struct class * agnocast_class;
static struct device * agnocast_device;

// TODO: should be made larger when applied for Autoware
#define MAX_PUBLISHER_NUM 2   // At least 2 is required for sample application
#define MAX_SUBSCRIBER_NUM 8  // At least 6 is required for pointcloud topic in Autoware

// =========================================
// data structure

#define AGNOCAST_HASH_BITS 10  // hash table size : 2^AGNOCAST_HASH_BITS

// TODO: data structures for mapping pid to shm_addr during initialization
#define MAX_PROCESS_NUM 1024
uint32_t pid_index = 0;
uint32_t process_ids[MAX_PROCESS_NUM];
uint64_t shm_addrs[MAX_PROCESS_NUM];

// TODO: assume 0x40000000000~ is allocatable
uint64_t allocatable_addr = 0x40000000000;

struct publisher_info
{
  uint32_t pid;
  uint32_t entries_num;
  struct publisher_info * next;
};

struct topic_struct
{
  uint32_t entries_num;
  struct rb_root entries;
  struct publisher_info *
    pub_info;  // This linked list also includes publishers that have already exited.
  uint32_t non_exited_publisher_num;
  uint32_t non_exited_publisher_pids[MAX_PUBLISHER_NUM];
  unsigned int subscriber_num;
  uint32_t subscriber_pids[MAX_SUBSCRIBER_NUM];
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
  uint32_t subscriber_reference_count;
  uint32_t referencing_subscriber_pids[MAX_SUBSCRIBER_NUM];
  bool published;
  /*
   * NOTE:
   *   unreceived_subscriber_count currently has no effect on the release timing of the message.
   *   It is retained for future use such as early release or logging. However, since the count
   *   is not correctly decremented when a subscriber exits, the value of
   *   unreceived_subscriber_count becomes unreliable as soon as even one subscriber exits.
   */
  uint32_t unreceived_subscriber_count;
};

DEFINE_HASHTABLE(topic_hashtable, AGNOCAST_HASH_BITS);

static unsigned long agnocast_hash(const char * str)
{
  unsigned long hash = full_name_hash(NULL /*namespace*/, str, strlen(str));
  return hash_min(hash, AGNOCAST_HASH_BITS);
}

static int insert_topic(const char * topic_name)
{
  struct topic_wrapper * wrapper = kmalloc(sizeof(struct topic_wrapper), GFP_KERNEL);
  if (!wrapper) {
    dev_warn(agnocast_device, "kmalloc failed. (insert_topic)\n");
    return -1;
  }

  wrapper->key = kstrdup(topic_name, GFP_KERNEL);
  if (!wrapper->key) {
    dev_warn(agnocast_device, "kstrdup failed. (insert_topic)\n");
    kfree(wrapper);
    return -1;
  }

  wrapper->topic.entries_num = 0;
  wrapper->topic.entries = RB_ROOT;
  wrapper->topic.pub_info = NULL;
  wrapper->topic.non_exited_publisher_num = 0;
  for (int i = 0; i < MAX_PUBLISHER_NUM; i++) {
    wrapper->topic.non_exited_publisher_pids[i] = 0;
  }
  wrapper->topic.subscriber_num = 0;
  for (int i = 0; i < MAX_SUBSCRIBER_NUM; i++) {
    wrapper->topic.subscriber_pids[i] = 0;
  }

  hash_add(topic_hashtable, &wrapper->node, agnocast_hash(topic_name));
  return 0;
}

static struct topic_wrapper * find_topic(const char * topic_name)
{
  struct topic_wrapper * entry;
  unsigned long hash_val = agnocast_hash(topic_name);

  hash_for_each_possible(topic_hashtable, entry, node, hash_val)
  {
    if (strcmp(entry->key, topic_name) == 0) return entry;
  }

  return NULL;
}

static int insert_subscriber_pid(const char * topic_name, uint32_t pid)
{
  struct topic_wrapper * wrapper = find_topic(topic_name);
  if (!wrapper) {
    dev_warn(
      agnocast_device, "Topic (topic_name=%s) not found. (insert_subscriber_pid)\n", topic_name);
    return -1;
  }

  // check whether subscriber_pids is full
  if (wrapper->topic.subscriber_num == MAX_SUBSCRIBER_NUM) {
    dev_warn(
      agnocast_device,
      "The number of subscribers for the topic (topic_name=%s) reached the upper "
      "bound (MAX_SUBSCRIBER_NUM=%d), so no new subscriber can be "
      "added. (insert_subscriber_pid)\n",
      topic_name, MAX_SUBSCRIBER_NUM);
    return -1;
  }

  // check whether pid already exists in subscriber_pids
  for (int i = 0; i < wrapper->topic.subscriber_num; i++) {
    if (pid == wrapper->topic.subscriber_pids[i]) {
      dev_warn(
        agnocast_device,
        "Subscriber (pid=%d) already exists in the topic (topic_name=%s). "
        "(insert_subscriber_pid)\n",
        pid, topic_name);
      return -1;
    }
  }

  wrapper->topic.subscriber_pids[wrapper->topic.subscriber_num] = pid;
  wrapper->topic.subscriber_num++;

  dev_info(
    agnocast_device,
    "Subscriber (pid=%d) is added to the topic (topic_name=%s). (insert_subscriber_pid)\n", pid,
    topic_name);
  return 0;
}

static struct publisher_info * find_publisher_info(
  const struct topic_wrapper * wrapper, uint32_t publisher_pid)
{
  struct publisher_info * info = wrapper->topic.pub_info;
  while (info) {
    if (publisher_pid == info->pid) {
      return info;
    }

    info = info->next;
  }

  return NULL;
}

static int insert_publisher_info(struct topic_wrapper * wrapper, uint32_t publisher_pid)
{
  struct publisher_info * info = find_publisher_info(wrapper, publisher_pid);
  if (info) {
    dev_warn(
      agnocast_device,
      "Publisher (pid=%d) already exists in the topic (topic_name=%s). "
      "(insert_publisher_info)\n",
      publisher_pid, wrapper->key);
    return -1;
  }

  struct publisher_info * new_info = kmalloc(sizeof(struct publisher_info), GFP_KERNEL);
  if (!new_info) {
    dev_warn(agnocast_device, "kmalloc failed. (insert_publisher_info)\n");
    return -1;
  }

  new_info->pid = publisher_pid;
  new_info->entries_num = 0;
  new_info->next = wrapper->topic.pub_info;
  wrapper->topic.pub_info = new_info;

  return 0;
}

static int increment_publisher_info(struct topic_wrapper * wrapper, uint32_t publisher_pid)
{
  struct publisher_info * info = find_publisher_info(wrapper, publisher_pid);
  if (info) {
    dev_warn(
      agnocast_device,
      "Publisher (pid=%d) doesn't exist in the topic (topic_name=%s). "
      "(increment_publisher_info)\n",
      publisher_pid, wrapper->key);
    return -1;
  }
  info->entries_num++;

  return 0;
}

static int decrement_publisher_info(struct topic_wrapper * wrapper, uint32_t publisher_pid)
{
  struct publisher_info * info = find_publisher_info(wrapper, publisher_pid);
  if (info) {
    dev_warn(
      agnocast_device,
      "Publisher (pid=%d) doesn't exist in the topic (topic_name=%s). "
      "(decrement_publisher_info)\n",
      publisher_pid, wrapper->key);
    return -1;
  }
  info->entries_num--;

  return 0;
}

static struct entry_node * find_message_entry(
  const char * topic_name, uint32_t publisher_pid, uint64_t msg_timestamp)
{
  struct topic_wrapper * wrapper = find_topic(topic_name);
  if (!wrapper) {
    dev_warn(
      agnocast_device, "Topic (topic_name=%s) not found. (find_message_entry)\n", topic_name);
    return NULL;
  }

  struct rb_root * root = &wrapper->topic.entries;
  struct rb_node ** new = &(root->rb_node);

  while (*new) {
    struct entry_node * this = container_of(*new, struct entry_node, node);

    if (msg_timestamp < this->timestamp) {
      new = &((*new)->rb_left);
    } else if (msg_timestamp > this->timestamp) {
      new = &((*new)->rb_right);
    } else {  // It is not expected for there to be messages with exactly the same timestamp.
      return this;
    }
  }

  return NULL;
}

static int decrement_message_entry_rc(
  const char * topic_name, uint32_t subscriber_pid, uint32_t publisher_pid, uint64_t msg_timestamp)
{
  struct entry_node * en = find_message_entry(topic_name, publisher_pid, msg_timestamp);
  if (!en) {
    dev_warn(
      agnocast_device,
      "Message entry (topic_name=%s publisher_pid=%d timestamp=%lld) not found. "
      "(decrement_message_entry_rc)\n",
      topic_name, publisher_pid, msg_timestamp);
    return -1;
  }

  bool referencing = false;
  for (int i = 0; i < en->subscriber_reference_count; i++) {
    if (en->referencing_subscriber_pids[i] == subscriber_pid) {
      referencing = true;
    }
    if (referencing && i < MAX_SUBSCRIBER_NUM - 1) {
      en->referencing_subscriber_pids[i] = en->referencing_subscriber_pids[i + 1];
    }
  }
  if (!referencing) {
    dev_warn(
      agnocast_device,
      "Subscriber (pid=%d) is not referencing (topic_name=%s publisher_pid=%d "
      "timestamp=%lld). (decrement_message_entry_rc)\n",
      subscriber_pid, topic_name, publisher_pid, msg_timestamp);
    return -1;
  }
  en->subscriber_reference_count--;
  return 0;
}

static int insert_message_entry(
  const char * topic_name, uint32_t publisher_pid, uint64_t msg_virtual_address, uint64_t timestamp)
{
  struct topic_wrapper * wrapper = find_topic(topic_name);
  if (!wrapper) {
    dev_warn(
      agnocast_device, "Topic (topic_name=%s) not found. (find_message_entry)\n", topic_name);
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
  new_node->subscriber_reference_count = 0;
  for (int i = 0; i < MAX_SUBSCRIBER_NUM; i++) {
    new_node->referencing_subscriber_pids[i] = 0;
  }
  new_node->unreceived_subscriber_count = 0;
  new_node->published = false;

  rb_link_node(&new_node->node, parent, new);
  rb_insert_color(&new_node->node, root);

  if (increment_publisher_info(wrapper, publisher_pid) == -1) return -1;
  wrapper->topic.entries_num++;

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

static int value;

static ssize_t show_name(struct kobject * kobj, struct kobj_attribute * attr, char * buf)
{
  return scnprintf(buf, PAGE_SIZE, "agnocast\n");
}

static ssize_t show_value(struct kobject * kobj, struct kobj_attribute * attr, char * buf)
{
  return scnprintf(buf, PAGE_SIZE, "%d\n", value);
}

static ssize_t store_value(
  struct kobject * kobj, struct kobj_attribute * attr, const char * buf, size_t count)
{
  int res = kstrtoint(buf, 10, &value);
  if (res < 0) {
    return res;
  }
  return count;
}

#define BUFFER_SIZE 30
static ssize_t show_all(struct kobject * kobj, struct kobj_attribute * attr, char * buf)
{
  // TODO: Implement show_all for debugging.

  return -1;
}

static struct kobject * status_kobj;
static struct kobj_attribute name_attribute = __ATTR(name, 0444, show_name, NULL);
static struct kobj_attribute value_attribute = __ATTR(value, 0644, show_value, store_value);
static struct kobj_attribute all_attribute = __ATTR(all, 0444, show_all, NULL);

static struct attribute * attrs[] = {
  &name_attribute.attr,
  &value_attribute.attr,
  &all_attribute.attr,
  NULL,
};

static struct attribute_group attribute_group = {
  .attrs = attrs,
};

// =========================================
// /dev/agnocast

#define AGNOCAST_TOPIC_ADD_PUB_CMD _IOW('T', 1, char *)
static int topic_add_pub(const char * topic_name)
{
  struct topic_wrapper * wrapper = find_topic(topic_name);
  if (wrapper) {
    dev_info(
      agnocast_device, "Topic (topic_name=%s) already exists. (topic_add_pub)\n", topic_name);
    return 0;
  }

  if (insert_topic(topic_name) < 0) {
    dev_warn(
      agnocast_device, "Failed to add a new topic (topic_name=%s). (topic_add_pub)\n", topic_name);
    return -1;
  }

  dev_info(agnocast_device, "Topic (topic_name=%s) added. (topic_add_pub)\n", topic_name);
  return 0;
}

#define MAX_QOS_DEPTH 10  // Maximum depth of transient local usage part in Autoware

union ioctl_add_topic_sub_args {
  struct
  {
    char * topic_name;
    uint32_t qos_depth;
    uint32_t subscriber_pid;
  };
  struct
  {
    uint32_t ret_len;
    uint32_t ret_publisher_pids[MAX_QOS_DEPTH];
    uint64_t ret_timestamps[MAX_QOS_DEPTH];
    uint64_t ret_last_msg_addrs[MAX_QOS_DEPTH];
  };
};

union ioctl_subscriber_args {
  struct
  {
    char * topic_name;
    uint32_t pid;
  };
  struct
  {
    uint32_t ret_publisher_num;
    uint32_t ret_pids[MAX_PUBLISHER_NUM];
    uint64_t ret_addrs[MAX_PUBLISHER_NUM];
  };
};

union ioctl_publisher_args {
  struct
  {
    const char * topic_name;
    uint32_t publisher_pid;
  };
  struct
  {
    uint64_t ret_shm_addr;
    uint32_t ret_subscriber_len;
    uint32_t ret_subscriber_pids[MAX_SUBSCRIBER_NUM];
  };
};

union ioctl_update_entry_args {
  struct
  {
    char * topic_name;
    uint32_t subscriber_pid;
    uint32_t publisher_pid;
    uint64_t msg_timestamp;
  };
  uint64_t ret;
};

union ioctl_receive_msg_args {
  struct
  {
    char * topic_name;
    uint32_t subscriber_pid;
    uint32_t publisher_pid;
    uint64_t msg_timestamp;
    uint32_t qos_depth;
  };
  uint64_t ret;
};

union ioctl_publish_args {
  struct
  {
    char * topic_name;
    uint32_t publisher_pid;
    uint64_t msg_timestamp;
  };
  struct
  {
    uint32_t ret_pids[MAX_SUBSCRIBER_NUM];
    uint32_t ret_len;
  };
};

union ioctl_enqueue_and_release_args {
  struct
  {
    char * topic_name;
    uint32_t publisher_pid;
    uint32_t qos_depth;
    uint64_t msg_virtual_address;
    uint64_t timestamp;
  };
  struct
  {
    uint32_t ret_len;
    uint64_t ret_released_addrs[MAX_QOS_DEPTH];  // TODO: reconsider length
  };
};

union ioctl_new_shm_args {
  uint32_t pid;
  uint64_t ret_addr;
};

union ioctl_get_subscriber_num_args {
  const char * topic_name;
  uint32_t ret_subscriber_num;
};

#define AGNOCAST_TOPIC_ADD_SUB_CMD _IOW('T', 2, union ioctl_add_topic_sub_args)
static int topic_add_sub(
  const char * topic_name, uint32_t qos_depth, uint32_t subscriber_pid,
  union ioctl_add_topic_sub_args * ioctl_ret)
{
  ioctl_ret->ret_len = 0;
  struct topic_wrapper * wrapper = find_topic(topic_name);
  if (wrapper) {
    dev_info(
      agnocast_device, "Topic (topic_name=%s) already exists. (topic_add_sub)\n", topic_name);

    if (qos_depth == 0) return 0;  // transient local is disabled

    // TODO: Implement transient local
    dev_err(agnocast_device, "transient local is not supported yet.");

    return 0;
  }

  if (insert_topic(topic_name) < 0) {
    dev_warn(
      agnocast_device, "Failed to add a new topic (topic_name=%s). (topic_add_sub)\n", topic_name);
    return -1;
  }

  dev_info(agnocast_device, "Topic (topic_name=%s) added. (topic_add_sub)\n", topic_name);
  return 0;
}

#define AGNOCAST_SUBSCRIBER_ADD_CMD _IOW('S', 1, union ioctl_subscriber_args)
static int get_shm(char * topic_name, union ioctl_subscriber_args * ioctl_ret)
{
  // get all publisher id and addr from topic_name

  struct topic_wrapper * wrapper = find_topic(topic_name);
  if (!wrapper) {
    dev_warn(agnocast_device, "Topic (topic_name=%s) not found. (get_shm)\n", topic_name);
    return -1;
  }

  if (wrapper->topic.non_exited_publisher_num > MAX_PUBLISHER_NUM) {
    dev_warn(
      agnocast_device,
      "The number of publishers for the topic (topic_name=%s) reached the "
      "upper bound (MAX_PUBLISHER_NUM=%d), so no new subscriber can be "
      "added. (get_shm)\n",
      topic_name, MAX_PUBLISHER_NUM);
    return -1;
  }

  for (int i = 0; i < wrapper->topic.non_exited_publisher_num; i++) {
    ioctl_ret->ret_pids[i] = wrapper->topic.non_exited_publisher_pids[i];
    for (int j = 0; j < pid_index; j++) {
      if (process_ids[j] == wrapper->topic.non_exited_publisher_pids[i]) {
        ioctl_ret->ret_addrs[i] = shm_addrs[j];
        break;
      }
    }
  }
  ioctl_ret->ret_publisher_num = wrapper->topic.non_exited_publisher_num;

  return 0;
}

static int subscriber_add(char * topic_name, uint32_t pid, union ioctl_subscriber_args * ioctl_ret)
{
  if (insert_subscriber_pid(topic_name, pid) == -1) {
    return -1;
  }

  return get_shm(topic_name, ioctl_ret);
}

#define AGNOCAST_PUBLISHER_ADD_CMD _IOW('P', 1, union ioctl_publisher_args)
static int publisher_add(
  const char * topic_name, uint32_t pid, union ioctl_publisher_args * ioctl_ret)
{
  struct topic_wrapper * wrapper = find_topic(topic_name);
  if (!wrapper) {
    dev_warn(agnocast_device, "Topic (topic_name=%s) not found. (publisher_add)\n", topic_name);
    return -1;
  }

  if (insert_publisher_info(wrapper, pid) == -1) {
    return -1;
  }
  wrapper->topic.non_exited_publisher_pids[wrapper->topic.non_exited_publisher_num] = pid;
  wrapper->topic.non_exited_publisher_num++;

  // set shm addr to ioctl_ret
  bool found = false;
  for (int i = 0; i < pid_index; i++) {
    if (process_ids[i] == pid) {
      ioctl_ret->ret_shm_addr = shm_addrs[i];
      found = true;
      break;
    }
  }

  if (!found) {
    dev_warn(agnocast_device, "Publisher (pid=%d) not found. (publisher_add)\n", pid);
    return -1;
  }

  // set subscriber info to ioctl_ret
  ioctl_ret->ret_subscriber_len = wrapper->topic.subscriber_num;
  memcpy(
    ioctl_ret->ret_subscriber_pids, wrapper->topic.subscriber_pids,
    wrapper->topic.subscriber_num * sizeof(uint32_t));

  dev_info(
    agnocast_device, "Publisher (pid=%d) is added to the topic (topic_name=%s)\n", pid, topic_name);
  return 0;
}

#define AGNOCAST_ENQUEUE_AND_RELEASE_CMD _IOW('E', 1, union ioctl_enqueue_and_release_args)
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

  // The searched message is either deleted or, if a reference count remains, is not deleted.
  // In both cases, this number of searches is sufficient, as it does not affect the Queue size of
  // QoS.
  while (num_search_entries > 0) {
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
    if (en->subscriber_reference_count > 0) continue;

    ioctl_ret->ret_released_addrs[ioctl_ret->ret_len] = en->msg_virtual_address;
    ioctl_ret->ret_len++;
    if (decrement_publisher_info(wrapper, publisher_pid) == -1) return -1;
    rb_erase(&en->node, &wrapper->topic.entries);
    kfree(en);

    wrapper->topic.entries_num--;

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

#define AGNOCAST_DECREMENT_RC_CMD _IOW('M', 2, union ioctl_update_entry_args)

#define AGNOCAST_RECEIVE_MSG_CMD _IOW('M', 3, union ioctl_receive_msg_args)
static int receive_and_update(
  char * topic_name, uint32_t subscriber_pid, uint32_t publisher_pid, uint64_t msg_timestamp,
  uint32_t qos_depth, union ioctl_receive_msg_args * ioctl_ret)
{
  struct entry_node * en = find_message_entry(topic_name, publisher_pid, msg_timestamp);
  if (!en) {
    dev_warn(
      agnocast_device,
      "Message entry with (topic_name=%s publisher_pid=%d timestamp=%lld) not found. "
      "(receive_and_update)\n",
      topic_name, publisher_pid, msg_timestamp);
    return -1;
  }

  if (en->unreceived_subscriber_count == 0) {
    dev_warn(
      agnocast_device,
      "Tried to decrement unreceived_subscriber_count 0 with (topic_name=%s publisher_pid=%d "
      "timestamp=%lld). (receive_and_update)\n",
      topic_name, publisher_pid, msg_timestamp);
    return -1;
  }

  struct topic_wrapper * wrapper = find_topic(topic_name);
  if (!wrapper) {
    dev_warn(
      agnocast_device, "Topic (topic_name=%s) not found. (receive_and_update)\n", topic_name);
    return -1;
  }

  // Count number of nodes that have greater (newer) timestamp than the received message entry.
  // If the count is greater than qos_depth, the received message is ignored.
  uint32_t newer_entry_count = 0;
  for (struct rb_node * node = rb_last(&wrapper->topic.entries); node; node = rb_prev(node)) {
    struct entry_node * compared_en = container_of(node, struct entry_node, node);
    if (compared_en->timestamp <= msg_timestamp) break;
    newer_entry_count++;
  }

  if (newer_entry_count > qos_depth) {
    // Received message is ignored.
    en->unreceived_subscriber_count--;
    ioctl_ret->ret = 0;
    return 0;
  }

  en->unreceived_subscriber_count--;
  en->referencing_subscriber_pids[en->subscriber_reference_count] = subscriber_pid;
  en->subscriber_reference_count++;
  ioctl_ret->ret = en->msg_virtual_address;
  return 0;
}

#define AGNOCAST_PUBLISH_MSG_CMD _IOW('M', 4, union ioctl_publish_args)
static int publish_msg(
  char * topic_name, uint32_t publisher_pid, uint64_t msg_timestamp,
  union ioctl_publish_args * ioctl_ret)
{
  struct topic_wrapper * wrapper = find_topic(topic_name);
  if (!wrapper) {
    dev_warn(agnocast_device, "Topic (topic_name=%s) not found. (publish_msg)\n", topic_name);
    return -1;
  }

  struct entry_node * en = find_message_entry(topic_name, publisher_pid, msg_timestamp);
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

  const uint32_t subscriber_num = wrapper->topic.subscriber_num;

  en->published = true;
  en->unreceived_subscriber_count = subscriber_num;

  ioctl_ret->ret_len = subscriber_num;
  memcpy(ioctl_ret->ret_pids, wrapper->topic.subscriber_pids, subscriber_num * sizeof(uint32_t));

  return 0;
}

#define AGNOCAST_NEW_SHM_CMD _IOW('I', 1, union ioctl_new_shm_args)
static int new_shm_addr(uint32_t pid, union ioctl_new_shm_args * ioctl_ret)
{
  if (pid_index >= MAX_PROCESS_NUM) {
    dev_warn(
      agnocast_device,
      "The number of processes has reached the upper bound (MAX_PROCESS_NUM=%d), "
      "so no new shared memory segments can be allocated. (new_shm_addr)\n",
      MAX_PROCESS_NUM);
    return -1;
  }

  process_ids[pid_index] = pid;
  shm_addrs[pid_index] = allocatable_addr;

  // TODO: allocate 0x00400000000 size for each process, currently
  allocatable_addr += 0x00400000000;

  ioctl_ret->ret_addr = shm_addrs[pid_index];
  pid_index++;
  return 0;
}

#define AGNOCAST_GET_SUBSCRIBER_NUM_CMD _IOW('G', 1, union ioctl_get_subscriber_num_args)
static int get_subscriber_num(char * topic_name, union ioctl_get_subscriber_num_args * ioctl_ret)
{
  struct topic_wrapper * wrapper = find_topic(topic_name);
  if (!wrapper) {
    dev_warn(
      agnocast_device, "Topic (topic_name=%s) not found. (get_subscription_num)\n", topic_name);
    return -1;
  }

  ioctl_ret->ret_subscriber_num = wrapper->topic.subscriber_num;
  return 0;
}

static DEFINE_MUTEX(global_mutex);

static long agnocast_ioctl(struct file * file, unsigned int cmd, unsigned long arg)
{
  mutex_lock(&global_mutex);
  int ret = 0;
  char topic_name_buf[256];
  union ioctl_add_topic_sub_args add_topic_sub_args;
  union ioctl_subscriber_args sub_args;
  union ioctl_publisher_args pub_args;
  union ioctl_enqueue_and_release_args enqueue_release_args;
  union ioctl_update_entry_args entry_args;
  union ioctl_receive_msg_args receive_msg_args;
  union ioctl_publish_args publish_args;
  union ioctl_new_shm_args new_shm_args;
  union ioctl_get_subscriber_num_args get_subscriber_num_args;

  switch (cmd) {
    case AGNOCAST_TOPIC_ADD_PUB_CMD:
      if (copy_from_user(topic_name_buf, (char __user *)arg, sizeof(topic_name_buf)))
        goto unlock_mutex_and_return;
      ret = topic_add_pub(topic_name_buf);
      break;
    case AGNOCAST_TOPIC_ADD_SUB_CMD:
      if (copy_from_user(
            &add_topic_sub_args, (union ioctl_add_topic_sub_args __user *)arg,
            sizeof(add_topic_sub_args)))
        goto unlock_mutex_and_return;
      if (copy_from_user(
            topic_name_buf, (char __user *)add_topic_sub_args.topic_name, sizeof(topic_name_buf)))
        goto unlock_mutex_and_return;
      ret = topic_add_sub(
        topic_name_buf, add_topic_sub_args.qos_depth, add_topic_sub_args.subscriber_pid,
        &add_topic_sub_args);
      if (copy_to_user(
            (union ioctl_add_topic_sub_args __user *)arg, &add_topic_sub_args,
            sizeof(add_topic_sub_args)))
        goto unlock_mutex_and_return;
      break;
    case AGNOCAST_SUBSCRIBER_ADD_CMD:
      if (copy_from_user(&sub_args, (union ioctl_subscriber_args __user *)arg, sizeof(sub_args)))
        goto unlock_mutex_and_return;
      if (copy_from_user(
            topic_name_buf, (char __user *)sub_args.topic_name, sizeof(topic_name_buf)))
        goto unlock_mutex_and_return;
      ret = subscriber_add(topic_name_buf, sub_args.pid, &sub_args);
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
        topic_name_buf, receive_msg_args.subscriber_pid, receive_msg_args.publisher_pid,
        receive_msg_args.msg_timestamp, receive_msg_args.qos_depth, &receive_msg_args);
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
    case AGNOCAST_NEW_SHM_CMD:
      if (copy_from_user(
            &new_shm_args, (union ioctl_new_shm_args __user *)arg, sizeof(new_shm_args)))
        goto unlock_mutex_and_return;
      ret = new_shm_addr(new_shm_args.pid, &new_shm_args);
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

static int pre_handler_do_exit(struct kprobe * p, struct pt_regs * regs)
{
  mutex_lock(&global_mutex);

  // Quickly determine if it is an Agnocast-related process.
  bool agnocast_related = false;
  for (int i = 0; i < pid_index; i++) {
    if (process_ids[i] == current->pid) {
      agnocast_related = true;
      break;
    }
  }

  if (!agnocast_related) {
    mutex_unlock(&global_mutex);
    return 0;
  }

  // TODO: Implement an exit handler.

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

static void free_all_topics(void)
{
  // TODO: Implement memory deallocation when 'rmmod' is called.
}

static void agnocast_exit(void)
{
  mutex_lock(&global_mutex);
  free_all_topics();
  mutex_unlock(&global_mutex);

  // Decrement reference count
  kobject_put(status_kobj);

  device_destroy(agnocast_class, MKDEV(major, 0));
  class_destroy(agnocast_class);
  unregister_chrdev(major, "agnocast");

  unregister_kprobe(&kp);

  dev_info(agnocast_device, "Agnocast removed!\n");
}

module_init(agnocast_init) module_exit(agnocast_exit)
