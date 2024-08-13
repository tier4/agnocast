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

MODULE_LICENSE("Dual BSD/GPL");

#define MAX_PUBLISHER_NUM 16  // only for ioctl_get_shm_args currently
#define MAX_SUBSCRIBER_NUM 16

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

struct publisher_queue_node
{
  uint32_t pid;
  uint32_t entries_num;
  struct rb_root entries;
  bool publisher_exited;
  struct publisher_queue_node * next;
};

struct topic_struct
{
  unsigned int publisher_num;  // This also includes publishers that have already exited.
  struct publisher_queue_node * publisher_queues;  // linked list
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
  uint64_t msg_virtual_address;
  uint32_t reference_count;
  bool published;
  /*
   * NOTE:
   *   unreceived_subscriber_count currently has no effect on the release timing of the message.
   *   However, it is retained for future use such as early release or logging.
   */
  uint32_t unreceived_subscriber_count;
};

DEFINE_HASHTABLE(topic_hashtable, AGNOCAST_HASH_BITS);

static unsigned long agnocast_hash(const char * str)
{
  unsigned long hash = full_name_hash(NULL /*namespace*/, str, strlen(str));
  return hash_min(hash, AGNOCAST_HASH_BITS);
}

static void free_rb_tree(struct rb_root * root)
{
  struct rb_node * next = rb_first(root);
  while (next) {
    struct entry_node * en = rb_entry(next, struct entry_node, node);
    next = rb_next(next);
    rb_erase(&en->node, root);
    kfree(en);
  }
}

static int insert_topic(const char * topic_name)
{
  struct topic_wrapper * wrapper = kmalloc(sizeof(struct topic_wrapper), GFP_KERNEL);
  if (!wrapper) {
    printk(KERN_WARNING "kmalloc failed (insert_topic)\n");
    return -1;
  }

  wrapper->key = kstrdup(topic_name, GFP_KERNEL);
  if (!wrapper->key) {
    printk(KERN_WARNING "kstrdup failed (insert_topic)\n");
    kfree(wrapper);
    return -1;
  }

  wrapper->topic.publisher_num = 0;
  wrapper->topic.publisher_queues = NULL;
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
    printk(KERN_WARNING "topic_name %s not found (insert_subscriber_pid)\n", topic_name);
    return -1;
  }

  // check whether subscriber_pids is full
  if (wrapper->topic.subscriber_num == MAX_SUBSCRIBER_NUM) {
    printk(
      KERN_WARNING
      "subscribers for topic_name=%s reached MAX_SUBSCRIBER_NUM=%d, so a new subscriber cannot be "
      "added (insert_subscriber_pid)\n",
      topic_name, MAX_SUBSCRIBER_NUM);
    return -1;
  }

  // check whether pid already exists in subscriber_pids
  for (int i = 0; i < wrapper->topic.subscriber_num; i++) {
    if (pid == wrapper->topic.subscriber_pids[i]) {
      printk(
        KERN_WARNING "subscriber (pid=%d) already exists in %s (insert_subscriber_pid)\n", pid,
        topic_name);
      return -1;
    }
  }

  wrapper->topic.subscriber_pids[wrapper->topic.subscriber_num] = pid;
  wrapper->topic.subscriber_num++;

  printk(KERN_INFO "subscriber (pid=%d) is added to %s\n", pid, topic_name);
  return 0;
}

static struct publisher_queue_node * find_publisher_queue(
  const char * topic_name, uint32_t publisher_pid)
{
  struct topic_wrapper * wrapper = find_topic(topic_name);
  if (!wrapper) {
    printk(KERN_WARNING "topic_name %s not found (find_publisher_queue)\n", topic_name);
    return NULL;
  }

  struct publisher_queue_node * node = wrapper->topic.publisher_queues;
  while (node) {
    if (publisher_pid == node->pid) {
      return node;
    }

    node = node->next;
  }

  return NULL;
}

static int insert_publisher_queue(const char * topic_name, uint32_t publisher_pid)
{
  struct topic_wrapper * wrapper = find_topic(topic_name);
  if (!wrapper) {
    printk(KERN_WARNING "topic_name %s not found (insert_publisher_queue)\n", topic_name);
    return -1;
  }

  struct publisher_queue_node * node = find_publisher_queue(topic_name, publisher_pid);
  if (node) {
    printk(
      KERN_INFO "publisher (pid=%d) already exists in topic_name=%s (insert_publisher_queue)\n",
      publisher_pid, topic_name);
    return -1;
  }

  struct publisher_queue_node * new_node = kmalloc(sizeof(struct publisher_queue_node), GFP_KERNEL);
  if (!new_node) {
    printk(KERN_WARNING "kmalloc failed (insert_publisher_queue)\n");
    return -1;
  }

  new_node->pid = publisher_pid;
  new_node->entries_num = 0;
  new_node->entries = RB_ROOT;
  new_node->publisher_exited = false;

  new_node->next = wrapper->topic.publisher_queues;
  wrapper->topic.publisher_queues = new_node;

  wrapper->topic.publisher_num++;

  return 0;
}

static struct entry_node * find_message_entry(
  const char * topic_name, uint32_t publisher_pid, uint64_t msg_timestamp)
{
  struct publisher_queue_node * pubq = find_publisher_queue(topic_name, publisher_pid);
  if (!pubq) {
    printk(
      KERN_WARNING
      "publisher queue with topic_name=%s publisher_pid=%d not found (find_message_entry)\n",
      topic_name, publisher_pid);
    return NULL;
  }

  struct rb_root * root = &pubq->entries;
  struct rb_node ** new = &(root->rb_node);

  while (*new) {
    struct entry_node * this = container_of(*new, struct entry_node, node);

    if (msg_timestamp < this->timestamp) {
      new = &((*new)->rb_left);
    } else if (msg_timestamp > this->timestamp) {
      new = &((*new)->rb_right);
    } else {
      return this;
    }
  }

  return NULL;
}

static int increment_message_entry_rc(
  const char * topic_name, uint32_t publisher_pid, uint64_t msg_timestamp)
{
  struct entry_node * en = find_message_entry(topic_name, publisher_pid, msg_timestamp);
  if (!en) {
    printk(
      KERN_WARNING
      "message entry with topic_name=%s publisher_pid=%d timestamp=%lld not found "
      "(increment_message_entry_rc)\n",
      topic_name, publisher_pid, msg_timestamp);
    return -1;
  }

  en->reference_count++;
  return 0;
}

static int decrement_message_entry_rc(
  const char * topic_name, uint32_t publisher_pid, uint64_t msg_timestamp)
{
  struct entry_node * en = find_message_entry(topic_name, publisher_pid, msg_timestamp);
  if (!en) {
    printk(
      KERN_WARNING
      "message entry with topic_name=%s publisher_pid=%d timestamp=%lld not found "
      "(decrement_message_entry_rc)\n",
      topic_name, publisher_pid, msg_timestamp);
    return -1;
  }

  if (en->reference_count == 0) {
    printk(
      KERN_WARNING
      "tried to decrement reference count 0 with topic_name=%s publisher_pid=%d "
      "timestamp=%lld (decrement_message_entry_rc)\n",
      topic_name, publisher_pid, msg_timestamp);
    return -1;
  }

  en->reference_count--;
  return 0;
}

static int insert_message_entry(
  const char * topic_name, uint32_t publisher_pid, uint64_t msg_virtual_address, uint64_t timestamp)
{
  struct publisher_queue_node * publisher_queue = find_publisher_queue(topic_name, publisher_pid);
  if (!publisher_queue) {
    printk(
      KERN_WARNING "publisher (pid=%d) not found in %s (insert_message_entry)\n", publisher_pid,
      topic_name);
    return -1;
  }

  struct rb_root * root = &publisher_queue->entries;
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
      printk(
        KERN_WARNING
        "message entry timestamp=%lld already exists in publisher (pid=%d) queue in %s "
        "(insert_message_entry)\n",
        timestamp, publisher_pid, topic_name);
      return -1;
    }
  }

  struct entry_node * new_node = kmalloc(sizeof(struct entry_node), GFP_KERNEL);
  if (!new_node) {
    printk(KERN_WARNING "kmalloc failed (insert_message_entry)\n");
    return -1;
  }

  new_node->timestamp = timestamp;
  new_node->msg_virtual_address = msg_virtual_address;
  new_node->reference_count = 0;
  new_node->unreceived_subscriber_count = 0;
  new_node->published = false;

  rb_link_node(&new_node->node, parent, new);
  rb_insert_color(&new_node->node, root);

  publisher_queue->entries_num++;

  printk(
    KERN_INFO
    "enqueue entry: topic_name=%s publisher_pid=%d msg_virtual_address=%lld timestamp=%lld",
    topic_name, publisher_pid, msg_virtual_address, timestamp);
  return 0;
}

static int remove_subscriber_pid(const char * topic_name, uint32_t pid)
{
  struct topic_wrapper * wrapper = find_topic(topic_name);
  if (!wrapper) {
    printk(KERN_WARNING "topic_name %s not found (remove_subscriber_pid)\n", topic_name);
    return -1;
  }

  bool found = false;
  for (int i = 0; i < wrapper->topic.subscriber_num; i++) {
    if (pid == wrapper->topic.subscriber_pids[i]) {
      found = true;
    }

    if (found && i < MAX_SUBSCRIBER_NUM - 1) {
      wrapper->topic.subscriber_pids[i] = wrapper->topic.subscriber_pids[i + 1];
    }
  }

  if (!found) {
    printk(
      KERN_WARNING
      "tried to remove subscriber (pid=%d), but not found in %s (remove_subscriber_pid)\n",
      pid, topic_name);
    return -1;
  }

  wrapper->topic.subscriber_num--;

  printk(KERN_INFO "subscriber (pid=%d) is removed from %s\n", pid, topic_name);
  return 0;
}

static int remove_publisher_queue(const char * topic_name, uint32_t publisher_pid)
{
  struct topic_wrapper * wrapper = find_topic(topic_name);
  if (!wrapper) {
    printk(KERN_WARNING "topic_name %s not found (remove_publisher_queue)\n", topic_name);
    return -1;
  }

  struct publisher_queue_node * prev = wrapper->topic.publisher_queues;
  struct publisher_queue_node * node = wrapper->topic.publisher_queues;
  while (node) {
    if (publisher_pid == node->pid) {
      prev->next = node->next;
      wrapper->topic.publisher_num--;
      free_rb_tree(&node->entries);
      printk(KERN_INFO "publisher (pid=%d) is removed from %s\n", publisher_pid, topic_name);
      return 0;
    }

    prev = node;
    node = node->next;
  }

  printk(
    KERN_WARNING
    "tried to remove publisher (pid=%d), but not found in %s (remove_publisher_queue)\n",
    publisher_pid, topic_name);
  return -1;
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
  // at least 500 bytes would be needed as an initial buffer size
  size_t buf_size = 1024;

  char * local_buf = kmalloc(buf_size, GFP_KERNEL);
  local_buf[0] = '\0';

  struct topic_wrapper * entry;
  struct hlist_node * node;
  int bkt;
  size_t buf_len = 0;

  hash_for_each_safe(topic_hashtable, bkt, node, entry, node)
  {
    strcat(local_buf, entry->key);
    strcat(local_buf, "\n");
    buf_len += strlen(entry->key) + 1;

    strcat(local_buf, " subscriber_pids:");
    buf_len += 17;
    for (int i = 0; i < entry->topic.subscriber_num; i++) {
      char num_str[BUFFER_SIZE];
      scnprintf(num_str, sizeof(num_str), " %u", entry->topic.subscriber_pids[i]);
      strcat(local_buf, num_str);
      buf_len += BUFFER_SIZE;
    }
    strcat(local_buf, "\n");
    buf_len += 1;

    strcat(local_buf, " publishers:\n");
    buf_len += 13;

    struct publisher_queue_node * pub_node = entry->topic.publisher_queues;
    while (pub_node) {
      char num_str[BUFFER_SIZE];
      scnprintf(num_str, sizeof(num_str), "  pid=%u:\n", pub_node->pid);
      strcat(local_buf, num_str);
      buf_len += BUFFER_SIZE;

      struct rb_root * root = &pub_node->entries;
      struct rb_node * node;
      for (node = rb_first(root); node; node = rb_next(node)) {
        struct entry_node * en = container_of(node, struct entry_node, node);

        strcat(local_buf, "   entry: ");
        buf_len += 10;

        char num_str_timestamp[BUFFER_SIZE];
        scnprintf(num_str_timestamp, sizeof(num_str_timestamp), "time=%lld ", en->timestamp);
        strcat(local_buf, num_str_timestamp);
        buf_len += BUFFER_SIZE;

        char num_str_msg_addr[BUFFER_SIZE];
        scnprintf(
          num_str_msg_addr, sizeof(num_str_msg_addr), "addr=%lld ", en->msg_virtual_address);
        strcat(local_buf, num_str_msg_addr);
        buf_len += BUFFER_SIZE;

        char num_str_rc[BUFFER_SIZE];
        scnprintf(num_str_rc, sizeof(num_str_rc), "rc=%d ", en->reference_count);
        strcat(local_buf, num_str_rc);
        buf_len += BUFFER_SIZE;

        char num_str_usc[BUFFER_SIZE];
        scnprintf(num_str_usc, sizeof(num_str_usc), "usc=%d\n", en->unreceived_subscriber_count);
        strcat(local_buf, num_str_usc);
        buf_len += BUFFER_SIZE;

        if (buf_len * 2 > buf_size) {
          buf_size *= 2;
          local_buf = krealloc(local_buf, buf_size, GFP_KERNEL);
        }
      }

      pub_node = pub_node->next;
    }
    strcat(local_buf, "\n");
    buf_len += 1;
  }

  ssize_t ret = scnprintf(buf, PAGE_SIZE, "%s\n", local_buf);

  kfree(local_buf);

  return ret;
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
int topic_add_pub(const char * topic_name)
{
  struct topic_wrapper * wrapper = find_topic(topic_name);
  if (wrapper) {
    printk(KERN_INFO "Topic %s already exists (topic_add_pub)\n", topic_name);
    return 0;
  }

  if (insert_topic(topic_name) < 0) {
    printk(KERN_WARNING "Failed to add a new topic %s (topic_add_pub)\n", topic_name);
    return -1;
  }

  printk(KERN_INFO "Topic %s added\n", topic_name);
  return 0;
}

#define MAX_QOS_DEPTH 10  // Maximum depth of transient local usage part in Autoware

union ioctl_add_topic_sub_args {
  struct
  {
    char * topic_name;
    uint32_t qos_depth;
  };
  struct
  {
    uint32_t ret_len;
    uint32_t ret_publisher_pids[MAX_QOS_DEPTH];
    uint64_t ret_timestamps[MAX_QOS_DEPTH];
    uint64_t ret_last_msg_addrs[MAX_QOS_DEPTH];
  };
};

struct ioctl_subscriber_args
{
  char * topic_name;
  uint32_t pid;
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
    uint32_t publisher_pid;
    uint64_t msg_timestamp;
  };
  uint64_t ret;
};

union ioctl_receive_msg_args {
  struct
  {
    char * topic_name;
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

union ioctl_get_shm_args {
  const char * topic_name;
  struct
  {
    uint32_t ret_publisher_num;
    uint32_t ret_pids[MAX_PUBLISHER_NUM];
    uint64_t ret_addrs[MAX_PUBLISHER_NUM];
  };
};

#define AGNOCAST_TOPIC_ADD_SUB_CMD _IOW('T', 2, union ioctl_add_topic_sub_args)
int topic_add_sub(
  const char * topic_name, uint32_t qos_depth, union ioctl_add_topic_sub_args * ioctl_ret)
{
  ioctl_ret->ret_len = 0;
  struct topic_wrapper * wrapper = find_topic(topic_name);
  if (wrapper) {
    printk(KERN_INFO "Topic %s already exists (topic_add_sub)\n", topic_name);

    if (qos_depth == 0) return 0;  // transient local is disabled

    // Return qos_depth messages in order from newest to oldest for transient local
    struct rb_node * backward_trackers[MAX_PUBLISHER_NUM];
    uint32_t pids[MAX_PUBLISHER_NUM];
    struct publisher_queue_node * pubq = wrapper->topic.publisher_queues;
    uint32_t pubq_num = 0;
    while (pubq) {
      backward_trackers[pubq_num] = rb_last(&pubq->entries);
      pids[pubq_num] = pubq->pid;
      pubq = pubq->next;
      pubq_num++;
    }

    while (ioctl_ret->ret_len < qos_depth) {
      uint64_t newest_timestamp = 0;
      size_t newest_i;
      for (size_t i = 0; i < pubq_num; i++) {
        if (backward_trackers[i]) {
          struct entry_node * en = container_of(backward_trackers[i], struct entry_node, node);
          if (en->timestamp > newest_timestamp) {
            newest_timestamp = en->timestamp;
            newest_i = i;
          }
        }
      }

      if (newest_timestamp == 0) break;  // all messages are searched

      struct entry_node * en = container_of(backward_trackers[newest_i], struct entry_node, node);
      if (en->published) {
        en->reference_count++;
        ioctl_ret->ret_publisher_pids[ioctl_ret->ret_len] = pids[newest_i];
        ioctl_ret->ret_timestamps[ioctl_ret->ret_len] = en->timestamp;
        ioctl_ret->ret_last_msg_addrs[ioctl_ret->ret_len] = en->msg_virtual_address;
        ioctl_ret->ret_len++;
      }

      backward_trackers[newest_i] = rb_prev(backward_trackers[newest_i]);
    }

    return 0;
  }

  if (insert_topic(topic_name) < 0) {
    printk(KERN_WARNING "Failed to add a new topic %s (topic_add_sub)\n", topic_name);
    return -1;
  }

  printk(KERN_INFO "Topic %s added\n", topic_name);
  return 0;
}

#define AGNOCAST_SUBSCRIBER_ADD_CMD _IOW('S', 1, struct ioctl_subscriber_args)

#define AGNOCAST_SUBSCRIBER_REMOVE_CMD _IOW('S', 2, struct ioctl_subscriber_args)

#define AGNOCAST_PUBLISHER_ADD_CMD _IOW('P', 1, union ioctl_publisher_args)
int publisher_queue_add(
  const char * topic_name, uint32_t pid, union ioctl_publisher_args * ioctl_ret)
{
  if (insert_publisher_queue(topic_name, pid) == -1) {
    return -1;
  }

  struct topic_wrapper * wrapper = find_topic(topic_name);
  if (!wrapper) {
    printk(KERN_WARNING "topic_name %s not found (publisher_queue_add)\n", topic_name);
    return -1;
  }

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
    printk(KERN_WARNING "publisher (pid=%d) not found (publisher_queue_add)\n", pid);
    return -1;
  }

  // set subscriber info to ioctl_ret
  ioctl_ret->ret_subscriber_len = wrapper->topic.subscriber_num;
  memcpy(
    ioctl_ret->ret_subscriber_pids, wrapper->topic.subscriber_pids,
    wrapper->topic.subscriber_num * sizeof(uint32_t));

  printk(KERN_INFO "publisher (pid=%d) is added to %s\n", pid, topic_name);
  return 0;
}

#define AGNOCAST_PUBLISHER_REMOVE_CMD _IOW('P', 2, union ioctl_publisher_args)

#define AGNOCAST_ENQUEUE_AND_RELEASE_CMD _IOW('E', 1, union ioctl_enqueue_and_release_args)
uint64_t release_msgs_to_meet_depth(
  const char * topic_name, const uint32_t publisher_pid, const uint32_t qos_depth,
  union ioctl_enqueue_and_release_args * ioctl_ret)
{
  ioctl_ret->ret_len = 0;

  struct publisher_queue_node * publisher_queue = find_publisher_queue(topic_name, publisher_pid);
  if (!publisher_queue) {
    printk(
      KERN_WARNING "publisher (pid=%d) not found in %s (release_msgs_to_meet_depth)\n",
      publisher_pid, topic_name);
    return -1;
  }

  if (publisher_queue->entries_num <= qos_depth) {
    return 0;
  }

  const uint32_t leak_warn_threshold =
    (qos_depth <= 100) ? 100 + qos_depth : qos_depth * 2;  // This is rough value.
  if (publisher_queue->entries_num > leak_warn_threshold) {
    printk(
      KERN_WARNING
      "For some reason the reference count of the message is not reduced and the queue size is "
      "huge: publisher queue publisher_pid=%d, topic_name=%s "
      "(release_msgs_to_meet_depth)\n",
      publisher_pid, topic_name);
    return -1;
  }

  struct rb_node * node = rb_first(&publisher_queue->entries);
  if (!node) {
    printk(
      KERN_WARNING
      "Failed to get message entries in publisher (pid=%d) (release_msgs_to_meet_depth)\n",
      publisher_pid);
    return -1;
  }

  // Number of entries exceeding qos_depth
  const uint32_t num_search_entries = publisher_queue->entries_num - qos_depth;

  // The searched message is either deleted or, if a reference count remains, is not deleted.
  // In both cases, this number of searches is sufficient, as it does not affect the Queue size of
  // QoS.
  for (uint32_t _ = 0; _ < num_search_entries; _++) {
    struct entry_node * en = container_of(node, struct entry_node, node);
    node = rb_next(node);
    if (!node) {
      printk(KERN_WARNING
             "entries_num is inconsistent with actual message entry num "
             "(release_msgs_to_meet_depth)\n");
      return -1;
    }

    if (en->reference_count > 0) continue;  // This is not counted in a Queue size of QoS.

    ioctl_ret->ret_released_addrs[ioctl_ret->ret_len] = en->msg_virtual_address;
    ioctl_ret->ret_len++;
    publisher_queue->entries_num--;
    rb_erase(&en->node, &publisher_queue->entries);
    kfree(en);

    printk(
      KERN_INFO
      "Release oldest message in %s publisher_pid=%d with qos_depth=%d "
      "(release_msgs_to_meet_depth)\n",
      topic_name, publisher_pid, qos_depth);
  }

  return 0;
}

uint64_t enqueue_and_release(
  const char * topic_name, const uint32_t publisher_pid, const uint32_t qos_depth,
  const uint64_t msg_virtual_address, const uint64_t timestamp,
  union ioctl_enqueue_and_release_args * ioctl_ret)
{
  if (insert_message_entry(topic_name, publisher_pid, msg_virtual_address, timestamp) == -1) {
    return -1;
  }
  return release_msgs_to_meet_depth(topic_name, publisher_pid, qos_depth, ioctl_ret);
}

#define AGNOCAST_INCREMENT_RC_CMD _IOW('M', 1, union ioctl_update_entry_args)

#define AGNOCAST_DECREMENT_RC_CMD _IOW('M', 2, union ioctl_update_entry_args)

#define AGNOCAST_RECEIVE_MSG_CMD _IOW('M', 3, union ioctl_receive_msg_args)
int receive_and_update(
  char * topic_name, uint32_t publisher_pid, uint64_t msg_timestamp, uint32_t qos_depth,
  union ioctl_receive_msg_args * ioctl_ret)
{
  struct entry_node * en = find_message_entry(topic_name, publisher_pid, msg_timestamp);
  if (!en) {
    printk(
      KERN_WARNING
      "message entry with topic_name=%s publisher_pid=%d timestamp=%lld not found "
      "(receive_and_update)\n",
      topic_name, publisher_pid, msg_timestamp);
    return -1;
  }

  if (en->unreceived_subscriber_count == 0) {
    printk(
      KERN_WARNING
      "tried to decrement unreceived_subscriber_count 0 with topic_name=%s publisher_pid=%d "
      "timestamp=%lld (receive_and_update)\n",
      topic_name, publisher_pid, msg_timestamp);
    return -1;
  }

  struct topic_wrapper * wrapper = find_topic(topic_name);
  if (!wrapper) {
    printk(KERN_WARNING "topic_name %s not found (receive_and_update)\n", topic_name);
    return -1;
  }

  // Count number of nodes that have greater (newer) timestamp than the received message entry.
  // If the count is greater than qos_depth, the received message is ignored.
  uint32_t newer_entry_count = 0;
  struct publisher_queue_node * pubq = wrapper->topic.publisher_queues;
  while (pubq && newer_entry_count <= qos_depth) {
    for (struct rb_node * node = rb_last(&pubq->entries); node; node = rb_prev(node)) {
      struct entry_node * compared_en = container_of(node, struct entry_node, node);
      if (compared_en->timestamp <= msg_timestamp) break;
      newer_entry_count++;
    }

    pubq = pubq->next;
  }

  if (newer_entry_count > qos_depth) {
    // Received message is ignored.
    en->unreceived_subscriber_count--;
    ioctl_ret->ret = 0;
    return 0;
  }

  en->unreceived_subscriber_count--;
  en->reference_count++;
  ioctl_ret->ret = en->msg_virtual_address;
  return 0;
}

#define AGNOCAST_PUBLISH_MSG_CMD _IOW('M', 4, union ioctl_publish_args)
int publish_msg(
  char * topic_name, uint32_t publisher_pid, uint64_t msg_timestamp,
  union ioctl_publish_args * ioctl_ret)
{
  struct topic_wrapper * wrapper = find_topic(topic_name);
  if (!wrapper) {
    printk(KERN_WARNING "topic_name %s not found (publish_msg)\n", topic_name);
    return -1;
  }

  struct entry_node * en = find_message_entry(topic_name, publisher_pid, msg_timestamp);
  if (!en) {
    printk(
      KERN_WARNING
      "message entry with topic_name=%s publisher_pid=%d timestamp=%lld not found "
      "(publish_msg)\n",
      topic_name, publisher_pid, msg_timestamp);
    return -1;
  }

  if (en->published) {
    printk(
      KERN_WARNING
      "tried to already published message with topic_name=%s publisher_pid=%d "
      "timestamp=%lld (publish_msg)\n",
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
int new_shm_addr(uint32_t pid, union ioctl_new_shm_args * ioctl_ret)
{
  if (pid_index >= MAX_PROCESS_NUM) {
    printk(KERN_WARNING "processes are too much (new_shm_addr)\n");
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

static DEFINE_MUTEX(global_mutex);

#define AGNOCAST_GET_SHM_CMD _IOW('I', 2, union ioctl_get_shm_args)
int get_shm(char * topic_name, union ioctl_get_shm_args * ioctl_ret)
{
  // get all publisher id and addr from topic_name

  struct topic_wrapper * wrapper = find_topic(topic_name);
  if (!wrapper) {
    printk(KERN_WARNING "topic_name %s not found (get_shm)\n", topic_name);
    return -1;
  }

  if (wrapper->topic.publisher_num > MAX_PUBLISHER_NUM) {
    printk(KERN_WARNING "publishers for %s topic are too much\n", topic_name);
    return -1;
  }

  ioctl_ret->ret_publisher_num = wrapper->topic.publisher_num;

  int index = 0;
  struct publisher_queue_node * node = wrapper->topic.publisher_queues;
  while (node) {
    if (!node->publisher_exited) {  // Publisher is alive
      ioctl_ret->ret_pids[index] = node->pid;
      for (int j = 0; j < pid_index; j++) {
        if (process_ids[j] == node->pid) {
          ioctl_ret->ret_addrs[index] = shm_addrs[j];
          index++;
          break;
        }
      }
    }
    node = node->next;
  }
  ioctl_ret->ret_publisher_num = index;

  return 0;
}

static long agnocast_ioctl(struct file * file, unsigned int cmd, unsigned long arg)
{
  mutex_lock(&global_mutex);
  int ret = 0;
  char topic_name_buf[256];
  union ioctl_add_topic_sub_args add_topic_sub_args;
  struct ioctl_subscriber_args sub_args;
  union ioctl_publisher_args pub_args;
  union ioctl_enqueue_and_release_args enqueue_release_args;
  union ioctl_update_entry_args entry_args;
  union ioctl_receive_msg_args receive_msg_args;
  union ioctl_publish_args publish_args;
  union ioctl_new_shm_args new_shm_args;
  union ioctl_get_shm_args get_shm_args;

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
      ret = topic_add_sub(topic_name_buf, add_topic_sub_args.qos_depth, &add_topic_sub_args);
      if (copy_to_user(
            (union ioctl_add_topic_sub_args __user *)arg, &add_topic_sub_args,
            sizeof(add_topic_sub_args)))
        goto unlock_mutex_and_return;
      break;
    case AGNOCAST_SUBSCRIBER_ADD_CMD:
      if (copy_from_user(&sub_args, (struct ioctl_subscriber_args __user *)arg, sizeof(sub_args)))
        goto unlock_mutex_and_return;
      if (copy_from_user(
            topic_name_buf, (char __user *)sub_args.topic_name, sizeof(topic_name_buf)))
        goto unlock_mutex_and_return;
      ret = insert_subscriber_pid(topic_name_buf, sub_args.pid);
      break;
    case AGNOCAST_SUBSCRIBER_REMOVE_CMD:
      if (copy_from_user(&sub_args, (struct ioctl_subscriber_args __user *)arg, sizeof(sub_args)))
        goto unlock_mutex_and_return;
      if (copy_from_user(
            topic_name_buf, (char __user *)sub_args.topic_name, sizeof(topic_name_buf)))
        goto unlock_mutex_and_return;
      ret = remove_subscriber_pid(topic_name_buf, sub_args.pid);
      break;
    case AGNOCAST_PUBLISHER_ADD_CMD:
      if (copy_from_user(&pub_args, (union ioctl_publisher_args __user *)arg, sizeof(pub_args)))
        goto unlock_mutex_and_return;
      if (copy_from_user(
            topic_name_buf, (char __user *)pub_args.topic_name, sizeof(topic_name_buf)))
        goto unlock_mutex_and_return;
      ret = publisher_queue_add(topic_name_buf, pub_args.publisher_pid, &pub_args);
      if (copy_to_user((union ioctl_publisher_args __user *)arg, &pub_args, sizeof(pub_args)))
        goto unlock_mutex_and_return;
      break;
    case AGNOCAST_PUBLISHER_REMOVE_CMD:
      if (copy_from_user(&pub_args, (union ioctl_publisher_args __user *)arg, sizeof(pub_args)))
        goto unlock_mutex_and_return;
      if (copy_from_user(
            topic_name_buf, (char __user *)pub_args.topic_name, sizeof(topic_name_buf)))
        goto unlock_mutex_and_return;
      ret = remove_publisher_queue(topic_name_buf, pub_args.publisher_pid);
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
        topic_name_buf, entry_args.publisher_pid, entry_args.msg_timestamp);
      break;
    case AGNOCAST_DECREMENT_RC_CMD:
      if (copy_from_user(
            &entry_args, (union ioctl_update_entry_args __user *)arg, sizeof(entry_args)))
        goto unlock_mutex_and_return;
      if (copy_from_user(
            topic_name_buf, (char __user *)entry_args.topic_name, sizeof(topic_name_buf)))
        goto unlock_mutex_and_return;
      ret = decrement_message_entry_rc(
        topic_name_buf, entry_args.publisher_pid, entry_args.msg_timestamp);
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
        topic_name_buf, receive_msg_args.publisher_pid, receive_msg_args.msg_timestamp,
        receive_msg_args.qos_depth, &receive_msg_args);
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
    case AGNOCAST_GET_SHM_CMD:
      if (copy_from_user(
            &get_shm_args, (union ioctl_get_shm_args __user *)arg, sizeof(get_shm_args)))
        goto unlock_mutex_and_return;
      if (copy_from_user(
            topic_name_buf, (char __user *)get_shm_args.topic_name, sizeof(topic_name_buf)))
        goto unlock_mutex_and_return;
      ret = get_shm(topic_name_buf, &get_shm_args);
      if (copy_to_user((union ioctl_get_shm_args __user *)arg, &get_shm_args, sizeof(get_shm_args)))
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

static char * agnocast_devnode(const struct device * dev, umode_t * mode)
{
  if (mode) {
    *mode = 0666;
  }
  return NULL;
}

static struct file_operations fops = {
  .unlocked_ioctl = agnocast_ioctl,
};

static int major;
static struct class * agnocast_class;
static struct device * agnocast_device;

// =========================================
// Handler for publisher process exit
void free_entry_node(
  struct publisher_queue_node * publisher_queue, struct entry_node * en, struct rb_root * root)
{
  publisher_queue->entries_num--;
  rb_erase(&en->node, root);
  kfree(en);
}

void publisher_exit(struct publisher_queue_node * publisher_queue)
{
  struct rb_root * root = &publisher_queue->entries;
  struct rb_node * node = rb_first(root);
  while (node) {
    struct entry_node * en = rb_entry(node, struct entry_node, node);
    node = rb_next(node);
    // unreceived_subscriber_count is not checked when releasing the message.
    if (en->reference_count == 0) {
      free_entry_node(publisher_queue, en, root);
    }
  }

  publisher_queue->publisher_exited = true;
}

void exit_if_publisher(struct topic_wrapper * entry)
{
  struct publisher_queue_node * publisher_queue = entry->topic.publisher_queues;
  struct publisher_queue_node dummy_head;
  dummy_head.next = publisher_queue;
  struct publisher_queue_node * prev_pub_queue = &dummy_head;

  while (publisher_queue) {
    if (publisher_queue->pid != current->pid) {
      prev_pub_queue = publisher_queue;
      publisher_queue = publisher_queue->next;
      continue;
    }

    printk(KERN_INFO "Process %d is exiting as a publisher.\n", current->pid);

    publisher_exit(publisher_queue);
    if (publisher_queue->entries_num == 0) {  // Delete the publisher_queue_node since there are no
                                              // entry_node remains.
      entry->topic.publisher_num--;
      prev_pub_queue->next = publisher_queue->next;
      kfree(publisher_queue);
    }

    break;
  }
  entry->topic.publisher_queues = dummy_head.next;
}

static int pre_handler_do_exit(struct kprobe * p, struct pt_regs * regs)
{
  mutex_lock(&global_mutex);

  struct topic_wrapper * entry;
  struct hlist_node * node;
  int bkt;

  // TODO: Introduce a function to quickly determine if it is an Agnocast-related process.

  hash_for_each_safe(topic_hashtable, bkt, node, entry, node)
  {
    // Exit handler for publisher
    exit_if_publisher(entry);

    // Exit handler for subscriber
    // exit_if_subscriber(entry);

    // Check if we can release the topic_wrapper
    if (entry->topic.publisher_num == 0 && entry->topic.subscriber_num == 0) {
      hash_del(&entry->node);
      if (entry->key) {
        kfree(entry->key);
      }
      kfree(entry);
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
  printk(KERN_INFO "Hello, World!\n");

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

  if (register_kprobe(&kp) < 0) {
    printk(KERN_INFO "register_kprobe failed, returned %d\n", ret);
    return ret;
  }
  printk(KERN_INFO "Planted kprobe at %p\n", kp.addr);

  major = register_chrdev(0, "agnocast" /*device driver name*/, &fops);
  agnocast_class = class_create("agnocast_class");
  agnocast_class->devnode = agnocast_devnode;
  agnocast_device =
    device_create(agnocast_class, NULL, MKDEV(major, 0), NULL, "agnocast" /*file name*/);

  return 0;
}

// TODO: Implement memory free later
static void free_all_topics(void)
{
  struct topic_wrapper * entry;
  struct hlist_node * tmp;
  int bkt;

  hash_for_each_safe(topic_hashtable, bkt, tmp, entry, node)
  {
    hash_del(&entry->node);
    if (entry->key) {
      kfree(entry->key);
    }
    // TODO: free messages
    kfree(entry);
  }
}

static void agnocast_exit(void)
{
  printk(KERN_INFO "Goodbye\n");

  free_all_topics();

  // Decrement reference count
  kobject_put(status_kobj);

  device_destroy(agnocast_class, MKDEV(major, 0));
  class_destroy(agnocast_class);
  unregister_chrdev(major, "agnocast");

  unregister_kprobe(&kp);
}

module_init(agnocast_init) module_exit(agnocast_exit)
