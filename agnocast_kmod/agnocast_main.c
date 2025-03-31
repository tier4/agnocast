#include "agnocast.h"
#include "agnocast_memory_allocator.h"

#include <linux/device.h>
#include <linux/fs.h>
#include <linux/hashtable.h>
#include <linux/kernel.h>
#include <linux/kprobes.h>
#include <linux/kthread.h>
#include <linux/namei.h>
#include <linux/pid.h>
#include <linux/rcupdate.h>
#include <linux/slab.h>  // kmalloc, kfree
#include <linux/spinlock.h>
#include <linux/statfs.h>
#include <linux/version.h>

MODULE_LICENSE("Dual BSD/GPL");

static int major;
static struct class * agnocast_class;
static struct device * agnocast_device;
static DEFINE_MUTEX(global_mutex);

#ifndef VERSION
#define VERSION "unknown"
#endif

// =========================================
// data structure

// hashtable size becomes 2^HASH_BITS
#define TOPIC_HASH_BITS 10
#define PUB_INFO_HASH_BITS 3
#define SUB_INFO_HASH_BITS 5
#define PROC_INFO_HASH_BITS 10

// Maximum number of referencing Publisher/Subscriber per entry: +1 for the publisher
#define MAX_REFERENCING_PUBSUB_NUM_PER_ENTRY (MAX_SUBSCRIBER_NUM + 1)

// Maximum length of topic name: 256 characters
#define TOPIC_NAME_BUFFER_SIZE 256

// Maximum number of topic info ret
#define MAX_TOPIC_INFO_RET_NUM max(MAX_PUBLISHER_NUM, MAX_SUBSCRIBER_NUM)

#ifndef KUNIT_BUILD
static int (*do_unlinkat)(int, struct filename *);
#endif

struct process_info
{
  pid_t pid;
  uint64_t shm_size;
  struct mempool_entry * mempool_entry;
  struct hlist_node node;
};

DEFINE_HASHTABLE(proc_info_htable, PROC_INFO_HASH_BITS);

struct publisher_info
{
  topic_local_id_t id;
  pid_t pid;
  char * node_name;
  uint32_t qos_depth;
  bool qos_is_transient_local;
  uint32_t entries_num;
  struct hlist_node node;
};

struct subscriber_info
{
  topic_local_id_t id;
  pid_t pid;
  uint32_t qos_depth;
  bool qos_is_transient_local;
  int64_t latest_received_entry_id;
  char * node_name;
  bool is_take_sub;
  bool need_mmap_update;
  struct hlist_node node;
};

struct topic_struct
{
  struct rb_root entries;
  DECLARE_HASHTABLE(pub_info_htable, PUB_INFO_HASH_BITS);
  DECLARE_HASHTABLE(sub_info_htable, SUB_INFO_HASH_BITS);
  topic_local_id_t current_pubsub_id;
  int64_t current_entry_id;
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
  int64_t entry_id;  // rbtree key
  topic_local_id_t publisher_id;
  uint64_t msg_virtual_address;
  topic_local_id_t referencing_ids[MAX_REFERENCING_PUBSUB_NUM_PER_ENTRY];
  uint8_t reference_count[MAX_REFERENCING_PUBSUB_NUM_PER_ENTRY];
};

DEFINE_HASHTABLE(topic_hashtable, TOPIC_HASH_BITS);

#ifndef KUNIT_BUILD
// When running a ROS 2 App inside a container, the host and container may have different PID
// namespaces. The kernel module has only two entry points: the do_exit handler and ioctl. The
// do_exit handler operates in the global PID namespace, whereas the PID passed as an argument to
// ioctl belongs to the local PID namespace. The kernel module should be designed to handle global
// PIDs in its data structures and source code. Therefore, functions called from the ioctl entry
// point should convert between global and local PIDs at both the beginning and the end of
// execution.
static pid_t convert_pid_to_global(pid_t local_pid)
{
  struct pid * pid_struct;
  pid_t global_pid = -1;

  rcu_read_lock();

  pid_struct = find_vpid(local_pid);
  if (!pid_struct) {
    dev_err(agnocast_device, "Internal error: Invalid PID %d (covnert_pid_to_global)\n", local_pid);
    goto out;
  }

  global_pid = pid_nr_ns(pid_struct, &init_pid_ns);

out:
  rcu_read_unlock();
  return global_pid;
}

static pid_t convert_pid_to_local(pid_t global_pid)
{
  struct pid * pid_struct;
  pid_t local_pid = -1;

  rcu_read_lock();

  pid_struct = find_pid_ns(global_pid, &init_pid_ns);
  if (!pid_struct) {
    dev_err(agnocast_device, "Internal error: Invalid PID %d (convert_pid_to_local)\n", global_pid);
    goto out;
  }

  local_pid = pid_vnr(pid_struct);

out:
  rcu_read_unlock();
  return local_pid;
}
#endif

static unsigned long get_topic_hash(const char * str)
{
  unsigned long hash = full_name_hash(NULL /*namespace*/, str, strlen(str));
  return hash_min(hash, TOPIC_HASH_BITS);
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

static int add_topic(const char * topic_name, struct topic_wrapper ** wrapper)
{
  *wrapper = find_topic(topic_name);
  if (*wrapper) {
    return 0;
  }

  *wrapper = kmalloc(sizeof(struct topic_wrapper), GFP_KERNEL);
  if (!*wrapper) {
    dev_warn(
      agnocast_device, "Failed to add a new topic (topic_name=%s) by kmalloc. (add_topic)\n",
      topic_name);
    return -ENOMEM;
  }

  (*wrapper)->key = kstrdup(topic_name, GFP_KERNEL);
  if (!(*wrapper)->key) {
    dev_warn(
      agnocast_device, "Failed to add a new topic (topic_name=%s) by kstrdup. (add_topic)\n",
      topic_name);
    kfree(*wrapper);
    return -ENOMEM;
  }

  (*wrapper)->topic.entries = RB_ROOT;
  hash_init((*wrapper)->topic.pub_info_htable);
  hash_init((*wrapper)->topic.sub_info_htable);
  (*wrapper)->topic.current_pubsub_id = 0;
  (*wrapper)->topic.current_entry_id = 0;
  hash_add(topic_hashtable, &(*wrapper)->node, get_topic_hash(topic_name));

  dev_info(agnocast_device, "Topic (topic_name=%s) added. (add_topic)\n", topic_name);

  return 0;
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
  const struct topic_wrapper * wrapper, const topic_local_id_t subscriber_id)
{
  struct subscriber_info * info;
  uint32_t hash_val = hash_min(subscriber_id, SUB_INFO_HASH_BITS);
  hash_for_each_possible(wrapper->topic.sub_info_htable, info, node, hash_val)
  {
    if (info->id == subscriber_id) {
      return info;
    }
  }

  return NULL;
}

static int insert_subscriber_info(
  struct topic_wrapper * wrapper, const char * node_name, const pid_t subscriber_pid,
  const uint32_t qos_depth, const bool qos_is_transient_local, const bool is_take_sub,
  struct subscriber_info ** new_info)
{
  if (qos_depth > MAX_QOS_DEPTH) {
    dev_warn(
      agnocast_device,
      "Subscriber's (topic_local_id=%s, pid=%d, qos_depth=%d) qos_depth can't be larger than "
      "MAX_QOS_DEPTH(=%d). (insert_subscriber_info)\n",
      wrapper->key, subscriber_pid, qos_depth, MAX_QOS_DEPTH);
    return -EINVAL;
  }

  int count = get_size_sub_info_htable(wrapper);
  if (count == MAX_SUBSCRIBER_NUM) {
    dev_warn(
      agnocast_device,
      "The number of subscribers for the topic (topic_name=%s) reached the upper "
      "bound (MAX_SUBSCRIBER_NUM=%d), so no new subscriber can be "
      "added. (insert_subscriber_info)\n",
      wrapper->key, MAX_SUBSCRIBER_NUM);
    return -ENOBUFS;
  }

  *new_info = kmalloc(sizeof(struct subscriber_info), GFP_KERNEL);
  if (!*new_info) {
    dev_warn(agnocast_device, "kmalloc failed. (insert_subscriber_info)\n");
    return -ENOMEM;
  }

  char * node_name_copy = kstrdup(node_name, GFP_KERNEL);
  if (!node_name_copy) {
    dev_warn(agnocast_device, "kstrdup failed. (insert_subscriber_info)\n");
    kfree(*new_info);
    return -ENOMEM;
  }

  const topic_local_id_t new_id = wrapper->topic.current_pubsub_id;
  wrapper->topic.current_pubsub_id++;

  (*new_info)->id = new_id;
  (*new_info)->pid = subscriber_pid;
  (*new_info)->qos_depth = qos_depth;
  (*new_info)->qos_is_transient_local = qos_is_transient_local;
  if (qos_is_transient_local) {
    (*new_info)->latest_received_entry_id = -1;
  } else {
    (*new_info)->latest_received_entry_id = wrapper->topic.current_entry_id++;
  }
  (*new_info)->node_name = node_name_copy;
  (*new_info)->is_take_sub = is_take_sub;
  (*new_info)->need_mmap_update = true;
  INIT_HLIST_NODE(&(*new_info)->node);
  uint32_t hash_val = hash_min(new_id, SUB_INFO_HASH_BITS);
  hash_add(wrapper->topic.sub_info_htable, &(*new_info)->node, hash_val);

  dev_info(
    agnocast_device,
    "Subscriber (topic_local_id=%d, pid=%d) is added to the topic (topic_name=%s). "
    "(insert_subscriber_info)\n",
    new_id, subscriber_pid, wrapper->key);

  // Check if the topic has any volatile publishers.
  if (qos_is_transient_local) {
    struct publisher_info * pub_info;
    int bkt_pub_info;
    hash_for_each(wrapper->topic.pub_info_htable, bkt_pub_info, pub_info, node)
    {
      if (!pub_info->qos_is_transient_local) {
        dev_warn(
          agnocast_device,
          "Incompatible QoS is set for the topic (topic_name=%s): subscriber is transient local "
          "but publisher is volatile. (insert_subscriber_info)\n",
          wrapper->key);
        break;
      }
    }
  }

  return 0;
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
  const struct topic_wrapper * wrapper, const topic_local_id_t publisher_id)
{
  struct publisher_info * info;
  uint32_t hash_val = hash_min(publisher_id, PUB_INFO_HASH_BITS);
  hash_for_each_possible(wrapper->topic.pub_info_htable, info, node, hash_val)
  {
    if (info->id == publisher_id) {
      return info;
    }
  }

  return NULL;
}

static int insert_publisher_info(
  struct topic_wrapper * wrapper, const char * node_name, const pid_t publisher_pid,
  const uint32_t qos_depth, const bool qos_is_transient_local, struct publisher_info ** new_info)
{
  int count = get_size_pub_info_htable(wrapper);
  if (count == MAX_PUBLISHER_NUM) {
    dev_warn(
      agnocast_device,
      "The number of publishers for the topic (topic_name=%s) reached the upper "
      "bound (MAX_PUBLISHER_NUM=%d), so no new publisher can be "
      "added. (insert_publisher_info)\n",
      wrapper->key, MAX_PUBLISHER_NUM);
    return -ENOBUFS;
  }

  *new_info = kmalloc(sizeof(struct publisher_info), GFP_KERNEL);
  if (!*new_info) {
    dev_warn(agnocast_device, "kmalloc failed. (insert_publisher_info)\n");
    return -ENOMEM;
  }

  char * node_name_copy = kstrdup(node_name, GFP_KERNEL);
  if (!node_name_copy) {
    dev_warn(agnocast_device, "kstrdup failed. (insert_publisher_info)\n");
    kfree(*new_info);
    return -ENOMEM;
  }

  const topic_local_id_t new_id = wrapper->topic.current_pubsub_id;
  wrapper->topic.current_pubsub_id++;

  (*new_info)->id = new_id;
  (*new_info)->pid = publisher_pid;
  (*new_info)->node_name = node_name_copy;
  (*new_info)->qos_depth = qos_depth;
  (*new_info)->qos_is_transient_local = qos_is_transient_local;
  (*new_info)->entries_num = 0;
  INIT_HLIST_NODE(&(*new_info)->node);
  uint32_t hash_val = hash_min(new_id, PUB_INFO_HASH_BITS);
  hash_add(wrapper->topic.pub_info_htable, &(*new_info)->node, hash_val);

  dev_info(
    agnocast_device,
    "Publisher (topic_local_id=%d, pid=%d) is added to the topic (topic_name=%s). "
    "(insert_publisher_info)\n",
    new_id, publisher_pid, wrapper->key);

  // Check if the topic has any transient local subscribers.
  if (!qos_is_transient_local) {
    struct subscriber_info * sub_info;
    int bkt_sub_info;
    hash_for_each(wrapper->topic.sub_info_htable, bkt_sub_info, sub_info, node)
    {
      if (sub_info->qos_is_transient_local) {
        dev_warn(
          agnocast_device,
          "Incompatible QoS is set for the topic (topic_name=%s): publisher is volatile "
          "but subscriber is transient local. (insert_publisher_info)\n",
          wrapper->key);
        break;
      }
    }
  }

  return 0;
}

static bool is_referenced(struct entry_node * en)
{
  // The referencing_ids array is always populated starting from the smallest index.
  // Therefore, the value -1 at index 0 is equivalent to a non-existent referencing.
  return (en->referencing_ids[0] != -1);
}

static void remove_reference_by_index(struct entry_node * en, int index)
{
  for (int i = index; i < MAX_REFERENCING_PUBSUB_NUM_PER_ENTRY - 1; i++) {
    en->referencing_ids[i] = en->referencing_ids[i + 1];
    en->reference_count[i] = en->reference_count[i + 1];
  }

  en->referencing_ids[MAX_REFERENCING_PUBSUB_NUM_PER_ENTRY - 1] = -1;
  en->reference_count[MAX_REFERENCING_PUBSUB_NUM_PER_ENTRY - 1] = 0;
  return;
}

static int increment_sub_rc(struct entry_node * en, const topic_local_id_t id)
{
  for (int i = 0; i < MAX_REFERENCING_PUBSUB_NUM_PER_ENTRY; i++) {
    if (en->referencing_ids[i] == id) {
      en->reference_count[i]++;
      return 0;
    }

    if (en->reference_count[i] == 0) {
      en->referencing_ids[i] = id;
      en->reference_count[i] = 1;
      return 0;
    }
  }

  dev_warn(
    agnocast_device,
    "Unreachable. The number of referencing publisher and subscribers reached the upper bound "
    "(MAX_REFERENCING_PUBSUB_NUM_PER_ENTRY=%d), so no new subscriber can reference. "
    "(increment_sub_rc)\n",
    MAX_REFERENCING_PUBSUB_NUM_PER_ENTRY);

  return -ENOBUFS;
}

static struct entry_node * find_message_entry(
  struct topic_wrapper * wrapper, const int64_t entry_id)
{
  struct rb_root * root = &wrapper->topic.entries;
  struct rb_node ** new = &(root->rb_node);

  while (*new) {
    struct entry_node * this = container_of(*new, struct entry_node, node);

    if (entry_id < this->entry_id) {
      new = &((*new)->rb_left);
    } else if (entry_id > this->entry_id) {
      new = &((*new)->rb_right);
    } else {
      return this;
    }
  }

  return NULL;
}

int increment_message_entry_rc(
  const char * topic_name, const topic_local_id_t pubsub_id, const int64_t entry_id)
{
  struct topic_wrapper * wrapper = find_topic(topic_name);
  if (!wrapper) {
    dev_warn(
      agnocast_device, "Topic (topic_name=%s) not found. (increment_message_entry_rc)\n",
      topic_name);
    return -EINVAL;
  }

  struct entry_node * en = find_message_entry(wrapper, entry_id);
  if (!en) {
    dev_warn(
      agnocast_device,
      "Message entry (topic_name=%s entry_id=%lld) not found. "
      "(increment_message_entry_rc)\n",
      topic_name, entry_id);
    return -EINVAL;
  }

  // Incrementing reference count is allowed only for subscribers
  if (!find_subscriber_info(wrapper, pubsub_id)) {
    dev_warn(
      agnocast_device,
      "Subscriber (id=%d) not found in the topic (topic_name=%s). (increment_message_entry_rc)\n",
      pubsub_id, wrapper->key);
    return -EINVAL;
  }

  int ret = increment_sub_rc(en, pubsub_id);
  if (ret < 0) {
    return ret;
  }

  return 0;
}

int decrement_message_entry_rc(
  const char * topic_name, const topic_local_id_t pubsub_id, const int64_t entry_id)
{
  struct topic_wrapper * wrapper = find_topic(topic_name);
  if (!wrapper) {
    dev_warn(
      agnocast_device, "Topic (topic_name=%s) not found. (decrement_message_entry_rc)\n",
      topic_name);
    return -EINVAL;
  }

  struct entry_node * en = find_message_entry(wrapper, entry_id);
  if (!en) {
    dev_warn(
      agnocast_device,
      "Message entry (topic_name=%s entry_id=%lld) not found. "
      "(decrement_message_entry_rc)\n",
      topic_name, entry_id);
    return -EINVAL;
  }

  // decrement reference_count
  for (int i = 0; i < MAX_REFERENCING_PUBSUB_NUM_PER_ENTRY; i++) {
    if (en->referencing_ids[i] == pubsub_id) {
      en->reference_count[i]--;
      if (en->reference_count[i] == 0) {
        remove_reference_by_index(en, i);
      }

      return 0;
    }
  }

  dev_warn(
    agnocast_device,
    "Try to decrement reference of Publisher/Subscriber (pubsub_id=%d) for message entry "
    "(topic_name=%s entry_id=%lld), but it is not found. (decrement_message_entry_rc)\n",
    pubsub_id, topic_name, entry_id);

  return -EINVAL;
}

static int insert_message_entry(
  struct topic_wrapper * wrapper, struct publisher_info * pub_info, uint64_t msg_virtual_address,
  union ioctl_publish_args * ioctl_ret)
{
  struct entry_node * new_node = kmalloc(sizeof(struct entry_node), GFP_KERNEL);
  if (!new_node) {
    dev_warn(agnocast_device, "kmalloc failed. (insert_message_entry)\n");
    return -ENOMEM;
  }

  new_node->entry_id = wrapper->topic.current_entry_id++;
  new_node->publisher_id = pub_info->id;
  new_node->msg_virtual_address = msg_virtual_address;
  new_node->referencing_ids[0] = pub_info->id;
  new_node->reference_count[0] = 1;
  for (int i = 1; i < MAX_REFERENCING_PUBSUB_NUM_PER_ENTRY; i++) {
    new_node->referencing_ids[i] = -1;
    new_node->reference_count[i] = 0;
  }

  struct rb_root * root = &wrapper->topic.entries;
  struct rb_node ** new = &(root->rb_node);
  struct rb_node * parent = NULL;

  while (*new) {
    const struct entry_node * this = container_of(*new, struct entry_node, node);
    parent = *new;

    if (new_node->entry_id > this->entry_id) {
      new = &((*new)->rb_right);
    } else {
      dev_warn(
        agnocast_device,
        "Unreachable: New message entry (entry_id=%lld) does not have the largest entry_id in the "
        "topic (topic_name=%s). (insert_message_entry)\n",
        new_node->entry_id, wrapper->key);
      kfree(new_node);
      return -ECANCELED;
    }
  }

  rb_link_node(&new_node->node, parent, new);
  rb_insert_color(&new_node->node, root);

  pub_info->entries_num++;

  dev_dbg(
    agnocast_device,
    "Insert a message entry (topic_name=%s entry_id=%lld msg_virtual_address=%lld). "
    "(insert_message_entry)\n",
    wrapper->key, new_node->entry_id, msg_virtual_address);

  ioctl_ret->ret_entry_id = new_node->entry_id;

  return 0;
}

static struct process_info * find_process_info(const pid_t pid)
{
  struct process_info * proc_info;
  uint32_t hash_val = hash_min(pid, PROC_INFO_HASH_BITS);
  hash_for_each_possible(proc_info_htable, proc_info, node, hash_val)
  {
    if (proc_info->pid == pid) {
      return proc_info;
    }
  }

  return NULL;
}


static int set_publisher_shm_info(
  const struct topic_wrapper * wrapper, const pid_t subscriber_pid,
  struct publisher_shm_info * pub_shm_info)
{
  uint32_t publisher_num = 0;
  struct publisher_info * pub_info;
  int bkt;
  hash_for_each(wrapper->topic.pub_info_htable, bkt, pub_info, node)
  {
    if (subscriber_pid == pub_info->pid) {
      continue;
    }

    const struct process_info * proc_info = find_process_info(pub_info->pid);
    if (!proc_info) {
      continue;
    }

    int ret = reference_memory(proc_info->mempool_entry, subscriber_pid);
    if (ret < 0) {
      if (ret == -EEXIST) {
        continue;
      } else if (ret == -ENOBUFS) {
        dev_warn(
          agnocast_device,
          "Process (pid=%d)'s memory pool is already full (MAX_PROCESS_NUM_PER_MEMPOOL=%d), so no "
          "new mapping from pid=%d can be created. (set_publisher_shm_info)\n",
          pub_info->pid, MAX_PROCESS_NUM_PER_MEMPOOL, subscriber_pid);
        return ret;
      } else {
        dev_warn(
          agnocast_device,
          "Unreachable: process (pid=%d) failed to reference memory of (pid=%d). "
          "(set_publisher_shm_info)\n",
          subscriber_pid, pub_info->pid);
        return ret;
      }
    }

    if (publisher_num == MAX_PUBLISHER_NUM) {
      dev_warn(
        agnocast_device,
        "Unreachable: the number of publisher processes to be mapped exceeds the maximum number "
        "that can be returned at once in a call from this subscriber process (topic_name=%s, "
        "subscriber_pid=%d). (set_publisher_shm_info)\n",
        wrapper->key, subscriber_pid);
      return -ENOBUFS;
    }

    pub_shm_info->publisher_pids[publisher_num] = pub_info->pid;
    pub_shm_info->shm_addrs[publisher_num] = proc_info->mempool_entry->addr;
    pub_shm_info->shm_sizes[publisher_num] = proc_info->shm_size;
    publisher_num++;
  }

  pub_shm_info->publisher_num = publisher_num;

  return 0;
}

int subscriber_add(
  const char * topic_name, const char * node_name, const pid_t subscriber_pid_arg,
  const uint32_t qos_depth, const bool qos_is_transient_local, const bool is_take_sub,
  union ioctl_subscriber_args * ioctl_ret)
{
  int ret = 0;
  ioctl_ret->ret_pub_shm_info.publisher_num = 0;

#ifdef KUNIT_BUILD
  const pid_t subscriber_pid = subscriber_pid_arg;
#else
  const pid_t subscriber_pid = convert_pid_to_global(subscriber_pid_arg);
#endif

  struct topic_wrapper * wrapper;
  ret = add_topic(topic_name, &wrapper);
  if (ret < 0) {
    goto out;
  }

  struct subscriber_info * sub_info;
  ret = insert_subscriber_info(
    wrapper, node_name, subscriber_pid, qos_depth, qos_is_transient_local, is_take_sub, &sub_info);
  if (ret < 0) {
    goto out;
  }

  ioctl_ret->ret_id = sub_info->id;

out:
#ifndef KUNIT_BUILD
  for (uint32_t i = 0; i < ioctl_ret->ret_pub_shm_info.publisher_num; i++) {
    ioctl_ret->ret_pub_shm_info.publisher_pids[i] =
      convert_pid_to_local(ioctl_ret->ret_pub_shm_info.publisher_pids[i]);
  }
#endif

  return ret;
}

int publisher_add(
  const char * topic_name, const char * node_name, const pid_t publisher_pid_arg,
  const uint32_t qos_depth, const bool qos_is_transient_local,
  union ioctl_publisher_args * ioctl_ret)
{
  int ret;

#ifdef KUNIT_BUILD
  const pid_t publisher_pid = publisher_pid_arg;
#else
  const pid_t publisher_pid = convert_pid_to_global(publisher_pid_arg);
#endif

  struct topic_wrapper * wrapper;
  ret = add_topic(topic_name, &wrapper);
  if (ret < 0) {
    return ret;
  }

  struct publisher_info * pub_info;
  ret = insert_publisher_info(
    wrapper, node_name, publisher_pid, qos_depth, qos_is_transient_local, &pub_info);
  if (ret < 0) {
    return ret;
  }

  ioctl_ret->ret_id = pub_info->id;

  // set true to subscriber_info.need_mmap_update to notify
  struct subscriber_info * sub_info;
  int bkt_sub_info;
  hash_for_each(wrapper->topic.sub_info_htable, bkt_sub_info, sub_info, node)
  {
    sub_info->need_mmap_update = true;
  }

  return 0;
}

static int release_msgs_to_meet_depth(
  struct topic_wrapper * wrapper, struct publisher_info * pub_info,
  union ioctl_publish_args * ioctl_ret)
{
  ioctl_ret->ret_released_num = 0;

  if (pub_info->entries_num <= pub_info->qos_depth) {
    return 0;
  }

  const uint32_t leak_warn_threshold = (pub_info->qos_depth <= 100)
                                         ? 100 + pub_info->qos_depth
                                         : pub_info->qos_depth * 2;  // This is rough value.
  if (pub_info->entries_num > leak_warn_threshold) {
    dev_warn(
      agnocast_device,
      "For some reason, the reference count hasn't been decremented, causing the number of "
      "messages for this publisher to increase. (topic_name=%s, id=%d, entries_num=%d)."
      "(release_msgs_to_meet_depth)\n",
      wrapper->key, pub_info->id, pub_info->entries_num);
  }

  struct rb_node * node = rb_first(&wrapper->topic.entries);
  if (!node) {
    dev_warn(
      agnocast_device,
      "Unreachable: Failed to get message entries in publisher (id=%d). "
      "(release_msgs_to_meet_depth)\n",
      pub_info->id);
    return -ENODATA;
  }

  // Number of entries exceeding qos_depth
  uint32_t num_search_entries = pub_info->entries_num - pub_info->qos_depth;

  // NOTE:
  //   The searched message is either deleted or, if a reference count remains, is not deleted.
  //   In both cases, this number of searches is sufficient, as it does not affect the Queue size of
  //   QoS.
  //
  // HACK:
  //   The current implementation only releases a maximum of MAX_RELEASE_NUM messages at a time, and
  //   if there are more messages to release, qos_depth is temporarily not met.
  //   However, it is rare for the reference_count of more than MAX_RELEASE_NUM messages
  //   that are out of qos_depth to be zero at a specific time. If this happens, as long as the
  //   publisher's qos_depth is greater than the subscriber's qos_depth, this has little effect on
  //   system behavior.
  while (num_search_entries > 0 && ioctl_ret->ret_released_num < MAX_RELEASE_NUM) {
    struct entry_node * en = container_of(node, struct entry_node, node);
    node = rb_next(node);
    if (!node) {
      dev_warn(
        agnocast_device,
        "Unreachable: entries_num is inconsistent with actual message entry num. "
        "(release_msgs_to_meet_depth)\n");
      return -ENODATA;
    }

    if (en->publisher_id != pub_info->id) continue;

    num_search_entries--;

    // This is not counted in a Queue size of QoS.
    if (is_referenced(en)) continue;

    ioctl_ret->ret_released_addrs[ioctl_ret->ret_released_num] = en->msg_virtual_address;
    ioctl_ret->ret_released_num++;

    rb_erase(&en->node, &wrapper->topic.entries);
    kfree(en);

    pub_info->entries_num--;

    dev_dbg(
      agnocast_device,
      "Release oldest message in the publisher_info (id=$%d) of the topic "
      "(topic_name=%s) with qos_depth=%d. (release_msgs_to_meet_depth)\n",
      pub_info->id, wrapper->key, pub_info->qos_depth);
  }

  return 0;
}

int receive_msg(
  const char * topic_name, const topic_local_id_t subscriber_id,
  union ioctl_receive_msg_args * ioctl_ret)
{
  int ret = 0;
  ioctl_ret->ret_pub_shm_info.publisher_num = 0;

  struct topic_wrapper * wrapper = find_topic(topic_name);
  if (!wrapper) {
    dev_warn(agnocast_device, "Topic (topic_name=%s) not found. (receive_msg)\n", topic_name);
    ret = -EINVAL;
    goto out;
  }

  struct subscriber_info * sub_info = find_subscriber_info(wrapper, subscriber_id);
  if (!sub_info) {
    dev_warn(
      agnocast_device,
      "Subscriber (id=%d) for the topic (topic_name=%s) not found. "
      "(receive_msg)\n",
      subscriber_id, topic_name);
    ret = -EINVAL;
    goto out;
  }

  // Receive msg
  ioctl_ret->ret_entry_num = 0;
  bool sub_info_updated = false;
  int64_t latest_received_entry_id = sub_info->latest_received_entry_id;
  for (struct rb_node * node = rb_last(&wrapper->topic.entries); node; node = rb_prev(node)) {
    struct entry_node * en = container_of(node, struct entry_node, node);
    if (
      (en->entry_id <= latest_received_entry_id) ||
      (sub_info->qos_depth == ioctl_ret->ret_entry_num)) {
      break;
    }

    const struct publisher_info * pub_info = find_publisher_info(wrapper, en->publisher_id);
    if (!pub_info) {
      dev_warn(
        agnocast_device,
        "Unreachable: corresponding publisher(id=%d) not found for entry(id=%lld) in "
        "topic(topic_name=%s). (receive_msg)\n",
        en->publisher_id, en->entry_id, topic_name);
      return -ENODATA;
    }

    const struct process_info * proc_info = find_process_info(pub_info->pid);
    if (!proc_info) {
      continue;
    }

    int ret = increment_sub_rc(en, subscriber_id);
    if (ret < 0) {
      goto out;
    }

    ioctl_ret->ret_entry_ids[ioctl_ret->ret_entry_num] = en->entry_id;
    ioctl_ret->ret_entry_addrs[ioctl_ret->ret_entry_num] = en->msg_virtual_address;
    ioctl_ret->ret_entry_num++;

    if (!sub_info_updated) {
      sub_info->latest_received_entry_id = en->entry_id;
      sub_info_updated = true;
    }
  }

  // Check if there is any publisher that need to be mmapped
  if (!sub_info->need_mmap_update) {
    ioctl_ret->ret_pub_shm_info.publisher_num = 0;
    goto out;
  }

  ret = set_publisher_shm_info(wrapper, sub_info->pid, &ioctl_ret->ret_pub_shm_info);
  if (ret < 0) {
    goto out;
  }

  sub_info->need_mmap_update = false;

out:
#ifndef KUNIT_BUILD
  for (uint32_t i = 0; i < ioctl_ret->ret_pub_shm_info.publisher_num; i++) {
    ioctl_ret->ret_pub_shm_info.publisher_pids[i] =
      convert_pid_to_local(ioctl_ret->ret_pub_shm_info.publisher_pids[i]);
  }
#endif

  return ret;
}

int publish_msg(
  const char * topic_name, const topic_local_id_t publisher_id, const uint64_t msg_virtual_address,
  union ioctl_publish_args * ioctl_ret)
{
  struct topic_wrapper * wrapper = find_topic(topic_name);
  if (!wrapper) {
    dev_warn(agnocast_device, "Topic (topic_name=%s) not found. (publish_msg)\n", topic_name);
    return -EINVAL;
  }

  struct publisher_info * pub_info = find_publisher_info(wrapper, publisher_id);
  if (!pub_info) {
    dev_warn(
      agnocast_device, "Publisher (id=%d) not found in the topic (topic_name=%s). (publish_msg)\n",
      publisher_id, topic_name);
    return -EINVAL;
  }

  int ret = insert_message_entry(wrapper, pub_info, msg_virtual_address, ioctl_ret);
  if (ret < 0) {
    return ret;
  }

  ret = release_msgs_to_meet_depth(wrapper, pub_info, ioctl_ret);
  if (ret < 0) {
    return ret;
  }

  int subscriber_num = 0;
  struct subscriber_info * sub_info;
  int bkt_sub_info;
  hash_for_each(wrapper->topic.sub_info_htable, bkt_sub_info, sub_info, node)
  {
    if (sub_info->is_take_sub) continue;
    ioctl_ret->ret_subscriber_ids[subscriber_num] = sub_info->id;
    subscriber_num++;
  }
  ioctl_ret->ret_subscriber_num = subscriber_num;

  return 0;
}

int take_msg(
  const char * topic_name, const topic_local_id_t subscriber_id, bool allow_same_message,
  union ioctl_take_msg_args * ioctl_ret)
{
  int ret = 0;
  ioctl_ret->ret_pub_shm_info.publisher_num = 0;

  struct topic_wrapper * wrapper = find_topic(topic_name);
  if (!wrapper) {
    dev_warn(agnocast_device, "Topic (topic_name=%s) not found. (take_msg)\n", topic_name);
    ret = -EINVAL;
    goto out;
  }

  struct subscriber_info * sub_info = find_subscriber_info(wrapper, subscriber_id);
  if (!sub_info) {
    dev_warn(
      agnocast_device, "Subscriber (id=%d) for the topic (topic_name=%s) not found. (take_msg)\n",
      subscriber_id, topic_name);
    ret = -EINVAL;
    goto out;
  }

  // These remains 0 if no message is found to take.
  ioctl_ret->ret_addr = 0;
  ioctl_ret->ret_entry_id = -1;

  uint32_t searched_count = 0;
  struct entry_node * candidate_en = NULL;
  struct rb_node * node = rb_last(&wrapper->topic.entries);
  while (node && searched_count < sub_info->qos_depth) {
    struct entry_node * en = container_of(node, struct entry_node, node);
    node = rb_prev(node);

    if (!allow_same_message && en->entry_id == sub_info->latest_received_entry_id) {
      break;  // Don't take the same message if it's not allowed
    }

    if (en->entry_id < sub_info->latest_received_entry_id) {
      break;  // Never take any messages that are older than the most recently received
    }

    const struct publisher_info * pub_info = find_publisher_info(wrapper, en->publisher_id);
    if (!pub_info) {
      dev_warn(
        agnocast_device,
        "Unreachable: corresponding publisher(id=%d) not found for entry(id=%lld) in "
        "topic(topic_name=%s). (take_msg)\n",
        en->publisher_id, en->entry_id, topic_name);
      return -ENODATA;
    }

    const struct process_info * proc_info = find_process_info(pub_info->pid);
    if (!proc_info) {
      continue;
    }

    candidate_en = en;
    searched_count++;
  }

  if (candidate_en) {
    ret = increment_sub_rc(candidate_en, subscriber_id);
    if (ret < 0) {
      goto out;
    }

    ioctl_ret->ret_addr = candidate_en->msg_virtual_address;
    ioctl_ret->ret_entry_id = candidate_en->entry_id;

    sub_info->latest_received_entry_id = ioctl_ret->ret_entry_id;
  }

  // Check if there is any publisher that need to be mmapped
  if (!sub_info->need_mmap_update) {
    ioctl_ret->ret_pub_shm_info.publisher_num = 0;
    goto out;
  }

  ret = set_publisher_shm_info(wrapper, sub_info->pid, &ioctl_ret->ret_pub_shm_info);
  if (ret < 0) {
    goto out;
  }

  sub_info->need_mmap_update = false;

out:
#ifndef KUNIT_BUILD
  for (uint32_t i = 0; i < ioctl_ret->ret_pub_shm_info.publisher_num; i++) {
    ioctl_ret->ret_pub_shm_info.publisher_pids[i] =
      convert_pid_to_local(ioctl_ret->ret_pub_shm_info.publisher_pids[i]);
  }
#endif

  return ret;
}

int new_shm_addr(const pid_t pid_arg, uint64_t shm_size, union ioctl_new_shm_args * ioctl_ret)
{
#ifdef KUNIT_BUILD
  const pid_t pid = pid_arg;
#else
  const pid_t pid = convert_pid_to_global(pid_arg);
#endif

  if (shm_size % PAGE_SIZE != 0) {
    dev_warn(
      agnocast_device, "shm_size=%llu is not aligned to PAGE_SIZE=%lu. (new_shm_addr)\n", shm_size,
      PAGE_SIZE);
    return -EINVAL;
  }

  if (find_process_info(pid)) {
    dev_warn(agnocast_device, "Process (pid=%d) already exists. (new_shm_addr)\n", pid);
    return -EINVAL;
  }

  struct process_info * new_proc_info = kmalloc(sizeof(struct process_info), GFP_KERNEL);
  if (!new_proc_info) {
    dev_warn(agnocast_device, "kmalloc failed. (new_shm_addr)\n");
    return -ENOMEM;
  }

  new_proc_info->pid = pid;
  new_proc_info->shm_size = shm_size;

  new_proc_info->mempool_entry = assign_memory(pid, shm_size);
  if (!new_proc_info->mempool_entry) {
    dev_warn(
      agnocast_device,
      "Process (pid=%d) failed to allocate memory (shm_size=%llu). (new_shm_addr)\n", pid,
      shm_size);
    kfree(new_proc_info);
    return -ENOMEM;
  }

  INIT_HLIST_NODE(&new_proc_info->node);
  uint32_t hash_val = hash_min(new_proc_info->pid, PROC_INFO_HASH_BITS);
  hash_add(proc_info_htable, &new_proc_info->node, hash_val);

  ioctl_ret->ret_addr = new_proc_info->mempool_entry->addr;
  return 0;
}

static int get_version(struct ioctl_get_version_args * ioctl_ret)
{
  memcpy(ioctl_ret->ret_version, VERSION, strlen(VERSION) + 1);

  return 0;
}

int get_subscriber_num(const char * topic_name, union ioctl_get_subscriber_num_args * ioctl_ret)
{
  struct topic_wrapper * wrapper = find_topic(topic_name);
  if (wrapper) {
    ioctl_ret->ret_subscriber_num = get_size_sub_info_htable(wrapper);
  } else {
    ioctl_ret->ret_subscriber_num = 0;
  }

  return 0;
}

int get_topic_list(union ioctl_topic_list_args * topic_list_args)
{
  uint32_t topic_num = 0;

  struct topic_wrapper * wrapper;
  int bkt_topic;
  hash_for_each(topic_hashtable, bkt_topic, wrapper, node)
  {
    if (topic_num >= MAX_TOPIC_NUM) {
      dev_warn(agnocast_device, "The number of topics is over MAX_TOPIC_NUM=%d\n", MAX_TOPIC_NUM);
      return -ENOBUFS;
    }

    if (copy_to_user(
          (char __user *)(topic_list_args->topic_name_buffer_addr +
                          topic_num * TOPIC_NAME_BUFFER_SIZE),
          wrapper->key, strlen(wrapper->key) + 1)) {
      return -EFAULT;
    }

    topic_num++;
  }

  topic_list_args->ret_topic_num = topic_num;

  return 0;
}

static int get_node_subscriber_topics(
  const char * node_name, union ioctl_node_info_args * node_info_args)
{
  uint32_t topic_num = 0;

  struct topic_wrapper * wrapper;
  int bkt_topic;

  hash_for_each(topic_hashtable, bkt_topic, wrapper, node)
  {
    struct subscriber_info * sub_info;
    int bkt_sub_info;
    hash_for_each(wrapper->topic.sub_info_htable, bkt_sub_info, sub_info, node)
    {
      if (strncmp(sub_info->node_name, node_name, strlen(node_name)) == 0) {
        if (topic_num >= MAX_TOPIC_NUM) {
          dev_warn(
            agnocast_device, "The number of topics is over MAX_TOPIC_NUM=%d\n", MAX_TOPIC_NUM);
          return -ENOBUFS;
        }

        if (copy_to_user(
              (char __user *)(node_info_args->topic_name_buffer_addr +
                              topic_num * TOPIC_NAME_BUFFER_SIZE),
              wrapper->key, strlen(wrapper->key) + 1)) {
          return -EFAULT;
        }

        topic_num++;
        break;
      }
    }
  }

  node_info_args->ret_topic_num = topic_num;

  return 0;
}

static int get_node_publisher_topics(
  const char * node_name, union ioctl_node_info_args * node_info_args)
{
  uint32_t topic_num = 0;

  struct topic_wrapper * wrapper;
  int bkt_topic;

  hash_for_each(topic_hashtable, bkt_topic, wrapper, node)
  {
    struct publisher_info * pub_info;
    int bkt_pub_info;
    hash_for_each(wrapper->topic.pub_info_htable, bkt_pub_info, pub_info, node)
    {
      if (strncmp(pub_info->node_name, node_name, strlen(node_name)) == 0) {
        if (topic_num >= MAX_TOPIC_NUM) {
          dev_warn(
            agnocast_device, "The number of topics is over MAX_TOPIC_NUM=%d\n", MAX_TOPIC_NUM);
          return -ENOBUFS;
        }

        if (copy_to_user(
              (char __user *)(node_info_args->topic_name_buffer_addr +
                              topic_num * TOPIC_NAME_BUFFER_SIZE),
              wrapper->key, strlen(wrapper->key) + 1)) {
          return -EFAULT;
        }

        topic_num++;
        break;
      }
    }
  }

  node_info_args->ret_topic_num = topic_num;

  return 0;
}

static int get_topic_subscriber_info(
  const char * topic_name, union ioctl_topic_info_args * topic_info_args)
{
  topic_info_args->ret_topic_info_ret_num = 0;

  struct topic_wrapper * wrapper = find_topic(topic_name);
  if (!wrapper) {
    return 0;
  }

  uint32_t subscriber_num = 0;
  struct subscriber_info * sub_info;
  int bkt_sub_info;

  struct topic_info_ret __user * user_buffer =
    (struct topic_info_ret *)topic_info_args->topic_info_ret_buffer_addr;

  struct topic_info_ret * topic_info_mem =
    kmalloc(sizeof(struct topic_info_ret) * MAX_TOPIC_INFO_RET_NUM, GFP_KERNEL);
  if (!topic_info_mem) {
    return -ENOMEM;
  }

  hash_for_each(wrapper->topic.sub_info_htable, bkt_sub_info, sub_info, node)
  {
    if (subscriber_num >= MAX_TOPIC_INFO_RET_NUM) {
      dev_warn(
        agnocast_device, "The number of subscribers is over MAX_TOPIC_INFO_RET_NUM=%d\n",
        MAX_TOPIC_INFO_RET_NUM);
      kfree(topic_info_mem);
      return -ENOBUFS;
    }

    if (!sub_info->node_name) {
      kfree(topic_info_mem);
      return -EFAULT;
    }

    struct topic_info_ret * temp_info = &topic_info_mem[subscriber_num];

    strncpy(temp_info->node_name, sub_info->node_name, strlen(sub_info->node_name));
    temp_info->qos_depth = sub_info->qos_depth;
    temp_info->qos_is_transient_local = sub_info->qos_is_transient_local;

    subscriber_num++;
  }

  if (copy_to_user(user_buffer, topic_info_mem, sizeof(struct topic_info_ret) * subscriber_num)) {
    kfree(topic_info_mem);
    return -EFAULT;
  }

  kfree(topic_info_mem);
  topic_info_args->ret_topic_info_ret_num = subscriber_num;

  return 0;
}

static int get_topic_publisher_info(
  const char * topic_name, union ioctl_topic_info_args * topic_info_args)
{
  topic_info_args->ret_topic_info_ret_num = 0;

  struct topic_wrapper * wrapper = find_topic(topic_name);
  if (!wrapper) {
    return 0;
  }

  uint32_t publisher_num = 0;
  struct publisher_info * pub_info;
  int bkt_pub_info;

  struct topic_info_ret __user * user_buffer =
    (struct topic_info_ret *)topic_info_args->topic_info_ret_buffer_addr;

  struct topic_info_ret * topic_info_mem =
    kmalloc(sizeof(struct topic_info_ret) * MAX_TOPIC_INFO_RET_NUM, GFP_KERNEL);
  if (!topic_info_mem) {
    return -ENOMEM;
  }

  hash_for_each(wrapper->topic.pub_info_htable, bkt_pub_info, pub_info, node)
  {
    if (publisher_num >= MAX_TOPIC_INFO_RET_NUM) {
      dev_warn(
        agnocast_device, "The number of publishers is over MAX_TOPIC_INFO_RET_NUM=%d\n",
        MAX_TOPIC_INFO_RET_NUM);
      kfree(topic_info_mem);
      return -ENOBUFS;
    }

    if (!pub_info->node_name) {
      kfree(topic_info_mem);
      return -EFAULT;
    }

    struct topic_info_ret * temp_info = &topic_info_mem[publisher_num];

    strncpy(temp_info->node_name, pub_info->node_name, strlen(pub_info->node_name));
    temp_info->qos_depth = pub_info->qos_depth;
    temp_info->qos_is_transient_local = pub_info->qos_is_transient_local;

    publisher_num++;
  }

  if (copy_to_user(user_buffer, topic_info_mem, sizeof(struct topic_info_ret) * publisher_num)) {
    kfree(topic_info_mem);
    return -EFAULT;
  }

  kfree(topic_info_mem);
  topic_info_args->ret_topic_info_ret_num = publisher_num;

  return 0;
}

static long agnocast_ioctl(struct file * file, unsigned int cmd, unsigned long arg)
{
  mutex_lock(&global_mutex);
  int ret = 0;

  if (cmd == AGNOCAST_SUBSCRIBER_ADD_CMD) {
    union ioctl_subscriber_args sub_args;
    char topic_name_buf[TOPIC_NAME_BUFFER_SIZE];
    char node_name_buf[NODE_NAME_BUFFER_SIZE];
    if (copy_from_user(&sub_args, (union ioctl_subscriber_args __user *)arg, sizeof(sub_args)))
      goto return_EFAULT;
    if (
      sub_args.topic_name.len >= TOPIC_NAME_BUFFER_SIZE ||
      sub_args.node_name.len >= NODE_NAME_BUFFER_SIZE)
      goto return_EINVAL;
    if (copy_from_user(
          topic_name_buf, (char __user *)sub_args.topic_name.ptr, sub_args.topic_name.len))
      goto return_EFAULT;
    topic_name_buf[sub_args.topic_name.len] = '\0';
    if (copy_from_user(
          node_name_buf, (char __user *)sub_args.node_name.ptr, sub_args.node_name.len))
      goto return_EFAULT;
    node_name_buf[sub_args.node_name.len] = '\0';
    ret = subscriber_add(
      topic_name_buf, node_name_buf, sub_args.subscriber_pid, sub_args.qos_depth,
      sub_args.qos_is_transient_local, sub_args.is_take_sub, &sub_args);
    if (copy_to_user((union ioctl_subscriber_args __user *)arg, &sub_args, sizeof(sub_args)))
      goto return_EFAULT;
  } else if (cmd == AGNOCAST_PUBLISHER_ADD_CMD) {
    union ioctl_publisher_args pub_args;
    char topic_name_buf[TOPIC_NAME_BUFFER_SIZE];
    char node_name_buf[NODE_NAME_BUFFER_SIZE];
    if (copy_from_user(&pub_args, (union ioctl_publisher_args __user *)arg, sizeof(pub_args)))
      goto return_EFAULT;
    if (
      pub_args.topic_name.len >= TOPIC_NAME_BUFFER_SIZE ||
      pub_args.node_name.len >= NODE_NAME_BUFFER_SIZE)
      goto return_EINVAL;
    if (copy_from_user(
          topic_name_buf, (char __user *)pub_args.topic_name.ptr, pub_args.topic_name.len))
      goto return_EFAULT;
    topic_name_buf[pub_args.topic_name.len] = '\0';
    if (copy_from_user(
          node_name_buf, (char __user *)pub_args.node_name.ptr, pub_args.node_name.len))
      goto return_EFAULT;
    node_name_buf[pub_args.node_name.len] = '\0';
    ret = publisher_add(
      topic_name_buf, node_name_buf, pub_args.publisher_pid, pub_args.qos_depth,
      pub_args.qos_is_transient_local, &pub_args);
    if (copy_to_user((union ioctl_publisher_args __user *)arg, &pub_args, sizeof(pub_args)))
      goto return_EFAULT;
  } else if (cmd == AGNOCAST_INCREMENT_RC_CMD) {
    struct ioctl_update_entry_args entry_args;
    char topic_name_buf[TOPIC_NAME_BUFFER_SIZE];
    if (copy_from_user(
          &entry_args, (struct ioctl_update_entry_args __user *)arg, sizeof(entry_args)))
      goto return_EFAULT;
    if (entry_args.topic_name.len >= TOPIC_NAME_BUFFER_SIZE) goto return_EINVAL;
    if (copy_from_user(
          topic_name_buf, (char __user *)entry_args.topic_name.ptr, entry_args.topic_name.len))
      goto return_EFAULT;
    topic_name_buf[entry_args.topic_name.len] = '\0';
    ret = increment_message_entry_rc(topic_name_buf, entry_args.pubsub_id, entry_args.entry_id);
  } else if (cmd == AGNOCAST_DECREMENT_RC_CMD) {
    struct ioctl_update_entry_args entry_args;
    char topic_name_buf[TOPIC_NAME_BUFFER_SIZE];
    if (copy_from_user(
          &entry_args, (struct ioctl_update_entry_args __user *)arg, sizeof(entry_args)))
      goto return_EFAULT;
    if (entry_args.topic_name.len >= TOPIC_NAME_BUFFER_SIZE) goto return_EINVAL;
    if (copy_from_user(
          topic_name_buf, (char __user *)entry_args.topic_name.ptr, entry_args.topic_name.len))
      goto return_EFAULT;
    topic_name_buf[entry_args.topic_name.len] = '\0';
    ret = decrement_message_entry_rc(topic_name_buf, entry_args.pubsub_id, entry_args.entry_id);
  } else if (cmd == AGNOCAST_RECEIVE_MSG_CMD) {
    union ioctl_receive_msg_args receive_msg_args;
    char topic_name_buf[TOPIC_NAME_BUFFER_SIZE];
    if (copy_from_user(
          &receive_msg_args, (union ioctl_receive_msg_args __user *)arg, sizeof(receive_msg_args)))
      goto return_EFAULT;
    if (receive_msg_args.topic_name.len >= TOPIC_NAME_BUFFER_SIZE) goto return_EINVAL;
    if (copy_from_user(
          topic_name_buf, (char __user *)receive_msg_args.topic_name.ptr,
          receive_msg_args.topic_name.len))
      goto return_EFAULT;
    topic_name_buf[receive_msg_args.topic_name.len] = '\0';
    ret = receive_msg(topic_name_buf, receive_msg_args.subscriber_id, &receive_msg_args);
    if (copy_to_user(
          (union ioctl_receive_msg_args __user *)arg, &receive_msg_args, sizeof(receive_msg_args)))
      goto return_EFAULT;
  } else if (cmd == AGNOCAST_PUBLISH_MSG_CMD) {
    union ioctl_publish_args publish_args;
    char topic_name_buf[TOPIC_NAME_BUFFER_SIZE];
    if (copy_from_user(&publish_args, (union ioctl_publish_args __user *)arg, sizeof(publish_args)))
      goto return_EFAULT;
    if (publish_args.topic_name.len >= TOPIC_NAME_BUFFER_SIZE) goto return_EINVAL;
    if (copy_from_user(
          topic_name_buf, (char __user *)publish_args.topic_name.ptr, publish_args.topic_name.len))
      goto return_EFAULT;
    topic_name_buf[publish_args.topic_name.len] = '\0';
    ret = publish_msg(
      topic_name_buf, publish_args.publisher_id, publish_args.msg_virtual_address, &publish_args);
    if (copy_to_user((union ioctl_publish_args __user *)arg, &publish_args, sizeof(publish_args)))
      goto return_EFAULT;
  } else if (cmd == AGNOCAST_TAKE_MSG_CMD) {
    union ioctl_take_msg_args take_args;
    char topic_name_buf[TOPIC_NAME_BUFFER_SIZE];
    if (copy_from_user(&take_args, (union ioctl_take_msg_args __user *)arg, sizeof(take_args)))
      goto return_EFAULT;
    if (take_args.topic_name.len >= TOPIC_NAME_BUFFER_SIZE) goto return_EINVAL;
    if (copy_from_user(
          topic_name_buf, (char __user *)take_args.topic_name.ptr, take_args.topic_name.len))
      goto return_EFAULT;
    topic_name_buf[take_args.topic_name.len] = '\0';
    ret =
      take_msg(topic_name_buf, take_args.subscriber_id, take_args.allow_same_message, &take_args);
    if (copy_to_user((union ioctl_take_msg_args __user *)arg, &take_args, sizeof(take_args)))
      goto return_EFAULT;
  } else if (cmd == AGNOCAST_NEW_SHM_CMD) {
    union ioctl_new_shm_args new_shm_args;
    if (copy_from_user(&new_shm_args, (union ioctl_new_shm_args __user *)arg, sizeof(new_shm_args)))
      goto return_EFAULT;
    ret = new_shm_addr(new_shm_args.pid, new_shm_args.shm_size, &new_shm_args);
    if (copy_to_user((union ioctl_new_shm_args __user *)arg, &new_shm_args, sizeof(new_shm_args)))
      goto return_EFAULT;
  } else if (cmd == AGNOCAST_GET_VERSION_CMD) {
    struct ioctl_get_version_args get_version_args;
    ret = get_version(&get_version_args);
    if (copy_to_user(
          (struct ioctl_get_version_args __user *)arg, &get_version_args, sizeof(get_version_args)))
      goto return_EFAULT;
  } else if (cmd == AGNOCAST_GET_SUBSCRIBER_NUM_CMD) {
    union ioctl_get_subscriber_num_args get_subscriber_num_args;
    char topic_name_buf[TOPIC_NAME_BUFFER_SIZE];
    if (copy_from_user(
          &get_subscriber_num_args, (union ioctl_get_subscriber_num_args __user *)arg,
          sizeof(get_subscriber_num_args)))
      goto return_EFAULT;
    if (get_subscriber_num_args.topic_name.len >= TOPIC_NAME_BUFFER_SIZE) goto return_EINVAL;
    if (copy_from_user(
          topic_name_buf, (char __user *)get_subscriber_num_args.topic_name.ptr,
          get_subscriber_num_args.topic_name.len))
      goto return_EFAULT;
    topic_name_buf[get_subscriber_num_args.topic_name.len] = '\0';
    ret = get_subscriber_num(topic_name_buf, &get_subscriber_num_args);
    if (copy_to_user(
          (union ioctl_get_subscriber_num_args __user *)arg, &get_subscriber_num_args,
          sizeof(get_subscriber_num_args)))
      goto return_EFAULT;
  } else if (cmd == AGNOCAST_GET_TOPIC_LIST_CMD) {
    union ioctl_topic_list_args topic_list_args;
    if (copy_from_user(
          &topic_list_args, (union ioctl_topic_list_args __user *)arg, sizeof(topic_list_args)))
      goto return_EFAULT;
    ret = get_topic_list(&topic_list_args);
    if (copy_to_user(
          (union ioctl_topic_list_args __user *)arg, &topic_list_args, sizeof(topic_list_args)))
      goto return_EFAULT;
  } else if (cmd == AGNOCAST_GET_NODE_SUBSCRIBER_TOPICS_CMD) {
    char node_name_buf[NODE_NAME_BUFFER_SIZE];
    union ioctl_node_info_args node_info_sub_args;
    if (copy_from_user(
          &node_info_sub_args, (union ioctl_node_info_args __user *)arg,
          sizeof(node_info_sub_args)))
      goto return_EFAULT;
    if (node_info_sub_args.node_name.len >= NODE_NAME_BUFFER_SIZE) goto return_EINVAL;
    if (copy_from_user(
          node_name_buf, (char __user *)node_info_sub_args.node_name.ptr,
          node_info_sub_args.node_name.len))
      goto return_EFAULT;
    node_name_buf[node_info_sub_args.node_name.len] = '\0';
    ret = get_node_subscriber_topics(node_name_buf, &node_info_sub_args);
    if (copy_to_user(
          (union ioctl_node_info_args __user *)arg, &node_info_sub_args,
          sizeof(node_info_sub_args)))
      goto return_EFAULT;
  } else if (cmd == AGNOCAST_GET_NODE_PUBLISHER_TOPICS_CMD) {
    char node_name_buf[NODE_NAME_BUFFER_SIZE];
    union ioctl_node_info_args node_info_pub_args;
    if (copy_from_user(
          &node_info_pub_args, (union ioctl_node_info_args __user *)arg,
          sizeof(node_info_pub_args)))
      goto return_EFAULT;
    if (node_info_pub_args.node_name.len >= NODE_NAME_BUFFER_SIZE) goto return_EINVAL;
    if (copy_from_user(
          node_name_buf, (char __user *)node_info_pub_args.node_name.ptr,
          node_info_pub_args.node_name.len))
      goto return_EFAULT;
    node_name_buf[node_info_pub_args.node_name.len] = '\0';
    ret = get_node_publisher_topics(node_name_buf, &node_info_pub_args);
    if (copy_to_user(
          (union ioctl_node_info_args __user *)arg, &node_info_pub_args,
          sizeof(node_info_pub_args)))
      goto return_EFAULT;
  } else if (cmd == AGNOCAST_GET_TOPIC_SUBSCRIBER_INFO_CMD) {
    char topic_name_buf[TOPIC_NAME_BUFFER_SIZE];
    union ioctl_topic_info_args topic_info_sub_args;
    if (copy_from_user(
          &topic_info_sub_args, (union ioctl_topic_info_args __user *)arg,
          sizeof(topic_info_sub_args)))
      goto return_EFAULT;
    if (topic_info_sub_args.topic_name.len >= TOPIC_NAME_BUFFER_SIZE) goto return_EINVAL;
    if (copy_from_user(
          topic_name_buf, (char __user *)topic_info_sub_args.topic_name.ptr,
          topic_info_sub_args.topic_name.len))
      goto return_EFAULT;
    topic_name_buf[topic_info_sub_args.topic_name.len] = '\0';
    ret = get_topic_subscriber_info(topic_name_buf, &topic_info_sub_args);
    if (copy_to_user(
          (union ioctl_topic_info_args __user *)arg, &topic_info_sub_args,
          sizeof(topic_info_sub_args)))
      goto return_EFAULT;
  } else if (cmd == AGNOCAST_GET_TOPIC_PUBLISHER_INFO_CMD) {
    char topic_name_buf[TOPIC_NAME_BUFFER_SIZE];
    union ioctl_topic_info_args topic_info_pub_args;
    if (copy_from_user(
          &topic_info_pub_args, (union ioctl_topic_info_args __user *)arg,
          sizeof(topic_info_pub_args)))
      goto return_EFAULT;
    if (topic_info_pub_args.topic_name.len >= TOPIC_NAME_BUFFER_SIZE) goto return_EINVAL;
    if (copy_from_user(
          topic_name_buf, (char __user *)topic_info_pub_args.topic_name.ptr,
          topic_info_pub_args.topic_name.len))
      goto return_EFAULT;
    topic_name_buf[topic_info_pub_args.topic_name.len] = '\0';
    ret = get_topic_publisher_info(topic_name_buf, &topic_info_pub_args);
    if (copy_to_user(
          (union ioctl_topic_info_args __user *)arg, &topic_info_pub_args,
          sizeof(topic_info_pub_args)))
      goto return_EFAULT;
  } else {
    goto return_EINVAL;
  }

  mutex_unlock(&global_mutex);
  return ret;

return_EFAULT:
  mutex_unlock(&global_mutex);
  return -EFAULT;

return_EINVAL:
  mutex_unlock(&global_mutex);
  return -EINVAL;
}

// =========================================
// helper functions for KUnit test

#ifdef KUNIT_BUILD

int get_proc_info_htable_size(void)
{
  int count = 0;
  struct process_info * proc_info;
  int bkt_proc_info;
  hash_for_each(proc_info_htable, bkt_proc_info, proc_info, node)
  {
    count++;
  }
  return count;
}

bool is_in_proc_info_htable(const pid_t pid)
{
  struct process_info * proc_info;
  hash_for_each_possible(proc_info_htable, proc_info, node, hash_min(pid, PROC_INFO_HASH_BITS))
  {
    if (proc_info->pid == pid) {
      return true;
    }
  }
  return false;
}

int get_topic_entries_num(const char * topic_name)
{
  struct topic_wrapper * wrapper = find_topic(topic_name);
  if (!wrapper) {
    return 0;
  }

  struct rb_root * root = &wrapper->topic.entries;
  struct rb_node * node;
  int count = 0;
  for (node = rb_first(root); node; node = rb_next(node)) {
    count++;
  }
  return count;
}

bool is_in_topic_entries(const char * topic_name, int64_t entry_id)
{
  struct topic_wrapper * wrapper = find_topic(topic_name);
  if (!wrapper) {
    return false;
  }
  const struct entry_node * en = find_message_entry(wrapper, entry_id);
  if (!en) {
    return false;
  }

  return true;
}

int get_entry_rc(const char * topic_name, const int64_t entry_id, const topic_local_id_t pubsub_id)
{
  struct topic_wrapper * wrapper = find_topic(topic_name);
  if (!wrapper) {
    return -1;
  }

  const struct entry_node * en = find_message_entry(wrapper, entry_id);
  if (!en) {
    return -1;
  }

  for (int i = 0; i < MAX_REFERENCING_PUBSUB_NUM_PER_ENTRY; i++) {
    if (en->referencing_ids[i] == pubsub_id) {
      return en->reference_count[i];
    }
  }

  return 0;
}

int64_t get_latest_received_entry_id(const char * topic_name, const topic_local_id_t subscriber_id)
{
  const struct topic_wrapper * wrapper = find_topic(topic_name);
  if (!wrapper) {
    return -1;
  }
  const struct subscriber_info * sub_info = find_subscriber_info(wrapper, subscriber_id);
  if (!sub_info) {
    return -1;
  }

  return sub_info->latest_received_entry_id;
}

bool is_in_subscriber_htable(const char * topic_name, const topic_local_id_t subscriber_id)
{
  const struct topic_wrapper * wrapper = find_topic(topic_name);
  if (!wrapper) {
    return false;
  }
  const struct subscriber_info * sub_info = find_subscriber_info(wrapper, subscriber_id);
  if (!sub_info) {
    return false;
  }
  return true;
}

int get_publisher_num(const char * topic_name)
{
  struct topic_wrapper * wrapper = find_topic(topic_name);
  if (!wrapper) {
    return 0;
  }
  return get_size_pub_info_htable(wrapper);
}

bool is_in_publisher_htable(const char * topic_name, const topic_local_id_t publisher_id)
{
  const struct topic_wrapper * wrapper = find_topic(topic_name);
  if (!wrapper) {
    return false;
  }
  const struct publisher_info * pub_info = find_publisher_info(wrapper, publisher_id);
  if (!pub_info) {
    return false;
  }
  return true;
}

int get_topic_num(void)
{
  int count = 0;
  struct topic_wrapper * wrapper;
  int bkt_wrapper;
  hash_for_each(topic_hashtable, bkt_wrapper, wrapper, node)
  {
    count++;
  }
  return count;
}

bool is_in_topic_htable(const char * topic_name)
{
  return find_topic(topic_name) != NULL;
}

#endif

// =========================================
// Initialize and cleanup

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

static void remove_entry_node(struct topic_wrapper * wrapper, struct entry_node * en)
{
  rb_erase(&en->node, &wrapper->topic.entries);
  kfree(en);
}

static void pre_handler_subscriber_exit(struct topic_wrapper * wrapper, const pid_t pid)
{
  struct subscriber_info * sub_info;
  int bkt_sub_info;
  struct hlist_node * tmp_sub_info;
  hash_for_each_safe(wrapper->topic.sub_info_htable, bkt_sub_info, tmp_sub_info, sub_info, node)
  {
    if (sub_info->pid != pid) continue;

    const topic_local_id_t subscriber_id = sub_info->id;
    hash_del(&sub_info->node);
    kfree(sub_info->node_name);
    kfree(sub_info);

    struct rb_root * root = &wrapper->topic.entries;
    struct rb_node * node = rb_first(root);
    while (node) {
      struct entry_node * en = rb_entry(node, struct entry_node, node);
      node = rb_next(node);

      for (int i = 0; i < MAX_REFERENCING_PUBSUB_NUM_PER_ENTRY; i++) {
        if (en->referencing_ids[i] == subscriber_id) {
          remove_reference_by_index(en, i);
        }
      }

      if (is_referenced(en)) continue;

      bool publisher_exited = false;
      struct publisher_info * pub_info;
      uint32_t hash_val = hash_min(en->publisher_id, PUB_INFO_HASH_BITS);
      hash_for_each_possible(wrapper->topic.pub_info_htable, pub_info, node, hash_val)
      {
        if (pub_info->id == en->publisher_id) {
          if (!find_process_info(pub_info->pid)) {
            publisher_exited = true;
          }
          break;
        }
      }
      if (!publisher_exited) continue;

      remove_entry_node(wrapper, en);

      pub_info->entries_num--;
      if (pub_info->entries_num == 0) {
        hash_del(&pub_info->node);
        kfree(pub_info->node_name);
        kfree(pub_info);
      }
    }
  }
}

static void pre_handler_publisher_exit(struct topic_wrapper * wrapper, const pid_t pid)
{
  struct publisher_info * pub_info;
  int bkt_pub_info;
  struct hlist_node * tmp_pub_info;
  hash_for_each_safe(wrapper->topic.pub_info_htable, bkt_pub_info, tmp_pub_info, pub_info, node)
  {
    if (pub_info->pid != pid) continue;

    const topic_local_id_t publisher_id = pub_info->id;

    struct rb_root * root = &wrapper->topic.entries;
    struct rb_node * node = rb_first(root);
    while (node) {
      struct entry_node * en = rb_entry(node, struct entry_node, node);
      node = rb_next(node);

      if (en->publisher_id != publisher_id) continue;

      for (int i = 0; i < MAX_REFERENCING_PUBSUB_NUM_PER_ENTRY; i++) {
        if (en->referencing_ids[i] == publisher_id) {
          remove_reference_by_index(en, i);
        }
      }

      if (!is_referenced(en)) {
        pub_info->entries_num--;
        remove_entry_node(wrapper, en);
      }
    }

    if (pub_info->entries_num == 0) {
      hash_del(&pub_info->node);
      kfree(pub_info->node_name);
      kfree(pub_info);
    }
  }
}

// Ring buffer to hold exited pids
static DEFINE_SPINLOCK(pid_queue_lock);
static pid_t exit_pid_queue[EXIT_QUEUE_SIZE];
static uint32_t queue_head;
static uint32_t queue_tail;

// For controling the kernel thread
static struct task_struct * worker_task;
static DECLARE_WAIT_QUEUE_HEAD(worker_wait);
static int has_new_pid = false;

#ifndef KUNIT_BUILD
static void unlink_shm(const pid_t pid)
{
  char filename_buffer[32];  // Larger enough than when pid is 4,194,304 (Linux default pid_max).
  scnprintf(filename_buffer, sizeof(filename_buffer), "/dev/shm/agnocast@%d", pid);

  struct filename * filename = getname_kernel(filename_buffer);
  if (!filename) {
    dev_warn(agnocast_device, "getname_kernel failed. (unlink_shm)\n");
  }

  int ret = do_unlinkat(AT_FDCWD, filename);
  if (ret < 0) {
    dev_warn(agnocast_device, "do_unlinkat failed, returned:%d. (unlink_shm)\n", ret);
  }
}
#endif

void process_exit_cleanup(const pid_t pid)
{
  // Quickly determine if it is an Agnocast-related process.
  struct process_info * proc_info;
  struct hlist_node * tmp;
  uint32_t hash_val = hash_min(pid, PROC_INFO_HASH_BITS);
  bool agnocast_related = false;
  hash_for_each_possible_safe(proc_info_htable, proc_info, tmp, node, hash_val)
  {
    if (proc_info->pid == pid) {
      hash_del(&proc_info->node);
      kfree(proc_info);
      agnocast_related = true;
      break;
    }
  }

  if (!agnocast_related) return;

#ifndef KUNIT_BUILD
  unlink_shm(pid);
#endif

  free_memory(pid);

  struct topic_wrapper * wrapper;
  struct hlist_node * node;
  int bkt;
  hash_for_each_safe(topic_hashtable, bkt, node, wrapper, node)
  {
    pre_handler_publisher_exit(wrapper, pid);

    pre_handler_subscriber_exit(wrapper, pid);

    // Check if we can release the topic_wrapper
    if (get_size_pub_info_htable(wrapper) == 0 && get_size_sub_info_htable(wrapper) == 0) {
      hash_del(&wrapper->node);
      if (wrapper->key) {
        kfree(wrapper->key);
      }
      kfree(wrapper);
    }
  }

#ifndef KUNIT_BUILD
  dev_info(agnocast_device, "Process (pid=%d) has exited. (process_exit_cleanup)\n", pid);
#endif
}

static int exit_worker_thread(void * data)
{
  while (!kthread_should_stop()) {
    pid_t pid;
    unsigned long flags;
    bool got_pid = false;

    wait_event_interruptible(worker_wait, smp_load_acquire(&has_new_pid) || kthread_should_stop());

    if (kthread_should_stop()) break;

    spin_lock_irqsave(&pid_queue_lock, flags);

    if (queue_head != queue_tail) {
      pid = exit_pid_queue[queue_head];
      queue_head = (queue_head + 1) & (EXIT_QUEUE_SIZE - 1);
      got_pid = true;
    }

    // queue is empty
    if (queue_head == queue_tail) smp_store_release(&has_new_pid, 0);

    spin_unlock_irqrestore(&pid_queue_lock, flags);

    if (got_pid) {
      mutex_lock(&global_mutex);
      process_exit_cleanup(pid);
      mutex_unlock(&global_mutex);
    }
  }

  return 0;
}

void enqueue_exit_pid(const pid_t pid)
{
  unsigned long flags;
  uint32_t next;

  bool need_wakeup = false;

  spin_lock_irqsave(&pid_queue_lock, flags);

  // Assumes EXIT_QUEUE_SIZE is 2^N
  next = (queue_tail + 1) & (EXIT_QUEUE_SIZE - 1);

  if (next != queue_head) {  // queue is not full
    exit_pid_queue[queue_tail] = pid;
    queue_tail = next;
    smp_store_release(&has_new_pid, 1);
    need_wakeup = true;
  }

  spin_unlock_irqrestore(&pid_queue_lock, flags);

  if (need_wakeup) {
    wake_up_interruptible(&worker_wait);
  } else {
    dev_warn(
      agnocast_device,
      "exit_pid_queue is full! consider expanding the queue size. (pre_handler_do_exit)\n");
  }
}

static int pre_handler_do_exit(struct kprobe * p, struct pt_regs * regs)
{
  const pid_t pid = current->pid;
  enqueue_exit_pid(pid);
  return 0;
}

static struct kprobe kp_do_exit = {
  .symbol_name = "do_exit",
  .pre_handler = pre_handler_do_exit,
};

#ifndef KUNIT_BUILD
static int check_dev_shm_available(void)
{
  struct path path;
  struct kstatfs st;
  int ret = kern_path("/dev/shm/", LOOKUP_FOLLOW, &path);
  if (ret < 0) {
    return ret;
  }

  ret = vfs_statfs(&path, &st);
  if (ret < 0) {
    return ret;
  }

  if (st.f_type != TMPFS_MAGIC) {  // TMPFS_MAGIC has the same value as SHMFS_SUPER_MAGIC in glibc.
    dev_warn(
      agnocast_device,
      "/dev/shm cannot be used as shared memory file system.(check_dev_shm_availability)\n");
    return -ECANCELED;
  }

  return 0;
}

/* Look up and set do_unlinkat using kprobe */
static int setup_for_unlink_shm(void)
{
  struct kprobe kp_do_unlinkat;

  memset(&kp_do_unlinkat, 0, sizeof(struct kprobe));
  kp_do_unlinkat.symbol_name = "do_unlinkat";

  int ret = register_kprobe(&kp_do_unlinkat);
  if (ret < 0) {
    dev_warn(
      agnocast_device,
      "register_kprobe for do_unlinkat failed, returned %d. (setup_for_unlink_shm)\n", ret);
    return ret;
  }

  do_unlinkat = (int (*)(int, struct filename *))kp_do_unlinkat.addr;
  unregister_kprobe(&kp_do_unlinkat);

  ret = check_dev_shm_available();
  if (ret < 0) {
    return ret;
  }

  return 0;
}
#endif

void agnocast_init_mutexes(void)
{
  mutex_init(&global_mutex);
}

void agnocast_init_device(void)
{
  major = register_chrdev(0, "agnocast" /*device driver name*/, &fops);

#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 3, 0)
  agnocast_class = class_create("agnocast_class");
#else
  agnocast_class = class_create(THIS_MODULE, "agnocast_class");
#endif

  agnocast_class->devnode = agnocast_devnode;
  agnocast_device =
    device_create(agnocast_class, NULL, MKDEV(major, 0), NULL, "agnocast" /*file name*/);
}

int agnocast_init_kthread(void)
{
  queue_head = queue_tail = 0;

  worker_task = kthread_run(exit_worker_thread, NULL, "agnocast_exit_worker");
  if (IS_ERR(worker_task)) {
    dev_warn(agnocast_device, "failed to create kernel thread. (agnocast_init_kthread)\n");
    return PTR_ERR(worker_task);
  }

  return 0;
}

int agnocast_init_kprobe(void)
{
  int ret = register_kprobe(&kp_do_exit);
  if (ret < 0) {
    dev_warn(
      agnocast_device, "register_kprobe for do_exit failed, returned %d. (agnocast_init_kprobe)\n",
      ret);
    return ret;
  }

#ifndef KUNIT_BUILD
  ret = setup_for_unlink_shm();
  if (ret < 0) {
    return ret;
  }
#endif

  return 0;
}

#ifndef KUNIT_BUILD
static int agnocast_init(void)
{
  int ret;

  agnocast_init_mutexes();

  agnocast_init_device();

  ret = agnocast_init_kthread();
  if (ret < 0) return ret;

  ret = agnocast_init_kprobe();
  if (ret < 0) return ret;

  init_memory_allocator();

  dev_info(agnocast_device, "Agnocast installed! v%s\n", VERSION);
  return 0;
}
#endif

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
      kfree(pub_info->node_name);
      kfree(pub_info);
    }

    struct subscriber_info * sub_info;
    int bkt_sub_info;
    struct hlist_node * tmp_sub_info;
    hash_for_each_safe(wrapper->topic.sub_info_htable, bkt_sub_info, tmp_sub_info, sub_info, node)
    {
      hash_del(&sub_info->node);
      kfree(sub_info->node_name);
      kfree(sub_info);
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

void agnocast_exit_free_data(void)
{
  mutex_lock(&global_mutex);
  remove_all_topics();
  remove_all_process_info();
  mutex_unlock(&global_mutex);
}

void agnocast_exit_kthread(void)
{
  wake_up_interruptible(&worker_wait);
  kthread_stop(worker_task);
}

void agnocast_exit_kprobe(void)
{
  unregister_kprobe(&kp_do_exit);
}

void agnocast_exit_device(void)
{
  device_destroy(agnocast_class, MKDEV(major, 0));
  class_destroy(agnocast_class);
  unregister_chrdev(major, "agnocast");
}

#ifndef KUNIT_BUILD
static void agnocast_exit(void)
{
  agnocast_exit_kthread();
  agnocast_exit_kprobe();

  agnocast_exit_free_data();
  dev_info(agnocast_device, "Agnocast removed!\n");
  agnocast_exit_device();
}
#endif

#ifndef KUNIT_BUILD
module_init(agnocast_init) module_exit(agnocast_exit)
#endif
