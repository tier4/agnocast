#include <linux/module.h>
#include <linux/kobject.h>
#include <linux/sysfs.h>
#include <linux/kernel.h>
#include <linux/fs.h>
#include <linux/uaccess.h>
#include <linux/init.h>
#include <linux/device.h>
#include <linux/slab.h> // kmalloc, kfree
#include <linux/string.h> // strcmp, strdup
#include <linux/hashtable.h> // hash table utilities
#include <linux/hash.h> // hash_64
#include <linux/rbtree.h>
#include <linux/kprobes.h>

MODULE_LICENSE("Dual BSD/GPL");

#define MAX_PUBLISHER_NUM 16  // only for ioctl_get_shm_args currently
#define MAX_SUBSCRIBER_NUM 16

// =========================================
// data structure

#define AGNOCAST_HASH_BITS 10 // hash table size : 2^AGNOCAST_HASH_BITS

// TODO: data structures for mapping pid to shm_addr during initialization
#define MAX_PROCESS_NUM 1024
uint32_t pid_index = 0;
uint32_t process_ids[MAX_PROCESS_NUM];
uint64_t shm_addrs[MAX_PROCESS_NUM];

// TODO: assume 0x40000000000~ is allocatable
uint64_t allocatable_addr = 0x40000000000;

struct topic_struct {
	unsigned int publisher_num;
	struct rb_root publisher_queues;
	unsigned int subscriber_num;
	uint32_t subscriber_pids[MAX_SUBSCRIBER_NUM];
};

struct topic_wrapper {
	char *key;
	struct topic_struct topic;
	struct hlist_node node;
};

struct pid_node {
	struct rb_node node;
	uint32_t pid; // rbtree key
};

struct publisher_queue_node {
	struct rb_node node;
	uint32_t pid; // rbtree key
	uint32_t queue_size;
	struct rb_root entries;
};

struct entry_node {
	struct rb_node node;
	uint64_t timestamp; // rbtree key
	uint64_t msg_virtual_address;
	uint32_t reference_count;
	/*
	 * NOTE:
	 *   unreceived_subscriber_count currently has no effect on the release timing of the message. 
	 *   However, it is retained for future use such as early release or logging.
	 */
	uint32_t unreceived_subscriber_count;
};

DEFINE_HASHTABLE(topic_hashtable, AGNOCAST_HASH_BITS);

static unsigned long agnocast_hash(const char *str) {
	unsigned long hash = full_name_hash(NULL /*namespace*/, str, strlen(str));
	return hash_min(hash, AGNOCAST_HASH_BITS);
}

static void insert_topic(const char *topic_name/*, struct topic_struct topic*/) {
	struct topic_wrapper *wrapper = kmalloc(sizeof(struct topic_wrapper), GFP_KERNEL);
	if (!wrapper) {
		printk(KERN_WARNING "kmalloc failed in insert_topic\n");
	}

	wrapper->key = kstrdup(topic_name, GFP_KERNEL);
	if (!wrapper->key) {
		printk(KERN_WARNING "kstrdup failed in insert_topic\n");
		kfree(wrapper);
		return;
	}

	wrapper->topic.publisher_num = 0;
	wrapper->topic.publisher_queues = RB_ROOT;
	wrapper->topic.subscriber_num = 0;
	for (int i = 0; i < MAX_SUBSCRIBER_NUM; i++) {
		wrapper->topic.subscriber_pids[i] = 0;
	}

	hash_add(topic_hashtable, &wrapper->node, agnocast_hash(topic_name));
}

static struct topic_wrapper *find_topic(const char *topic_name) {
	struct topic_wrapper *entry;
	unsigned long hash_val = agnocast_hash(topic_name);

	hash_for_each_possible(topic_hashtable, entry, node, hash_val) {
		if (strcmp(entry->key, topic_name) == 0) return entry;
	}

	return NULL;
}

static void insert_subscriber_pid(const char *topic_name, uint32_t pid) {
	struct topic_wrapper *wrapper = find_topic(topic_name);
	if (!wrapper) {
		printk(KERN_WARNING "topic_name %s not found (insert_subscriber_pid)\n", topic_name);
		return;
	}

	// check whether subscriber_pids is full
	if (wrapper->topic.subscriber_num == MAX_SUBSCRIBER_NUM) {
		printk(KERN_WARNING "subscribers for topic_name=%s reached MAX_SUBSCRIBER_NUM=%d, so a new subscriber cannot be added\n",
		  topic_name, MAX_SUBSCRIBER_NUM);
		return;
	}

	// check whether pid already exists in subscriber_pids
	for (int i = 0; i < wrapper->topic.subscriber_num; i++) {
		if (pid == wrapper->topic.subscriber_pids[i]) {
			printk(KERN_INFO "pid=%d already exists in %s (insert_subscriber_pid)\n", pid, topic_name);
			return;
		}
	}

	wrapper->topic.subscriber_pids[wrapper->topic.subscriber_num] = pid;
	wrapper->topic.subscriber_num++;
}

static int insert_publisher_queue(const char *topic_name, uint32_t publisher_pid) {
	struct topic_wrapper *wrapper = find_topic(topic_name);
	if (!wrapper) {
		printk(KERN_WARNING "topic_name %s not found (insert_publisher_queue)\n", topic_name);
		return -1;
	}

	struct publisher_queue_node *new_node = kmalloc(sizeof(struct publisher_queue_node), GFP_KERNEL);
	struct rb_root *root = &wrapper->topic.publisher_queues;
	struct rb_node **new = &(root->rb_node);
	struct rb_node *parent = NULL;

	if (!new_node) {
		printk(KERN_WARNING "kmalloc failed (insert_publisher_queue)\n");
		return -1;
	}

	new_node->pid = publisher_pid;
	new_node->queue_size = 0;
	new_node->entries = RB_ROOT;

	while (*new) {
		struct publisher_queue_node *this = container_of(*new, struct publisher_queue_node, node);
		parent = *new;

		if (publisher_pid < this->pid) {
			new = &((*new)->rb_left);
		} else if (publisher_pid > this->pid) {
			new = &((*new)->rb_right);
		} else {
			printk(KERN_INFO "publisher_pid=%d already exists in %s (insert_publisher_queue)\n", publisher_pid, topic_name);
			kfree(new_node);
			return -1;
		}
	}

	rb_link_node(&new_node->node, parent, new);
	rb_insert_color(&new_node->node, root);

	wrapper->topic.publisher_num++;

	return 0;
}

static struct publisher_queue_node* find_publisher_queue(const char *topic_name, uint32_t publisher_pid) {
	struct topic_wrapper *wrapper = find_topic(topic_name);
	if (!wrapper) {
		printk(KERN_WARNING "topic_name %s not found (find_publisher_queue)\n", topic_name);
		return NULL;
	}

	struct rb_root *root = &wrapper->topic.publisher_queues;
	struct rb_node **new = &(root->rb_node);

	while (*new) {
		struct publisher_queue_node *this = container_of(*new, struct publisher_queue_node, node);

		if (publisher_pid < this->pid) {
			new = &((*new)->rb_left);
		} else if (publisher_pid > this->pid) {
			new = &((*new)->rb_right);
		} else {
			return this;
		}
	}

	printk(KERN_INFO "publisher queue publisher_pid=%d not found in %s (find_publisher_queue)\n", publisher_pid, topic_name);
	return NULL;
}

static struct entry_node* find_message_entry(const char *topic_name, uint32_t publisher_pid, uint64_t msg_timestamp) {
	struct publisher_queue_node *pubq = find_publisher_queue(topic_name, publisher_pid);
	if (!pubq) {
		printk(KERN_WARNING "publisher queue with topic_name=%s publisher_pid=%d not found (find_message_entry)\n",
			topic_name, publisher_pid);
		return NULL;
	}

	struct rb_root *root = &pubq->entries;
	struct rb_node **new = &(root->rb_node);

	while (*new) {
		struct entry_node *this = container_of(*new, struct entry_node, node);

		if (msg_timestamp < this->timestamp) {
			new = &((*new)->rb_left);
		} else if (msg_timestamp > this->timestamp) {
			new = &((*new)->rb_right);
		} else {
			return this;
		}
	}

	printk(KERN_INFO "message entry publisher_pid=%d timestamp=%lld not found in %s (find_publisher_queue)\n", publisher_pid, msg_timestamp, topic_name);
	return NULL;
}

static void increment_message_entry_rc(const char *topic_name, uint32_t publisher_pid, uint64_t msg_timestamp) {
	struct entry_node *en = find_message_entry(topic_name, publisher_pid, msg_timestamp);
	if (!en) {
		printk(KERN_WARNING "message entry with topic_name=%s publisher_pid=%d timestamp=%lld not found (increment_message_entry_rc)\n",
			topic_name, publisher_pid, msg_timestamp);
		return;
	}

	en->reference_count++;
}

static void decrement_message_entry_rc(const char *topic_name, uint32_t publisher_pid, uint64_t msg_timestamp) {
	struct entry_node *en = find_message_entry(topic_name, publisher_pid, msg_timestamp);
	if (!en) {
		printk(KERN_WARNING "message entry with topic_name=%s publisher_pid=%d timestamp=%lld not found (decrement_message_entry_rc)\n",
			topic_name, publisher_pid, msg_timestamp);
		return;
	}

	if (en->reference_count == 0) {
		printk(KERN_WARNING "tried to decrement reference count 0 with topic_name=%s publisher_pid=%d timestamp=%lld(decrement_message_entry_rc)\n",
			topic_name, publisher_pid, msg_timestamp);
		return;
	}

	en->reference_count--;
}

static uint64_t receive_and_update(const char *topic_name, uint32_t publisher_pid, uint64_t msg_timestamp, uint32_t qos_depth) {
	struct entry_node *en = find_message_entry(topic_name, publisher_pid, msg_timestamp);
	if (!en) {
		printk(KERN_WARNING "message entry with topic_name=%s publisher_pid=%d timestamp=%lld not found (receive_and_update)\n",
			topic_name, publisher_pid, msg_timestamp);
		return 0;
	}

	if (en->unreceived_subscriber_count == 0) {
		printk(KERN_WARNING "tried to decrement unreceived_subscriber_count 0 with topic_name=%s publisher_pid=%d timestamp=%lld(receive_and_update)\n",
			topic_name, publisher_pid, msg_timestamp);
		return 0;
	}

	// Count number of nodes that have greater timestamp than the current message entry.
	// If the count is greater than qos_depth, the current message is ignored.
	struct publisher_queue_node *publisher_queue = find_publisher_queue(topic_name, publisher_pid);
	if (!publisher_queue) {
		printk(KERN_WARNING "publisher queue publisher_pid=%d not found in %s (receive_and_update)\n", publisher_pid, topic_name);
		return 0;
	}
	if (publisher_queue->queue_size > qos_depth) {
		uint32_t older_count = 0;
		struct rb_node *next_node = rb_next(&en->node);
		while (next_node) {
			older_count++;
			next_node = rb_next(next_node);
		}
		if (older_count > qos_depth) {
			en->unreceived_subscriber_count--;
			return 0;
		}
	}
	
	en->unreceived_subscriber_count--;
	en->reference_count++;
	return en->msg_virtual_address;
}

static void set_message_entry_usc(char *topic_name, uint32_t publisher_pid, uint64_t msg_timestamp, uint32_t *pids_ret, uint32_t *pid_ret_len) {
	struct topic_wrapper *wrapper = find_topic(topic_name);
	uint32_t subscriber_num = wrapper->topic.subscriber_num;

	struct entry_node *en = find_message_entry(topic_name, publisher_pid, msg_timestamp);
	if (!en) {
		printk(KERN_WARNING "message entry with topic_name=%s publisher_pid=%d timestamp=%lld not found (set_message_entry_usc)\n",
			topic_name, publisher_pid, msg_timestamp);
		return;
	}

	if (en->unreceived_subscriber_count != 0) {
		printk(KERN_WARNING "tried to already published message with topic_name=%s publisher_pid=%d timestamp=%lld(set_message_entry_usc)\n",
			topic_name, publisher_pid, msg_timestamp);
		return;
	}

	en->unreceived_subscriber_count = subscriber_num;

	*pid_ret_len = subscriber_num;
	memcpy(pids_ret, wrapper->topic.subscriber_pids, subscriber_num * sizeof(uint32_t));
}

static void insert_message_entry(const char *topic_name, uint32_t publisher_pid, uint64_t msg_virtual_address, uint64_t timestamp) {
	struct publisher_queue_node *publisher_queue = find_publisher_queue(topic_name, publisher_pid);
	if (!publisher_queue) {
		printk(KERN_WARNING "publisher queue publisher_pid=%d not found in %s (insert_message_entry)\n", publisher_pid, topic_name);
		return;
	}

	struct entry_node *new_node = kmalloc(sizeof(struct entry_node), GFP_KERNEL);
	struct rb_root *root = &publisher_queue->entries;
	struct rb_node **new = &(root->rb_node);
	struct rb_node *parent = NULL;

	if (!new_node) {
		printk(KERN_WARNING "kmalloc failed (insert_message_entry)\n");
		return;
	}

	new_node->timestamp = timestamp;
	new_node->msg_virtual_address = msg_virtual_address;
	new_node->reference_count = 0;
	new_node->unreceived_subscriber_count = 0;

	while (*new) {
		struct entry_node *this = container_of(*new, struct entry_node, node);
		parent = *new;

		if (timestamp < this->timestamp) {
			new = &((*new)->rb_left);
		} else if (timestamp > this->timestamp) {
			new = &((*new)->rb_right);
		} else {
			printk(KERN_INFO "message entry timestamp=%lld already exists in publisher queue pid=%d %s (insert_message_entry)\n",
				timestamp, publisher_pid, topic_name);
			kfree(new_node);
			return;
		}
	}

	rb_link_node(&new_node->node, parent, new);
	rb_insert_color(&new_node->node, root);

	publisher_queue->queue_size++;
}

static uint64_t try_release_removable_oldest_message(const char *topic_name, uint32_t publisher_pid, uint32_t qos_depth) {
	struct publisher_queue_node *publisher_queue = find_publisher_queue(topic_name, publisher_pid);
	if (!publisher_queue) {
		printk(KERN_WARNING "publisher queue publisher_pid=%d not found in %s (try_release_removable_oldest_message)\n", publisher_pid, topic_name);
		return 0;
	}

	if (publisher_queue->queue_size <= qos_depth) return 0;

	uint32_t leak_warn_threshold = (qos_depth <= 100) ? 100 + qos_depth : qos_depth * 2;  // This is rough value.
	if (publisher_queue->queue_size > leak_warn_threshold) {
		printk(KERN_WARNING "For some reason the reference count of the message is not reduced and the queue size is huge: publisher queue publisher_pid=%d, topic_name=%s (try_release_removable_oldest_message)\n", publisher_pid, topic_name);
	}

	uint32_t num_search_entries = publisher_queue->queue_size - qos_depth + 1;  // Number of entries exceeding qos_depth. +1 is for the message to be enqueued later.
	struct rb_node *node = rb_first(&publisher_queue->entries);
	if (!node) return 0;

	// The searched message is either deleted or, if a reference count remains, is not deleted.
	// In both cases, this number of searches is sufficient, as it does not affect the Queue size of QoS.
	for (uint32_t _ = 0; _ < num_search_entries; _++) {
		struct entry_node* en = container_of(node, struct entry_node, node);
		if (en->reference_count > 0) {
			// This is not counted in a Queue size of QoS.
			node = rb_next(node);
			if (!node) return 0;
		} else {
			uint64_t msg_addr = en->msg_virtual_address;
			rb_erase(&en->node, &publisher_queue->entries);
			publisher_queue->queue_size--;
			kfree(en);

			return msg_addr;
		}
	}

	return 0;
}

static void remove_subscriber_pid(const char *topic_name, uint32_t pid) {
	struct topic_wrapper *wrapper = find_topic(topic_name);
	if (!wrapper) {
		printk(KERN_WARNING "topic_name %s not found (remove_subscriber_pid)\n", topic_name);
		return;
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

	if (found) {
		wrapper->topic.subscriber_num--;
	} else {
		printk(KERN_WARNING "tried to remove subscriber pid %d, but not found in %s (remove_subscriber_pid)\n", pid, topic_name);
	}
}

// TODO: deallocate entries rbtree
static void remove_publisher_queue(const char *topic_name, uint32_t publisher_pid) {
	struct topic_wrapper *wrapper = find_topic(topic_name);
	if (!wrapper) {
		printk(KERN_WARNING "topic_name %s not found (remove_publisher_queue)\n", topic_name);
		return;
	}

	struct rb_node *node = wrapper->topic.publisher_queues.rb_node;

	while (node) {
		struct publisher_queue_node *data = container_of(node, struct publisher_queue_node, node);

		if (publisher_pid < data->pid) {
			node = node->rb_left;
		} else if (publisher_pid > data->pid) {
			node = node->rb_right;
		} else {
			rb_erase(&data->node, &wrapper->topic.publisher_queues);
			kfree(data);
			return;
		}
	}

	printk(KERN_INFO "tried to remove publisher_queue pid %d, but not found in %s (remove_publisher_queue)\n", publisher_pid, topic_name);
}

// =========================================
// "/sys/module/agnocast/status/*"

static int value;

static ssize_t show_name(struct kobject *kobj, struct kobj_attribute *attr, char *buf) {
	return scnprintf(buf, PAGE_SIZE, "agnocast\n");
}

static ssize_t show_value(struct kobject *kobj, struct kobj_attribute *attr, char *buf) {
	return scnprintf(buf, PAGE_SIZE, "%d\n", value);
}

static ssize_t store_value(struct kobject *kobj, struct kobj_attribute *attr, const char *buf, size_t count) {
	int res = kstrtoint(buf, 10, &value);
	if (res < 0) {
		return res;
	}
	return count;
}

#define PRINT_BUF_SIZE 512
static ssize_t show_all(struct kobject *kobj, struct kobj_attribute *attr, char *buf) {
	char local_buf[PRINT_BUF_SIZE];
	local_buf[0] = '\0';

	struct topic_wrapper *entry;
	struct hlist_node *node;
	int bkt;
	size_t buf_len = 0;

	hash_for_each_safe(topic_hashtable, bkt, node, entry, node) {
		size_t key_len = strlen(entry->key);

		// TODO: reconsider buffer size in terms of pids array
		if (buf_len + key_len + 1 < PRINT_BUF_SIZE - 100 /*tmp*/) {
			strcat(local_buf, entry->key);
			strcat(local_buf, "\nsubscribers:\n");
			buf_len += key_len + 1;

			for (int i = 0; i < entry->topic.subscriber_num; i++) {
				char num_str[13];
				scnprintf(num_str, sizeof(num_str), "%u ", entry->topic.subscriber_pids[i]);
				strcat(local_buf, num_str);
				// TODO: count pids string length
			}

			strcat(local_buf, "\npublisher queues:\n");
			struct rb_root *root = &entry->topic.publisher_queues;
			struct rb_node *node;
			for (node = rb_first(root); node; node = rb_next(node)) {
				struct publisher_queue_node *data = container_of(node, struct publisher_queue_node, node);
				char num_str[21];
				scnprintf(num_str, sizeof(num_str), "pubpid=%u :\n", data->pid);
				strcat(local_buf, num_str);
				// TODO: count pids string length

				struct rb_root *pubq_root = &data->entries;
				struct rb_node *node2;
				for (node2 = rb_first(pubq_root); node2; node2 = rb_next(node2)) {
					struct entry_node *en = container_of(node2, struct entry_node, node);

					char num_str_timestamp[25];
					char num_str_msg_addr[25];
					char num_str_rc[16];
					char num_str_usc[16];

					scnprintf(num_str_timestamp, sizeof(num_str_timestamp), "time=%lld ", en->timestamp);
					scnprintf(num_str_msg_addr, sizeof(num_str_msg_addr), "addr=%lld ", en->msg_virtual_address);
					scnprintf(num_str_rc, sizeof(num_str_rc), "rc=%d ", en->reference_count);
					scnprintf(num_str_usc, sizeof(num_str_usc), "usc=%d\n", en->unreceived_subscriber_count);

					strcat(local_buf, num_str_timestamp);
					strcat(local_buf, num_str_msg_addr);
					strcat(local_buf, num_str_rc);
					strcat(local_buf, num_str_usc);
				}
			}

			strcat(local_buf, "\n");
		} else {
			printk(KERN_WARNING "buffer is full, cannot serialize all topic info\n");
			break;
		}
	}

	return scnprintf(buf, PAGE_SIZE, "%s\n", local_buf);
}

static struct kobject *status_kobj;
static struct kobj_attribute name_attribute = __ATTR(name, 0444, show_name, NULL);
static struct kobj_attribute value_attribute = __ATTR(value, 0644, show_value, store_value);
static struct kobj_attribute all_attribute = __ATTR(all, 0444, show_all, NULL);

static struct attribute *attrs[] = {
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

#define AGNOCAST_TOPIC_ADD_CMD _IOW('T', 1, char *)
void topic_add(const char *topic_name) {
	struct topic_wrapper *wrapper = find_topic(topic_name);
	if (wrapper) {
		printk(KERN_INFO "Topic %s already exists (topic_add)\n", topic_name);
		return;
	}

	printk(KERN_INFO "%s added\n", topic_name);	
	insert_topic(topic_name);
}

struct ioctl_subscriber_args {
	char *topic_name;
	uint32_t pid;
};

union ioctl_publisher_args {
    struct {
        const char *topic_name;
        uint32_t publisher_pid;
    };
    struct {
        uint64_t ret_shm_addr;
        uint32_t ret_subscriber_len;
        uint32_t ret_subscriber_pids[MAX_SUBSCRIBER_NUM];
    };
};

struct ioctl_enqueue_entry_args {
	char *topic_name;
	uint32_t publisher_pid;
	uint64_t msg_virtual_address;
	uint64_t timestamp;
};

union ioctl_update_entry_args {
	struct {
		char *topic_name;
		uint32_t publisher_pid;
		uint64_t msg_timestamp;
	};
	uint64_t ret;
};

union ioctl_receive_msg_args {
	struct {
		char *topic_name;
		uint32_t publisher_pid;
		uint64_t msg_timestamp;
		uint32_t qos_depth;
	};
	uint64_t ret;
};

union ioctl_publish_args {
	struct {
		char *topic_name;
		uint32_t publisher_pid;
		uint64_t msg_timestamp;
	};
	struct {
		uint32_t ret_pids[MAX_SUBSCRIBER_NUM];
		uint32_t ret_len;
	};
};

union ioctl_release_oldest_args {
	struct {
		char *topic_name;
		uint32_t publisher_pid;
		uint32_t qos_depth;
	};
	uint64_t ret;
};

union ioctl_new_shm_args {
    uint32_t pid;
    uint64_t ret_addr;
};

union ioctl_get_shm_args {
    const char *topic_name;
    struct {
        uint32_t ret_publisher_num;
        uint32_t ret_pids[MAX_PUBLISHER_NUM];
        uint64_t ret_addrs[MAX_PUBLISHER_NUM];
    };
};

#define AGNOCAST_SUBSCRIBER_ADD_CMD _IOW('S', 1, struct ioctl_subscriber_args)
void subscriber_pid_add(const char *topic_name, uint32_t pid) {
	printk(KERN_INFO "subscriber (pid=%d) is added to %s\n", pid, topic_name);
	insert_subscriber_pid(topic_name, pid);
}

#define AGNOCAST_SUBSCRIBER_REMOVE_CMD _IOW('S', 2, struct ioctl_subscriber_args)
void subscriber_pid_remove(const char *topic_name, uint32_t pid) {
	printk(KERN_INFO "subscriber (pid=%d) is removed from %s\n", pid, topic_name);
	remove_subscriber_pid(topic_name, pid);
}

#define AGNOCAST_PUBLISHER_ADD_CMD _IOW('P', 1, union ioctl_publisher_args)
int publisher_queue_add(const char *topic_name, uint32_t pid, union ioctl_publisher_args *ioctl_ret) {
	printk(KERN_INFO "publisher (pid=%d) is added to %s\n", pid, topic_name);

	if (insert_publisher_queue(topic_name, pid) == -1) {
		return -1;
	}

	struct topic_wrapper *wrapper = find_topic(topic_name);
	if (!wrapper) {
		printk(KERN_WARNING "topic_name %s not found (publisher_queue_add)\n", topic_name);
		return -1;
	}

    // set shm addr to ioctl_ret
	for (int i = 0; i < pid_index; i++) {
		if (process_ids[i] == pid) {
			ioctl_ret->ret_shm_addr = shm_addrs[i];
			break;
		}
	}

	// set subscriber info to ioctl_ret
	uint32_t subscriber_len = 0;
	struct rb_root *root = &wrapper->topic.subscriber_pids;
	struct rb_node *node;
	for (node = rb_first(root); node; node = rb_next(node)) {
		struct pid_node *data = container_of(node, struct pid_node, node);
		ioctl_ret->ret_subscriber_pids[subscriber_len] = data->pid;
		subscriber_len++;
	}
	ioctl_ret->ret_subscriber_len = subscriber_len;

	return 0;
}

#define AGNOCAST_PUBLISHER_REMOVE_CMD _IOW('P', 2, union ioctl_publisher_args)
void publisher_queue_remove(const char *topic_name, uint32_t pid) {
	printk(KERN_INFO "publisher (pid=%d) is removed from %s\n", pid, topic_name);
	remove_publisher_queue(topic_name, pid);
}

#define AGNOCAST_RELEASE_MSG_CMD _IOW('P', 3, union ioctl_release_oldest_args)
uint64_t release_removable_oldest_message(const char *topic_name, uint32_t publisher_pid, uint32_t qos_depth) {
	printk(KERN_INFO "Try to release oldest message in %s publisher_pid=%d with qos_depth=%d (release_removable_oldest_message)\n",
		topic_name, publisher_pid, qos_depth);
	return try_release_removable_oldest_message(topic_name, publisher_pid, qos_depth);
}


#define AGNOCAST_ENQUEUE_ENTRY_CMD _IOW('E', 1, struct ioctl_enqueue_entry_args)
void enqueue_entry(const char *topic_name, uint32_t publisher_pid, uint64_t msg_virtual_address, uint64_t timestamp) {
	printk(KERN_INFO "enqueue entry: topic_name=%s publisher_pid=%d msg_virtual_address=%lld timestamp=%lld",
		topic_name, publisher_pid, msg_virtual_address, timestamp);
	insert_message_entry(topic_name, publisher_pid, msg_virtual_address, timestamp);
}

#define AGNOCAST_INCREMENT_RC_CMD _IOW('M', 1, union ioctl_update_entry_args)
void increment_rc(char *topic_name, uint32_t publisher_pid, uint64_t msg_timestamp) {
	printk(KERN_INFO "increment message reference count in topic_name=%s publisher_pid=%d timestamp=%lld",
		topic_name, publisher_pid, msg_timestamp);
	increment_message_entry_rc(topic_name, publisher_pid, msg_timestamp);
}

#define AGNOCAST_DECREMENT_RC_CMD _IOW('M', 2, union ioctl_update_entry_args)
void decrement_rc(char *topic_name, uint32_t publisher_pid, uint64_t msg_timestamp) {
	printk(KERN_INFO "decrement message reference count in topic_name=%s publisher_pid=%d timestamp=%lld",
		topic_name, publisher_pid, msg_timestamp);
	decrement_message_entry_rc(topic_name, publisher_pid, msg_timestamp);
}

#define AGNOCAST_RECEIVE_MSG_CMD _IOW('M', 3, union ioctl_receive_msg_args)
uint64_t receive_msg(char *topic_name, uint32_t publisher_pid, uint64_t msg_timestamp, uint32_t qos_depth) {
	printk(KERN_INFO "a subscriber receives message timestamp=%lld topic_name=%s publisher_pid=%d",
		msg_timestamp, topic_name, publisher_pid);
	return receive_and_update(topic_name, publisher_pid, msg_timestamp, qos_depth);
}

#define AGNOCAST_PUBLISH_MSG_CMD _IOW('M', 4, union ioctl_publish_args)
void publish_msg(char *topic_name, uint32_t publisher_pid, uint64_t msg_timestamp, union ioctl_publish_args *ioctl_ret) {
	uint32_t pids_ret[MAX_SUBSCRIBER_NUM];
	uint32_t pid_ret_len;

	set_message_entry_usc(topic_name, publisher_pid, msg_timestamp, pids_ret, &pid_ret_len);

	ioctl_ret->ret_len = pid_ret_len;
	memcpy(ioctl_ret->ret_pids, pids_ret, pid_ret_len * sizeof(uint32_t));
}

#define AGNOCAST_NEW_SHM_CMD _IOW('I', 1, union ioctl_new_shm_args)
uint64_t new_shm_addr(uint32_t pid) {
	process_ids[pid_index] = pid;
	shm_addrs[pid_index] = allocatable_addr;
    allocatable_addr += 0x00400000000; // TODO: allocate 0x00400000000 size for each process, currently
	return shm_addrs[pid_index++];
}

static DEFINE_MUTEX(global_mutex);

#define AGNOCAST_GET_SHM_CMD _IOW('I', 2, union ioctl_get_shm_args)
void get_shm(char *topic_name, union ioctl_get_shm_args *ioctl_ret) {
	// get all publisher id and addr from topic_name
	
    struct topic_wrapper *wrapper = find_topic(topic_name);
	if (!wrapper) {
		printk(KERN_WARNING "topic_name %s not found (get_shm)\n", topic_name);
		return;
	}

	ioctl_ret->ret_publisher_num = wrapper->topic.publisher_num;
	
	uint32_t index = 0;
	struct rb_root *root = &wrapper->topic.publisher_queues;
	struct rb_node *node;
	for (node = rb_first(root); node; node = rb_next(node)) {
		struct publisher_queue_node *data = container_of(node, struct publisher_queue_node, node);
		for (uint32_t i = 0; i < pid_index; i++) {
			if (process_ids[i] == data->pid) {
				ioctl_ret->ret_pids[index] = process_ids[i];
				ioctl_ret->ret_addrs[index] = shm_addrs[i];
				index++;
				break;
			}
		}
	}
}

static long agnocast_ioctl(struct file *file, unsigned int cmd, unsigned long arg) {
	mutex_lock(&global_mutex);
	int ret = 0;
	char topic_name_buf[256];
	struct ioctl_subscriber_args sub_args;
	union ioctl_publisher_args pub_args;
	struct ioctl_enqueue_entry_args enqueue_args;
	union ioctl_update_entry_args entry_args;
	union ioctl_receive_msg_args receive_msg_args;
	union ioctl_publish_args publish_args;
	union ioctl_release_oldest_args release_args;
	union ioctl_new_shm_args new_shm_args;
	union ioctl_get_shm_args get_shm_args;

	switch (cmd) {
	case AGNOCAST_TOPIC_ADD_CMD:
		if (copy_from_user(topic_name_buf, (char __user *)arg, sizeof(topic_name_buf))) goto unlock_mutex_and_return;
		topic_add(topic_name_buf);
		break;
	case AGNOCAST_SUBSCRIBER_ADD_CMD:
		if (copy_from_user(&sub_args, (struct ioctl_subscriber_args __user *)arg, sizeof(sub_args))) goto unlock_mutex_and_return;
		if (copy_from_user(topic_name_buf, (char __user *)sub_args.topic_name, sizeof(topic_name_buf))) goto unlock_mutex_and_return;
		subscriber_pid_add(topic_name_buf, sub_args.pid);
		break;
	case AGNOCAST_SUBSCRIBER_REMOVE_CMD:	
		if (copy_from_user(&sub_args, (struct ioctl_subscriber_args __user *)arg, sizeof(sub_args))) goto unlock_mutex_and_return;
		if (copy_from_user(topic_name_buf, (char __user *)sub_args.topic_name, sizeof(topic_name_buf))) goto unlock_mutex_and_return;
		subscriber_pid_remove(topic_name_buf, sub_args.pid);
		break;
	case AGNOCAST_PUBLISHER_ADD_CMD:
		if (copy_from_user(&pub_args, (union ioctl_publisher_args __user *)arg, sizeof(pub_args))) goto unlock_mutex_and_return;
		if (copy_from_user(topic_name_buf, (char __user *)pub_args.topic_name, sizeof(topic_name_buf))) goto unlock_mutex_and_return;
		ret = publisher_queue_add(topic_name_buf, pub_args.publisher_pid, &pub_args);
		if (copy_to_user((union ioctl_publisher_args __user *)arg, &pub_args, sizeof(pub_args))) goto unlock_mutex_and_return;
		break;
	case AGNOCAST_PUBLISHER_REMOVE_CMD:
		if (copy_from_user(&pub_args, (union ioctl_publisher_args __user *)arg, sizeof(pub_args))) goto unlock_mutex_and_return;
		if (copy_from_user(topic_name_buf, (char __user *)pub_args.topic_name, sizeof(topic_name_buf))) goto unlock_mutex_and_return;
		publisher_queue_remove(topic_name_buf, pub_args.publisher_pid);
		break;
	case AGNOCAST_RELEASE_MSG_CMD:
		if (copy_from_user(&release_args, (union ioctl_release_oldest_args __user *)arg, sizeof(release_args))) goto unlock_mutex_and_return;
		if (copy_from_user(topic_name_buf, (char __user *)release_args.topic_name, sizeof(topic_name_buf))) goto unlock_mutex_and_return;
		uint64_t release_addr = release_removable_oldest_message(topic_name_buf, release_args.publisher_pid, release_args.qos_depth);
		if (copy_to_user((uint64_t __user *)arg, &release_addr, sizeof(uint64_t))) goto unlock_mutex_and_return;
		break;
	case AGNOCAST_ENQUEUE_ENTRY_CMD:
		if (copy_from_user(&enqueue_args, (struct ioctl_enqueue_entry_args __user *)arg, sizeof(enqueue_args))) goto unlock_mutex_and_return;
		if (copy_from_user(topic_name_buf, (char __user *)enqueue_args.topic_name, sizeof(topic_name_buf))) goto unlock_mutex_and_return;
		enqueue_entry(topic_name_buf, enqueue_args.publisher_pid, enqueue_args.msg_virtual_address, enqueue_args.timestamp);
		break;
	case AGNOCAST_INCREMENT_RC_CMD:
		if (copy_from_user(&entry_args, (union ioctl_update_entry_args __user *)arg, sizeof(entry_args))) goto unlock_mutex_and_return;
		if (copy_from_user(topic_name_buf, (char __user *)entry_args.topic_name, sizeof(topic_name_buf))) goto unlock_mutex_and_return;
		increment_message_entry_rc(topic_name_buf, entry_args.publisher_pid, entry_args.msg_timestamp);
		break;
	case AGNOCAST_DECREMENT_RC_CMD:
		if (copy_from_user(&entry_args, (union ioctl_update_entry_args __user *)arg, sizeof(entry_args))) goto unlock_mutex_and_return;
		if (copy_from_user(topic_name_buf, (char __user *)entry_args.topic_name, sizeof(topic_name_buf))) goto unlock_mutex_and_return;
		decrement_message_entry_rc(topic_name_buf, entry_args.publisher_pid, entry_args.msg_timestamp);
		break;
	case AGNOCAST_RECEIVE_MSG_CMD:
		if (copy_from_user(&receive_msg_args, (union ioctl_receive_msg_args __user *)arg, sizeof(receive_msg_args))) goto unlock_mutex_and_return;
		if (copy_from_user(topic_name_buf, (char __user *)receive_msg_args.topic_name, sizeof(topic_name_buf))) goto unlock_mutex_and_return;
		uint64_t msg_addr = receive_and_update(topic_name_buf, receive_msg_args.publisher_pid, receive_msg_args.msg_timestamp, receive_msg_args.qos_depth);
		if (copy_to_user((uint64_t __user *)arg, &msg_addr, sizeof(uint64_t))) goto unlock_mutex_and_return;
		break;
	case AGNOCAST_PUBLISH_MSG_CMD:
		if (copy_from_user(&publish_args, (union ioctl_publish_args __user *)arg, sizeof(publish_args))) goto unlock_mutex_and_return;
		if (copy_from_user(topic_name_buf, (char __user *)publish_args.topic_name, sizeof(topic_name_buf))) goto unlock_mutex_and_return;
		publish_msg(topic_name_buf, publish_args.publisher_pid, publish_args.msg_timestamp, &publish_args);
		if (copy_to_user((union ioctl_publish_args __user *)arg, &publish_args, sizeof(publish_args))) goto unlock_mutex_and_return;
		break;
	case AGNOCAST_NEW_SHM_CMD:
		if (copy_from_user(&new_shm_args, (union ioctl_new_shm_args __user *)arg, sizeof(new_shm_args))) goto unlock_mutex_and_return;
		uint64_t shm_addr = new_shm_addr(new_shm_args.pid);
		if (copy_to_user((union ioctl_new_shm_args __user *)arg, &shm_addr, sizeof(new_shm_args))) goto unlock_mutex_and_return;
		break;
	case AGNOCAST_GET_SHM_CMD:
		if (copy_from_user(&get_shm_args, (union ioctl_get_shm_args __user *)arg, sizeof(get_shm_args))) goto unlock_mutex_and_return;
		if (copy_from_user(topic_name_buf, (char __user *)get_shm_args.topic_name, sizeof(topic_name_buf))) goto unlock_mutex_and_return;
		get_shm(topic_name_buf, &get_shm_args);
		if (copy_to_user((union ioctl_get_shm_args __user *)arg, &get_shm_args, sizeof(get_shm_args))) goto unlock_mutex_and_return;
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

static char *agnocast_devnode(const struct device *dev, umode_t *mode) {
	if (mode) {
		*mode = 0666;
	}
	return NULL;
}

static struct file_operations fops = {
	.unlocked_ioctl = agnocast_ioctl,
};

static int major;
static struct class *agnocast_class;
static struct device *agnocast_device;

// =========================================
// Handler for process exit

// TODO: Modify agnocast kmod's data structure to keep its validity
static int pre_handler_do_exit(struct kprobe *p, struct pt_regs *regs) {
    printk(KERN_INFO "Process %d is exiting.\n", current->pid);
    return 0;
}

static struct kprobe kp = {
    .symbol_name    = "do_exit",
    .pre_handler    = pre_handler_do_exit,
};

// =========================================

static int agnocast_init(void) {
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
	agnocast_device = device_create(agnocast_class, NULL, MKDEV(major, 0), NULL, "agnocast"/*file name*/);

	return 0;
}

static void free_rb_tree(struct rb_root *root) {
    struct rb_node *next = rb_first(root);
    while (next) {
        struct pid_node *pn = rb_entry(next, struct pid_node, node);
        next = rb_next(next);
        rb_erase(&pn->node, root);
        kfree(pn);
    }
}

// TODO: Implement memory free later
static void free_all_topics(void) {
    struct topic_wrapper *entry;
    struct hlist_node *tmp;
    int bkt;

    hash_for_each_safe(topic_hashtable, bkt, tmp, entry, node) {
        hash_del(&entry->node);
        if (entry->key) {
            kfree(entry->key);
        }
		// TODO: free messages
        kfree(entry);
    }
}

static void agnocast_exit(void) {
	printk(KERN_INFO "Goodbye\n");

	free_all_topics();

	// Decrement reference count
	kobject_put(status_kobj);

    device_destroy(agnocast_class, MKDEV(major, 0));
    class_destroy(agnocast_class);
	unregister_chrdev(major, "agnocast");

	unregister_kprobe(&kp);
}

module_init(agnocast_init)
module_exit(agnocast_exit)
