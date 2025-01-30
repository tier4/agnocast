#include "agnocast.hpp"

namespace agnocast
{

mqd_t mq_new_publisher = -1;

extern std::vector<std::thread> threads;

SubscriptionBase::SubscriptionBase(
  rclcpp::Node * node, const std::string & topic_name, const rclcpp::QoS & qos)
: index_(0),
  topic_name_(node->get_node_topics_interface()->resolve_topic_name(topic_name)),
  qos_(qos)
{
  validate_ld_preload();
}

static void wait_for_new_publisher(const pid_t subscriber_pid)
{
  static pthread_mutex_t wait_newpub_mtx = PTHREAD_MUTEX_INITIALIZER;

  pthread_mutex_lock(&wait_newpub_mtx);

  static bool is_initialized = false;
  if (is_initialized) {
    pthread_mutex_unlock(&wait_newpub_mtx);
    return;
  }
  is_initialized = true;

  pthread_mutex_unlock(&wait_newpub_mtx);

  const std::string mq_name = create_mq_name_new_publisher(subscriber_pid);

  struct mq_attr attr = {};
  attr.mq_flags = 0;         // Blocking queue
  const int mq_maxmsg = 10;  // Maximum number of messages in the queue
  attr.mq_maxmsg = mq_maxmsg;
  attr.mq_msgsize = sizeof(MqMsgNewPublisher);  // Maximum message size
  attr.mq_curmsgs = 0;  // Number of messages currently in the queue (not set by mq_open)

  const int mq_mode = 0666;
  mqd_t mq = mq_open(mq_name.c_str(), O_CREAT | O_RDONLY, mq_mode, &attr);
  if (mq == -1) {
    RCLCPP_ERROR(logger, "mq_open for new publisher failed: %s", strerror(errno));
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }
  mq_new_publisher = mq;

  // Create a thread that maps the areas for publishers afterwards
  auto th = std::thread([=]() {
    while (agnocast::ok()) {
      MqMsgNewPublisher mq_msg = {};
      auto ret = mq_receive(mq, reinterpret_cast<char *>(&mq_msg), sizeof(mq_msg), nullptr);
      if (ret == -1) {
        RCLCPP_ERROR(logger, "mq_receive for new publisher failed: %s", strerror(errno));
        close(agnocast_fd);
        exit(EXIT_FAILURE);
      }

      const uint32_t publisher_pid = mq_msg.publisher_pid;
      const uint64_t publisher_shm_addr = mq_msg.shm_addr;
      const uint64_t publisher_shm_size = mq_msg.shm_size;
      map_read_only_area(publisher_pid, publisher_shm_addr, publisher_shm_size);
    }
  });

  threads.push_back(std::move(th));
}

union ioctl_subscriber_args SubscriptionBase::initialize(bool is_take_sub)
{
  const pid_t subscriber_pid = getpid();

  // Open a mq for new publisher appearences.
  wait_for_new_publisher(subscriber_pid);

  // Register topic and subscriber info with the kernel module, and receive the publisher's shared
  // memory information along with messages needed to achieve transient local, if neccessary.
  union ioctl_subscriber_args subscriber_args = {};
  subscriber_args.topic_name = topic_name_.c_str();
  subscriber_args.qos_depth = (qos_.durability() == rclcpp::DurabilityPolicy::TransientLocal)
                                ? static_cast<uint32_t>(qos_.depth())
                                : 0;
  subscriber_args.subscriber_pid = static_cast<uint32_t>(subscriber_pid);
  subscriber_args.init_timestamp = agnocast_get_timestamp();
  subscriber_args.is_take_sub = is_take_sub;
  if (ioctl(agnocast_fd, AGNOCAST_SUBSCRIBER_ADD_CMD, &subscriber_args) < 0) {
    RCLCPP_ERROR(logger, "AGNOCAST_SUBSCRIBER_ADD_CMD failed: %s", strerror(errno));
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  for (uint32_t i = 0; i < subscriber_args.ret_publisher_num; i++) {
    if (static_cast<pid_t>(subscriber_args.ret_publisher_pids[i]) == subscriber_pid) {
      continue;
    }

    const uint32_t pid = subscriber_args.ret_publisher_pids[i];
    const uint64_t addr = subscriber_args.ret_shm_addrs[i];
    const uint64_t size = subscriber_args.ret_shm_sizes[i];
    map_read_only_area(pid, addr, size);
  }

  return subscriber_args;
}

mqd_t open_mq_for_subscription(
  const std::string & topic_name, const uint32_t subscriber_index,
  std::pair<mqd_t, std::string> & mq_subscription)
{
  std::string mq_name = create_mq_name(topic_name, subscriber_index);
  struct mq_attr attr = {};
  attr.mq_flags = 0;                        // Blocking queue
  attr.mq_msgsize = sizeof(MqMsgAgnocast);  // Maximum message size
  attr.mq_curmsgs = 0;  // Number of messages currently in the queue (not set by mq_open)
  attr.mq_maxmsg = 1;

  const int mq_mode = 0666;
  mqd_t mq = mq_open(mq_name.c_str(), O_CREAT | O_RDONLY | O_NONBLOCK, mq_mode, &attr);
  if (mq == -1) {
    RCLCPP_ERROR(logger, "mq_open failed: %s", strerror(errno));
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }
  mq_subscription = std::make_pair(mq, mq_name);

  return mq;
}

void remove_mq(const std::pair<mqd_t, std::string> & mq_subscription)
{
  /* It's best to notify the publisher and have it call mq_close, but currently
    this is not being done. The message queue is destroyed when the publisher process exits. */
  if (mq_close(mq_subscription.first) == -1) {
    RCLCPP_ERROR(logger, "mq_close failed: %s", strerror(errno));
  }
  if (mq_unlink(mq_subscription.second.c_str()) == -1) {
    RCLCPP_ERROR(logger, "mq_unlink failed: %s", strerror(errno));
  }
}

rclcpp::CallbackGroup::SharedPtr get_valid_callback_group(
  const rclcpp::node_interfaces::NodeBaseInterface::SharedPtr & node,
  const SubscriptionOptions & options)
{
  rclcpp::CallbackGroup::SharedPtr callback_group = options.callback_group;

  if (callback_group) {
    if (!node->callback_group_in_node(callback_group)) {
      RCLCPP_ERROR(logger, "Cannot create agnocast subscription, callback group not in node.");
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }
  } else {
    callback_group = node->get_default_callback_group();
  }

  return callback_group;
}

}  // namespace agnocast
