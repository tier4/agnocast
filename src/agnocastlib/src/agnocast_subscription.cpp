#include "agnocast.hpp"

namespace agnocast
{

SubscriptionBase::SubscriptionBase(
  rclcpp::Node * node, const std::string & topic_name, const rclcpp::QoS & qos)
: id_(0), topic_name_(node->get_node_topics_interface()->resolve_topic_name(topic_name)), qos_(qos)
{
  validate_ld_preload();
}

union ioctl_subscriber_args SubscriptionBase::initialize(bool is_take_sub)
{
  const pid_t subscriber_pid = getpid();

  // Register topic and subscriber info with the kernel module, and receive the publisher's shared
  // memory information along with messages needed to achieve transient local, if neccessary.
  union ioctl_subscriber_args subscriber_args = {};
  subscriber_args.topic_name = topic_name_.c_str();
  subscriber_args.qos_depth = (qos_.durability() == rclcpp::DurabilityPolicy::TransientLocal)
                                ? static_cast<uint32_t>(qos_.depth())
                                : 0;
  subscriber_args.subscriber_pid = subscriber_pid;
  subscriber_args.is_take_sub = is_take_sub;
  if (ioctl(agnocast_fd, AGNOCAST_SUBSCRIBER_ADD_CMD, &subscriber_args) < 0) {
    RCLCPP_ERROR(logger, "AGNOCAST_SUBSCRIBER_ADD_CMD failed: %s", strerror(errno));
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  for (uint32_t i = 0; i < subscriber_args.pub_shm_info.ret_publisher_num; i++) {
    const pid_t pid = subscriber_args.pub_shm_info.ret_publisher_pids[i];
    const uint64_t addr = subscriber_args.pub_shm_info.ret_shm_addrs[i];
    const uint64_t size = subscriber_args.pub_shm_info.ret_shm_sizes[i];
    map_read_only_area(pid, addr, size);
  }

  return subscriber_args;
}

mqd_t open_mq_for_subscription(
  const std::string & topic_name, const topic_local_id_t subscriber_id,
  std::pair<mqd_t, std::string> & mq_subscription)
{
  std::string mq_name = create_mq_name(topic_name, subscriber_id);
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
