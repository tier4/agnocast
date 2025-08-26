#include "agnocast/agnocast.hpp"

namespace agnocast
{

void launch_bridge_daemon_process(
  const rclcpp::Logger & logger, const std::string & shared_lib_path,
  const std::string & mangled_name, const std::string & topic_name, const rclcpp::QoS & qos)
{
  std::string daemon_name = "agnocast_bridge_daemon";
  std::string executable_path;
  try {
    std::string package_prefix = ament_index_cpp::get_package_prefix("agnocastlib");
    executable_path = package_prefix + "/lib/agnocastlib/" + daemon_name;
  } catch (const ament_index_cpp::PackageNotFoundError & e) {
    RCLCPP_ERROR(
      logger, "Could not find package 'agnocastlib' to locate bridge daemon. Error: %s", e.what());
    return;
  }

  pid_t pid = fork();

  if (pid < 0) {
    RCLCPP_ERROR(logger, "fork() failed for bridge daemon: %s", strerror(errno));
    return;
  }

  if (pid == 0) {
    const auto & rmw_qos = qos.get_rmw_qos_profile();
    std::vector<std::string> string_args = {
      daemon_name,
      shared_lib_path,
      mangled_name,
      topic_name,
      std::to_string(rmw_qos.history),
      std::to_string(rmw_qos.depth),
      std::to_string(rmw_qos.reliability)};

    std::vector<char *> argv;
    argv.reserve(string_args.size() + 1);
    for (auto & arg : string_args) {
      argv.push_back(arg.data());
    }
    argv.push_back(nullptr);

    execv(executable_path.c_str(), argv.data());
    perror(("execv failed for " + executable_path).c_str());
    _exit(EXIT_FAILURE);
  }
}

SubscriptionBase::SubscriptionBase(rclcpp::Node * node, const std::string & topic_name)
: id_(0), topic_name_(node->get_node_topics_interface()->resolve_topic_name(topic_name))
{
  validate_ld_preload();
}

union ioctl_add_subscriber_args SubscriptionBase::initialize(
  const rclcpp::QoS & qos, const bool is_take_sub, const std::string & node_name)
{
  union ioctl_add_subscriber_args add_subscriber_args = {};
  add_subscriber_args.topic_name = {topic_name_.c_str(), topic_name_.size()};
  add_subscriber_args.node_name = {node_name.c_str(), node_name.size()};
  add_subscriber_args.qos_depth = static_cast<uint32_t>(qos.depth());
  add_subscriber_args.qos_is_transient_local =
    qos.durability() == rclcpp::DurabilityPolicy::TransientLocal;
  add_subscriber_args.is_take_sub = is_take_sub;
  if (ioctl(agnocast_fd, AGNOCAST_ADD_SUBSCRIBER_CMD, &add_subscriber_args) < 0) {
    RCLCPP_ERROR(logger, "AGNOCAST_ADD_SUBSCRIBER_CMD failed: %s", strerror(errno));
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  return add_subscriber_args;
}

mqd_t open_mq_for_subscription(
  const std::string & topic_name, const topic_local_id_t subscriber_id,
  std::pair<mqd_t, std::string> & mq_subscription)
{
  std::string mq_name = create_mq_name_for_agnocast_publish(topic_name, subscriber_id);
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
  /* The message queue is destroyed after all the publisher processes close it. */
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
