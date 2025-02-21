#include "node_for_no_starvation_test.hpp"

NodeForNoStarvation::NodeForNoStarvation(
  const int64_t num_agnocast_sub_cbs, const int64_t num_ros2_sub_cbs,
  const std::chrono::milliseconds pub_period)
: Node("node_for_no_starvation")
{
  // For Agnocast
  agnocast_timer_ =
    create_wall_timer(pub_period, std::bind(&NodeForNoStarvation::agnocast_timer_cb, this));
  for (int64_t i = 0; i < num_agnocast_sub_cbs; i++) {
    auto cbg = create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive);
    rclcpp::SubscriptionOptions options;
    options.callback_group = cbg;
    agnocast_sub_cbgs_.push_back(cbg);
    std::pair<mqd_t, std::string> mq_subscription;
    auto mq = agnocast::open_mq_for_subscription(agnocast_topic_name_, i, mq_subscription);
    mq_subscriptions_.push_back(mq_subscription);
    std::function<void(const agnocast::ipc_shared_ptr<std_msgs::msg::Bool> &)> callback =
      [this, i](const agnocast::ipc_shared_ptr<std_msgs::msg::Bool> & msg) {
        agnocast_sub_cb(msg, i);
      };
    agnocast::register_callback(callback, agnocast_topic_name_, i, mq, cbg);
  }
  agnocast_sub_cbs_called_.assign(num_agnocast_sub_cbs, false);

  // For ROS 2
  ros2_pub_ = create_publisher<std_msgs::msg::Bool>(ros2_topic_name_, 1);
  ros2_timer_ = create_wall_timer(pub_period, std::bind(&NodeForNoStarvation::ros2_timer_cb, this));
  for (int64_t i = 0; i < num_ros2_sub_cbs; i++) {
    auto cbg = create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive);
    rclcpp::SubscriptionOptions options;
    options.callback_group = cbg;
    ros2_sub_cbgs_.push_back(cbg);
    ros2_subs_.push_back(create_subscription<std_msgs::msg::Bool>(
      ros2_topic_name_, 1,
      [this, i](const std::shared_ptr<const std_msgs::msg::Bool> msg) { ros2_sub_cb(msg, i); },
      options));
  }
  ros2_sub_cbs_called_.assign(num_ros2_sub_cbs, false);
}

NodeForNoStarvation::~NodeForNoStarvation()
{
  for (auto & mq_subscription : mq_subscriptions_) {
    agnocast::remove_mq(mq_subscription);
  }
}

void NodeForNoStarvation::agnocast_timer_cb()
{
  for (auto & mq_subscription : mq_subscriptions_) {
    mqd_t mq = 0;
    if (mq_publishers_.find(mq_subscription.second) != mq_publishers_.end()) {
      mq = mq_publishers_[mq_subscription.second];
    } else {
      mq = mq_open(mq_subscription.second.c_str(), O_WRONLY | O_NONBLOCK);
      if (mq == -1) {
        std::cerr << "mq_open failed: " << strerror(errno) << std::endl;
        continue;
      }
      mq_publishers_.insert({mq_subscription.second, mq});
    }

    agnocast::MqMsgAgnocast mq_msg = {};
    if (mq_send(mq, reinterpret_cast<char *>(&mq_msg), 0 /*msg_len*/, 0) == -1) {
      if (errno != EAGAIN) {
        std::cerr << "mq_send failed: " << strerror(errno) << std::endl;
        continue;
      }
    }
  }
}

void NodeForNoStarvation::agnocast_sub_cb(
  [[maybe_unused]] const agnocast::ipc_shared_ptr<std_msgs::msg::Bool> & msg, int64_t cb_i)
{
  // Each callback only accesses its own index, so it's safe to access the vector without a mutex.
  agnocast_sub_cbs_called_[cb_i] = true;
}

void NodeForNoStarvation::ros2_timer_cb()
{
  std_msgs::msg::Bool msg;
  msg.data = true;
  ros2_pub_->publish(msg);
}

void NodeForNoStarvation::ros2_sub_cb(
  [[maybe_unused]] const std::shared_ptr<const std_msgs::msg::Bool> & msg, int64_t cb_i)
{
  // Each callback only accesses its own index, so it's safe to access the vector without a mutex.
  ros2_sub_cbs_called_[cb_i] = true;
}

bool NodeForNoStarvation::is_all_ros2_sub_cbs_called() const
{
  return std::all_of(ros2_sub_cbs_called_.begin(), ros2_sub_cbs_called_.end(), [](bool is_called) {
    return is_called;
  });
}

bool NodeForNoStarvation::is_all_agnocast_sub_cbs_called() const
{
  return std::all_of(
    agnocast_sub_cbs_called_.begin(), agnocast_sub_cbs_called_.end(),
    [](bool is_called) { return is_called; });
}
