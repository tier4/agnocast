#pragma once
#include "agnocast/agnocast.hpp"

#include <std_msgs/msg/bool.hpp>

#include <vector>

class NodeForNoStarvation : public rclcpp::Node
{
private:
  // For Agnocast
  rclcpp::TimerBase::SharedPtr agnocast_timer_;
  std::vector<bool> agnocast_sub_cbs_called_;
  std::string agnocast_topic_name_ = "/dummy_agnocast_topic";
  // These mqueues are used to execute the agnocast callbacks without Publisher and Subscription.
  std::vector<std::pair<mqd_t, std::string>> mq_receivers_;
  std::unordered_map<std::string, mqd_t> mq_senders_;

  void add_agnocast_sub_cb();
  mqd_t open_mq_for_receiver(const int64_t cb_i);
  void agnocast_timer_cb();
  void agnocast_sub_cb(const agnocast::ipc_shared_ptr<std_msgs::msg::Bool> & msg, int64_t cb_i);

  // For ROS 2
  rclcpp::TimerBase::SharedPtr ros2_timer_;
  rclcpp::Publisher<std_msgs::msg::Bool>::SharedPtr ros2_pub_;
  std::vector<rclcpp::Subscription<std_msgs::msg::Bool>::SharedPtr> ros2_subs_;
  std::vector<bool> ros2_sub_cbs_called_;
  std::string ros2_topic_name_ = "/dummy_ros2_topic";

  void ros2_timer_cb();
  void ros2_sub_cb(const std::shared_ptr<const std_msgs::msg::Bool> & msg, int64_t cb_i);

public:
  explicit NodeForNoStarvation(
    const int64_t num_agnocast_sub_cbs, const int64_t num_ros2_sub_cbs,
    const int64_t num_agnocast_cbs_to_be_added, const std::chrono::milliseconds pub_period);

  ~NodeForNoStarvation();

  bool is_all_ros2_sub_cbs_called() const;
  bool is_all_agnocast_sub_cbs_called() const;
};
