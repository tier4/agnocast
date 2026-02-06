#include "agnocast/agnocast_cie_utils.hpp"

#include "agnocast/agnocast.hpp"
#include "rclcpp/rclcpp.hpp"

#include "cie_config_msgs/msg/callback_group_info.hpp"

#include <functional>
#include <memory>
#include <sstream>
#include <string>

namespace agnocast
{

std::string create_callback_group_id(
  rclcpp::CallbackGroup::SharedPtr group,
  rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node,
  const std::vector<std::string> & agnocast_topics)
{
  std::stringstream ss;

  std::string ns = std::string(node->get_namespace());
  if (ns != "/") {
    ns = ns + "/";
  }

  ss << ns << node->get_name() << "@";

  auto sub_func = [&ss](const rclcpp::SubscriptionBase::SharedPtr & sub) {
    ss << "Subscription(" << sub->get_topic_name() << ")@";
  };

  auto service_func = [&ss](const rclcpp::ServiceBase::SharedPtr & service) {
    ss << "Service(" << service->get_service_name() << ")@";
  };

  auto client_func = [&ss](const rclcpp::ClientBase::SharedPtr & client) {
    ss << "Client(" << client->get_service_name() << ")@";
  };

  auto timer_func = [&ss](const rclcpp::TimerBase::SharedPtr & timer) {
    std::shared_ptr<const rcl_timer_t> timer_handle = timer->get_timer_handle();
    int64_t period;
    rcl_ret_t ret = rcl_timer_get_period(timer_handle.get(), &period);
    (void)ret;

    ss << "Timer(" << period << ")@";
  };

  auto waitable_func = [](auto &&) {};

  group->collect_all_ptrs(sub_func, service_func, client_func, timer_func, waitable_func);

  // Agnocast Callbacks
  {
    for (const auto & topic : agnocast_topics) {
      if (topic.rfind("/AGNOCAST_SRV_REQUEST", 0) == 0) {
        ss << "AgnocastService(" << topic << ")@";
      } else if (topic.rfind("/AGNOCAST_SRV_RESPONSE", 0) == 0) {
        ss << "AgnocastClient(" << topic << ")@";
      } else {
        ss << "AgnocastSubscription(" << topic << ")@";
      }
    }
  }

  std::string ret = ss.str();
  ret.pop_back();

  return ret;
}

std::string create_callback_group_id(
  rclcpp::CallbackGroup::SharedPtr group, rclcpp::Node::SharedPtr node,
  const std::vector<std::string> & agnocast_topics)
{
  return create_callback_group_id(group, node->get_node_base_interface(), agnocast_topics);
}

agnocast::Publisher<cie_config_msgs::msg::CallbackGroupInfo>::SharedPtr create_client_publisher()
{
  static int idx = 1;

  auto node = std::make_shared<rclcpp::Node>(
    "client_node" + std::to_string(idx++), "/cie_thread_configurator");
  auto publisher = agnocast::create_publisher<cie_config_msgs::msg::CallbackGroupInfo>(
    node.get(), "/cie_thread_configurator/callback_group_info", rclcpp::QoS(1000));
  return publisher;
}

void publish_callback_group_info(
  const agnocast::Publisher<cie_config_msgs::msg::CallbackGroupInfo>::SharedPtr & publisher,
  int64_t tid, const std::string & callback_group_id)
{
  auto message = publisher->borrow_loaned_message();
  message->thread_id = tid;
  message->callback_group_id = callback_group_id;
  publisher->publish(std::move(message));
}

}  // namespace agnocast
