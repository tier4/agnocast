#pragma once

#include "agnocast/agnocast_publisher.hpp"
#include "rclcpp/rclcpp.hpp"

#include <regex>

namespace agnocast
{

void bridge_process_main(const MqMsgBridge & msg);
QoSFlat flatten_qos(const rclcpp::QoS & qos);
rclcpp::QoS reconstruct_qos(const QoSFlat & q);
bool get_topic_publishers(
  const std::string & topic_name, std::vector<std::string> & publisher_names,
  rclcpp::Logger logger);

template <typename MessageT>
class BridgeNode : public rclcpp::Node
{
public:
  explicit BridgeNode(const BridgeArgs & args)
  : rclcpp::Node(
      "agnocast_bridge" + std::regex_replace(std::string(args.topic_name), std::regex("/"), "_"))
  {
    std::string topic_name(args.topic_name);
    rclcpp::QoS qos = reconstruct_qos(args.qos);

    agnocast::PublisherOptions pub_options;
    agnocast_pub_ =
      std::make_shared<agnocast::Publisher<MessageT>>(this, topic_name, qos, pub_options);

    auto callback = [this, topic_name](
                      const typename MessageT::ConstSharedPtr msg,
                      const rclcpp::MessageInfo & info) {
      using PublisherGidInfo = std::pair<std::string, rmw_gid_t>;
      std::vector<PublisherGidInfo> publisher_gids;
      std::vector<std::string> agnocast_publisher_names;
      std::vector<std::string> ros2_publisher_names;
      std::vector<rmw_gid_t> filter_gids;
      if (get_topic_publishers(topic_name, agnocast_publisher_names, this->get_logger())) {
        const auto ros2_publishers_info = this->get_publishers_info_by_topic(topic_name);
        for (const auto & info : ros2_publishers_info) {
          const std::string node_name = info.node_name();
          ros2_publisher_names.push_back(node_name);
          const auto & source_gid_data = info.endpoint_gid();

          rmw_gid_t gid;
          std::memset(&gid, 0, sizeof(rmw_gid_t));

          if (source_gid_data.size() == RMW_GID_STORAGE_SIZE) {
            std::memcpy(gid.data, source_gid_data.data(), source_gid_data.size());
            publisher_gids.emplace_back(node_name, gid);

          } else {
            RCLCPP_WARN(
              this->get_logger(),
              "GID size mismatch or unsupported format for node %s. Skipping GID storage.",
              info.node_name().c_str());
          }
        }

        for (const auto & agnocast_name : agnocast_publisher_names) {
          auto it =
            std::find(ros2_publisher_names.begin(), ros2_publisher_names.end(), agnocast_name);
          if (it != ros2_publisher_names.end()) {
            size_t index = std::distance(ros2_publisher_names.begin(), it);
            if (index < publisher_gids.size()) {
              const auto & gid_info = publisher_gids[index];
              filter_gids.push_back(gid_info.second);
            }
          }
        }
      } else {
        RCLCPP_ERROR(
          this->get_logger(), "Failed to get publisher information for topic '%s'.",
          topic_name.c_str());
      }

      rmw_gid_t msg_gid = info.get_rmw_message_info().publisher_gid;

      bool should_filter = false;
      for (const auto & gid : filter_gids) {
        if (std::memcmp(gid.data, msg_gid.data, RMW_GID_STORAGE_SIZE) == 0) {
          should_filter = true;
          break;
        }
      }

      if (should_filter) {
        return;
      }

      auto loaned_msg = this->agnocast_pub_->borrow_loaned_message();
      *loaned_msg = *msg;
      this->agnocast_pub_->publish(std::move(loaned_msg));
    };

    rclcpp::SubscriptionOptions sub_options;
    sub_options.ignore_local_publications = true;
    ros_sub_ = this->create_subscription<MessageT>(topic_name, qos, callback, sub_options);
  }

private:
  typename agnocast::Publisher<MessageT>::SharedPtr agnocast_pub_;
  typename rclcpp::Subscription<MessageT>::SharedPtr ros_sub_;
};

template <typename MessageT>
std::shared_ptr<rclcpp::Node> start_bridge_node(const BridgeArgs & args)
{
  return std::make_shared<BridgeNode<MessageT>>(args);
}

}  // namespace agnocast

using BridgeFn = std::shared_ptr<rclcpp::Node> (*)(const agnocast::BridgeArgs &);