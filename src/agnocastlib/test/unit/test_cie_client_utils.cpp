#include "agnocast/cie_client_utils.hpp"

#include <rclcpp/rclcpp.hpp>

#include <std_msgs/msg/bool.hpp>

#include <gtest/gtest.h>

#include <chrono>
#include <string>
#include <vector>

class CreateCallbackGroupIdTest : public ::testing::Test
{
protected:
  void SetUp() override
  {
    rclcpp::init(0, nullptr);
    node_ = std::make_shared<rclcpp::Node>("test_node");
  }

  void TearDown() override { rclcpp::shutdown(); }

  rclcpp::Node::SharedPtr node_;
};

TEST_F(CreateCallbackGroupIdTest, EmptyGroup)
{
  auto group = node_->create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive);
  std::vector<std::string> agnocast_topics;

  auto id = agnocast::create_callback_group_id(group, node_, agnocast_topics);

  EXPECT_EQ(id, "/test_node");
}

TEST_F(CreateCallbackGroupIdTest, SubscriptionOnly)
{
  auto group = node_->create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive);
  rclcpp::SubscriptionOptions sub_options;
  sub_options.callback_group = group;
  auto sub = node_->create_subscription<std_msgs::msg::Bool>(
    "/topic_a", 10, [](const std::shared_ptr<const std_msgs::msg::Bool>) {}, sub_options);

  std::vector<std::string> agnocast_topics;

  auto id = agnocast::create_callback_group_id(group, node_, agnocast_topics);

  EXPECT_EQ(id, "/test_node@Subscription(/topic_a)");
}

TEST_F(CreateCallbackGroupIdTest, TimerOnly)
{
  auto group = node_->create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive);
  auto timer = node_->create_wall_timer(std::chrono::seconds(1), []() {}, group);

  std::vector<std::string> agnocast_topics;

  auto id = agnocast::create_callback_group_id(group, node_, agnocast_topics);

  EXPECT_EQ(id, "/test_node@Timer(1000000000)");
}

TEST_F(CreateCallbackGroupIdTest, AgnocastSubscription)
{
  auto group = node_->create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive);
  std::vector<std::string> agnocast_topics = {"/topic_a"};

  auto id = agnocast::create_callback_group_id(group, node_, agnocast_topics);

  EXPECT_EQ(id, "/test_node@AgnocastSubscription(/topic_a)");
}

TEST_F(CreateCallbackGroupIdTest, AgnocastService)
{
  auto group = node_->create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive);
  std::vector<std::string> agnocast_topics = {"/AGNOCAST_SRV_REQUEST/my_service"};

  auto id = agnocast::create_callback_group_id(group, node_, agnocast_topics);

  EXPECT_EQ(id, "/test_node@AgnocastService(/AGNOCAST_SRV_REQUEST/my_service)");
}

TEST_F(CreateCallbackGroupIdTest, AgnocastClient)
{
  auto group = node_->create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive);
  std::vector<std::string> agnocast_topics = {"/AGNOCAST_SRV_RESPONSE/my_service_SEP_client_node"};

  auto id = agnocast::create_callback_group_id(group, node_, agnocast_topics);

  EXPECT_EQ(id, "/test_node@AgnocastClient(/AGNOCAST_SRV_RESPONSE/my_service_SEP_client_node)");
}

TEST_F(CreateCallbackGroupIdTest, MultipleAgnocastTopics)
{
  auto group = node_->create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive);
  std::vector<std::string> agnocast_topics = {"/topic_a", "/topic_b"};

  auto id = agnocast::create_callback_group_id(group, node_, agnocast_topics);

  EXPECT_EQ(id, "/test_node@AgnocastSubscription(/topic_a)@AgnocastSubscription(/topic_b)");
}

TEST_F(CreateCallbackGroupIdTest, MixedAgnocastAndRclcpp)
{
  auto group = node_->create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive);
  rclcpp::SubscriptionOptions sub_options;
  sub_options.callback_group = group;
  auto sub = node_->create_subscription<std_msgs::msg::Bool>(
    "/rclcpp_topic", 10, [](const std::shared_ptr<const std_msgs::msg::Bool>) {}, sub_options);
  std::vector<std::string> agnocast_topics = {"/agnocast_topic"};

  auto id = agnocast::create_callback_group_id(group, node_, agnocast_topics);

  // rclcpp callbacks appear first (from collect_all_ptrs), then agnocast topics
  EXPECT_EQ(id, "/test_node@Subscription(/rclcpp_topic)@AgnocastSubscription(/agnocast_topic)");
}

TEST_F(CreateCallbackGroupIdTest, NodeBaseInterfaceOverload)
{
  auto group = node_->create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive);
  std::vector<std::string> agnocast_topics;

  // Call the NodeBaseInterface overload directly
  auto id =
    agnocast::create_callback_group_id(group, node_->get_node_base_interface(), agnocast_topics);

  EXPECT_EQ(id, "/test_node");
}
