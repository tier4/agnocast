#include "agnocast/agnocast_subscription.hpp"

#include <gtest/gtest.h>

class GetValidCallbackGroupTest : public ::testing::Test
{
protected:
  void SetUp() override
  {
    rclcpp::init(0, nullptr);
    node = std::make_shared<rclcpp::Node>("dummy");
  }

  void TearDown() override { rclcpp::shutdown(); }

  std::shared_ptr<rclcpp::Node> node;
};

TEST_F(GetValidCallbackGroupTest, get_valid_callback_group_normal)
{
  agnocast::SubscriptionOptions options;
  options.callback_group =
    node->create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive);

  auto result = agnocast::get_valid_callback_group(node->get_node_base_interface(), options);

  EXPECT_EQ(result, options.callback_group);
}

TEST_F(GetValidCallbackGroupTest, get_valid_callback_group_not_in_node)
{
  auto other_node = std::make_shared<rclcpp::Node>("other_node");
  agnocast::SubscriptionOptions options;
  options.callback_group =
    other_node->create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive);

  EXPECT_EXIT(
    agnocast::get_valid_callback_group(node->get_node_base_interface(), options),
    ::testing::ExitedWithCode(EXIT_FAILURE),
    "Cannot create agnocast subscription, callback group not in node.");
}

TEST_F(GetValidCallbackGroupTest, get_valid_callback_group_nullptr)
{
  auto node_base = node->get_node_base_interface();
  agnocast::SubscriptionOptions options;

  auto result = agnocast::get_valid_callback_group(node_base, options);
  EXPECT_EQ(result, node_base->get_default_callback_group());
}
