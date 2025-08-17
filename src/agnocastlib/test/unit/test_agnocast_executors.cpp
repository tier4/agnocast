#include "agnocast/agnocast_callback_isolated_executor.hpp"

#include <gtest/gtest.h>

class CallbackIsolatedAgnocastExecutorTest : public ::testing::Test
{
protected:
  void SetUp() override
  {
    rclcpp::init(0, nullptr);
    executor =
      std::make_shared<agnocast::CallbackIsolatedAgnocastExecutor>(rclcpp::ExecutorOptions());
  }

  void TearDown() override { rclcpp::shutdown(); }

  std::shared_ptr<agnocast::CallbackIsolatedAgnocastExecutor> executor;
};

TEST_F(CallbackIsolatedAgnocastExecutorTest, add_remove_callback_group)
{
  auto node = std::make_shared<rclcpp::Node>("test_node");
  auto group = node->create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive);

  executor->add_callback_group(group, node->get_node_base_interface());

  auto groups = executor->get_manually_added_callback_groups();
  EXPECT_EQ(groups.size(), 1);
  EXPECT_TRUE(groups[0].lock() == group);

  executor->remove_callback_group(group);
  groups = executor->get_manually_added_callback_groups();
  EXPECT_EQ(groups.size(), 0);
}

TEST_F(CallbackIsolatedAgnocastExecutorTest, add_remove_node)
{
  auto node = std::make_shared<rclcpp::Node>("test_node");

  executor->add_node(node->get_node_base_interface());

  auto nodes = executor->get_automatically_added_callback_groups_from_nodes();
  EXPECT_EQ(nodes.size(), 1);

  executor->remove_node(node->get_node_base_interface());
  nodes = executor->get_automatically_added_callback_groups_from_nodes();
  EXPECT_EQ(nodes.size(), 0);
}

TEST_F(CallbackIsolatedAgnocastExecutorTest, get_all_callback_groups)
{
  auto node = std::make_shared<rclcpp::Node>("test_node");
  auto group = node->create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive);
  auto node2 = std::make_shared<rclcpp::Node>("test_node2");

  executor->add_callback_group(group, node->get_node_base_interface());
  executor->add_node(node2);

  auto groups = executor->get_all_callback_groups();
  EXPECT_EQ(groups.size(), 2);

  executor->remove_callback_group(group);
  groups = executor->get_all_callback_groups();
  EXPECT_EQ(groups.size(), 1);

  executor->remove_node(node2);
  groups = executor->get_all_callback_groups();
  EXPECT_EQ(groups.size(), 0);
}
