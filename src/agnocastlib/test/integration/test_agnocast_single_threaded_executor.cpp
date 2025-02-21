#include "node_for_no_starvation_test.hpp"

#include <gtest/gtest.h>

#include <thread>

class SingleThreadedAgnocastExecutorNoStarvationTest : public ::testing::TestWithParam<int>
{
protected:
  void SetUp() override
  {
    rclcpp::init(0, nullptr);
    executor = std::make_shared<agnocast::SingleThreadedAgnocastExecutor>(
      rclcpp::ExecutorOptions{}, GetParam());
    test_node =
      std::make_shared<NodeForNoStarvation>(NUM_ROS2_SUB_CBS, NUM_AGNOCAST_SUB_CBS, PUB_PERIOD);
    executor->add_node(test_node);
  }

  void TearDown() override { rclcpp::shutdown(); }

  std::shared_ptr<NodeForNoStarvation> test_node;
  std::shared_ptr<agnocast::SingleThreadedAgnocastExecutor> executor;

  // Parameters
  const std::chrono::seconds SPIN_DURATION = std::chrono::seconds(10);
  const uint64_t NUM_ROS2_SUB_CBS = 10;
  const uint64_t NUM_AGNOCAST_SUB_CBS = 10;
  const std::chrono::milliseconds PUB_PERIOD = std::chrono::milliseconds(100);
};

INSTANTIATE_TEST_SUITE_P(
  MyParametrizedTests, SingleThreadedAgnocastExecutorNoStarvationTest,
  ::testing::Values(25, 50, 100, 200, 400, 800, 1600));  // next_exec_timeout_ms

TEST_P(SingleThreadedAgnocastExecutorNoStarvationTest, test_normal)
{
  // Act
  std::thread spin_thread([this]() { this->executor->spin(); });
  std::this_thread::sleep_for(SPIN_DURATION);
  executor->cancel();
  spin_thread.join();

  // Assert
  EXPECT_TRUE(test_node->is_all_ros2_sub_cbs_called());
  EXPECT_TRUE(test_node->is_all_agnocast_sub_cbs_called());
}
