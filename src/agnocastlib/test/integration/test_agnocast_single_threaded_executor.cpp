#include "node_for_no_starvation_test.hpp"

#include <gtest/gtest.h>

#include <thread>

class SingleThreadedAgnocastExecutorNoStarvationTest : public ::testing::TestWithParam<int>
{
private:
  void set_spin_duration_based_on_params(const int next_exec_timeout_ms)
  {
    std::chrono::seconds buffer = std::chrono::seconds(3);  // Rough value
    spin_duration_ =
      std::chrono::seconds(
        next_exec_timeout_ms * (NUM_AGNOCAST_SUB_CBS + NUM_AGNOCAST_CBS_TO_BE_ADDED) / 1000) +
      buffer;
  }

protected:
  void SetUp() override
  {
    int next_exec_timeout_ms = GetParam();
    set_spin_duration_based_on_params(next_exec_timeout_ms);

    rclcpp::init(0, nullptr);
    executor_ = std::make_shared<agnocast::SingleThreadedAgnocastExecutor>(
      rclcpp::ExecutorOptions{}, GetParam());
    test_node_ = std::make_shared<NodeForNoStarvation>(
      NUM_AGNOCAST_SUB_CBS, NUM_ROS2_SUB_CBS, NUM_AGNOCAST_CBS_TO_BE_ADDED, PUB_PERIOD);
    executor_->add_node(test_node_);
  }

  void TearDown() override { rclcpp::shutdown(); }

  std::shared_ptr<NodeForNoStarvation> test_node_;
  std::shared_ptr<agnocast::SingleThreadedAgnocastExecutor> executor_;
  std::chrono::seconds spin_duration_;

  // Parameters
  const uint64_t NUM_ROS2_SUB_CBS = 10;
  const uint64_t NUM_AGNOCAST_SUB_CBS = 10;
  const uint64_t NUM_AGNOCAST_CBS_TO_BE_ADDED = 5;
  const std::chrono::milliseconds PUB_PERIOD = std::chrono::milliseconds(100);
};

INSTANTIATE_TEST_SUITE_P(
  SingleThreadedAgnocastExecutorNoStarvationTests, SingleThreadedAgnocastExecutorNoStarvationTest,
  ::testing::Values(25, 50, 100, 200, 400));  // next_exec_timeout_ms

TEST_P(SingleThreadedAgnocastExecutorNoStarvationTest, test_no_starvation)
{
  // Act
  std::thread spin_thread([this]() { this->executor_->spin(); });
  std::this_thread::sleep_for(spin_duration_);
  executor_->cancel();
  spin_thread.join();

  // Assert
  EXPECT_TRUE(test_node_->is_all_ros2_sub_cbs_called());
  EXPECT_TRUE(test_node_->is_all_agnocast_sub_cbs_called());
}
