#include "node_for_no_starvation_test.hpp"

#include <gtest/gtest.h>

#include <thread>

class MultiThreadedAgnocastExecutorNoStarvationTest
: public ::testing::TestWithParam<std::tuple<bool, int>>
{
private:
  void set_spin_duration_based_on_params(const int agnocast_next_exec_timeout_ms)
  {
    std::chrono::seconds buffer = std::chrono::seconds(3);  // Rough value
    spin_duration_ =
      std::chrono::seconds(
        agnocast_next_exec_timeout_ms * (NUM_AGNOCAST_SUB_CBS + NUM_AGNOCAST_CBS_TO_BE_ADDED) /
        1000 / NUMBER_OF_AGNOCAST_THREADS) +
      buffer;
  }

protected:
  void SetUp() override
  {
    bool yield_before_execute = std::get<0>(GetParam());
    int next_exec_timeout_ms = std::get<1>(GetParam());
    int agnocast_next_exec_timeout_ms = next_exec_timeout_ms;
    std::chrono::nanoseconds ros2_next_exec_timeout(next_exec_timeout_ms * 1000 * 1000);
    set_spin_duration_based_on_params(agnocast_next_exec_timeout_ms);

    rclcpp::init(0, nullptr);
    executor_ = std::make_shared<agnocast::MultiThreadedAgnocastExecutor>(
      rclcpp::ExecutorOptions{}, NUMBER_OF_ROS2_THREADS, NUMBER_OF_AGNOCAST_THREADS,
      yield_before_execute, ros2_next_exec_timeout, AGNOCAST_CALLBACK_GROUP_WAIT_TIME,
      agnocast_next_exec_timeout_ms);
    test_node_ = std::make_shared<NodeForNoStarvation>(
      NUM_AGNOCAST_SUB_CBS, NUM_ROS2_SUB_CBS, NUM_AGNOCAST_CBS_TO_BE_ADDED, PUB_PERIOD);
    executor_->add_node(test_node_);
  }

  void TearDown() override { rclcpp::shutdown(); }

  std::shared_ptr<NodeForNoStarvation> test_node_;
  std::shared_ptr<agnocast::MultiThreadedAgnocastExecutor> executor_;
  std::chrono::seconds spin_duration_;

  // Parameters
  const std::chrono::milliseconds PUB_PERIOD = std::chrono::milliseconds(50);
  const size_t NUMBER_OF_ROS2_THREADS = 3;
  const size_t NUMBER_OF_AGNOCAST_THREADS = 3;
  const uint64_t NUM_ROS2_SUB_CBS = NUMBER_OF_ROS2_THREADS * 3;
  const uint64_t NUM_AGNOCAST_SUB_CBS = NUMBER_OF_AGNOCAST_THREADS * 3;
  const uint64_t NUM_AGNOCAST_CBS_TO_BE_ADDED = NUMBER_OF_AGNOCAST_THREADS * 2;
  const std::chrono::nanoseconds AGNOCAST_CALLBACK_GROUP_WAIT_TIME =
    std::chrono::nanoseconds(10 * 1000 * 1000);
};

INSTANTIATE_TEST_SUITE_P(
  MultiThreadedAgnocastExecutorNoStarvationTests, MultiThreadedAgnocastExecutorNoStarvationTest,
  ::testing::Combine(
    ::testing::Values(true, false),  // yield_before_execute
    ::testing::Values(
      25, 50, 100, 200, 400)  // ros2_next_exec_timeout and agnocast_next_exec_timeout_ms
    ));

TEST_P(MultiThreadedAgnocastExecutorNoStarvationTest, test_no_starvation)
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
