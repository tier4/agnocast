#include "node_for_no_starvation_test.hpp"

#include <gtest/gtest.h>

#include <thread>

class MultiThreadedAgnocastExecutorNoStarvationTest
: public ::testing::TestWithParam<std::tuple<bool, int, std::string>>
{
private:
  void set_complex_params(const std::string cbg_type, const int agnocast_next_exec_timeout_ms)
  {
    // Set the execution time of each callback
    uint64_t num_cbs = NUM_AGNOCAST_SUB_CBS + NUM_AGNOCAST_CBS_TO_BE_ADDED + NUM_ROS2_SUB_CBS;
    if (cbg_type == "mutually_exclusive") {
      cb_exec_time_ =
        std::chrono::duration_cast<std::chrono::milliseconds>(PUB_PERIOD * 0.8 / (num_cbs));
    } else {  // individual or reentrant
      cb_exec_time_ = std::chrono::duration_cast<std::chrono::milliseconds>(
        PUB_PERIOD * 0.8 * (NUMBER_OF_AGNOCAST_THREADS + NUMBER_OF_ROS2_THREADS) / (num_cbs));
    }

    // Set the spin duration
    std::chrono::seconds buffer = std::chrono::seconds(1);  // Rough value
    spin_duration_ = std::max(
                       std::chrono::seconds(
                         (agnocast_next_exec_timeout_ms + cb_exec_time_.count()) *
                         (NUM_AGNOCAST_SUB_CBS + NUM_AGNOCAST_CBS_TO_BE_ADDED) / 1000),
                       std::chrono::duration_cast<std::chrono::seconds>(
                         PUB_PERIOD * NUM_AGNOCAST_CBS_TO_BE_ADDED)) +
                     buffer;
  }

protected:
  void SetUp() override
  {
    bool yield_before_execute = std::get<0>(GetParam());
    int next_exec_timeout_ms = std::get<1>(GetParam());
    std::string cbg_type = std::get<2>(GetParam());
    int agnocast_next_exec_timeout_ms = next_exec_timeout_ms;
    std::chrono::nanoseconds ros2_next_exec_timeout(next_exec_timeout_ms * 1000 * 1000);
    set_complex_params(cbg_type, agnocast_next_exec_timeout_ms);

    rclcpp::init(0, nullptr);
    executor_ = std::make_shared<agnocast::MultiThreadedAgnocastExecutor>(
      rclcpp::ExecutorOptions{}, NUMBER_OF_ROS2_THREADS, NUMBER_OF_AGNOCAST_THREADS,
      yield_before_execute, ros2_next_exec_timeout, agnocast_next_exec_timeout_ms);
    test_node_ = std::make_shared<NodeForNoStarvation>(
      NUM_AGNOCAST_SUB_CBS, NUM_ROS2_SUB_CBS, NUM_AGNOCAST_CBS_TO_BE_ADDED, PUB_PERIOD,
      cb_exec_time_, cbg_type);
    executor_->add_node(test_node_);
  }

  void TearDown() override { rclcpp::shutdown(); }

  std::chrono::milliseconds cb_exec_time_;
  std::chrono::seconds spin_duration_;
  std::shared_ptr<NodeForNoStarvation> test_node_;
  std::shared_ptr<agnocast::MultiThreadedAgnocastExecutor> executor_;

  // Fixed parameters
  const std::chrono::milliseconds PUB_PERIOD = std::chrono::milliseconds(100);
  const size_t NUMBER_OF_ROS2_THREADS = 2;
  const size_t NUMBER_OF_AGNOCAST_THREADS = 2;
  const uint64_t NUM_ROS2_SUB_CBS = NUMBER_OF_ROS2_THREADS * 2;
  const uint64_t NUM_AGNOCAST_SUB_CBS = NUMBER_OF_AGNOCAST_THREADS * 2;
  const uint64_t NUM_AGNOCAST_CBS_TO_BE_ADDED = NUMBER_OF_AGNOCAST_THREADS * 2;
};

INSTANTIATE_TEST_SUITE_P(
  MultiThreadedAgnocastExecutorNoStarvationTests, MultiThreadedAgnocastExecutorNoStarvationTest,
  ::testing::Combine(
    ::testing::Values(true, false),   // yield_before_execute
    ::testing::Values(25, 150, 400),  // ros2_next_exec_timeout and agnocast_next_exec_timeout_ms
    ::testing::Values("individual", "mutually_exclusive", "reentrant")));

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
