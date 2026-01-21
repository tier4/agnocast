#include "agnocast/node/tf2/buffer.hpp"

#include "tf2/exceptions.h"
#include "tf2_ros/buffer_interface.h"

#include <chrono>
#include <functional>
#include <limits>
#include <thread>

namespace agnocast
{

namespace
{
constexpr char threading_error[] =
  "Do not call canTransform or lookupTransform with a timeout "
  "unless you are using another thread for populating data. Without a dedicated thread it will "
  "always timeout. If you have a separate thread servicing tf messages, call "
  "setUsingDedicatedThread(true) on your Buffer instance.";
}  // namespace

Buffer::Buffer(rclcpp::Clock::SharedPtr clock, tf2::Duration cache_time)
: tf2::BufferCore(cache_time), clock_(clock), timer_interface_(nullptr)
{
  if (nullptr == clock_) {
    throw std::invalid_argument("clock must be a valid instance");
  }

  // Set up time jump callback
  auto post_jump_cb = [this](const rcl_time_jump_t & jump_info) { onTimeJump(jump_info); };

  rcl_jump_threshold_t jump_threshold;
  // Disable forward jump callbacks
  jump_threshold.min_forward.nanoseconds = 0;
  // Anything backwards is a jump
  jump_threshold.min_backward.nanoseconds = -1;
  // Callback if the clock changes too
  jump_threshold.on_clock_change = true;

  jump_handler_ = clock_->create_jump_callback(nullptr, post_jump_cb, jump_threshold);
}

void Buffer::onTimeJump(const rcl_time_jump_t & jump)
{
  if (
    RCL_ROS_TIME_ACTIVATED == jump.clock_change || RCL_ROS_TIME_DEACTIVATED == jump.clock_change) {
    RCLCPP_WARN(
      rclcpp::get_logger("agnocast_tf2_buffer"),
      "Detected time source change. Clearing TF buffer.");
    clear();
  } else if (jump.delta.nanoseconds < 0) {
    RCLCPP_WARN(
      rclcpp::get_logger("agnocast_tf2_buffer"), "Detected jump back in time. Clearing TF buffer.");
    clear();
  }
}

bool Buffer::checkAndErrorDedicatedThreadPresent(std::string * error_str) const
{
  if (isUsingDedicatedThread()) {
    return true;
  }

  if (error_str) {
    *error_str = threading_error;
  }

  RCLCPP_ERROR(rclcpp::get_logger("agnocast_tf2_buffer"), "%s", threading_error);
  return false;
}

bool Buffer::waitForTransformAvailable(
  const std::string & target_frame, const std::string & source_frame, const tf2::TimePoint & time,
  const tf2::Duration & timeout, std::string * errstr) const
{
  // If timeout is zero, don't wait
  if (timeout <= tf2::Duration::zero()) {
    return BufferCore::canTransform(target_frame, source_frame, time, errstr);
  }

  const auto start_time = clock_->now();
  const auto timeout_duration = std::chrono::duration_cast<std::chrono::nanoseconds>(timeout);
  const auto end_time = start_time + rclcpp::Duration(timeout_duration);

  // Polling interval (10ms, same as tf2_ros::Buffer)
  const auto poll_interval = std::chrono::milliseconds(10);

  while (clock_->now() < end_time &&
         !BufferCore::canTransform(target_frame, source_frame, time, errstr) &&
         (clock_->now() + rclcpp::Duration(3, 0) >= start_time) &&  // don't wait if bag loop
         rclcpp::ok()) {
    std::this_thread::sleep_for(poll_interval);
  }

  // Final check after timeout
  return BufferCore::canTransform(target_frame, source_frame, time, errstr);
}

geometry_msgs::msg::TransformStamped Buffer::lookupTransform(
  const std::string & target_frame, const std::string & source_frame, const tf2::TimePoint & time,
  const tf2::Duration timeout) const
{
  // Pass error string to suppress console spam
  std::string error;
  canTransform(target_frame, source_frame, time, timeout, &error);
  return BufferCore::lookupTransform(target_frame, source_frame, time);
}

geometry_msgs::msg::TransformStamped Buffer::lookupTransform(
  const std::string & target_frame, const tf2::TimePoint & target_time,
  const std::string & source_frame, const tf2::TimePoint & source_time,
  const std::string & fixed_frame, const tf2::Duration timeout) const
{
  // Pass error string to suppress console spam
  std::string error;
  canTransform(target_frame, target_time, source_frame, source_time, fixed_frame, timeout, &error);
  return BufferCore::lookupTransform(
    target_frame, target_time, source_frame, source_time, fixed_frame);
}

bool Buffer::canTransform(
  const std::string & target_frame, const std::string & source_frame, const tf2::TimePoint & time,
  const tf2::Duration timeout, std::string * errstr) const
{
  // Check dedicated thread if timeout is non-zero
  if (timeout > tf2::Duration::zero() && !checkAndErrorDedicatedThreadPresent(errstr)) {
    return false;
  }
  return waitForTransformAvailable(target_frame, source_frame, time, timeout, errstr);
}

bool Buffer::canTransform(
  const std::string & target_frame, const tf2::TimePoint & target_time,
  const std::string & source_frame, const tf2::TimePoint & source_time,
  const std::string & fixed_frame, const tf2::Duration timeout, std::string * errstr) const
{
  // Check dedicated thread if timeout is non-zero
  if (timeout > tf2::Duration::zero() && !checkAndErrorDedicatedThreadPresent(errstr)) {
    return false;
  }
  // Check if both transforms are available
  if (!waitForTransformAvailable(target_frame, fixed_frame, target_time, timeout, errstr)) {
    return false;
  }
  if (!waitForTransformAvailable(fixed_frame, source_frame, source_time, timeout, errstr)) {
    return false;
  }
  return true;
}

tf2_ros::TransformStampedFuture Buffer::waitForTransform(
  const std::string & target_frame, const std::string & source_frame, const tf2::TimePoint & time,
  const tf2::Duration & timeout, tf2_ros::TransformReadyCallback callback)
{
  if (nullptr == timer_interface_) {
    throw tf2_ros::CreateTimerInterfaceException(
      "timer interface not set before call to waitForTransform");
  }

  auto promise = std::make_shared<std::promise<geometry_msgs::msg::TransformStamped>>();
  tf2_ros::TransformStampedFuture future(promise->get_future());

  auto cb = [this, promise, callback, future](
              tf2::TransformableRequestHandle request_handle, const std::string & target_frame,
              const std::string & source_frame, tf2::TimePoint time,
              tf2::TransformableResult result) {
    (void)request_handle;

    bool timeout_occurred = true;
    {
      std::lock_guard<std::mutex> lock(this->timer_to_request_map_mutex_);
      // Check if a timeout already occurred
      for (auto it = timer_to_request_map_.begin(); it != timer_to_request_map_.end(); ++it) {
        if (request_handle == it->second) {
          // The request handle was found, so a timeout has not occurred
          this->timer_interface_->remove(it->first);
          this->timer_to_request_map_.erase(it->first);
          timeout_occurred = false;
          break;
        }
      }
    }

    if (timeout_occurred) {
      return;
    }

    if (result == tf2::TransformAvailable) {
      geometry_msgs::msg::TransformStamped msg_stamped =
        this->lookupTransform(target_frame, source_frame, time);
      promise->set_value(msg_stamped);
    } else {
      promise->set_exception(std::make_exception_ptr(
        tf2::LookupException("Failed to transform from " + source_frame + " to " + target_frame)));
    }
    callback(future);
  };

  auto handle = addTransformableRequest(cb, target_frame, source_frame, time);
  future.setHandle(handle);

  if (0 == handle) {
    // Immediately transformable
    geometry_msgs::msg::TransformStamped msg_stamped =
      lookupTransform(target_frame, source_frame, time);
    promise->set_value(msg_stamped);
    callback(future);
  } else if (0xffffffffffffffffULL == handle) {
    // Never transformable
    promise->set_exception(std::make_exception_ptr(
      tf2::LookupException("Failed to transform from " + source_frame + " to " + target_frame)));
    callback(future);
  } else {
    std::lock_guard<std::mutex> lock(timer_to_request_map_mutex_);
    auto timer_handle = timer_interface_->createTimer(
      clock_, timeout,
      std::bind(&Buffer::timerCallback, this, std::placeholders::_1, promise, future, callback));

    // Save association between timer and request handle
    timer_to_request_map_[timer_handle] = handle;
  }
  return future;
}

void Buffer::cancel(const tf2_ros::TransformStampedFuture & ts_future)
{
  cancelTransformableRequest(ts_future.getHandle());

  std::lock_guard<std::mutex> lock(timer_to_request_map_mutex_);
  auto iter = timer_to_request_map_.find(ts_future.getHandle());
  if (iter != timer_to_request_map_.end()) {
    timer_to_request_map_.erase(iter);
  }
}

void Buffer::timerCallback(
  const tf2_ros::TimerHandle & timer_handle,
  std::shared_ptr<std::promise<geometry_msgs::msg::TransformStamped>> promise,
  tf2_ros::TransformStampedFuture future, tf2_ros::TransformReadyCallback callback)
{
  bool timer_is_valid = false;
  tf2::TransformableRequestHandle request_handle = 0u;
  {
    std::lock_guard<std::mutex> lock(timer_to_request_map_mutex_);
    auto timer_and_request_it = timer_to_request_map_.find(timer_handle);
    timer_is_valid = (timer_to_request_map_.end() != timer_and_request_it);
    if (timer_is_valid) {
      request_handle = timer_and_request_it->second;
      timer_to_request_map_.erase(timer_handle);
      timer_interface_->remove(timer_handle);
    }
  }

  if (timer_is_valid) {
    cancelTransformableRequest(request_handle);
    promise->set_exception(
      std::make_exception_ptr(tf2::TimeoutException("Timed out waiting for transform")));
    callback(future);
  }
}

}  // namespace agnocast
