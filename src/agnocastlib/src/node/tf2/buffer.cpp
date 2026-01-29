#include "agnocast/node/tf2/buffer.hpp"

#include <sstream>
#include <string>
#include <thread>

namespace agnocast
{

static const char threading_error[] =
  "Do not call canTransform or lookupTransform with a timeout "
  "unless you are using another thread for populating data. Without a dedicated thread it will "
  "always timeout.  If you have a separate thread servicing tf messages, call "
  "setUsingDedicatedThread(true) on your Buffer instance.";

Buffer::Buffer(rclcpp::Clock::SharedPtr clock, tf2::Duration cache_time)
: BufferCore(cache_time), clock_(clock)
{
  if (nullptr == clock_) {
    throw std::invalid_argument("clock must be a valid instance");
  }

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

inline tf2::Duration from_rclcpp(const rclcpp::Duration & rclcpp_duration)
{
  return tf2::Duration(std::chrono::nanoseconds(rclcpp_duration.nanoseconds()));
}

inline rclcpp::Duration to_rclcpp(const tf2::Duration & duration)
{
  return rclcpp::Duration(std::chrono::nanoseconds(duration));
}

geometry_msgs::msg::TransformStamped Buffer::lookupTransform(
  const std::string & target_frame, const std::string & source_frame,
  const tf2::TimePoint & lookup_time, const tf2::Duration timeout) const
{
  // Pass error string to suppress console spam
  std::string error;
  canTransform(target_frame, source_frame, lookup_time, timeout, &error);
  return lookupTransform(target_frame, source_frame, lookup_time);
}

void Buffer::onTimeJump(const rcl_time_jump_t & jump)
{
  if (
    RCL_ROS_TIME_ACTIVATED == jump.clock_change || RCL_ROS_TIME_DEACTIVATED == jump.clock_change) {
    RCLCPP_WARN(getLogger(), "Detected time source change. Clearing TF buffer.");
    clear();
  } else if (jump.delta.nanoseconds < 0) {
    RCLCPP_WARN(getLogger(), "Detected jump back in time. Clearing TF buffer.");
    clear();
  }
}

geometry_msgs::msg::TransformStamped Buffer::lookupTransform(
  const std::string & target_frame, const tf2::TimePoint & target_time,
  const std::string & source_frame, const tf2::TimePoint & source_time,
  const std::string & fixed_frame, const tf2::Duration timeout) const
{
  // Pass error string to suppress console spam
  std::string error;
  canTransform(target_frame, target_time, source_frame, source_time, fixed_frame, timeout, &error);
  return lookupTransform(target_frame, target_time, source_frame, source_time, fixed_frame);
}

void conditionally_append_timeout_info(
  std::string * errstr, const rclcpp::Time & start_time, const rclcpp::Time & current_time,
  const rclcpp::Duration & timeout)
{
  if (errstr) {
    std::stringstream ss;
    ss << ". canTransform returned after "
       << tf2::durationToSec(from_rclcpp(current_time - start_time)) << " timeout was "
       << tf2::durationToSec(from_rclcpp(timeout)) << ".";
    (*errstr) += ss.str();
  }
}

bool Buffer::canTransform(
  const std::string & target_frame, const std::string & source_frame, const tf2::TimePoint & time,
  const tf2::Duration timeout, std::string * errstr) const
{
  if (!checkAndErrorDedicatedThreadPresent(errstr)) {
    return false;
  }

  rclcpp::Duration rclcpp_timeout(to_rclcpp(timeout));

  // poll for transform if timeout is set
  rclcpp::Time start_time = clock_->now();
  while (
    clock_->now() < start_time + rclcpp_timeout &&
    !canTransform(
      target_frame, source_frame, time, tf2::Duration(std::chrono::nanoseconds::zero()), errstr) &&
    (clock_->now() + rclcpp::Duration(3, 0) >= start_time) &&  // don't wait bag loop detected
    (rclcpp::ok()))  // Make sure we haven't been stopped (won't work for pytf)
  {
    // TODO(sloretz) sleep using clock_->sleep_for when implemented
    std::this_thread::sleep_for(std::chrono::milliseconds(10));
  }
  bool retval = canTransform(target_frame, source_frame, time, errstr);
  rclcpp::Time current_time = clock_->now();
  conditionally_append_timeout_info(errstr, start_time, current_time, rclcpp_timeout);
  return retval;
}

bool Buffer::canTransform(
  const std::string & target_frame, const tf2::TimePoint & target_time,
  const std::string & source_frame, const tf2::TimePoint & source_time,
  const std::string & fixed_frame, const tf2::Duration timeout, std::string * errstr) const
{
  if (!checkAndErrorDedicatedThreadPresent(errstr)) {
    return false;
  }

  rclcpp::Duration rclcpp_timeout(to_rclcpp(timeout));

  // poll for transform if timeout is set
  rclcpp::Time start_time = clock_->now();
  while (clock_->now() < start_time + rclcpp_timeout &&
         !canTransform(
           target_frame, target_time, source_frame, source_time, fixed_frame,
           tf2::Duration(std::chrono::nanoseconds::zero()), errstr) &&
         (clock_->now() + rclcpp::Duration(3, 0) >= start_time) &&  // don't wait bag loop detected
         (rclcpp::ok()))  // Make sure we haven't been stopped (won't work for pytf)
  {
    // TODO(sloretz) sleep using clock_->sleep_for when implemented
    std::this_thread::sleep_for(std::chrono::milliseconds(10));
  }
  bool retval =
    canTransform(target_frame, target_time, source_frame, source_time, fixed_frame, errstr);
  rclcpp::Time current_time = clock_->now();
  conditionally_append_timeout_info(errstr, start_time, current_time, rclcpp_timeout);
  return retval;
}

bool Buffer::checkAndErrorDedicatedThreadPresent(std::string * error_str) const
{
  if (isUsingDedicatedThread()) {
    return true;
  }

  if (error_str) {
    *error_str = threading_error;
  }

  RCLCPP_ERROR(getLogger(), "%s", threading_error);
  return false;
}

rclcpp::Logger Buffer::getLogger() const
{
  return rclcpp::get_logger("tf2_buffer");
}

}  // namespace agnocast
