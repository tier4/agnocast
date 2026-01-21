#ifndef AGNOCAST__NODE__TF2__BUFFER_HPP_
#define AGNOCAST__NODE__TF2__BUFFER_HPP_

#include "rcl/time.h"
#include "rclcpp/clock.hpp"
#include "rclcpp/duration.hpp"
#include "rclcpp/logging.hpp"
#include "rclcpp/time.hpp"
#include "tf2/buffer_core.h"
#include "tf2/time.h"
#include "tf2_ros/async_buffer_interface.h"
#include "tf2_ros/buffer_interface.h"
#include "tf2_ros/create_timer_interface.h"

#include "geometry_msgs/msg/transform_stamped.hpp"

#include <memory>
#include <mutex>
#include <string>
#include <unordered_map>

namespace agnocast
{

// Helper functions to convert between rclcpp and tf2 time types (same as tf2_ros)
inline tf2::TimePoint fromRclcpp(const rclcpp::Time & time)
{
  return tf2::TimePoint(std::chrono::nanoseconds(time.nanoseconds()));
}

inline tf2::Duration fromRclcpp(const rclcpp::Duration & duration)
{
  return tf2::Duration(std::chrono::nanoseconds(duration.nanoseconds()));
}

/// \brief A tf2 buffer implementation for Agnocast.
///
/// This class inherits from tf2::BufferCore for transform storage and computation,
/// tf2_ros::BufferInterface for synchronous operations, and
/// tf2_ros::AsyncBufferInterface for asynchronous operations.
///
/// This implementation is aligned with tf2_ros::Buffer.
class Buffer : public tf2::BufferCore,
               public tf2_ros::BufferInterface,
               public tf2_ros::AsyncBufferInterface
{
public:
  using tf2::BufferCore::canTransform;
  using tf2::BufferCore::lookupTransform;
  using SharedPtr = std::shared_ptr<Buffer>;

  /// \brief Constructor
  /// \param clock The clock to use for timing operations
  /// \param cache_time How long to keep transform history (default: 10 seconds)
  explicit Buffer(
    rclcpp::Clock::SharedPtr clock,
    tf2::Duration cache_time = tf2::Duration(tf2::BUFFER_CORE_DEFAULT_CACHE_TIME));

  virtual ~Buffer() = default;

  // ========== Synchronous lookupTransform ==========

  /// \brief Get the transform between two frames by frame ID.
  ///
  /// \param target_frame The frame to which data should be transformed
  /// \param source_frame The frame where the data originated
  /// \param time The time at which the value of the transform is desired (0 = latest)
  /// \param timeout How long to block before failing
  /// \return The transform between the frames
  /// \throws tf2::LookupException, tf2::ConnectivityException,
  ///         tf2::ExtrapolationException, tf2::InvalidArgumentException
  geometry_msgs::msg::TransformStamped lookupTransform(
    const std::string & target_frame, const std::string & source_frame, const tf2::TimePoint & time,
    const tf2::Duration timeout) const override;

  /// \brief Get the transform between two frames by frame ID (rclcpp overload).
  geometry_msgs::msg::TransformStamped lookupTransform(
    const std::string & target_frame, const std::string & source_frame, const rclcpp::Time & time,
    const rclcpp::Duration timeout = rclcpp::Duration::from_nanoseconds(0)) const
  {
    return lookupTransform(target_frame, source_frame, fromRclcpp(time), fromRclcpp(timeout));
  }

  /// \brief Get the transform between two frames by frame ID (advanced).
  geometry_msgs::msg::TransformStamped lookupTransform(
    const std::string & target_frame, const tf2::TimePoint & target_time,
    const std::string & source_frame, const tf2::TimePoint & source_time,
    const std::string & fixed_frame, const tf2::Duration timeout) const override;

  /// \brief Get the transform between two frames by frame ID (advanced, rclcpp overload).
  geometry_msgs::msg::TransformStamped lookupTransform(
    const std::string & target_frame, const rclcpp::Time & target_time,
    const std::string & source_frame, const rclcpp::Time & source_time,
    const std::string & fixed_frame,
    const rclcpp::Duration timeout = rclcpp::Duration::from_nanoseconds(0)) const
  {
    return lookupTransform(
      target_frame, fromRclcpp(target_time), source_frame, fromRclcpp(source_time), fixed_frame,
      fromRclcpp(timeout));
  }

  // ========== Synchronous canTransform ==========

  /// \brief Test if a transform is possible
  bool canTransform(
    const std::string & target_frame, const std::string & source_frame, const tf2::TimePoint & time,
    const tf2::Duration timeout, std::string * errstr = nullptr) const override;

  /// \brief Test if a transform is possible (rclcpp overload)
  bool canTransform(
    const std::string & target_frame, const std::string & source_frame, const rclcpp::Time & time,
    const rclcpp::Duration timeout = rclcpp::Duration::from_nanoseconds(0),
    std::string * errstr = nullptr) const
  {
    return canTransform(target_frame, source_frame, fromRclcpp(time), fromRclcpp(timeout), errstr);
  }

  /// \brief Test if a transform is possible (advanced)
  bool canTransform(
    const std::string & target_frame, const tf2::TimePoint & target_time,
    const std::string & source_frame, const tf2::TimePoint & source_time,
    const std::string & fixed_frame, const tf2::Duration timeout,
    std::string * errstr = nullptr) const override;

  /// \brief Test if a transform is possible (advanced, rclcpp overload)
  bool canTransform(
    const std::string & target_frame, const rclcpp::Time & target_time,
    const std::string & source_frame, const rclcpp::Time & source_time,
    const std::string & fixed_frame,
    const rclcpp::Duration timeout = rclcpp::Duration::from_nanoseconds(0),
    std::string * errstr = nullptr) const
  {
    return canTransform(
      target_frame, fromRclcpp(target_time), source_frame, fromRclcpp(source_time), fixed_frame,
      fromRclcpp(timeout), errstr);
  }

  // ========== Asynchronous waitForTransform ==========

  /// \brief Wait for a transform between two frames to become available.
  ///
  /// Before this method can be called, a tf2_ros::CreateTimerInterface must be registered
  /// by first calling setCreateTimerInterface.
  ///
  /// \param target_frame The frame into which to transform.
  /// \param source_frame The frame from which to transform.
  /// \param time The time at which to transform.
  /// \param timeout Duration after which waiting will be stopped.
  /// \param callback The function to be called when the transform becomes available or a timeout
  ///   occurs. In the case of timeout, an exception will be set on the future.
  /// \return A future to the requested transform.
  tf2_ros::TransformStampedFuture waitForTransform(
    const std::string & target_frame, const std::string & source_frame, const tf2::TimePoint & time,
    const tf2::Duration & timeout, tf2_ros::TransformReadyCallback callback) override;

  /// \brief Wait for a transform between two frames to become available (rclcpp overload).
  tf2_ros::TransformStampedFuture waitForTransform(
    const std::string & target_frame, const std::string & source_frame, const rclcpp::Time & time,
    const rclcpp::Duration & timeout, tf2_ros::TransformReadyCallback callback)
  {
    return waitForTransform(
      target_frame, source_frame, fromRclcpp(time), fromRclcpp(timeout), callback);
  }

  /// \brief Cancel the future to make sure the callback of requested transform is clean.
  /// \param ts_future The future to the requested transform.
  void cancel(const tf2_ros::TransformStampedFuture & ts_future) override;

  // ========== Configuration ==========

  /// \brief Get the clock used by this buffer
  rclcpp::Clock::SharedPtr getClock() const { return clock_; }

  /// \brief Set whether a dedicated thread is being used for TF updates.
  ///
  /// This is required before using canTransform or lookupTransform with a non-zero timeout.
  ///
  /// \param value True if a dedicated thread is servicing TF messages
  void setUsingDedicatedThread(bool value) { using_dedicated_thread_ = value; }

  /// \brief Check if a dedicated thread is being used for TF updates.
  bool isUsingDedicatedThread() const { return using_dedicated_thread_; }

  /// \brief Set the CreateTimerInterface for async operations.
  ///
  /// This must be called before using waitForTransform.
  ///
  /// \param create_timer_interface The timer interface for creating timers
  void setCreateTimerInterface(tf2_ros::CreateTimerInterface::SharedPtr create_timer_interface)
  {
    timer_interface_ = create_timer_interface;
  }

private:
  rclcpp::Clock::SharedPtr clock_;

  /// \brief Whether a dedicated thread is servicing TF messages
  bool using_dedicated_thread_ = false;

  /// \brief Reference to a jump handler registered to the clock
  rclcpp::JumpHandler::SharedPtr jump_handler_;

  /// \brief Interface for creating timers (for async operations)
  tf2_ros::CreateTimerInterface::SharedPtr timer_interface_;

  /// \brief Callback for time jumps (clears buffer on backward jumps or clock changes)
  void onTimeJump(const rcl_time_jump_t & jump);

  /// \brief Check if dedicated thread is present, log error if not
  bool checkAndErrorDedicatedThreadPresent(std::string * errstr) const;

  /// \brief A map from active timers to BufferCore request handles
  mutable std::unordered_map<tf2_ros::TimerHandle, tf2::TransformableRequestHandle>
    timer_to_request_map_;

  /// \brief A mutex on the timer_to_request_map_ data
  mutable std::mutex timer_to_request_map_mutex_;

  /// \brief Timer callback for async waitForTransform timeout
  void timerCallback(
    const tf2_ros::TimerHandle & timer_handle,
    std::shared_ptr<std::promise<geometry_msgs::msg::TransformStamped>> promise,
    tf2_ros::TransformStampedFuture future, tf2_ros::TransformReadyCallback callback);

  /// \brief Wait for transform to become available (polling-based, for sync operations)
  /// \return true if transform became available, false on timeout
  bool waitForTransformAvailable(
    const std::string & target_frame, const std::string & source_frame, const tf2::TimePoint & time,
    const tf2::Duration & timeout, std::string * errstr = nullptr) const;
};

}  // namespace agnocast

#endif  // AGNOCAST__NODE__TF2__BUFFER_HPP_
