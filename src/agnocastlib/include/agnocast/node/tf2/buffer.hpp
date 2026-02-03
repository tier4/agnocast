#ifndef AGNOCAST__NODE__TF2__BUFFER_HPP_
#define AGNOCAST__NODE__TF2__BUFFER_HPP_

#include "rcl/time.h"
#include "rclcpp/clock.hpp"
#include "rclcpp/duration.hpp"
#include "rclcpp/logging.hpp"
#include "rclcpp/time.hpp"
#include "tf2/buffer_core.h"
#include "tf2/time.h"
#include "tf2_ros/buffer_interface.h"

#include "geometry_msgs/msg/transform_stamped.hpp"

#include <memory>
#include <string>

namespace agnocast
{

/// This class inherits from tf2::BufferCore for transform storage and computation,
/// and tf2_ros::BufferInterface for synchronous operations.
class Buffer : public tf2::BufferCore, public tf2_ros::BufferInterface
{
public:
  using tf2::BufferCore::canTransform;
  using tf2::BufferCore::lookupTransform;
  using SharedPtr = std::shared_ptr<Buffer>;

  /// \brief Constructor for a Buffer object
  /// \param clock A clock to use for time and sleeping
  /// \param cache_time How long to keep a history of transforms
  explicit Buffer(
    rclcpp::Clock::SharedPtr clock,
    tf2::Duration cache_time = tf2::Duration(tf2::BUFFER_CORE_DEFAULT_CACHE_TIME));

  virtual ~Buffer() = default;

  /// \brief Get the transform between two frames by frame ID.
  /// \param target_frame The frame to which data should be transformed
  /// \param source_frame The frame where the data originated
  /// \param time The time at which the value of the transform is desired. (0 will get the latest)
  /// \param timeout How long to block before failing
  /// \return The transform between the frames
  ///
  /// Possible exceptions tf2::LookupException, tf2::ConnectivityException,
  /// tf2::ExtrapolationException, tf2::InvalidArgumentException
  geometry_msgs::msg::TransformStamped lookupTransform(
    const std::string & target_frame, const std::string & source_frame, const tf2::TimePoint & time,
    const tf2::Duration timeout) const override;

  /// \brief Get the transform between two frames by frame ID.
  /// \sa lookupTransform(const std::string&, const std::string&, const tf2::TimePoint&,
  ///                     const tf2::Duration)
  geometry_msgs::msg::TransformStamped lookupTransform(
    const std::string & target_frame, const std::string & source_frame, const rclcpp::Time & time,
    const rclcpp::Duration timeout = rclcpp::Duration::from_nanoseconds(0)) const
  {
    return lookupTransform(
      target_frame, source_frame, tf2_ros::fromRclcpp(time), tf2_ros::fromRclcpp(timeout));
  }

  /// \brief Get the transform between two frames by frame ID assuming fixed frame.
  /// \param target_frame The frame to which data should be transformed
  /// \param target_time The time to which the data should be transformed. (0 will get the latest)
  /// \param source_frame The frame where the data originated
  /// \param source_time The time at which the source_frame should be evaluated. (0 will get the
  /// latest)
  /// \param fixed_frame The frame in which to assume the transform is constant in time.
  /// \param timeout How long to block before failing
  /// \return The transform between the frames
  ///
  /// Possible exceptions tf2::LookupException, tf2::ConnectivityException,
  /// tf2::ExtrapolationException, tf2::InvalidArgumentException
  geometry_msgs::msg::TransformStamped lookupTransform(
    const std::string & target_frame, const tf2::TimePoint & target_time,
    const std::string & source_frame, const tf2::TimePoint & source_time,
    const std::string & fixed_frame, const tf2::Duration timeout) const override;

  /// \brief Get the transform between two frames by frame ID assuming fixed frame.
  /// \sa lookupTransform(const std::string&, const tf2::TimePoint&,
  ///                     const std::string&, const tf2::TimePoint&,
  ///                     const std::string&, const tf2::Duration)
  geometry_msgs::msg::TransformStamped lookupTransform(
    const std::string & target_frame, const rclcpp::Time & target_time,
    const std::string & source_frame, const rclcpp::Time & source_time,
    const std::string & fixed_frame,
    const rclcpp::Duration timeout = rclcpp::Duration::from_nanoseconds(0)) const
  {
    return lookupTransform(
      target_frame, tf2_ros::fromRclcpp(target_time), source_frame,
      tf2_ros::fromRclcpp(source_time), fixed_frame, tf2_ros::fromRclcpp(timeout));
  }

  /// \brief Test if a transform is possible
  /// \param target_frame The frame into which to transform
  /// \param source_frame The frame from which to transform
  /// \param target_time The time at which to transform
  /// \param timeout How long to block before failing
  /// \param errstr A pointer to a string which will be filled with why the transform failed, if not
  /// NULL
  /// \return True if the transform is possible, false otherwise
  bool canTransform(
    const std::string & target_frame, const std::string & source_frame, const tf2::TimePoint & time,
    const tf2::Duration timeout, std::string * errstr = NULL) const override;

  /// \brief Test if a transform is possible
  /// \sa canTransform(const std::string&, const std::string&,
  ///                  const tf2::TimePoint&, const tf2::Duration, std::string*)
  bool canTransform(
    const std::string & target_frame, const std::string & source_frame, const rclcpp::Time & time,
    const rclcpp::Duration timeout = rclcpp::Duration::from_nanoseconds(0),
    std::string * errstr = NULL) const
  {
    return canTransform(
      target_frame, source_frame, tf2_ros::fromRclcpp(time), tf2_ros::fromRclcpp(timeout), errstr);
  }

  /// \brief Test if a transform is possible
  /// \param target_frame The frame into which to transform
  /// \param target_time The time into which to transform
  /// \param source_frame The frame from which to transform
  /// \param source_time The time from which to transform
  /// \param fixed_frame The frame in which to treat the transform as constant in time
  /// \param timeout How long to block before failing
  /// \param errstr A pointer to a string which will be filled with why the transform failed, if not
  /// NULL
  /// \return True if the transform is possible, false otherwise
  bool canTransform(
    const std::string & target_frame, const tf2::TimePoint & target_time,
    const std::string & source_frame, const tf2::TimePoint & source_time,
    const std::string & fixed_frame, const tf2::Duration timeout,
    std::string * errstr = NULL) const override;

  /// \brief Test if a transform is possible
  /// \sa canTransform(const std::string&, const tf2::TimePoint&,
  ///                  const std::string&, const tf2::TimePoint&,
  ///                  const std::string&, const tf2::Duration, std::string*)
  bool canTransform(
    const std::string & target_frame, const rclcpp::Time & target_time,
    const std::string & source_frame, const rclcpp::Time & source_time,
    const std::string & fixed_frame,
    const rclcpp::Duration timeout = rclcpp::Duration::from_nanoseconds(0),
    std::string * errstr = NULL) const
  {
    return canTransform(
      target_frame, tf2_ros::fromRclcpp(target_time), source_frame,
      tf2_ros::fromRclcpp(source_time), fixed_frame, tf2_ros::fromRclcpp(timeout), errstr);
  }

  /// \brief Get the clock used by this buffer
  rclcpp::Clock::SharedPtr getClock() const { return clock_; }

private:
  /// \brief A clock to use for time and sleeping
  rclcpp::Clock::SharedPtr clock_;

  /// \brief Reference to a jump handler registered to the clock
  rclcpp::JumpHandler::SharedPtr jump_handler_;

  void onTimeJump(const rcl_time_jump_t & jump);

  // conditionally error if dedicated_thread unset.
  bool checkAndErrorDedicatedThreadPresent(std::string * errstr) const;

  /// Get the logger to use for calls to RCLCPP log macros.
  rclcpp::Logger getLogger() const;
};

static const char threading_error[] =
  "Do not call canTransform or lookupTransform with a timeout "
  "unless you are using another thread for populating data. Without a dedicated thread it will "
  "always timeout.  If you have a separate thread servicing tf messages, call "
  "setUsingDedicatedThread(true) on your Buffer instance.";

}  // namespace agnocast

#endif  // AGNOCAST__NODE__TF2__BUFFER_HPP_
