// Test program for agnocast tf2 support without rclcpp

#include "agnocast/agnocast.hpp"
#include "agnocast/node/tf2/tf2.hpp"

#include <chrono>
#include <iostream>
#include <thread>

using namespace std::chrono_literals;

class Tf2TestNode : public agnocast::Node
{
public:
  Tf2TestNode() : Node("tf2_test_node")
  {
    RCLCPP_INFO(get_logger(), "Tf2TestNode started.");

    // Create Buffer and TransformListener
    buffer_ = std::make_shared<agnocast::Buffer>(get_clock());
    listener_ = std::make_shared<agnocast::TransformListener>(*buffer_, *this);

    // Create TransformBroadcaster
    broadcaster_ = std::make_shared<agnocast::TransformBroadcaster>(*this);

    // Create StaticTransformBroadcaster for testing static transforms
    static_broadcaster_ = std::make_shared<agnocast::StaticTransformBroadcaster>(*this);

    // Publish a static transform: world -> base_link
    publish_static_transform();

    // Create a timer to periodically publish dynamic transforms and test lookups
    timer_ = create_wall_timer(100ms, [this]() { timer_callback(); });
  }

private:
  void publish_static_transform()
  {
    geometry_msgs::msg::TransformStamped static_tf;
    static_tf.header.stamp = now();
    static_tf.header.frame_id = "world";
    static_tf.child_frame_id = "base_link";
    static_tf.transform.translation.x = 1.0;
    static_tf.transform.translation.y = 0.0;
    static_tf.transform.translation.z = 0.0;
    static_tf.transform.rotation.x = 0.0;
    static_tf.transform.rotation.y = 0.0;
    static_tf.transform.rotation.z = 0.0;
    static_tf.transform.rotation.w = 1.0;

    static_broadcaster_->sendTransform(static_tf);
    RCLCPP_INFO(get_logger(), "Published static transform: world -> base_link");
  }

  void timer_callback()
  {
    // Publish dynamic transform: base_link -> sensor
    geometry_msgs::msg::TransformStamped dynamic_tf;
    dynamic_tf.header.stamp = now();
    dynamic_tf.header.frame_id = "base_link";
    dynamic_tf.child_frame_id = "sensor";
    dynamic_tf.transform.translation.x = 0.5;
    dynamic_tf.transform.translation.y = 0.0;
    dynamic_tf.transform.translation.z = 0.5;
    dynamic_tf.transform.rotation.x = 0.0;
    dynamic_tf.transform.rotation.y = 0.0;
    dynamic_tf.transform.rotation.z = 0.0;
    dynamic_tf.transform.rotation.w = 1.0;

    broadcaster_->sendTransform(dynamic_tf);

    callback_count_++;

    // Try to lookup transforms after a few callbacks (to allow time for subscription)
    if (callback_count_ > 5) {
      test_lookups();
    }
  }

  void test_lookups()
  {
    // Test 1: world -> base_link (static)
    try {
      auto tf = buffer_->lookupTransform(
        "world", "base_link", tf2::TimePointZero, tf2::durationFromSec(0.0));
      RCLCPP_INFO(
        get_logger(), "[OK] world -> base_link: translation=(%.2f, %.2f, %.2f)",
        tf.transform.translation.x, tf.transform.translation.y, tf.transform.translation.z);
    } catch (const tf2::TransformException & ex) {
      RCLCPP_WARN(get_logger(), "[FAIL] world -> base_link: %s", ex.what());
    }

    // Test 2: base_link -> sensor (dynamic)
    try {
      auto tf = buffer_->lookupTransform(
        "base_link", "sensor", tf2::TimePointZero, tf2::durationFromSec(0.0));
      RCLCPP_INFO(
        get_logger(), "[OK] base_link -> sensor: translation=(%.2f, %.2f, %.2f)",
        tf.transform.translation.x, tf.transform.translation.y, tf.transform.translation.z);
    } catch (const tf2::TransformException & ex) {
      RCLCPP_WARN(get_logger(), "[FAIL] base_link -> sensor: %s", ex.what());
    }

    // Test 3: world -> sensor (chained)
    try {
      auto tf = buffer_->lookupTransform(
        "world", "sensor", tf2::TimePointZero, tf2::durationFromSec(0.0));
      RCLCPP_INFO(
        get_logger(), "[OK] world -> sensor: translation=(%.2f, %.2f, %.2f)",
        tf.transform.translation.x, tf.transform.translation.y, tf.transform.translation.z);
    } catch (const tf2::TransformException & ex) {
      RCLCPP_WARN(get_logger(), "[FAIL] world -> sensor: %s", ex.what());
    }

    // Test 4: canTransform
    std::string error_string;
    bool can_transform =
      buffer_->canTransform("world", "sensor", tf2::TimePointZero, tf2::durationFromSec(0.0), &error_string);
    if (can_transform) {
      RCLCPP_INFO(get_logger(), "[OK] canTransform(world, sensor) = true");
    } else {
      RCLCPP_WARN(get_logger(), "[FAIL] canTransform(world, sensor) = false: %s", error_string.c_str());
    }

    // Only print once
    if (callback_count_ == 6) {
      RCLCPP_INFO(get_logger(), "--- TF2 test complete ---");
    }
  }

  agnocast::Buffer::SharedPtr buffer_;
  std::shared_ptr<agnocast::TransformListener> listener_;
  std::shared_ptr<agnocast::TransformBroadcaster> broadcaster_;
  std::shared_ptr<agnocast::StaticTransformBroadcaster> static_broadcaster_;
  agnocast::TimerBase::SharedPtr timer_;
  int callback_count_ = 0;
};

int main(int argc, char ** argv)
{
  agnocast::init(argc, argv);
  agnocast::AgnocastOnlySingleThreadedExecutor executor;
  auto node = std::make_shared<Tf2TestNode>();
  executor.add_node(node);
  executor.spin();
  return 0;
}
