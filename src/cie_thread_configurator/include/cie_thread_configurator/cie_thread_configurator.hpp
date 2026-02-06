#pragma once

#include "agnocast/agnocast.hpp"
#include "rclcpp/rclcpp.hpp"

#include "cie_config_msgs/msg/non_ros_thread_info.hpp"

#include <sys/syscall.h>
#include <unistd.h>

#include <map>
#include <string>
#include <thread>
#include <tuple>
#include <vector>

namespace cie_thread_configurator
{

// Get hardware information from lscpu command
std::map<std::string, std::string> get_hardware_info();

// Get default domain ID from ROS_DOMAIN_ID environment variable
size_t get_default_domain_id();

// Create a node for a different domain
rclcpp::Node::SharedPtr create_node_for_domain(size_t domain_id);

/// Spawn a thread whose scheduling policy can be managed through
/// cie_thread_configurator.
/// Caution: the `thread_name` must be unique among threads managed by
/// cie_thread_configurator.
template <class F, class... Args>
std::thread spawn_non_ros2_thread(const char * thread_name, F && f, Args &&... args)
{
  std::thread t([thread_name = std::string(thread_name), func = std::forward<F>(f),
                 captured_args = std::make_tuple(std::forward<Args>(args)...)]() mutable {
    // Create isolated rclcpp context for creating agnocast publisher
    rclcpp::InitOptions init_options;
    init_options.shutdown_on_signal = false;
    init_options.auto_initialize_logging(false);
    auto context = std::make_shared<rclcpp::Context>();
    context->init(0, nullptr, init_options);

    rclcpp::NodeOptions options;
    options.context(context);
    auto node =
      std::make_shared<rclcpp::Node>("cie_thread_client", "/cie_thread_configurator", options);

    auto publisher = agnocast::create_publisher<cie_config_msgs::msg::NonRosThreadInfo>(
      node.get(), "/cie_thread_configurator/non_ros_thread_info", rclcpp::QoS(1000));
    auto tid = static_cast<pid_t>(syscall(SYS_gettid));

    auto message = publisher->borrow_loaned_message();
    message->thread_id = tid;
    message->thread_name = thread_name;
    publisher->publish(std::move(message));

    context->shutdown("cie_thread_client finished.");

    std::apply(std::move(func), std::move(captured_args));
  });
  return t;
}

}  // namespace cie_thread_configurator
