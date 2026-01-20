#pragma once

#include "rclcpp/callback_group.hpp"

#include <atomic>
#include <functional>
#include <memory>

namespace agnocast
{

/// Executable unit for Agnocast event handling.
/// Wraps a callable with its associated callback group.
struct AgnocastExecutable
{
  std::shared_ptr<std::function<void()>> callable;
  rclcpp::CallbackGroup::SharedPtr callback_group{nullptr};
};

/// Global flag indicating whether any event source needs epoll registration update.
/// Set to true when a new subscription or timer is registered.
/// Checked by executors to trigger prepare_epoll_impl().
extern std::atomic<bool> need_epoll_updates;

}  // namespace agnocast
