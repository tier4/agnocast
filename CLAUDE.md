# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Agnocast is an rclcpp-compatible true zero-copy IPC middleware for ROS 2 that supports all ROS message types. It uses shared memory managed by a Linux kernel module for inter-process communication.

## Architecture

The system consists of three main components:

1. **agnocast_kmod** (Kernel Module): Linux kernel module that manages shared memory regions, message queues, and IPC coordination. Provides ioctl interface for user-space communication.

2. **agnocast_heaphook** (Rust): Custom heap allocator that intercepts malloc/free calls and redirects allocations during publish/borrow windows to shared memory. Must be LD_PRELOAD'd.

3. **agnocastlib** (C++ Library): User-facing API providing `agnocast::Publisher`, `agnocast::Subscription`, `agnocast::Node`, and custom executors compatible with rclcpp.

**Data flow**: User applications use agnocastlib API, which makes ioctl calls to the kernel module. The kernel module manages shared memory (`/agnocast@<pid>`) and message queues (`/agnocast@<topic>@<id>`) for zero-copy communication.

## Build Commands

```bash
# Full build (all components)
bash scripts/build_all

# Build ROS packages only (for development)
colcon build --symlink-install --cmake-args -DCMAKE_BUILD_TYPE=Release

# Build kernel module only
cd agnocast_kmod && make

# Build heaphook only
cd agnocast_heaphook && cargo build --release
```

## Testing

```bash
# Full test suite with coverage report
bash scripts/test_and_create_report

# Run colcon tests only
colcon test --event-handlers console_direct+

# Run a specific test package
colcon test --packages-select agnocastlib --event-handlers console_direct+

# E2E tests (64 combinations of QoS and subscription modes)
bash scripts/e2e_test_1to1_with_ros2sub

# Single E2E test scenario
bash scripts/e2e_test_1to1_with_ros2sub -s

# KUnit tests (requires custom kernel with CONFIG_KUNIT=y)
bash scripts/run_kunit
```

## Running Sample Applications

```bash
# Insert kernel module
sudo modprobe agnocast  # or: cd agnocast_kmod && sudo insmod agnocast.ko

# Run in separate terminals
bash scripts/run_listener
bash scripts/run_talker

# Remove kernel module when done
sudo modprobe -r agnocast
```

## Key API Patterns

```cpp
// Publisher with loaned message (zero-copy)
auto msg = publisher_->borrow_loaned_message();
msg->field = value;
publisher_->publish(std::move(msg));

// Subscription callback receives ipc_shared_ptr
auto callback = [](const agnocast::ipc_shared_ptr<MsgType>& msg) { ... };

// Custom executors for agnocast subscriptions
agnocast::SingleThreadedExecutor executor;
agnocast::MultiThreadedExecutor executor;
agnocast::CallbackIsolatedExecutor executor;
```

## Directory Structure

- `src/agnocastlib/` - Main C++ library with Publisher, Subscription, Node, Executors
- `src/agnocast_e2e_test/` - End-to-end test scenarios
- `src/agnocast_sample_application/` - Example publisher/subscriber
- `agnocast_kmod/` - Linux kernel module source
- `agnocast_heaphook/` - Rust heap allocator
- `scripts/` - Build, test, and run scripts

## System Requirements

Before running, set the message queue limit:

```bash
sudo sysctl -w fs.mqueue.msg_max=256  # temporary
# or add to /etc/sysctl.conf for permanent
```

## Debugging

```bash
# Watch kernel logs
sudo dmesg -w

# Enable debug logging
sudo su
echo 'file agnocast_main.c +p' > /sys/kernel/debug/dynamic_debug/control
```

## Resource Cleanup

If shared memory or message queues leak:

```bash
rm /dev/shm/agnocast@*
rm /dev/mqueue/agnocast@*
rm /dev/mqueue/agnocast_bridge_manager_*
```

## Pre-commit Setup

```bash
pip install pre-commit
pre-commit install
```

Runs clang-format, markdownlint, and KUnit tests on commit.
