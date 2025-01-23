#pragma once

#include "agnocast_ioctl.hpp"
#include "agnocast_utils.hpp"

#include <fcntl.h>
#include <mqueue.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>

// These are cut out of the class for information hiding.
void decrement_rc(
  const std::string & topic_name, const uint32_t publisher_index, const uint32_t subscriber_index,
  const uint64_t timestamp);
void increment_rc_core(
  const std::string & topic_name, const uint32_t publisher_index, const uint32_t subscriber_index,
  const uint64_t timestamp);

namespace agnocast
{

extern int agnocast_fd;

template <typename T>
class ipc_shared_ptr
{
  T * ptr_ = nullptr;
  std::string topic_name_;
  uint32_t publisher_index_;
  uint32_t subscriber_index_;
  uint64_t timestamp_;
  bool is_created_by_sub_;

  void increment_rc() const
  {
    if (!is_created_by_sub_) return;

    increment_rc_core(topic_name_, publisher_index_, subscriber_index_, timestamp_);
  }

  // Unimplemented operators. If these are called, a compile error is raised.
  ipc_shared_ptr & operator=(const ipc_shared_ptr & r) = delete;
  bool operator==(const ipc_shared_ptr & r) const = delete;
  bool operator!=(const ipc_shared_ptr & r) const = delete;

public:
  using element_type = T;

  const std::string get_topic_name() const { return topic_name_; }
  uint64_t get_timestamp() const { return timestamp_; }

  ipc_shared_ptr() = default;

  explicit ipc_shared_ptr(
    T * ptr, const std::string & topic_name, const uint32_t publisher_index,
    const uint64_t timestamp)
  : ptr_(ptr),
    topic_name_(topic_name),
    publisher_index_(publisher_index),
    subscriber_index_(-1),
    timestamp_(timestamp),
    is_created_by_sub_(false)
  {
  }

  explicit ipc_shared_ptr(
    T * ptr, const std::string & topic_name, const uint32_t publisher_index,
    const uint32_t subscriber_index, const uint64_t timestamp)
  : ptr_(ptr),
    topic_name_(topic_name),
    publisher_index_(publisher_index),
    subscriber_index_(subscriber_index),
    timestamp_(timestamp),
    is_created_by_sub_(true)
  {
  }

  ~ipc_shared_ptr() { reset(); }

  ipc_shared_ptr(const ipc_shared_ptr & r)
  : ptr_(r.ptr_),
    topic_name_(r.topic_name_),
    publisher_index_(r.publisher_index_),
    subscriber_index_(r.subscriber_index_),
    timestamp_(r.timestamp_),
    is_created_by_sub_(r.is_created_by_sub_)
  {
    if (ptr_ != nullptr && !is_created_by_sub_) {
      RCLCPP_ERROR(
        logger,
        "Copying an ipc_shared_ptr is not allowed if it was created by borrow_loaned_message().");
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }

    increment_rc();
  }

  ipc_shared_ptr(ipc_shared_ptr && r)
  : ptr_(r.ptr_),
    topic_name_(r.topic_name_),
    publisher_index_(r.publisher_index_),
    subscriber_index_(r.subscriber_index_),
    timestamp_(r.timestamp_),
    is_created_by_sub_(r.is_created_by_sub_)
  {
    r.ptr_ = nullptr;
  }

  ipc_shared_ptr & operator=(ipc_shared_ptr && r)
  {
    if (this != &r) {
      reset();
      ptr_ = r.ptr_;
      topic_name_ = r.topic_name_;
      publisher_index_ = r.publisher_index_;
      subscriber_index_ = r.subscriber_index_;
      timestamp_ = r.timestamp_;
      is_created_by_sub_ = r.is_created_by_sub_;

      r.ptr_ = nullptr;
    }
    return *this;
  }

  T & operator*() const noexcept { return *ptr_; }

  T * operator->() const noexcept { return ptr_; }

  operator bool() const noexcept { return ptr_; }

  T * get() const noexcept { return ptr_; }

  void reset()
  {
    if (ptr_ == nullptr) return;

    if (is_created_by_sub_) {
      decrement_rc(topic_name_, publisher_index_, subscriber_index_, timestamp_);
    }
    ptr_ = nullptr;
  }
};

}  // namespace agnocast
