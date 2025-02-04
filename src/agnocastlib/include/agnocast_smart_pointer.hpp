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

namespace agnocast
{

// These are cut out of the class for information hiding.
void decrement_rc(
  const std::string & topic_name, const topic_local_id_t subscriber_id, const uint64_t entry_id);
void increment_rc_core(
  const std::string & topic_name, const topic_local_id_t subscriber_id, const uint64_t entry_id);

extern int agnocast_fd;

template <typename T>
class ipc_shared_ptr
{
  T * ptr_ = nullptr;
  std::string topic_name_;
  topic_local_id_t subscriber_id_ = -1;
  uint64_t entry_id_ = -1;
  bool is_created_by_sub_ = false;

  void increment_rc() const
  {
    if (!is_created_by_sub_) return;

    increment_rc_core(topic_name_, subscriber_id_, entry_id_);
  }

  // Unimplemented operators. If these are called, a compile error is raised.
  ipc_shared_ptr & operator=(const ipc_shared_ptr & r) = delete;
  bool operator==(const ipc_shared_ptr & r) const = delete;
  bool operator!=(const ipc_shared_ptr & r) const = delete;

public:
  using element_type = T;

  const std::string get_topic_name() const { return topic_name_; }
  uint64_t get_entry_id() const { return entry_id_; }

  ipc_shared_ptr() = default;

  explicit ipc_shared_ptr(T * ptr, const std::string & topic_name)
  : ptr_(ptr), topic_name_(topic_name)
  {
  }

  explicit ipc_shared_ptr(
    T * ptr, const std::string & topic_name, const topic_local_id_t subscriber_id,
    const uint64_t entry_id)
  : ptr_(ptr),
    topic_name_(topic_name),
    subscriber_id_(subscriber_id),
    entry_id_(entry_id),
    is_created_by_sub_(true)
  {
  }

  ~ipc_shared_ptr() { reset(); }

  ipc_shared_ptr(const ipc_shared_ptr & r)
  : ptr_(r.ptr_),
    topic_name_(r.topic_name_),
    subscriber_id_(r.subscriber_id_),
    entry_id_(r.entry_id_),
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
    subscriber_id_(r.subscriber_id_),
    entry_id_(r.entry_id_),
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
      subscriber_id_ = r.subscriber_id_;
      entry_id_ = r.entry_id_;
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
      decrement_rc(topic_name_, subscriber_id_, entry_id_);
    }
    ptr_ = nullptr;
  }
};

}  // namespace agnocast
