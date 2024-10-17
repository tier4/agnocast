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

extern int agnocast_fd;

// These are cut out of the class for information hiding.
void decrement_rc(const std::string & topic_name, uint32_t publisher_pid, uint64_t timestamp);
void increment_rc_core(const std::string & topic_name, uint32_t publisher_pid, uint64_t timestamp);

template <typename T>
class ipc_shared_ptr
{
  T * ptr_ = nullptr;
  std::string topic_name_;
  uint32_t publisher_pid_ = 0;
  uint64_t timestamp_ = 0;
  bool need_rc_update_ = false;

  void release()
  {
    if (ptr_ == nullptr) return;
    if (!need_rc_update_) return;

    decrement_rc(topic_name_, publisher_pid_, timestamp_);
    ptr_ = nullptr;
  }

  void increment_rc() const
  {
    if (!need_rc_update_) return;

    increment_rc_core(topic_name_, publisher_pid_, timestamp_);
  }

  ipc_shared_ptr & operator=(const ipc_shared_ptr & r) = delete;

public:
  const std::string get_topic_name() const { return topic_name_; }
  uint32_t get_publisher_pid() const { return publisher_pid_; }
  uint64_t get_timestamp() const { return timestamp_; }

  ipc_shared_ptr() = default;

  explicit ipc_shared_ptr(
    T * ptr, const std::string & topic_name, uint32_t publisher_pid, uint64_t timestamp,
    bool need_rc_update)
  : ptr_(ptr),
    topic_name_(topic_name),
    publisher_pid_(publisher_pid),
    timestamp_(timestamp),
    need_rc_update_(need_rc_update)
  {
  }

  ~ipc_shared_ptr() { release(); }

  ipc_shared_ptr(const ipc_shared_ptr & r)
  : ptr_(r.ptr_),
    topic_name_(r.topic_name_),
    publisher_pid_(r.publisher_pid_),
    timestamp_(r.timestamp_),
    need_rc_update_(r.need_rc_update_)
  {
    increment_rc();
  }

  ipc_shared_ptr(ipc_shared_ptr && r)
  : ptr_(r.ptr_),
    topic_name_(r.topic_name_),
    publisher_pid_(r.publisher_pid_),
    timestamp_(r.timestamp_),
    need_rc_update_(r.need_rc_update_)
  {
    r.ptr_ = nullptr;
  }

  ipc_shared_ptr & operator=(ipc_shared_ptr && r)
  {
    if (this != &r) {
      release();

      ptr_ = r.ptr_;
      topic_name_ = r.topic_name_;
      publisher_pid_ = r.publisher_pid_;
      timestamp_ = r.timestamp_;
      need_rc_update_ = r.need_rc_update_;

      r.ptr_ = nullptr;
    }
    return *this;
  }

  T & operator*() const noexcept { return *ptr_; }

  T * operator->() const noexcept { return ptr_; }

  operator bool() const noexcept { return ptr_; }

  T * get() const noexcept { return ptr_; }
};

}  // namespace agnocast
