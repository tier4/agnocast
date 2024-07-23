#pragma once

#include <fcntl.h>
#include <mqueue.h>
#include <semaphore.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>
#include <cstdint>
#include <cstring>
#include <sys/ioctl.h>

#include "agnocast_ioctl.hpp"

namespace agnocast {

extern int agnocast_fd;

template<typename T>
class message_ptr {
  T *ptr_ = nullptr;
  const char *topic_name_;
  uint32_t publisher_pid_;
  uint64_t timestamp_;

  void release() {
    if (ptr_ == nullptr) return;

    union ioctl_update_entry_args entry_args;
    entry_args.topic_name = topic_name_;
    entry_args.publisher_pid = publisher_pid_;
    entry_args.msg_timestamp = timestamp_;
    if (ioctl(agnocast_fd, AGNOCAST_DECREMENT_RC_CMD, &entry_args) < 0) {
        perror("AGNOCAST_DECREMENT_RC_CMD failed");
        close(agnocast_fd);
        exit(EXIT_FAILURE);
    }

    ptr_ = nullptr;
  }

  void increment_rc() {
    union ioctl_update_entry_args entry_args;
    entry_args.topic_name = topic_name_;
    entry_args.publisher_pid = publisher_pid_;
    entry_args.msg_timestamp = timestamp_;
    if (ioctl(agnocast_fd, AGNOCAST_INCREMENT_RC_CMD, &entry_args) < 0) {
        perror("AGNOCAST_INCREMENT_RC_CMD failed");
        close(agnocast_fd);
        exit(EXIT_FAILURE);
    }
  }

public:
  const char* get_topic_name() { return topic_name_; }
  uint32_t get_publisher_pid() const { return publisher_pid_; }
  uint64_t get_timestamp() { return timestamp_; }

  message_ptr() { }

  explicit message_ptr(T *ptr, const char *topic_name, uint32_t publisher_pid, uint64_t timestamp, bool already_rc_incremented = false) :
      ptr_(ptr), topic_name_(topic_name), publisher_pid_(publisher_pid), timestamp_(timestamp) {
    if (!already_rc_incremented) {
      increment_rc();
    }
  }

  ~message_ptr() {
    release();
  }

  message_ptr(const message_ptr &r) :
      ptr_(r.ptr_), topic_name_(r.topic_name_), publisher_pid_(r.publisher_pid_), timestamp_(r.timestamp_) {
    increment_rc();
  }

  message_ptr& operator =(const message_ptr &r) {
    if (this == &r) return *this;

    release();

    ptr_ = r.ptr_;
    topic_name_ = r.topic_name_;
    publisher_pid_ = r.publisher_pid_;
    timestamp_ = r.timestamp_;

    increment_rc();
  }

  message_ptr(message_ptr &&r) :
      ptr_(r.ptr_), topic_name_(r.topic_name_), publisher_pid_(r.publisher_pid_), timestamp_(r.timestamp_) {
    r.ptr_ = nullptr;
  }

  message_ptr& operator =(message_ptr &&r) {
    release();
    
    ptr_ = r.ptr_;
    topic_name_ = r.topic_name_;
    publisher_pid_ = r.publisher_pid_;
    timestamp_ = r.timestamp_;

    r.ptr_ = nullptr;
  }

  T& operator *() const noexcept { return *ptr_; }

  T* operator ->() const noexcept { return ptr_; }

  T* get() const noexcept { return ptr_; }
};

} // namespace agnocast
