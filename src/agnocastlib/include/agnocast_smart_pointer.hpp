#pragma once

#include "agnocast_ioctl.hpp"

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
#include <iostream>

namespace agnocast
{

extern int agnocast_fd;

template <typename T>
class message_ptr
{
  T * ptr_ = nullptr;
  const char * topic_name_;
  uint32_t publisher_pid_;
  uint64_t timestamp_;
  bool need_rc_update_;

  void release()
  {
    if (ptr_ == nullptr) return;
    if (!need_rc_update_) return;

    union ioctl_update_entry_args entry_args;
    entry_args.topic_name = topic_name_;
    entry_args.subscriber_pid = getpid();
    entry_args.publisher_pid = publisher_pid_;
    entry_args.msg_timestamp = timestamp_;
    if (ioctl(agnocast_fd, AGNOCAST_DECREMENT_RC_CMD, &entry_args) < 0) {
      perror("AGNOCAST_DECREMENT_RC_CMD failed");
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }

    ptr_ = nullptr;
  }

  void increment_rc()
  {
    if (!need_rc_update_) return;

    union ioctl_update_entry_args entry_args;
    entry_args.topic_name = topic_name_;
    entry_args.subscriber_pid = getpid();
    entry_args.publisher_pid = publisher_pid_;
    entry_args.msg_timestamp = timestamp_;
    if (ioctl(agnocast_fd, AGNOCAST_INCREMENT_RC_CMD, &entry_args) < 0) {
      perror("AGNOCAST_INCREMENT_RC_CMD failed");
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }
  }

public:
  using element_type = T;

  const char * get_topic_name() { return topic_name_; }
  uint32_t get_publisher_pid() const { return publisher_pid_; }
  uint64_t get_timestamp() { return timestamp_; }

  message_ptr() {}

  explicit message_ptr(
    T * ptr, const char * topic_name, uint32_t publisher_pid, uint64_t timestamp,
    bool need_rc_update)
  : ptr_(ptr),
    topic_name_(topic_name),
    publisher_pid_(publisher_pid),
    timestamp_(timestamp),
    need_rc_update_(need_rc_update)
  {
  }

  ~message_ptr() { release(); }

  message_ptr(const message_ptr & r)
  : ptr_(r.ptr_),
    topic_name_(r.topic_name_),
    publisher_pid_(r.publisher_pid_),
    timestamp_(r.timestamp_),
    need_rc_update_(r.need_rc_update_)
  {
    increment_rc();
  }

  message_ptr & operator=(const message_ptr & r)
  {
    std::cout << "[Error]: copy assignment operator is not supported yet" << std::endl;
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  message_ptr(message_ptr && r)
  : ptr_(r.ptr_),
    topic_name_(r.topic_name_),
    publisher_pid_(r.publisher_pid_),
    timestamp_(r.timestamp_),
    need_rc_update_(r.need_rc_update_)
  {
    r.ptr_ = nullptr;
  }

  message_ptr & operator=(message_ptr && r)
  {
    std::cout << "[Error]: move assignment operator is not supported yet" << std::endl;
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  T & operator*() const noexcept { return *ptr_; }

  T * operator->() const noexcept { return ptr_; }

  T * get() const noexcept { return ptr_; }
};

}  // namespace agnocast
