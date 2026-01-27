#pragma once

#include "agnocast/agnocast_ioctl.hpp"
#include "agnocast/agnocast_utils.hpp"

#include <fcntl.h>
#include <mqueue.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

#include <atomic>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <memory>

// Branch prediction hints for GCC/Clang; fallback to identity on other compilers
#if defined(__GNUC__) || defined(__clang__)
#define AGNOCAST_LIKELY(x) __builtin_expect(!!(x), 1)
#define AGNOCAST_UNLIKELY(x) __builtin_expect(!!(x), 0)
#else
#define AGNOCAST_LIKELY(x) (!!(x))
#define AGNOCAST_UNLIKELY(x) (!!(x))
#endif

namespace agnocast
{

// These are cut out of the class for information hiding.
void release_subscriber_reference(
  const std::string & topic_name, const topic_local_id_t pubsub_id, const int64_t entry_id);
void decrement_borrowed_publisher_num();

extern int agnocast_fd;

// Forward declaration for friend access
template <typename MessageT, typename BridgeRequestPolicy>
class BasicPublisher;

template <typename T>
class ipc_shared_ptr
{
  // Allow BasicPublisher to call invalidate_all_references()
  template <typename MessageT, typename BridgeRequestPolicy>
  friend class BasicPublisher;
  // Control block for one-shot invalidation (publisher-side only).
  // Shared among all copies so that invalidate_all_references() affects them all.
  struct validity_control
  {
    std::atomic<uint32_t> valid{1U};
  };

  T * ptr_ = nullptr;
  std::string topic_name_;
  topic_local_id_t pubsub_id_ = -1;
  int64_t entry_id_ = -1;
  std::shared_ptr<validity_control> validity_;

  // Unimplemented operators. If these are called, a compile error is raised.
  bool operator==(const ipc_shared_ptr & r) const = delete;
  bool operator!=(const ipc_shared_ptr & r) const = delete;

  // Check if this handle has been invalidated (publisher-side invalidation).
  bool is_invalidated_() const noexcept
  {
    return validity_ && validity_->valid.load(std::memory_order_acquire) == 0U;
  }

  // Invalidates all references sharing this handle's control block (publisher-side only).
  // After this call, any dereference (operator->, operator*) on copies will std::terminate(),
  // and get()/operator bool() will return nullptr/false.
  // Private: only BasicPublisher::publish() should call this.
  void invalidate_all_references() noexcept
  {
    if (validity_) {
      validity_->valid.store(0U, std::memory_order_release);
    }
  }

public:
  using element_type = T;

  const std::string get_topic_name() const { return topic_name_; }
  topic_local_id_t get_pubsub_id() const { return pubsub_id_; }
  int64_t get_entry_id() const { return entry_id_; }
  void set_entry_id(const int64_t entry_id) { entry_id_ = entry_id; }

  ipc_shared_ptr() = default;

  // Publisher-side constructor (entry_id not yet assigned => entry_id == -1).
  // Creates validity_ control block for one-shot invalidation.
  explicit ipc_shared_ptr(T * ptr, const std::string & topic_name, const topic_local_id_t pubsub_id)
  : ptr_(ptr),
    topic_name_(topic_name),
    pubsub_id_(pubsub_id),
    validity_(ptr ? std::make_shared<validity_control>() : nullptr)
  {
  }

  // Subscriber-side constructor (entry_id already assigned => entry_id != -1).
  // Creates validity_ for reference counting (use_count() tracks subscriber references).
  explicit ipc_shared_ptr(
    T * ptr, const std::string & topic_name, const topic_local_id_t pubsub_id,
    const int64_t entry_id)
  : ptr_(ptr),
    topic_name_(topic_name),
    pubsub_id_(pubsub_id),
    entry_id_(entry_id),
    validity_(ptr ? std::make_shared<validity_control>() : nullptr)
  {
  }

  ~ipc_shared_ptr() { reset(); }

  ipc_shared_ptr(const ipc_shared_ptr & r)
  : ptr_(r.ptr_),
    topic_name_(r.topic_name_),
    pubsub_id_(r.pubsub_id_),
    entry_id_(r.entry_id_),
    validity_(r.validity_)
  {
    // Reference counting is handled by validity_.use_count() for both publisher and subscriber.
    // No ioctl needed on copy - only when the last reference is destroyed.
  }

  ipc_shared_ptr & operator=(const ipc_shared_ptr & r)
  {
    if (this != &r) {
      reset();
      ptr_ = r.ptr_;
      topic_name_ = r.topic_name_;
      pubsub_id_ = r.pubsub_id_;
      entry_id_ = r.entry_id_;
      validity_ = r.validity_;
      // Reference counting is handled by validity_.use_count() - no ioctl needed on copy.
    }
    return *this;
  }

  ipc_shared_ptr(ipc_shared_ptr && r)
  : ptr_(r.ptr_),
    topic_name_(std::move(r.topic_name_)),
    pubsub_id_(r.pubsub_id_),
    entry_id_(r.entry_id_),
    validity_(std::move(r.validity_))
  {
    r.ptr_ = nullptr;
  }

  ipc_shared_ptr & operator=(ipc_shared_ptr && r)
  {
    if (this != &r) {
      reset();
      ptr_ = r.ptr_;
      topic_name_ = std::move(r.topic_name_);
      pubsub_id_ = r.pubsub_id_;
      entry_id_ = r.entry_id_;
      validity_ = std::move(r.validity_);

      r.ptr_ = nullptr;
    }
    return *this;
  }

  T & operator*() const noexcept
  {
    if (AGNOCAST_UNLIKELY(is_invalidated_())) {
      std::fprintf(
        stderr,
        "[agnocast] FATAL: Attempted to dereference an invalidated ipc_shared_ptr.\n"
        "The message has already been published and this handle is no longer valid.\n"
        "Do not access message data after calling publish(). Please rewrite your application.\n");
      std::terminate();
    }
    return *ptr_;
  }

  T * operator->() const noexcept
  {
    if (AGNOCAST_UNLIKELY(is_invalidated_())) {
      std::fprintf(
        stderr,
        "[agnocast] FATAL: Attempted to access an invalidated ipc_shared_ptr.\n"
        "The message has already been published and this handle is no longer valid.\n"
        "Do not access message data after calling publish(). Please rewrite your application.\n");
      std::terminate();
    }
    return ptr_;
  }

  operator bool() const noexcept { return ptr_ != nullptr && !is_invalidated_(); }

  T * get() const noexcept { return is_invalidated_() ? nullptr : ptr_; }

  void reset()
  {
    if (ptr_ == nullptr) return;

    if (entry_id_ != -1) {
      // Subscriber side: notify kmod only when the last reference is destroyed.
      if (validity_ && validity_.use_count() == 1) {
        release_subscriber_reference(topic_name_, pubsub_id_, entry_id_);
      }
    } else if (
      validity_ && validity_.use_count() == 1 &&
      validity_->valid.load(std::memory_order_acquire) == 1U) {
      // Publisher side, last reference, not published: delete the memory.
      // This handles the case where borrow_loaned_message() was called but publish() was not.
      decrement_borrowed_publisher_num();
      delete ptr_;
    }

    ptr_ = nullptr;
    validity_.reset();
  }
};

}  // namespace agnocast
