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

// Sentinel value indicating entry_id has not been assigned (publisher-side, before publish).
constexpr int64_t ENTRY_ID_NOT_ASSIGNED = -1;

// Forward declaration for friend access
template <typename MessageT, typename BridgeRequestPolicy>
class BasicPublisher;

// A smart pointer for IPC message sharing between publishers and subscribers.
//
// Thread Safety:
//   This class is thread-safe. Multiple threads can safely access different instances that share
//   ownership (i.e., copies of the same pointer). The reference counting uses atomic operations
//   to ensure correct cleanup when the last reference is destroyed.
//
//   Note: Concurrent access to the *same* instance (e.g., one thread calling reset() while another
//   reads) still requires external synchronization, same as std::shared_ptr.
template <typename T>
class ipc_shared_ptr
{
  // Allow BasicPublisher to call invalidate_all_references()
  template <typename MessageT, typename BridgeRequestPolicy>
  friend class BasicPublisher;

  // Control block shared among all copies for thread-safe reference counting and invalidation.
  // Uses atomic operations to ensure correct behavior when multiple threads hold copies.
  // Also stores metadata (topic_name, pubsub_id, entry_id) to avoid copying on every ipc_shared_ptr
  // copy.
  struct control_block
  {
    std::atomic<uint32_t> ref_count{1U};
    std::atomic<uint32_t> valid{1U};
    std::string topic_name;
    topic_local_id_t pubsub_id;
    int64_t entry_id;

    control_block(std::string topic, topic_local_id_t pubsub, int64_t entry)
    : topic_name(std::move(topic)), pubsub_id(pubsub), entry_id(entry)
    {
    }

    void increment() noexcept { ref_count.fetch_add(1, std::memory_order_relaxed); }

    // Returns true if this was the last reference (i.e., previous count was 1).
    bool decrement_and_check() noexcept
    {
      return ref_count.fetch_sub(1, std::memory_order_acq_rel) == 1;
    }
  };

  T * ptr_ = nullptr;
  control_block * control_ = nullptr;

  // Unimplemented operators. If these are called, a compile error is raised.
  bool operator==(const ipc_shared_ptr & r) const = delete;
  bool operator!=(const ipc_shared_ptr & r) const = delete;

  // Check if this handle has been invalidated (publisher-side invalidation).
  bool is_invalidated_() const noexcept
  {
    return control_ && control_->valid.load(std::memory_order_acquire) == 0U;
  }

  // Invalidates all references sharing this handle's control block (publisher-side only).
  // After this call, any dereference (operator->, operator*) on copies will std::terminate(),
  // and get()/operator bool() will return nullptr/false.
  // Private: only BasicPublisher::publish() should call this.
  void invalidate_all_references() noexcept
  {
    if (control_) {
      control_->valid.store(0U, std::memory_order_release);
    }
  }

public:
  using element_type = T;

  const std::string get_topic_name() const { return control_ ? control_->topic_name : ""; }
  topic_local_id_t get_pubsub_id() const { return control_ ? control_->pubsub_id : -1; }
  int64_t get_entry_id() const { return control_ ? control_->entry_id : ENTRY_ID_NOT_ASSIGNED; }

  // Deprecated: This method is unused and kept only for backward compatibility.
  [[deprecated("set_entry_id() is unused and will be removed in a future release")]]
  void set_entry_id(const int64_t entry_id)
  {
    if (control_) control_->entry_id = entry_id;
  }

  ipc_shared_ptr() = default;

  // Publisher-side constructor (entry_id not yet assigned).
  // Creates control block for reference counting and one-shot invalidation.
  explicit ipc_shared_ptr(T * ptr, const std::string & topic_name, const topic_local_id_t pubsub_id)
  : ptr_(ptr),
    control_(ptr ? new control_block(topic_name, pubsub_id, ENTRY_ID_NOT_ASSIGNED) : nullptr)
  {
  }

  // Subscriber-side constructor (entry_id already assigned).
  // Creates control block for reference counting.
  explicit ipc_shared_ptr(
    T * ptr, const std::string & topic_name, const topic_local_id_t pubsub_id,
    const int64_t entry_id)
  : ptr_(ptr), control_(ptr ? new control_block(topic_name, pubsub_id, entry_id) : nullptr)
  {
  }

  ~ipc_shared_ptr() { reset(); }

  // Thread-safe: atomically increments reference count.
  // Metadata (topic_name, pubsub_id, entry_id) is stored in control_block, so no string copying.
  ipc_shared_ptr(const ipc_shared_ptr & r) : ptr_(r.ptr_), control_(r.control_)
  {
    if (control_) {
      control_->increment();
    }
  }

  // Thread-safe: atomically decrements old ref count and increments new ref count.
  // Metadata (topic_name, pubsub_id, entry_id) is stored in control_block, so no string copying.
  ipc_shared_ptr & operator=(const ipc_shared_ptr & r)
  {
    if (this != &r) {
      reset();
      ptr_ = r.ptr_;
      control_ = r.control_;
      if (control_) {
        control_->increment();
      }
    }
    return *this;
  }

  // Move constructor: transfers ownership without changing ref count.
  ipc_shared_ptr(ipc_shared_ptr && r) noexcept : ptr_(r.ptr_), control_(r.control_)
  {
    r.ptr_ = nullptr;
    r.control_ = nullptr;
  }

  // Move assignment: transfers ownership without changing ref count.
  ipc_shared_ptr & operator=(ipc_shared_ptr && r) noexcept
  {
    if (this != &r) {
      reset();
      ptr_ = r.ptr_;
      control_ = r.control_;

      r.ptr_ = nullptr;
      r.control_ = nullptr;
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

  // Thread-safe: atomically decrements ref count and performs cleanup if last reference.
  void reset()
  {
    if (control_ == nullptr) return;

    // Atomically decrement and check if we were the last reference.
    // fetch_sub returns the previous value, so if it was 1, we're now at 0 (last reference).
    const bool was_last = control_->decrement_and_check();

    if (was_last) {
      if (control_->entry_id != ENTRY_ID_NOT_ASSIGNED) {
        // Subscriber side: notify kmod that all references are released.
        release_subscriber_reference(control_->topic_name, control_->pubsub_id, control_->entry_id);
      } else if (control_->valid.load(std::memory_order_acquire) == 1U) {
        // Publisher side, last reference, not published: delete the memory.
        // This handles the case where borrow_loaned_message() was called but publish() was not.
        decrement_borrowed_publisher_num();
        delete ptr_;
      }
      delete control_;
    }

    ptr_ = nullptr;
    control_ = nullptr;
  }
};

}  // namespace agnocast
