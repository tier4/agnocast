# Agnocast Message Filters Design Document

## Overview

Agnocast message filters provide a message synchronization framework adapted from the ROS 2 `message_filters` package (https://github.com/ros2/message_filters). The framework enables filtering, synchronizing, and routing messages delivered via agnocast's shared memory IPC, while maintaining API compatibility with the upstream ROS 2 implementation where possible.

## Design Principles

1. **Const-only message model**: Agnocast subscriptions receive `ipc_shared_ptr<const M>` exclusively, as messages reside in read-only shared memory. The entire message_filters stack is designed under this premise — non-const message access is neither supported nor expected.

2. **Alignment with ROS 2 implementation**: To maximize extensibility and readability, the implementation aligns with the ROS 2 `message_filters` API and architecture as closely as possible. This reduces the learning curve for developers familiar with ROS 2 and simplifies the addition of new sync policies (e.g., `ApproximateTime`).

3. **Reuse of ROS 2 components**: Where the upstream ROS 2 `message_filters` implementation is type-agnostic or does not depend on `std::shared_ptr`, it is reused directly. This includes `Connection`, `NullFilter`, `NullType`, `noncopyable`, `message_traits::TimeStamp`, and `mp_count`.

## Architecture

```
Publisher
  │
  ▼ (agnocast shared memory IPC)
Subscriber<M> ──extends──▶ SimpleFilter<M>
  │                              │
  │ signalMessage(event)         │ Signal1<M>
  │                              │
  ▼                              ▼
Synchronizer<Policy>
  │ cb<i>(event) → Policy::add<i>(event)
  │
  ▼ Policy (e.g., ExactTime)
  │ timestamp matching / queue management
  │
  ▼ parent_->signal(e0, e1, ..., e8)
  │
  ▼ Signal9<M0, ..., M8>
  │
  ▼ User Callback
```

## Components

### MessageEvent (`message_event.hpp`)

Wraps an `ipc_shared_ptr<M const>` with receipt-time metadata.

- Enforces const messages via `static_assert(std::is_const<M>::value)`.
- Provides `getMessage()`, `getConstMessage()`, and `getReceiptTime()`.
- Supports comparison operators for use in ordered containers.

**Difference from ROS 2**: ROS 2 `MessageEvent` stores `std::shared_ptr` and supports both const and non-const messages. Agnocast's version only supports `ipc_shared_ptr<M const>`.

### ParameterAdapter (`parameter_adapter.hpp`)

Template specializations that convert `MessageEvent` into the callback parameter type expected by the user.

Supported parameter types:

| Parameter Type | Extraction |
|---|---|
| `const ipc_shared_ptr<M const>&` | `event.getMessage()` |
| `ipc_shared_ptr<M const>` (by value) | `event.getMessage()` |
| `const MessageEvent<M const>&` | `event` itself |

**Difference from ROS 2**: ROS 2 additionally supports `std::shared_ptr<M>` (non-const), `const M&`, and `M` (by value). These are omitted because agnocast messages are always accessed via `ipc_shared_ptr<const M>`.

### Signal1 (`signal1.hpp`)

Thread-safe single-message signal dispatcher. Uses `ParameterAdapter` to adapt callback signatures.

**Reused from ROS 2**: `Connection` for managing callback subscriptions.

### Signal9 (`signal9.hpp`)

Thread-safe 9-message signal dispatcher. Supports function pointers, member function pointers, and callable objects with 2–9 parameters.

**Reused from ROS 2**: `Connection`, `NullType`.

**Note**: Member function pointers are limited to 8 parameters because `std::bind` supports at most 9 arguments (object pointer + 8 message parameters).

### SimpleFilter (`simple_filter.hpp`)

Base class for single-output filters. Provides `registerCallback()` and `signalMessage()`.

**Reused from ROS 2**: `Connection`, `noncopyable`.

### Subscriber (`subscriber.hpp`)

Connects agnocast subscriptions to the message_filters chain. Wraps `agnocast::create_subscription()` and signals received messages as `MessageEvent<M const>`.

- Accepts both `std::shared_ptr<NodeType>` and raw `NodeType*`.
- Supports subscribe/unsubscribe/resubscribe.
- Supports `agnocast::SubscriptionOptions`.

**Difference from ROS 2**: ROS 2 `Subscriber` uses `rclcpp::Subscription` internally. Agnocast's version uses `agnocast::create_subscription()` and converts the received `ipc_shared_ptr<M>` to `ipc_shared_ptr<M const>` before signaling.

### Synchronizer (`synchronizer.hpp`)

Policy-based multi-message synchronizer. Routes messages from 2–9 input filters to a sync policy via `add<i>()`.

- Inherits from the `Policy` template parameter (CRTP-like pattern).
- `PolicyBase` provides common type aliases: `Messages`, `Events`, `Signal`, `RealTypeCount`.

**Reused from ROS 2**: `Connection`, `noncopyable`, `NullFilter`, `NullType`, `mp_count`.

### ExactTime Policy (`sync_policies/exact_time.hpp`)

Groups messages by exact timestamp match. When all message slots for a given timestamp are filled, the synchronized tuple is signaled to the user callback.

- Uses `std::map<rclcpp::Time, Tuple>` for timestamp-keyed buffering.
- Configurable `queue_size` limits buffered tuples.
- Supports drop callbacks for discarded tuples.
- Thread-safe via mutex.
- Requires `message_traits::TimeStamp<M>` specialization for each message type.

**Reused from ROS 2**: `Connection`, `NullType`, `message_traits::TimeStamp`.

## ROS 2 Reuse Summary

| Component | Source | Usage |
|---|---|---|
| `Connection` | `message_filters/connection.h` | Callback lifecycle management |
| `NullType` | `message_filters/null_types.h` | Padding for unused message slots |
| `NullFilter` | `message_filters/null_types.h` | Dummy filter for unused inputs |
| `noncopyable` | `message_filters/synchronizer.h` | Base class preventing copy |
| `mp_count` | `message_filters/synchronizer.h` | Counting non-NullType template args |
| `message_traits::TimeStamp` | `message_filters/message_traits.h` | Timestamp extraction from messages |
| `message_traits::HasHeader` | `message_filters/message_traits.h` | Header detection for auto TimeStamp |

## Test Structure

### Unit Tests (`test_unit_message_filters_agnocastlib`)

Use ioctl mock — no kernel module required. Run in CI.

| File | Coverage |
|---|---|
| `test_simple.cpp` | SimpleFilter callback type flexibility |
| `test_exact_time.cpp` | ExactTime timestamp matching, queue size, drop callback |
| `test_synchronizer.cpp` | Synchronizer compile tests (2–9 inputs), callback signatures, add routing |
| `ioctl_mock_for_mf.cpp` | Mock ioctl returning success for all agnocast calls |

### Integration Tests (`test_integration_message_filters_agnocastlib`)

Use real agnocast publishers with kernel module. Not run in CI.

| File | Coverage |
|---|---|
| `test_subscriber.cpp` | Full Publisher → Subscriber pipeline, subscribe/unsubscribe, multiple callbacks |
| `test_synchronizer.cpp` | Full Publisher → Subscriber → Synchronizer → ExactTime → callback pipeline, 9-channel sync, partial arrival, timestamp mismatch/match |

## File Layout

```
src/agnocastlib/include/agnocast/message_filters/
├── message_event.hpp
├── parameter_adapter.hpp
├── signal1.hpp
├── signal9.hpp
├── simple_filter.hpp
├── subscriber.hpp
├── synchronizer.hpp
└── sync_policies/
    └── exact_time.hpp

src/agnocastlib/test/unit/message_filters/
├── ioctl_mock_for_mf.cpp
├── test_simple.cpp
├── test_exact_time.cpp
└── test_synchronizer.cpp

src/agnocastlib/test/integration/message_filters/
├── test_subscriber.cpp
└── test_synchronizer.cpp
```

## Future Work

- **ApproximateTime sync policy**: The existing infrastructure (`PolicyBase`, `Synchronizer`, `Signal9`, `MessageEvent`, `message_traits::TimeStamp`) fully supports an `ApproximateTime` implementation. The adaptation pattern is the same as ExactTime — replace `std::shared_ptr` with `ipc_shared_ptr<const M>` in the ROS 2 source.
- **ROS message and agnocast message synchronization**: Enable synchronizing messages from both standard ROS 2 subscriptions (`std::shared_ptr<const M>`) and agnocast subscriptions (`ipc_shared_ptr<const M>`) within the same Synchronizer.
- **`agnocast::Node` support**: The current `Subscriber` accepts `rclcpp::Node`. Add support for `agnocast::Node` to align with the agnocast node abstraction.
- **Additional filter types**: Support filters beyond `Synchronizer`, such as `Cache` (time-indexed message history) and `Chain` (sequential filter pipeline).
