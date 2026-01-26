// Copyright 2025 The Autoware Contributors
// SPDX-License-Identifier: Apache-2.0

#include "agnocast/agnocast_smart_pointer.hpp"
#include "agnocast/message_filters/sync_policies/exact_time.hpp"
#include "agnocast/message_filters/synchronizer.hpp"

#include <gtest/gtest.h>
#include <sensor_msgs/msg/imu.hpp>

namespace agnocast
{
// Mock functions for ipc_shared_ptr
void decrement_rc(const std::string &, const topic_local_id_t, const int64_t) {}
void increment_rc(const std::string &, const topic_local_id_t, const int64_t) {}
}  // namespace agnocast

using ImuPtr = agnocast::ipc_shared_ptr<const sensor_msgs::msg::Imu>;
using NullPtr = agnocast::ipc_shared_ptr<const message_filters::NullType>;
using ExactTimePolicy =
  agnocast::message_filters::sync_policies::ExactTime<sensor_msgs::msg::Imu, sensor_msgs::msg::Imu>;
using Synchronizer = agnocast::message_filters::Synchronizer<ExactTimePolicy>;

class ExactSynchronizerTest : public ::testing::Test
{
protected:
  void SetUp() override
  {
    callback_count_ = 0;
    drop_callback_count_ = 0;
    last_msg0_value_ = -1.0;
    last_msg1_value_ = -1.0;
  }

  ImuPtr createImuMessage(double value, int64_t stamp_sec, uint32_t stamp_nsec)
  {
    auto * msg = new sensor_msgs::msg::Imu();
    msg->header.stamp.sec = stamp_sec;
    msg->header.stamp.nanosec = stamp_nsec;
    msg->linear_acceleration.x = value;
    return ImuPtr(msg, "test_topic", 0, 0);
  }

  int callback_count_;
  int drop_callback_count_;
  double last_msg0_value_;
  double last_msg1_value_;
};

// =========================================
// ExactTime Policy Tests
// =========================================

TEST_F(ExactSynchronizerTest, ExactTimeSameTimestampCallbackCalled)
{
  // Arrange
  Synchronizer sync(ExactTimePolicy(10));
  sync.registerCallback(
    [this](
      const ImuPtr & msg0, const ImuPtr & msg1, const NullPtr &, const NullPtr &, const NullPtr &,
      const NullPtr &, const NullPtr &, const NullPtr &, const NullPtr &) {
      callback_count_++;
      last_msg0_value_ = msg0->linear_acceleration.x;
      last_msg1_value_ = msg1->linear_acceleration.x;
    });

  auto msg0 = createImuMessage(1.0, 100, 0);
  auto msg1 = createImuMessage(2.0, 100, 0);

  // Act
  sync.add<0>(msg0);
  sync.add<1>(msg1);

  // Assert
  EXPECT_EQ(callback_count_, 1);
  EXPECT_DOUBLE_EQ(last_msg0_value_, 1.0);
  EXPECT_DOUBLE_EQ(last_msg1_value_, 2.0);
}

TEST_F(ExactSynchronizerTest, ExactTimeDifferentTimestampCallbackNotCalled)
{
  // Arrange
  Synchronizer sync(ExactTimePolicy(10));
  sync.registerCallback(
    [this](
      const ImuPtr &, const ImuPtr &, const NullPtr &, const NullPtr &, const NullPtr &,
      const NullPtr &, const NullPtr &, const NullPtr &, const NullPtr &) { callback_count_++; });

  auto msg0 = createImuMessage(1.0, 100, 0);
  auto msg1 = createImuMessage(2.0, 200, 0);  // Different timestamp

  // Act
  sync.add<0>(msg0);
  sync.add<1>(msg1);

  // Assert
  EXPECT_EQ(callback_count_, 0);
}

TEST_F(ExactSynchronizerTest, ExactTimeMultipleMatchesMultipleCallbacks)
{
  // Arrange
  Synchronizer sync(ExactTimePolicy(10));
  sync.registerCallback(
    [this](
      const ImuPtr &, const ImuPtr &, const NullPtr &, const NullPtr &, const NullPtr &,
      const NullPtr &, const NullPtr &, const NullPtr &, const NullPtr &) { callback_count_++; });

  // Act - Add messages with matching timestamps
  for (int i = 0; i < 5; ++i) {
    auto msg0 = createImuMessage(static_cast<double>(i), i, 0);
    auto msg1 = createImuMessage(static_cast<double>(i * 10), i, 0);
    sync.add<0>(msg0);
    sync.add<1>(msg1);
  }

  // Assert
  EXPECT_EQ(callback_count_, 5);
}

TEST_F(ExactSynchronizerTest, ExactTimeQueueOverflowDropCallbackCalled)
{
  // Arrange
  Synchronizer sync{ExactTimePolicy(2)};
  sync.registerCallback(
    [this](
      const ImuPtr &, const ImuPtr &, const NullPtr &, const NullPtr &, const NullPtr &,
      const NullPtr &, const NullPtr &, const NullPtr &, const NullPtr &) { callback_count_++; });
  sync.getPolicy()->registerDropCallback(
    [this](
      const ImuPtr &, const ImuPtr &, const NullPtr &, const NullPtr &, const NullPtr &,
      const NullPtr &, const NullPtr &, const NullPtr &, const NullPtr &) {
      drop_callback_count_++;
    });

  // Act - Add more unmatched messages than queue_size
  for (int i = 0; i < 5; ++i) {
    auto msg0 = createImuMessage(static_cast<double>(i), i, 0);
    sync.add<0>(msg0);  // Only add msg0, no matching msg1
  }

  // Assert - Should have dropped (5 - queue_size) = 3 messages
  EXPECT_EQ(callback_count_, 0);
  EXPECT_EQ(drop_callback_count_, 3);
}

TEST_F(ExactSynchronizerTest, ExactTimeNullMessageNoEffect)
{
  // Arrange
  Synchronizer sync(ExactTimePolicy(10));
  sync.registerCallback(
    [this](
      const ImuPtr &, const ImuPtr &, const NullPtr &, const NullPtr &, const NullPtr &,
      const NullPtr &, const NullPtr &, const NullPtr &, const NullPtr &) { callback_count_++; });

  ImuPtr null_msg;  // Empty/null message

  // Act
  sync.add<0>(null_msg);

  // Assert - No crash, no callback
  EXPECT_EQ(callback_count_, 0);
}

TEST_F(ExactSynchronizerTest, ExactTimeCopyConstructor)
{
  // Arrange
  Synchronizer sync1(ExactTimePolicy(10));
  int sync1_callback_count = 0;
  sync1.registerCallback(
    [&sync1_callback_count](
      const ImuPtr &, const ImuPtr &, const NullPtr &, const NullPtr &, const NullPtr &,
      const NullPtr &, const NullPtr &, const NullPtr &, const NullPtr &) {
      sync1_callback_count++;
    });

  auto msg0 = createImuMessage(1.0, 100, 0);
  sync1.add<0>(msg0);

  // Act - Copy policy from sync1 and create new sync
  ExactTimePolicy policy2(*sync1.getPolicy());
  Synchronizer sync2(policy2);
  int sync2_callback_count = 0;
  sync2.registerCallback(
    [&sync2_callback_count](
      const ImuPtr &, const ImuPtr &, const NullPtr &, const NullPtr &, const NullPtr &,
      const NullPtr &, const NullPtr &, const NullPtr &, const NullPtr &) {
      sync2_callback_count++;
    });

  // Add matching message to copied sync
  auto msg1 = createImuMessage(2.0, 100, 0);
  sync2.add<1>(msg1);

  // Assert - sync2 should have the pending msg0 from sync1's policy
  EXPECT_EQ(sync2_callback_count, 1);
}

TEST_F(ExactSynchronizerTest, ExactTimeCopyAssignment)
{
  // Arrange
  Synchronizer sync1(ExactTimePolicy(10));
  auto msg0 = createImuMessage(1.0, 100, 0);
  sync1.add<0>(msg0);

  ExactTimePolicy policy2(5);
  policy2 = *sync1.getPolicy();

  Synchronizer sync2(policy2);
  int sync2_callback_count = 0;
  sync2.registerCallback(
    [&sync2_callback_count](
      const ImuPtr &, const ImuPtr &, const NullPtr &, const NullPtr &, const NullPtr &,
      const NullPtr &, const NullPtr &, const NullPtr &, const NullPtr &) {
      sync2_callback_count++;
    });

  auto msg1 = createImuMessage(2.0, 100, 0);
  sync2.add<1>(msg1);

  // Assert
  EXPECT_EQ(sync2_callback_count, 1);
}

// =========================================
// Synchronizer Tests
// =========================================

TEST_F(ExactSynchronizerTest, SynchronizerPolicyConstructor)
{
  // Arrange
  ExactTimePolicy policy(10);

  // Act
  agnocast::message_filters::Synchronizer<ExactTimePolicy> sync(policy);

  // Assert
  EXPECT_NE(sync.getPolicy(), nullptr);
}

TEST_F(ExactSynchronizerTest, SynchronizerRegisterCallbackAndAdd)
{
  // Arrange
  ExactTimePolicy policy(10);
  Synchronizer sync(policy);
  sync.registerCallback(
    [this](
      const ImuPtr & msg0, const ImuPtr & msg1, const NullPtr &, const NullPtr &, const NullPtr &,
      const NullPtr &, const NullPtr &, const NullPtr &, const NullPtr &) {
      callback_count_++;
      last_msg0_value_ = msg0->linear_acceleration.x;
      last_msg1_value_ = msg1->linear_acceleration.x;
    });

  auto msg0 = createImuMessage(5.0, 100, 0);
  auto msg1 = createImuMessage(10.0, 100, 0);

  // Act
  sync.add<0>(msg0);
  sync.add<1>(msg1);

  // Assert
  EXPECT_EQ(callback_count_, 1);
  EXPECT_DOUBLE_EQ(last_msg0_value_, 5.0);
  EXPECT_DOUBLE_EQ(last_msg1_value_, 10.0);
}

TEST_F(ExactSynchronizerTest, SynchronizerDropCallbackViaPolicy)
{
  // Arrange
  ExactTimePolicy policy(2);
  Synchronizer sync(policy);
  sync.registerCallback(
    [this](
      const ImuPtr &, const ImuPtr &, const NullPtr &, const NullPtr &, const NullPtr &,
      const NullPtr &, const NullPtr &, const NullPtr &, const NullPtr &) { callback_count_++; });
  sync.getPolicy()->registerDropCallback(
    [this](
      const ImuPtr &, const ImuPtr &, const NullPtr &, const NullPtr &, const NullPtr &,
      const NullPtr &, const NullPtr &, const NullPtr &, const NullPtr &) {
      drop_callback_count_++;
    });

  // Act - Add unmatched messages exceeding queue size
  for (int i = 0; i < 5; ++i) {
    auto msg0 = createImuMessage(static_cast<double>(i), i, 0);
    sync.add<0>(msg0);
  }

  // Assert
  EXPECT_EQ(callback_count_, 0);
  EXPECT_EQ(drop_callback_count_, 3);
}

TEST_F(ExactSynchronizerTest, SynchronizerGetPolicy)
{
  // Arrange
  ExactTimePolicy policy(10);
  Synchronizer sync(policy);

  // Act
  auto * retrieved_policy = sync.getPolicy();

  // Assert
  EXPECT_NE(retrieved_policy, nullptr);

  // Verify we can use the sync to register callback
  sync.registerCallback(
    [this](
      const ImuPtr &, const ImuPtr &, const NullPtr &, const NullPtr &, const NullPtr &,
      const NullPtr &, const NullPtr &, const NullPtr &, const NullPtr &) { callback_count_++; });

  auto msg0 = createImuMessage(1.0, 100, 0);
  auto msg1 = createImuMessage(2.0, 100, 0);
  sync.add<0>(msg0);
  sync.add<1>(msg1);

  EXPECT_EQ(callback_count_, 1);
}

TEST_F(ExactSynchronizerTest, SynchronizerSetNameGetName)
{
  // Arrange
  Synchronizer sync(ExactTimePolicy(10));

  // Act
  sync.setName("test_synchronizer");

  // Assert
  EXPECT_EQ(sync.getName(), "test_synchronizer");
}

TEST_F(ExactSynchronizerTest, ExactTimeOrderIndependent)
{
  // Arrange
  Synchronizer sync(ExactTimePolicy(10));
  sync.registerCallback(
    [this](
      const ImuPtr &, const ImuPtr &, const NullPtr &, const NullPtr &, const NullPtr &,
      const NullPtr &, const NullPtr &, const NullPtr &, const NullPtr &) { callback_count_++; });

  auto msg0 = createImuMessage(1.0, 100, 0);
  auto msg1 = createImuMessage(2.0, 100, 0);

  // Act - Add in reverse order (msg1 first, then msg0)
  sync.add<1>(msg1);
  sync.add<0>(msg0);

  // Assert
  EXPECT_EQ(callback_count_, 1);
}

TEST_F(ExactSynchronizerTest, ExactTimeNanosecondPrecision)
{
  // Arrange
  Synchronizer sync(ExactTimePolicy(10));
  sync.registerCallback(
    [this](
      const ImuPtr &, const ImuPtr &, const NullPtr &, const NullPtr &, const NullPtr &,
      const NullPtr &, const NullPtr &, const NullPtr &, const NullPtr &) { callback_count_++; });

  // Create messages with same sec but different nsec
  auto msg0 = createImuMessage(1.0, 100, 1);
  auto msg1 = createImuMessage(2.0, 100, 2);  // Different nanoseconds

  // Act
  sync.add<0>(msg0);
  sync.add<1>(msg1);

  // Assert - Should NOT match because nanoseconds differ
  EXPECT_EQ(callback_count_, 0);
}

TEST_F(ExactSynchronizerTest, ExactTimeExactNanosecondMatch)
{
  // Arrange
  Synchronizer sync(ExactTimePolicy(10));
  sync.registerCallback(
    [this](
      const ImuPtr &, const ImuPtr &, const NullPtr &, const NullPtr &, const NullPtr &,
      const NullPtr &, const NullPtr &, const NullPtr &, const NullPtr &) { callback_count_++; });

  // Create messages with exactly matching timestamp including nanoseconds
  auto msg0 = createImuMessage(1.0, 100, 500);
  auto msg1 = createImuMessage(2.0, 100, 500);

  // Act
  sync.add<0>(msg0);
  sync.add<1>(msg1);

  // Assert
  EXPECT_EQ(callback_count_, 1);
}

// =========================================
// New API Tests (signal, connectInput, Connection)
// =========================================

TEST_F(ExactSynchronizerTest, SynchronizerSignalMethod)
{
  // Arrange
  Synchronizer sync(ExactTimePolicy(10));
  sync.registerCallback(
    [this](
      const ImuPtr & msg0, const ImuPtr & msg1, const NullPtr &, const NullPtr &, const NullPtr &,
      const NullPtr &, const NullPtr &, const NullPtr &, const NullPtr &) {
      callback_count_++;
      last_msg0_value_ = msg0->linear_acceleration.x;
      last_msg1_value_ = msg1->linear_acceleration.x;
    });

  auto msg0 = createImuMessage(3.0, 100, 0);
  auto msg1 = createImuMessage(6.0, 100, 0);
  NullPtr null_ptr;

  // Act - Call signal directly
  sync.signal(msg0, msg1, null_ptr, null_ptr, null_ptr, null_ptr, null_ptr, null_ptr, null_ptr);

  // Assert
  EXPECT_EQ(callback_count_, 1);
  EXPECT_DOUBLE_EQ(last_msg0_value_, 3.0);
  EXPECT_DOUBLE_EQ(last_msg1_value_, 6.0);
}

TEST_F(ExactSynchronizerTest, SynchronizerMultipleCallbacks)
{
  // Arrange
  Synchronizer sync(ExactTimePolicy(10));
  int callback1_count = 0;
  int callback2_count = 0;

  sync.registerCallback(
    [&callback1_count](
      const ImuPtr &, const ImuPtr &, const NullPtr &, const NullPtr &, const NullPtr &,
      const NullPtr &, const NullPtr &, const NullPtr &, const NullPtr &) { callback1_count++; });
  sync.registerCallback(
    [&callback2_count](
      const ImuPtr &, const ImuPtr &, const NullPtr &, const NullPtr &, const NullPtr &,
      const NullPtr &, const NullPtr &, const NullPtr &, const NullPtr &) { callback2_count++; });

  auto msg0 = createImuMessage(1.0, 100, 0);
  auto msg1 = createImuMessage(2.0, 100, 0);

  // Act
  sync.add<0>(msg0);
  sync.add<1>(msg1);

  // Assert - Both callbacks should be called
  EXPECT_EQ(callback1_count, 1);
  EXPECT_EQ(callback2_count, 1);
}

TEST_F(ExactSynchronizerTest, RegisterCallbackReturnsConnection)
{
  // Arrange
  Synchronizer sync(ExactTimePolicy(10));
  int callback_count_local = 0;

  // Act
  auto connection = sync.registerCallback(
    [&callback_count_local](
      const ImuPtr &, const ImuPtr &, const NullPtr &, const NullPtr &, const NullPtr &,
      const NullPtr &, const NullPtr &, const NullPtr &, const NullPtr &) { callback_count_local++; });

  auto msg0 = createImuMessage(1.0, 100, 0);
  auto msg1 = createImuMessage(2.0, 100, 0);
  sync.add<0>(msg0);
  sync.add<1>(msg1);

  // Assert - Callback was called
  EXPECT_EQ(callback_count_local, 1);

  // Disconnect and verify
  connection.disconnect();
  auto msg2 = createImuMessage(1.0, 200, 0);
  auto msg3 = createImuMessage(2.0, 200, 0);
  sync.add<0>(msg2);
  sync.add<1>(msg3);

  // Assert - Callback should not be called after disconnect
  EXPECT_EQ(callback_count_local, 1);
}

TEST_F(ExactSynchronizerTest, RegisterDropCallbackReturnsConnection)
{
  // Arrange
  ExactTimePolicy policy(2);
  Synchronizer sync(policy);

  int drop_count = 0;
  auto connection = sync.getPolicy()->registerDropCallback(
    [&drop_count](
      const ImuPtr &, const ImuPtr &, const NullPtr &, const NullPtr &, const NullPtr &,
      const NullPtr &, const NullPtr &, const NullPtr &, const NullPtr &) { drop_count++; });

  // Act - Overflow queue
  for (int i = 0; i < 5; ++i) {
    auto msg0 = createImuMessage(static_cast<double>(i), i, 0);
    sync.add<0>(msg0);
  }

  // Assert - Drop callback was called
  EXPECT_EQ(drop_count, 3);

  // Disconnect and add more
  connection.disconnect();
  for (int i = 10; i < 15; ++i) {
    auto msg0 = createImuMessage(static_cast<double>(i), i, 0);
    sync.add<0>(msg0);
  }

  // Assert - Drop callback should not be called after disconnect
  EXPECT_EQ(drop_count, 3);
}

// Test class for member function callback
class CallbackHandler
{
public:
  void handleCallback(const ImuPtr & msg0, const ImuPtr & msg1)
  {
    callback_count_++;
    last_value_ = msg0->linear_acceleration.x + msg1->linear_acceleration.x;
  }

  int callback_count_ = 0;
  double last_value_ = 0.0;
};

TEST_F(ExactSynchronizerTest, RegisterCallbackWithMemberFunction)
{
  // Arrange
  Synchronizer sync(ExactTimePolicy(10));
  CallbackHandler handler;

  sync.registerCallback(&CallbackHandler::handleCallback, &handler);

  auto msg0 = createImuMessage(5.0, 100, 0);
  auto msg1 = createImuMessage(7.0, 100, 0);

  // Act
  sync.add<0>(msg0);
  sync.add<1>(msg1);

  // Assert
  EXPECT_EQ(handler.callback_count_, 1);
  EXPECT_DOUBLE_EQ(handler.last_value_, 12.0);
}
