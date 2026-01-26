// Copyright 2025 The Autoware Contributors
// SPDX-License-Identifier: Apache-2.0

#include "agnocast/message_filters/subscriber.hpp"
#include "agnocast/message_filters/sync_policies/exact_time.hpp"
#include "agnocast/message_filters/synchronizer.hpp"

#include <rclcpp/rclcpp.hpp>
#include <rclcpp_components/register_node_macro.hpp>

#include <message_filters/null_types.h>
#include <sensor_msgs/msg/imu.hpp>

#include <functional>

namespace agnocastlib_test
{

using ImuPtr = agnocast::ipc_shared_ptr<const sensor_msgs::msg::Imu>;
using NullP = const agnocast::ipc_shared_ptr<const message_filters::NullType> &;
using Policy =
  agnocast::message_filters::sync_policies::ExactTime<sensor_msgs::msg::Imu, sensor_msgs::msg::Imu>;
using Sync = agnocast::message_filters::Synchronizer<Policy>;
using Sub = agnocast::message_filters::Subscriber<sensor_msgs::msg::Imu>;

// Test 1: Member function pointer with 2 arguments
class TestMemberFunctionCallback : public rclcpp::Node
{
public:
  explicit TestMemberFunctionCallback(const rclcpp::NodeOptions & options)
  : Node("test_member_function_callback", options),
    callback_group_(this->create_callback_group(rclcpp::CallbackGroupType::Reentrant)),
    sub1_(this, "imu_topic1", rclcpp::QoS(10), agnocast::SubscriptionOptions{callback_group_}),
    sub2_(this, "imu_topic2", rclcpp::QoS(10), agnocast::SubscriptionOptions{callback_group_}),
    sync_(Policy(10), sub1_, sub2_)
  {
    sync_.registerCallback(&TestMemberFunctionCallback::callback, this);
  }

private:
  void callback(const ImuPtr &, const ImuPtr &)
  {
    RCLCPP_INFO(this->get_logger(), "MemberFunction: Synchronized");
  }

  rclcpp::CallbackGroup::SharedPtr callback_group_;
  Sub sub1_;
  Sub sub2_;
  Sync sync_;
};

// Test 2: Free function pointer with 2 arguments
void free_function_callback(const ImuPtr &, const ImuPtr &)
{
  RCLCPP_INFO(rclcpp::get_logger("free_function"), "FreeFunction: Synchronized");
}

class TestFreeFunctionCallback : public rclcpp::Node
{
public:
  explicit TestFreeFunctionCallback(const rclcpp::NodeOptions & options)
  : Node("test_free_function_callback", options),
    callback_group_(this->create_callback_group(rclcpp::CallbackGroupType::Reentrant)),
    sub1_(this, "imu_topic1", rclcpp::QoS(10), agnocast::SubscriptionOptions{callback_group_}),
    sub2_(this, "imu_topic2", rclcpp::QoS(10), agnocast::SubscriptionOptions{callback_group_}),
    sync_(Policy(10), sub1_, sub2_)
  {
    sync_.registerCallback(free_function_callback);
  }

private:
  rclcpp::CallbackGroup::SharedPtr callback_group_;
  Sub sub1_;
  Sub sub2_;
  Sync sync_;
};

// Test 3: Lambda with 9 arguments (generic callable)
class TestLambda9ArgsCallback : public rclcpp::Node
{
public:
  explicit TestLambda9ArgsCallback(const rclcpp::NodeOptions & options)
  : Node("test_lambda_9args_callback", options),
    callback_group_(this->create_callback_group(rclcpp::CallbackGroupType::Reentrant)),
    sub1_(this, "imu_topic1", rclcpp::QoS(10), agnocast::SubscriptionOptions{callback_group_}),
    sub2_(this, "imu_topic2", rclcpp::QoS(10), agnocast::SubscriptionOptions{callback_group_}),
    sync_(Policy(10), sub1_, sub2_)
  {
    auto lambda = [this](
                    const ImuPtr &, const ImuPtr &, NullP, NullP, NullP, NullP, NullP, NullP,
                    NullP) { RCLCPP_INFO(this->get_logger(), "Lambda9Args: Synchronized"); };
    sync_.registerCallback(lambda);
  }

private:
  rclcpp::CallbackGroup::SharedPtr callback_group_;
  Sub sub1_;
  Sub sub2_;
  Sync sync_;
};

// Test 4: std::function with explicit types
class TestStdFunctionCallback : public rclcpp::Node
{
public:
  explicit TestStdFunctionCallback(const rclcpp::NodeOptions & options)
  : Node("test_std_function_callback", options),
    callback_group_(this->create_callback_group(rclcpp::CallbackGroupType::Reentrant)),
    sub1_(this, "imu_topic1", rclcpp::QoS(10), agnocast::SubscriptionOptions{callback_group_}),
    sub2_(this, "imu_topic2", rclcpp::QoS(10), agnocast::SubscriptionOptions{callback_group_}),
    sync_(Policy(10), sub1_, sub2_)
  {
    std::function<void(const ImuPtr &, const ImuPtr &, NullP, NullP, NullP, NullP, NullP, NullP, NullP)>
      func = [this](
               const ImuPtr &, const ImuPtr &, NullP, NullP, NullP, NullP, NullP, NullP, NullP) {
        RCLCPP_INFO(this->get_logger(), "StdFunction: Synchronized");
      };
    sync_.registerCallback(func);
  }

private:
  rclcpp::CallbackGroup::SharedPtr callback_group_;
  Sub sub1_;
  Sub sub2_;
  Sync sync_;
};

// Test 5: std::bind expression with member function
class TestStdBindCallback : public rclcpp::Node
{
public:
  explicit TestStdBindCallback(const rclcpp::NodeOptions & options)
  : Node("test_std_bind_callback", options),
    callback_group_(this->create_callback_group(rclcpp::CallbackGroupType::Reentrant)),
    sub1_(this, "imu_topic1", rclcpp::QoS(10), agnocast::SubscriptionOptions{callback_group_}),
    sub2_(this, "imu_topic2", rclcpp::QoS(10), agnocast::SubscriptionOptions{callback_group_}),
    sync_(Policy(10), sub1_, sub2_)
  {
    auto bound = std::bind(
      &TestStdBindCallback::callback_impl, this, std::placeholders::_1, std::placeholders::_2,
      std::placeholders::_3, std::placeholders::_4, std::placeholders::_5, std::placeholders::_6,
      std::placeholders::_7, std::placeholders::_8, std::placeholders::_9);
    sync_.registerCallback(bound);
  }

private:
  void callback_impl(
    const ImuPtr &, const ImuPtr &, NullP, NullP, NullP, NullP, NullP, NullP, NullP)
  {
    RCLCPP_INFO(this->get_logger(), "StdBind: Synchronized");
  }

  rclcpp::CallbackGroup::SharedPtr callback_group_;
  Sub sub1_;
  Sub sub2_;
  Sync sync_;
};

// Test 6: connectInput method (policy-only constructor + connectInput)
class TestConnectInputCallback : public rclcpp::Node
{
public:
  explicit TestConnectInputCallback(const rclcpp::NodeOptions & options)
  : Node("test_connect_input_callback", options),
    callback_group_(this->create_callback_group(rclcpp::CallbackGroupType::Reentrant)),
    sub1_(this, "imu_topic1", rclcpp::QoS(10), agnocast::SubscriptionOptions{callback_group_}),
    sub2_(this, "imu_topic2", rclcpp::QoS(10), agnocast::SubscriptionOptions{callback_group_}),
    sync_(Policy(10))
  {
    sync_.connectInput(sub1_, sub2_);
    sync_.registerCallback(&TestConnectInputCallback::callback, this);
  }

private:
  void callback(const ImuPtr &, const ImuPtr &)
  {
    RCLCPP_INFO(this->get_logger(), "ConnectInput: Synchronized");
  }

  rclcpp::CallbackGroup::SharedPtr callback_group_;
  Sub sub1_;
  Sub sub2_;
  Sync sync_;
};

// Test 7: Signal1 - registerCallback directly on Subscriber (without synchronization)
class TestSubscriberDirectCallback : public rclcpp::Node
{
public:
  explicit TestSubscriberDirectCallback(const rclcpp::NodeOptions & options)
  : Node("test_subscriber_direct_callback", options),
    callback_group_(this->create_callback_group(rclcpp::CallbackGroupType::Reentrant)),
    sub1_(this, "imu_topic1", rclcpp::QoS(10), agnocast::SubscriptionOptions{callback_group_}),
    sub2_(this, "imu_topic2", rclcpp::QoS(10), agnocast::SubscriptionOptions{callback_group_})
  {
    // Register callbacks directly on each Subscriber using Signal1
    sub1_.registerCallback(&TestSubscriberDirectCallback::callback1, this);
    sub2_.registerCallback(&TestSubscriberDirectCallback::callback2, this);
  }

private:
  void callback1(const ImuPtr &)
  {
    RCLCPP_INFO(this->get_logger(), "Signal1-Sub1: Received");
  }

  void callback2(const ImuPtr &)
  {
    RCLCPP_INFO(this->get_logger(), "Signal1-Sub2: Received");
  }

  rclcpp::CallbackGroup::SharedPtr callback_group_;
  Sub sub1_;
  Sub sub2_;
};

}  // namespace agnocastlib_test

RCLCPP_COMPONENTS_REGISTER_NODE(agnocastlib_test::TestSubscriberDirectCallback)
RCLCPP_COMPONENTS_REGISTER_NODE(agnocastlib_test::TestMemberFunctionCallback)
RCLCPP_COMPONENTS_REGISTER_NODE(agnocastlib_test::TestFreeFunctionCallback)
RCLCPP_COMPONENTS_REGISTER_NODE(agnocastlib_test::TestLambda9ArgsCallback)
RCLCPP_COMPONENTS_REGISTER_NODE(agnocastlib_test::TestStdFunctionCallback)
RCLCPP_COMPONENTS_REGISTER_NODE(agnocastlib_test::TestStdBindCallback)
RCLCPP_COMPONENTS_REGISTER_NODE(agnocastlib_test::TestConnectInputCallback)
