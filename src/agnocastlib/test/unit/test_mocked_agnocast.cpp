#include "agnocast.hpp"
#include "agnocast_callback_info.hpp"
#include "agnocast_publisher.hpp"
#include "agnocast_smart_pointer.hpp"
#include "rclcpp/rclcpp.hpp"

#include "std_msgs/msg/int32.hpp"

#include <gmock-global/gmock-global.h>
#include <gmock/gmock.h>

using namespace agnocast;
using testing::_;

MOCK_GLOBAL_FUNC3(
  decrement_rc_mock, void(const std::string &, const topic_local_id_t, const int64_t));
MOCK_GLOBAL_FUNC3(
  increment_rc_mock, void(const std::string &, const topic_local_id_t, const int64_t));
MOCK_GLOBAL_FUNC3(
  initialize_publisher_mock,
  topic_local_id_t(const pid_t, const std::string &, const rclcpp::QoS &));
MOCK_GLOBAL_FUNC5(
  publish_core_mock, union ioctl_publish_args(
                       const void *, const std::string &, const topic_local_id_t, const uint64_t,
                       std::unordered_map<std::string, mqd_t> &));

namespace agnocast
{
void decrement_rc(const std::string & tn, const topic_local_id_t sub_id, const int64_t entry_id)
{
  decrement_rc_mock(tn, sub_id, entry_id);
}
void increment_rc(const std::string & tn, const topic_local_id_t sub_id, const int64_t entry_id)
{
  increment_rc_mock(tn, sub_id, entry_id);
}
topic_local_id_t initialize_publisher(
  const pid_t publisher_pid, const std::string & topic_name, const rclcpp::QoS & qos)
{
  return initialize_publisher_mock(publisher_pid, topic_name, qos);
}
union ioctl_publish_args publish_core(
  const void * publisher_handle, const std::string & topic_name,
  const topic_local_id_t publisher_id, const uint64_t msg_virtual_address,
  std::unordered_map<std::string, mqd_t> & opened_mqs)
{
  return publish_core_mock(
    publisher_handle, topic_name, publisher_id, msg_virtual_address, opened_mqs);
}
}  // namespace agnocast

// =========================================
// Publisher tests
// =========================================

class AgnocastPublisherTest : public ::testing::Test
{
protected:
  void SetUp() override
  {
    rclcpp::init(0, nullptr);
    dummy_tn = "/dummy";
    pid = getpid();
    node = std::make_shared<rclcpp::Node>("dummy_node");
    EXPECT_GLOBAL_CALL(
      initialize_publisher_mock, initialize_publisher_mock(pid, dummy_tn, dummy_qos))
      .Times(1);
    dummy_publisher =
      agnocast::create_publisher<std_msgs::msg::Int32>(node.get(), dummy_tn, dummy_qos);
  }

  void TearDown() override { rclcpp::shutdown(); }

  std::shared_ptr<rclcpp::Node> node;
  agnocast::Publisher<std_msgs::msg::Int32>::SharedPtr dummy_publisher;
  std::string dummy_tn;
  pid_t pid;
  rclcpp::QoS dummy_qos{10};
};

TEST_F(AgnocastPublisherTest, test_publish_normal)
{
  EXPECT_GLOBAL_CALL(decrement_rc_mock, decrement_rc_mock(dummy_tn, _, _)).Times(1);
  EXPECT_GLOBAL_CALL(publish_core_mock, publish_core_mock(_, dummy_tn, _, _, _)).Times(1);
  agnocast::ipc_shared_ptr<std_msgs::msg::Int32> message = dummy_publisher->borrow_loaned_message();
  dummy_publisher->publish(std::move(message));
}

TEST_F(AgnocastPublisherTest, test_publish_null_message)
{
  agnocast::ipc_shared_ptr<std_msgs::msg::Int32> message;

  EXPECT_EXIT(
    dummy_publisher->publish(std::move(message)), ::testing::ExitedWithCode(EXIT_FAILURE),
    "Invalid message to publish.");
}

TEST_F(AgnocastPublisherTest, test_publish_already_published_message)
{
  EXPECT_GLOBAL_CALL(decrement_rc_mock, decrement_rc_mock(dummy_tn, _, _)).Times(1);
  EXPECT_GLOBAL_CALL(publish_core_mock, publish_core_mock(_, dummy_tn, _, _, _)).Times(1);

  agnocast::ipc_shared_ptr<std_msgs::msg::Int32> message = dummy_publisher->borrow_loaned_message();

  dummy_publisher->publish(std::move(message));

  EXPECT_EXIT(
    dummy_publisher->publish(std::move(message)), ::testing::ExitedWithCode(EXIT_FAILURE),
    "Invalid message to publish.");
}

TEST_F(AgnocastPublisherTest, test_publish_different_message)
{
  std::string diff_dummy_tn = "/dummy2";
  EXPECT_GLOBAL_CALL(decrement_rc_mock, decrement_rc_mock(dummy_tn, _, _)).Times(1);
  EXPECT_GLOBAL_CALL(decrement_rc_mock, decrement_rc_mock(diff_dummy_tn, _, _)).Times(1);
  EXPECT_GLOBAL_CALL(
    initialize_publisher_mock, initialize_publisher_mock(pid, diff_dummy_tn, dummy_qos))
    .Times(1);
  EXPECT_GLOBAL_CALL(publish_core_mock, publish_core_mock(_, dummy_tn, _, _, _)).Times(0);

  agnocast::Publisher<std_msgs::msg::Int32>::SharedPtr diff_publisher =
    agnocast::create_publisher<std_msgs::msg::Int32>(node.get(), diff_dummy_tn, dummy_qos);
  agnocast::ipc_shared_ptr<std_msgs::msg::Int32> diff_message =
    diff_publisher->borrow_loaned_message();
  agnocast::ipc_shared_ptr<std_msgs::msg::Int32> message = dummy_publisher->borrow_loaned_message();

  EXPECT_EXIT(
    dummy_publisher->publish(std::move(diff_message)), ::testing::ExitedWithCode(EXIT_FAILURE),
    "Invalid message to publish.");
}

// =========================================
// ipc_shared_ptr tests
// =========================================

class AgnocastSmartPointerTest : public ::testing::Test
{
protected:
  void SetUp() override
  {
    dummy_tn = "dummy";
    dummy_pubsub_id = 1;
    dummy_entry_id = 2;
  }

  std::string dummy_tn;
  topic_local_id_t dummy_pubsub_id;
  int64_t dummy_entry_id;
};

TEST_F(AgnocastSmartPointerTest, reset_normal)
{
  EXPECT_GLOBAL_CALL(
    decrement_rc_mock, decrement_rc_mock(dummy_tn, dummy_pubsub_id, dummy_entry_id))
    .Times(1);
  agnocast::ipc_shared_ptr<int> sut{new int(0), dummy_tn, dummy_pubsub_id, dummy_entry_id};

  sut.reset();

  EXPECT_EQ(nullptr, sut.get());
}

TEST_F(AgnocastSmartPointerTest, reset_nullptr)
{
  EXPECT_GLOBAL_CALL(decrement_rc_mock, decrement_rc_mock(_, _, _)).Times(0);
  std::shared_ptr<agnocast::ipc_shared_ptr<int>> sut;
  sut.reset();
}

TEST_F(AgnocastSmartPointerTest, copy_constructor_normal)
{
  EXPECT_GLOBAL_CALL(
    increment_rc_mock, increment_rc_mock(dummy_tn, dummy_pubsub_id, dummy_entry_id))
    .Times(1);
  EXPECT_GLOBAL_CALL(
    decrement_rc_mock, decrement_rc_mock(dummy_tn, dummy_pubsub_id, dummy_entry_id))
    .Times(2);
  agnocast::ipc_shared_ptr<int> sut{new int(0), dummy_tn, dummy_pubsub_id, dummy_entry_id};

  agnocast::ipc_shared_ptr<int> sut2 = sut;

  EXPECT_EQ(sut.get(), sut2.get());
  EXPECT_EQ(sut.get_topic_name(), sut2.get_topic_name());
  EXPECT_EQ(sut.get_entry_id(), sut2.get_entry_id());
}

TEST_F(AgnocastSmartPointerTest, copy_constructor_empty)
{
  EXPECT_GLOBAL_CALL(increment_rc_mock, increment_rc_mock(_, _, _)).Times(1);
  EXPECT_GLOBAL_CALL(decrement_rc_mock, decrement_rc_mock(_, _, _)).Times(0);

  agnocast::ipc_shared_ptr<int> sut;
  EXPECT_NO_THROW(agnocast::ipc_shared_ptr<int> sut2{sut});
}

TEST_F(AgnocastSmartPointerTest, copy_assignment_normal)
{
  int * ptr = new int(0);
  int * ptr2 = new int(1);
  std::string dummy_tn2 = "dummy2";
  topic_local_id_t dummy_pubsub_id2 = 2;
  int64_t dummy_entry_id2 = 3;

  EXPECT_GLOBAL_CALL(
    increment_rc_mock, increment_rc_mock(dummy_tn, dummy_pubsub_id, dummy_entry_id))
    .Times(1);
  EXPECT_GLOBAL_CALL(
    decrement_rc_mock, decrement_rc_mock(dummy_tn, dummy_pubsub_id, dummy_entry_id))
    .Times(2);
  EXPECT_GLOBAL_CALL(
    increment_rc_mock, increment_rc_mock(dummy_tn2, dummy_pubsub_id2, dummy_entry_id2))
    .Times(0);
  EXPECT_GLOBAL_CALL(
    decrement_rc_mock, decrement_rc_mock(dummy_tn2, dummy_pubsub_id2, dummy_entry_id2))
    .Times(1);

  agnocast::ipc_shared_ptr<int> sut{ptr, dummy_tn, dummy_pubsub_id, dummy_entry_id};
  agnocast::ipc_shared_ptr<int> sut2{ptr2, dummy_tn2, dummy_pubsub_id2, dummy_entry_id2};

  sut2 = sut;

  EXPECT_EQ(ptr, sut2.get());
  EXPECT_EQ(dummy_tn, sut2.get_topic_name());
  EXPECT_EQ(dummy_pubsub_id, sut2.get_pubsub_id());
  EXPECT_EQ(dummy_entry_id, sut2.get_entry_id());
}

TEST_F(AgnocastSmartPointerTest, copy_assignment_self)
{
  int * ptr = new int(0);

  EXPECT_GLOBAL_CALL(
    increment_rc_mock, increment_rc_mock(dummy_tn, dummy_pubsub_id, dummy_entry_id))
    .Times(0);
  EXPECT_GLOBAL_CALL(
    decrement_rc_mock, decrement_rc_mock(dummy_tn, dummy_pubsub_id, dummy_entry_id))
    .Times(1);

  agnocast::ipc_shared_ptr<int> sut{ptr, dummy_tn, dummy_pubsub_id, dummy_entry_id};

  sut = sut;

  EXPECT_EQ(ptr, sut.get());
  EXPECT_EQ(dummy_tn, sut.get_topic_name());
  EXPECT_EQ(dummy_pubsub_id, sut.get_pubsub_id());
  EXPECT_EQ(dummy_entry_id, sut.get_entry_id());
}

TEST_F(AgnocastSmartPointerTest, move_constructor_normal)
{
  int * ptr = new int(0);
  EXPECT_GLOBAL_CALL(
    increment_rc_mock, increment_rc_mock(dummy_tn, dummy_pubsub_id, dummy_entry_id))
    .Times(0);
  EXPECT_GLOBAL_CALL(
    decrement_rc_mock, decrement_rc_mock(dummy_tn, dummy_pubsub_id, dummy_entry_id))
    .Times(1);
  agnocast::ipc_shared_ptr<int> sut{ptr, dummy_tn, dummy_pubsub_id, dummy_entry_id};

  agnocast::ipc_shared_ptr<int> sut2 = std::move(sut);

  EXPECT_EQ(nullptr, sut.get());
  EXPECT_EQ(ptr, sut2.get());
  EXPECT_EQ(dummy_tn, sut2.get_topic_name());
  EXPECT_EQ(dummy_entry_id, sut2.get_entry_id());
}

TEST_F(AgnocastSmartPointerTest, move_assignment_normal)
{
  int * ptr = new int(0);
  EXPECT_GLOBAL_CALL(
    increment_rc_mock, increment_rc_mock(dummy_tn, dummy_pubsub_id, dummy_entry_id))
    .Times(0);
  EXPECT_GLOBAL_CALL(
    decrement_rc_mock, decrement_rc_mock(dummy_tn, dummy_pubsub_id, dummy_entry_id))
    .Times(1);
  agnocast::ipc_shared_ptr<int> sut{ptr, dummy_tn, dummy_pubsub_id, dummy_entry_id};

  agnocast::ipc_shared_ptr<int> sut2;
  sut2 = std::move(sut);

  EXPECT_EQ(nullptr, sut.get());
  EXPECT_EQ(ptr, sut2.get());
  EXPECT_EQ(dummy_tn, sut2.get_topic_name());
  EXPECT_EQ(dummy_entry_id, sut2.get_entry_id());
}

TEST_F(AgnocastSmartPointerTest, move_assignment_self)
{
  int * ptr = new int(0);
  EXPECT_GLOBAL_CALL(
    increment_rc_mock, increment_rc_mock(dummy_tn, dummy_pubsub_id, dummy_entry_id))
    .Times(0);
  EXPECT_GLOBAL_CALL(
    decrement_rc_mock, decrement_rc_mock(dummy_tn, dummy_pubsub_id, dummy_entry_id))
    .Times(1);
  agnocast::ipc_shared_ptr<int> sut{ptr, dummy_tn, dummy_pubsub_id, dummy_entry_id};

  sut = std::move(sut);

  EXPECT_EQ(ptr, sut.get());
  EXPECT_EQ(dummy_tn, sut.get_topic_name());
  EXPECT_EQ(dummy_entry_id, sut.get_entry_id());
}

TEST_F(AgnocastSmartPointerTest, dereference_operator)
{
  int * ptr = new int(0);
  EXPECT_GLOBAL_CALL(
    decrement_rc_mock, decrement_rc_mock(dummy_tn, dummy_pubsub_id, dummy_entry_id))
    .Times(1);
  agnocast::ipc_shared_ptr<int> sut{ptr, dummy_tn, dummy_pubsub_id, dummy_entry_id};

  int & result = *sut;

  EXPECT_EQ(ptr, &result);
}

TEST_F(AgnocastSmartPointerTest, arrow_operator)
{
  EXPECT_GLOBAL_CALL(
    decrement_rc_mock, decrement_rc_mock(dummy_tn, dummy_pubsub_id, dummy_entry_id))
    .Times(1);
  agnocast::ipc_shared_ptr<std::vector<int>> sut{
    new std::vector<int>{0}, dummy_tn, dummy_pubsub_id, dummy_entry_id};

  size_t result = sut->size();

  EXPECT_EQ(1, result);
}

TEST_F(AgnocastSmartPointerTest, bool_operator_true)
{
  EXPECT_GLOBAL_CALL(
    decrement_rc_mock, decrement_rc_mock(dummy_tn, dummy_pubsub_id, dummy_entry_id))
    .Times(1);
  agnocast::ipc_shared_ptr<int> sut{new int(0), dummy_tn, dummy_pubsub_id, dummy_entry_id};

  bool result = static_cast<bool>(sut);

  EXPECT_TRUE(result);
}

TEST_F(AgnocastSmartPointerTest, bool_operator_false)
{
  agnocast::ipc_shared_ptr<int> sut;

  bool result = static_cast<bool>(sut);

  EXPECT_FALSE(result);
}

// =========================================
// CallbackInfo tests
// =========================================

class AgnocastCallbackInfoTest : public ::testing::Test
{
protected:
  void SetUp() override
  {
    dummy_tn = "dummy";
    dummy_pubsub_id = 1;
  }

  std::string dummy_tn;
  topic_local_id_t dummy_pubsub_id;
};

TEST_F(AgnocastCallbackInfoTest, callback_first_arg)
{
  using FuncType = std::function<void(int, float)>;
  using FirstArgType = agnocast::callback_first_arg<FuncType>::type;
  EXPECT_TRUE((std::is_same<FirstArgType, int>::value));
}

TEST_F(AgnocastCallbackInfoTest, get_erased_callback_normal)
{
  EXPECT_GLOBAL_CALL(decrement_rc_mock, decrement_rc_mock(dummy_tn, dummy_pubsub_id, _)).Times(1);
  bool callback_called = false;
  int data = 0;
  agnocast::TypedMessagePtr<int> int_arg{
    agnocast::ipc_shared_ptr<int>(&data, dummy_tn, dummy_pubsub_id)};
  auto int_callback = [&](const agnocast::ipc_shared_ptr<int> & /*unused_arg*/) {
    callback_called = true;
  };

  agnocast::TypeErasedCallback erased_callback = agnocast::get_erased_callback<int>(int_callback);
  erased_callback(int_arg);

  EXPECT_TRUE(callback_called);
}

TEST_F(AgnocastCallbackInfoTest, get_erased_callback_invalid_type)
{
  EXPECT_GLOBAL_CALL(decrement_rc_mock, decrement_rc_mock(dummy_tn, dummy_pubsub_id, _)).Times(1);
  int data = 0;
  agnocast::TypedMessagePtr<int> int_arg{
    agnocast::ipc_shared_ptr<int>(&data, dummy_tn, dummy_pubsub_id)};
  auto float_callback = [&](agnocast::ipc_shared_ptr<float> /*unused_arg*/) {};

  agnocast::TypeErasedCallback erased_callback =
    agnocast::get_erased_callback<float>(float_callback);

  EXPECT_EXIT(
    erased_callback(int_arg), ::testing::ExitedWithCode(EXIT_FAILURE),
    "Agnocast internal implementation error: bad allocation when callback is called");
}
