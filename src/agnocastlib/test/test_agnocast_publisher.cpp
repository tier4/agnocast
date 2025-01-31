#include "agnocast.hpp"
#include "agnocast_publisher.hpp"

#include "std_msgs/msg/int32.hpp"

#include <gmock-global/gmock-global.h>
#include <gmock/gmock.h>

using namespace agnocast;
using testing::_;

MOCK_GLOBAL_FUNC2(
  initialize_publisher_mock,
  topic_local_id_t(const pid_t publisher_pid, const std::string & topic_name));
MOCK_GLOBAL_FUNC5(
  borrow_loaned_message_core_mock,
  std::vector<uint64_t>(
    const std::string & topic_name, const topic_local_id_t publisher_id, const uint32_t qos_depth,
    const uint64_t msg_virtual_address, const uint64_t timestamp));
MOCK_GLOBAL_FUNC4(
  publish_core_mock,
  void(
    const std::string & topic_name, const topic_local_id_t publisher_id, const uint64_t timestamp,
    std::unordered_map<std::string, mqd_t> & opened_mqs));

namespace agnocast
{
topic_local_id_t initialize_publisher(const pid_t publisher_pid, const std::string & topic_name)
{
  return initialize_publisher_mock(publisher_pid, topic_name);
}
std::vector<uint64_t> borrow_loaned_message_core(
  const std::string & topic_name, const topic_local_id_t publisher_id, const uint32_t qos_depth,
  const uint64_t msg_virtual_address, const uint64_t timestamp)
{
  return borrow_loaned_message_core_mock(
    topic_name, publisher_id, qos_depth, msg_virtual_address, timestamp);
}
void publish_core(
  const std::string & topic_name, const topic_local_id_t publisher_id, const uint64_t timestamp,
  std::unordered_map<std::string, mqd_t> & opened_mqs)
{
  publish_core_mock(topic_name, publisher_id, timestamp, opened_mqs);
}
}  // namespace agnocast

class AgnocastPublisherTest : public ::testing::Test
{
protected:
  void SetUp() override
  {
    rclcpp::init(0, nullptr);
    dummy_tn = "/dummy";
    id = -1;
    pid = getpid();
    node = std::make_shared<rclcpp::Node>("dummy_node");
    dummy_qd = 10;
    EXPECT_GLOBAL_CALL(initialize_publisher_mock, initialize_publisher_mock(pid, dummy_tn))
      .Times(1);
    dummy_publisher =
      agnocast::create_publisher<std_msgs::msg::Int32>(node.get(), dummy_tn, dummy_qd);
  }

  void TearDown() override { rclcpp::shutdown(); }

  std::shared_ptr<rclcpp::Node> node;
  agnocast::Publisher<std_msgs::msg::Int32>::SharedPtr dummy_publisher;
  std::string dummy_tn;
  topic_local_id_t id;
  pid_t pid;
  uint32_t dummy_qd;
};

TEST_F(AgnocastPublisherTest, test_publish_normal)
{
  EXPECT_GLOBAL_CALL(
    borrow_loaned_message_core_mock, borrow_loaned_message_core_mock(dummy_tn, _, dummy_qd, _, _))
    .WillOnce(testing::Return(std::vector<uint64_t>()));
  EXPECT_GLOBAL_CALL(publish_core_mock, publish_core_mock(dummy_tn, _, _, _)).Times(1);
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
  EXPECT_GLOBAL_CALL(
    borrow_loaned_message_core_mock, borrow_loaned_message_core_mock(dummy_tn, _, _, _, _))
    .WillOnce(testing::Return(std::vector<uint64_t>()));
  EXPECT_GLOBAL_CALL(publish_core_mock, publish_core_mock(dummy_tn, _, _, _)).Times(1);

  agnocast::ipc_shared_ptr<std_msgs::msg::Int32> message = dummy_publisher->borrow_loaned_message();

  dummy_publisher->publish(std::move(message));

  EXPECT_EXIT(
    dummy_publisher->publish(std::move(message)), ::testing::ExitedWithCode(EXIT_FAILURE),
    "Invalid message to publish.");
}

TEST_F(AgnocastPublisherTest, test_publish_different_message)
{
  std::string diff_dummy_tn = "/dummy2";
  EXPECT_GLOBAL_CALL(initialize_publisher_mock, initialize_publisher_mock(pid, diff_dummy_tn))
    .Times(1);
  EXPECT_GLOBAL_CALL(
    borrow_loaned_message_core_mock,
    borrow_loaned_message_core_mock(diff_dummy_tn, _, dummy_qd, _, _))
    .WillOnce(testing::Return(std::vector<uint64_t>()));
  EXPECT_GLOBAL_CALL(
    borrow_loaned_message_core_mock, borrow_loaned_message_core_mock(dummy_tn, _, dummy_qd, _, _))
    .WillOnce(testing::Return(std::vector<uint64_t>()));
  EXPECT_GLOBAL_CALL(publish_core_mock, publish_core_mock(dummy_tn, _, _, _)).Times(0);

  agnocast::Publisher<std_msgs::msg::Int32>::SharedPtr diff_publisher =
    agnocast::create_publisher<std_msgs::msg::Int32>(node.get(), diff_dummy_tn, dummy_qd);
  agnocast::ipc_shared_ptr<std_msgs::msg::Int32> diff_message =
    diff_publisher->borrow_loaned_message();
  agnocast::ipc_shared_ptr<std_msgs::msg::Int32> message = dummy_publisher->borrow_loaned_message();

  EXPECT_EXIT(
    dummy_publisher->publish(std::move(diff_message)), ::testing::ExitedWithCode(EXIT_FAILURE),
    "Invalid message to publish.");
}
