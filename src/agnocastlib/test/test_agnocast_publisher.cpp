#include "agnocast.hpp"
#include "agnocast_publisher.hpp"

#include "std_msgs/msg/int32.hpp"

#include <gmock-global/gmock-global.h>
#include <gmock/gmock.h>

MOCK_GLOBAL_FUNC2(
  initialize_publisher, void(uint32_t publisher_pid, const std::string & topic_name));
MOCK_GLOBAL_FUNC5(
  borrow_loaned_message_core,
  std::vector<uint64_t>(
    const std::string & topic_name, uint32_t publisher_pid, uint32_t qos_depth,
    uint64_t msg_virtual_address, uint64_t timestamp));
MOCK_GLOBAL_FUNC4(
  publish_core, void(
                  const std::string & topic_name, uint32_t publisher_pid, uint64_t timestamp,
                  std::unordered_map<std::string, mqd_t> & opened_mqs));

using testing::_;

class AgnocastPublisherTest : public ::testing::Test
{
protected:
  void SetUp() override
  {
    rclcpp::init(0, nullptr);
    pid = getpid();
    dummy_tn = "dummy";
    node = std::make_shared<rclcpp::Node>(dummy_tn);
    dummy_qd = 10;
    EXPECT_GLOBAL_CALL(initialize_publisher, initialize_publisher(pid, dummy_tn)).Times(1);
    dummy_publisher =
      agnocast::create_publisher<std_msgs::msg::Int32>(node.get(), dummy_tn, dummy_qd);
  }

  void TearDown() override { rclcpp::shutdown(); }

  std::shared_ptr<rclcpp::Node> node;
  agnocast::Publisher<std_msgs::msg::Int32>::SharedPtr dummy_publisher;
  uint32_t pid;
  std::string dummy_tn;
  uint32_t dummy_qd;
};

TEST_F(AgnocastPublisherTest, test_publish_normal)
{
  EXPECT_GLOBAL_CALL(
    borrow_loaned_message_core, borrow_loaned_message_core(dummy_tn, pid, dummy_qd, _, _))
    .WillOnce(testing::Return(std::vector<uint64_t>()));
  EXPECT_GLOBAL_CALL(publish_core, publish_core(dummy_tn, pid, _, _)).Times(1);
  agnocast::ipc_shared_ptr<std_msgs::msg::Int32> message = dummy_publisher->borrow_loaned_message();

  dummy_publisher->publish(std::move(message));
}

TEST_F(AgnocastPublisherTest, test_publish_null_message)
{
  EXPECT_GLOBAL_CALL(publish_core, publish_core(dummy_tn, pid, _, _)).Times(0);
  agnocast::ipc_shared_ptr<std_msgs::msg::Int32> message;

  EXPECT_EXIT(
    dummy_publisher->publish(std::move(message)), ::testing::ExitedWithCode(EXIT_FAILURE),
    "Invalid message to publish.");
}

TEST_F(AgnocastPublisherTest, test_publish_already_published_message)
{
  EXPECT_GLOBAL_CALL(
    borrow_loaned_message_core, borrow_loaned_message_core(dummy_tn, pid, dummy_qd, _, _))
    .WillOnce(testing::Return(std::vector<uint64_t>()));
  EXPECT_GLOBAL_CALL(publish_core, publish_core(dummy_tn, pid, _, _)).Times(1);
  agnocast::ipc_shared_ptr<std_msgs::msg::Int32> message = dummy_publisher->borrow_loaned_message();

  dummy_publisher->publish(std::move(message));

  EXPECT_EXIT(
    dummy_publisher->publish(std::move(message)), ::testing::ExitedWithCode(EXIT_FAILURE),
    "Invalid message to publish.");
}

TEST_F(AgnocastPublisherTest, test_publish_different_message)
{
  std::string diff_dummy_tn = "dummy2";
  EXPECT_GLOBAL_CALL(initialize_publisher, initialize_publisher(pid, diff_dummy_tn)).Times(1);
  EXPECT_GLOBAL_CALL(borrow_loaned_message_core, borrow_loaned_message_core(_, pid, _, _, _))
    .WillRepeatedly(testing::Return(std::vector<uint64_t>()));
  EXPECT_GLOBAL_CALL(publish_core, publish_core(dummy_tn, pid, _, _)).Times(0);
  agnocast::Publisher<std_msgs::msg::Int32>::SharedPtr diff_publisher =
    agnocast::create_publisher<std_msgs::msg::Int32>(node.get(), diff_dummy_tn, 10);
  agnocast::ipc_shared_ptr<std_msgs::msg::Int32> diff_message =
    diff_publisher->borrow_loaned_message();
  agnocast::ipc_shared_ptr<std_msgs::msg::Int32> message = dummy_publisher->borrow_loaned_message();

  EXPECT_EXIT(
    dummy_publisher->publish(std::move(diff_message)), ::testing::ExitedWithCode(EXIT_FAILURE),
    "Invalid message to publish.");
}
