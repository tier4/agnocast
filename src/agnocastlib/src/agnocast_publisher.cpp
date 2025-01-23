#include "agnocast_publisher.hpp"

using namespace agnocast;

thread_local uint32_t borrowed_publisher_num = 0;

extern "C" uint32_t agnocast::get_borrowed_publisher_num()
{
  return borrowed_publisher_num;
}

void increment_borrowed_publisher_num()
{
  borrowed_publisher_num++;
}

void decrement_borrowed_publisher_num()
{
  if (borrowed_publisher_num == 0) {
    RCLCPP_ERROR(
      logger,
      "The number of publish() called exceeds the number of borrow_loaned_message() called.");
    exit(EXIT_FAILURE);
  }
  borrowed_publisher_num--;
}

void publish_core(
  const std::string & topic_name, const uint32_t publisher_index, const uint64_t timestamp,
  std::unordered_map<std::string, mqd_t> & opened_mqs)
{
  union ioctl_publish_args publish_args = {};
  publish_args.topic_name = topic_name.c_str();
  publish_args.publisher_index = publisher_index;
  publish_args.msg_timestamp = timestamp;
  if (ioctl(agnocast_fd, AGNOCAST_PUBLISH_MSG_CMD, &publish_args) < 0) {
    RCLCPP_ERROR(logger, "AGNOCAST_PUBLISH_MSG_CMD failed: %s", strerror(errno));
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  for (uint32_t i = 0; i < publish_args.ret_subscriber_num; i++) {
    const uint32_t subscriber_index = publish_args.ret_subscriber_indexes[i];

    const std::string mq_name = create_mq_name(topic_name, subscriber_index);
    mqd_t mq = 0;
    if (opened_mqs.find(mq_name) != opened_mqs.end()) {
      mq = opened_mqs[mq_name];
    } else {
      mq = mq_open(mq_name.c_str(), O_WRONLY | O_NONBLOCK);
      if (mq == -1) {
        RCLCPP_ERROR(logger, "mq_open failed: %s", strerror(errno));
        continue;
      }
      opened_mqs.insert({mq_name, mq});
    }

    struct MqMsgAgnocast mq_msg = {};
    if (mq_send(mq, reinterpret_cast<char *>(&mq_msg), sizeof(mq_msg), 0) == -1) {
      // If it returns EAGAIN, it means mq_send has already been executed, but the subscriber
      // hasn't received it yet. Thus, there's no need to send it again since the notification has
      // already been sent.
      if (errno != EAGAIN) {
        RCLCPP_ERROR(logger, "mq_send failed: %s", strerror(errno));
      }
    }
  }
}

std::vector<uint64_t> borrow_loaned_message_core(
  const std::string & topic_name, const uint32_t publisher_index, const uint32_t qos_depth,
  const uint64_t msg_virtual_address, const uint64_t timestamp)
{
  union ioctl_enqueue_and_release_args ioctl_args = {};
  ioctl_args.topic_name = topic_name.c_str();
  ioctl_args.publisher_index = publisher_index;
  ioctl_args.qos_depth = qos_depth;
  ioctl_args.msg_virtual_address = msg_virtual_address;
  ioctl_args.timestamp = timestamp;
  if (ioctl(agnocast_fd, AGNOCAST_ENQUEUE_AND_RELEASE_CMD, &ioctl_args) < 0) {
    RCLCPP_ERROR(logger, "AGNOCAST_ENQUEUE_AND_RELEASE_CMD failed: %s", strerror(errno));
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  std::vector<uint64_t> addresses(ioctl_args.ret_len);
  std::copy_n(
    static_cast<const uint64_t *>(ioctl_args.ret_released_addrs), ioctl_args.ret_len,
    addresses.begin());
  return addresses;
}

uint32_t get_subscription_count_core(const std::string & topic_name)
{
  union ioctl_get_subscriber_num_args get_subscriber_count_args = {};
  get_subscriber_count_args.topic_name = topic_name.c_str();
  if (ioctl(agnocast_fd, AGNOCAST_GET_SUBSCRIBER_NUM_CMD, &get_subscriber_count_args) < 0) {
    RCLCPP_ERROR(logger, "AGNOCAST_GET_SUBSCRIBER_NUM_CMD failed: %s", strerror(errno));
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  return get_subscriber_count_args.ret_subscriber_num;
}
