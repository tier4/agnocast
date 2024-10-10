#include "agnocast_publisher.hpp"

namespace agnocast
{

void validate_ld_preload();
std::string create_mq_name(const std::string & topic_name, const uint32_t pid);

void initialize_publisher(uint32_t publisher_pid, const std::string & topic_name)
{
  validate_ld_preload();

  union ioctl_publisher_args pub_args;
  pub_args.publisher_pid = publisher_pid;
  pub_args.topic_name = topic_name.c_str();
  if (ioctl(agnocast_fd, AGNOCAST_PUBLISHER_ADD_CMD, &pub_args) < 0) {
    RCLCPP_ERROR(logger, "AGNOCAST_PUBLISHER_ADD_CMD failed: %s", strerror(errno));
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  // Send messages to subscribers to notify that a new publisher appears
  for (uint32_t i = 0; i < pub_args.ret_subscriber_len; i++) {
    if (pub_args.ret_subscriber_pids[i] == publisher_pid) {
      /*
       * NOTE: In ROS2, communication should work fine even if the same process exists as both a
       * publisher and a subscriber for a given topic. However, in Agnocast, to avoid applying
       * Agnocast to topic communication within a component container, the system will explicitly
       * fail with an error during initialization.
       */
      RCLCPP_ERROR(
        logger,
        "This process (pid=%d) already exists in the topic (topic_name=%s) "
        "as a publisher.",
        publisher_pid, topic_name.c_str());
      exit(EXIT_FAILURE);
    }
    const std::string mq_name = "/new_publisher@" + std::to_string(pub_args.ret_subscriber_pids[i]);
    mqd_t mq = mq_open(mq_name.c_str(), O_WRONLY);
    if (mq == -1) {
      RCLCPP_ERROR(logger, "mq_open for new publisher failed: %s", strerror(errno));
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }

    MqMsgNewPublisher mq_msg;
    mq_msg.publisher_pid = publisher_pid;
    mq_msg.shm_addr = pub_args.ret_shm_addr;
    mq_msg.shm_size = pub_args.ret_shm_size;
    if (mq_send(mq, reinterpret_cast<char *>(&mq_msg), sizeof(mq_msg), 0) == -1) {
      RCLCPP_ERROR(logger, "mq_send for new publisher failed: %s", strerror(errno));
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }
  }
}

void publish_core(const std::string & topic_name, uint32_t publisher_pid, uint64_t timestamp)
{
  union ioctl_publish_args publish_args;
  publish_args.topic_name = topic_name.c_str();
  publish_args.publisher_pid = publisher_pid;
  publish_args.msg_timestamp = timestamp;
  if (ioctl(agnocast_fd, AGNOCAST_PUBLISH_MSG_CMD, &publish_args) < 0) {
    RCLCPP_ERROR(logger, "AGNOCAST_PUBLISH_MSG_CMD failed: %s", strerror(errno));
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  for (uint32_t i = 0; i < publish_args.ret_len; i++) {
    uint32_t pid = publish_args.ret_pids[i];

    const std::string mq_name = create_mq_name(topic_name, pid);
    mqd_t mq = mq_open(mq_name.c_str(), O_WRONLY | O_NONBLOCK);
    if (mq == -1) {
      RCLCPP_ERROR(logger, "mq_open failed: %s", strerror(errno));
      continue;
    }

    struct MqMsgAgnocast mq_msg;
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

uint32_t get_subscription_count_core(const std::string & topic_name)
{
  union ioctl_get_subscriber_num_args get_subscriber_count_args;
  get_subscriber_count_args.topic_name = topic_name.c_str();
  if (ioctl(agnocast_fd, AGNOCAST_GET_SUBSCRIBER_NUM_CMD, &get_subscriber_count_args) < 0) {
    RCLCPP_ERROR(logger, "AGNOCAST_GET_SUBSCRIBER_NUM_CMD failed: %s", strerror(errno));
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  return get_subscriber_count_args.ret_subscriber_num;
}

}  // namespace agnocast
