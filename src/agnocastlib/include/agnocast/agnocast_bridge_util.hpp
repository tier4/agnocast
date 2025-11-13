#pragma once

#include "agnocast/agnocast_bridge_node.hpp"
#include "rclcpp/rclcpp.hpp"

#include <dlfcn.h>
#include <mqueue.h>

namespace agnocast
{

QoSFlat flatten_qos(const rclcpp::QoS & qos);

void safe_strncpy(char * dest, const char * src, size_t dest_size);

template <typename MessageT>
void send_bridge_request(
  const std::string & topic_name, const rclcpp::QoS & qos, BridgeDirection direction)
{
  (void)qos;

  const std::string mq_name_str = create_mq_name_for_bridge();
  const char * mq_name = mq_name_str.c_str();
  mqd_t mq = mq_open(mq_name, O_WRONLY);

  if (mq == (mqd_t)-1) {
    RCLCPP_ERROR(
      logger, "Failed to open bridge manager message queue '%s'. Error: %s", mq_name,
      strerror(errno));
    return;
  }

  BridgeFn fn = &start_bridge_node<MessageT>;

  Dl_info info{};
  if (dladdr(reinterpret_cast<void *>(fn), &info) == 0) {
    throw std::runtime_error("dladdr failed");
  }

  MqMsgBridge msg = {};

  safe_strncpy(msg.shared_lib_path, info.dli_fname, MAX_NAME_LENGTH);
  const char * symbol_name = info.dli_sname ? info.dli_sname : "__MAIN_EXECUTABLE__";
  safe_strncpy(msg.symbol_name, symbol_name, MAX_NAME_LENGTH);
  msg.fn_ptr = reinterpret_cast<uintptr_t>(fn);
  msg.direction = direction;
  safe_strncpy(msg.args.topic_name, topic_name.c_str(), sizeof(msg.args.topic_name));
  msg.args.qos = flatten_qos(qos);

  if (mq_send(mq, (const char *)&msg, sizeof(msg), 0) == -1) {
    RCLCPP_ERROR(
      logger, "Failed to send bridge request via mq '%s'. Error: %s", mq_name, strerror(errno));
  }

  mq_close(mq);
}

}  // namespace agnocast
