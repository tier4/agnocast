#pragma once

#include <fcntl.h>
#include <mqueue.h>
#include <semaphore.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>
#include <cstring>
#include <functional>
#include <memory>
#include <sys/ioctl.h>

#include "agnocast_publisher.hpp"
#include "agnocast_subscription.hpp"

namespace agnocast {

void initialize_agnocast();

template<typename MessageT>
std::shared_ptr<Publisher<MessageT>> create_publisher(std::string topic_name) {
  return std::make_shared<Publisher<MessageT>>(topic_name);
}

template<typename MessageT>
std::shared_ptr<Subscription<MessageT>> create_subscription(const char* topic_name, std::function<void(const agnocast::message_ptr<MessageT> &)> callback) {
  subscribe_topic_agnocast(topic_name, callback);
  return std::make_shared<Subscription<MessageT>>();
}

} // namespace agnocast
