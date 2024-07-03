#pragma once

#include <fcntl.h>
#include <mqueue.h>
#include <semaphore.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>
#include <atomic>
#include <cstdint>
#include <cstring>
#include <functional>
#include <iostream>
#include <memory>
#include <thread>
#include <vector>
#include <chrono>
#include <sys/ioctl.h>

#include "agnocast_publisher.hpp"
#include "agnocast_subscription.hpp"

namespace agnocast {

void initialize_agnocast();

template<typename MessageT>
std::shared_ptr<Publisher<MessageT>> create_publisher(std::string topic_name) {
  initialize_agnocast();

  return std::make_shared<Publisher<MessageT>>(topic_name);
}

template<typename MessageT>
std::shared_ptr<Subscription<MessageT>> create_subscription(const char* topic_name, std::function<void(const agnocast::message_ptr<MessageT> &)> callback) {
  initialize_agnocast();

  subscribe_topic_agnocast(topic_name, callback);
  return std::make_shared<Subscription<MessageT>>();
}

} // namespace agnocast
