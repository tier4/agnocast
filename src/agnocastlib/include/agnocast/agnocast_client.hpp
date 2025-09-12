#pragma once

#include "agnocast/agnocast_ioctl.hpp"
#include "agnocast/agnocast_publisher.hpp"
#include "agnocast/agnocast_smart_pointer.hpp"
#include "agnocast/agnocast_subscription.hpp"
#include "rclcpp/rclcpp.hpp"

#include <atomic>
#include <chrono>
#include <cstdlib>
#include <functional>
#include <future>
#include <memory>
#include <mutex>
#include <string>
#include <unordered_map>
#include <utility>

namespace agnocast
{

bool wait_for_service_nanoseconds(
  rclcpp::Context::SharedPtr context, const std::string & service_name,
  std::chrono::nanoseconds timeout);

extern int agnocast_fd;

template <typename ServiceT>
class Client
{
public:
  // To avoid name conflicts, members of RequestT and ResponseT are given an underscore prefix.
  struct RequestT : public ServiceT::Request
  {
    std::string _node_name;
    uint64_t _sequence_number;
  };
  struct ResponseT : public ServiceT::Response
  {
    std::string _node_name;
    uint64_t _sequence_number;
  };

  using SharedPtr = std::shared_ptr<Client<ServiceT>>;
  using SharedFuture = std::shared_future<ipc_shared_ptr<ResponseT>>;

private:
  struct RequestInfo
  {
    std::promise<ipc_shared_ptr<ResponseT>> promise;
    std::optional<std::function<void(SharedFuture)>> callback;

    RequestInfo() = default;
    explicit RequestInfo(std::function<void(SharedFuture)> && cb) : callback(std::move(cb)) {}
  };

  std::atomic<uint64_t> next_sequence_number_;
  std::mutex seqno2_request_info_mtx_;
  std::unordered_map<uint64_t, RequestInfo> seqno2_request_info_;
  rclcpp::Node * node_;
  const std::string service_name_;
  typename AgnocastOnlyPublisher<RequestT>::SharedPtr publisher_;
  typename Subscription<ResponseT>::SharedPtr subscriber_;

public:
  Client(
    rclcpp::Node * node, const std::string & service_name, const rclcpp::QoS & qos,
    rclcpp::CallbackGroup::SharedPtr group)
  : node_(node),
    service_name_(node_->get_node_services_interface()->resolve_service_name(service_name)),
    publisher_(
      std::make_shared<AgnocastOnlyPublisher<RequestT>>(node, service_name_ + "_request", qos))
  {
    auto subscriber_callback = [this](ipc_shared_ptr<ResponseT> && response) {
      if (response->_node_name != node_->get_fully_qualified_name()) {
        // not a response for this client
        return;
      }

      std::unique_lock<std::mutex> lock(seqno2_request_info_mtx_);
      /* --- critical section begin --- */
      // Get the corresponding RequestInfo and remove it from the map
      auto it = seqno2_request_info_.find(response->_sequence_number);
      if (it == seqno2_request_info_.end()) {
        lock.unlock();
        RCLCPP_ERROR(
          node_->get_logger(), "Agnocast internal implementation error: bad sequence number");
        return;
      }
      RequestInfo info = std::move(it->second);
      seqno2_request_info_.erase(it);
      /* --- critical section end --- */
      lock.unlock();

      info.promise.set_value(std::move(response));
      if (info.callback.has_value()) {
        (info.callback.value())(info.promise.get_future().share());
      }
    };

    SubscriptionOptions options{group};
    subscriber_ = std::make_shared<Subscription<ResponseT>>(
      node_, service_name_ + "_response", qos, std::move(subscriber_callback), options);
  }

  ipc_shared_ptr<RequestT> borrow_loaned_request()
  {
    auto request = publisher_->borrow_loaned_message();
    request->_node_name = node_->get_fully_qualified_name();
    request->_sequence_number = next_sequence_number_.fetch_add(1);
    return request;
  }

  template <typename RepT, typename RatioT>
  bool wait_for_service(
    std::chrono::duration<RepT, RatioT> timeout = std::chrono::nanoseconds(-1)) const
  {
    return wait_for_service_nanoseconds(
      node_->get_node_base_interface()->get_context(), service_name_,
      std::chrono::duration_cast<std::chrono::nanoseconds>(timeout));
  }

  void async_send_request(
    ipc_shared_ptr<RequestT> && request, std::function<void(SharedFuture)> callback)
  {
    {
      std::lock_guard<std::mutex> lock(seqno2_request_info_mtx_);
      seqno2_request_info_.try_emplace(request->_sequence_number, std::move(callback));
    }

    publisher_->publish(std::move(request));
  }

  SharedFuture async_send_request(ipc_shared_ptr<RequestT> && request)
  {
    std::unique_lock<std::mutex> lock(seqno2_request_info_mtx_);
    auto it = seqno2_request_info_.try_emplace(request->_sequence_number).first;
    SharedFuture ret = it->second.promise.get_future().share();
    lock.unlock();

    publisher_->publish(std::move(request));
    return ret;
  }
};

}  // namespace agnocast
