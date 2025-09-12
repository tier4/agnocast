#pragma once

#include "agnocast/agnocast_publisher.hpp"
#include "agnocast/agnocast_smart_pointer.hpp"
#include "agnocast/agnocast_subscription.hpp"
#include "rclcpp/rclcpp.hpp"

#include <memory>
#include <string>
#include <type_traits>
#include <utility>

namespace agnocast
{

template <typename ServiceT>
class Service
{
public:
  // To avoid name conflicts, members of RequestT and ResponseT are given an underscore prefix.
  struct RequestT : public ServiceT::Request
  {
    std::string _node_name;
  };
  struct ResponseT : public ServiceT::Response
  {
    std::string _node_name;
    int64_t _request_entry_id;
  };

private:
  const std::string service_name_;
  typename AgnocastOnlyPublisher<ResponseT>::SharedPtr publisher_;
  typename Subscription<RequestT>::SharedPtr subscriber_;

public:
  using SharedPtr = std::shared_ptr<Service<ServiceT>>;

  template <typename Func>
  Service(
    rclcpp::Node * node, const std::string & service_name, Func && callback,
    const rclcpp::QoS & qos, rclcpp::CallbackGroup::SharedPtr group)
  : service_name_(node->get_node_services_interface()->resolve_service_name(service_name)),
    publisher_(
      std::make_shared<AgnocastOnlyPublisher<ResponseT>>(node, service_name_ + "_response", qos))
  {
    static_assert(
      std::is_invocable_v<
        std::decay_t<Func>, const ipc_shared_ptr<RequestT> &, ipc_shared_ptr<ResponseT> &>,
      "Callback must be callable with "
      "(const ipc_shared_ptr<RequestT> &, ipc_shared_ptr<ResponseT> &)");

    auto subscriber_callback =
      [this, callback = std::forward<Func>(callback)](const ipc_shared_ptr<RequestT> & request) {
        ipc_shared_ptr<ResponseT> response = this->publisher_->borrow_loaned_message();
        response->_node_name = request->_node_name;
        response->_request_entry_id = request.get_entry_id();

        callback(request, response);

        this->publisher_->publish(std::move(response));
      };

    SubscriptionOptions options{group};
    subscriber_ = std::make_shared<Subscription<RequestT>>(
      node, service_name_ + "_request", qos, std::move(subscriber_callback), options);
  }
};

}  // namespace agnocast
