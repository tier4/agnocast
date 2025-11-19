#include "agnocast/agnocast_callback_info.hpp"
#include "agnocast/agnocast_ioctl.hpp"
#include "agnocast/agnocast_mq.hpp"
#include "agnocast/agnocast_smart_pointer.hpp"
#include "agnocast/agnocast_tracepoint_wrapper.h"
#include "agnocast/agnocast_utils.hpp"

namespace agnocast
{

class TmpSubscriptionBase
{
protected:
  topic_local_id_t id_;
  const std::string topic_name_;

  union ioctl_add_subscriber_args initialize(
    const rclcpp::QoS & qos, const bool is_take_sub, const std::string & node_name)
  {
    union ioctl_add_subscriber_args add_subscriber_args = {};
    add_subscriber_args.topic_name = {topic_name_.c_str(), topic_name_.size()};
    add_subscriber_args.node_name = {node_name.c_str(), node_name.size()};
    add_subscriber_args.qos_depth = static_cast<uint32_t>(qos.depth());
    add_subscriber_args.qos_is_transient_local =
      qos.durability() == rclcpp::DurabilityPolicy::TransientLocal;
    add_subscriber_args.is_take_sub = is_take_sub;
    if (ioctl(agnocast_fd, AGNOCAST_ADD_SUBSCRIBER_CMD, &add_subscriber_args) < 0) {
      RCLCPP_ERROR(logger, "AGNOCAST_ADD_SUBSCRIBER_CMD failed: %s", strerror(errno));
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }

    return add_subscriber_args;
  }

public:
  TmpSubscriptionBase(/*rclcpp::Node * node,*/ const std::string & topic_name)
  : id_(0), topic_name_(topic_name)
  {
    validate_ld_preload();
  }
};

template <typename MessageT>
class TmpSubscription : public TmpSubscriptionBase
{
  std::pair<mqd_t, std::string> mq_subscription_;

public:
  using SharedPtr = std::shared_ptr<TmpSubscription<MessageT>>;

  template <typename Func>
  TmpSubscription(
    /*rclcpp::Node * node */ const std::string & node_name, const std::string & topic_name,
    const rclcpp::QoS & qos, Func && callback, agnocast::SubscriptionOptions options)
  : TmpSubscriptionBase(/*node,*/ topic_name)
  {
    union ioctl_add_subscriber_args add_subscriber_args = initialize(qos, false, node_name);

    id_ = add_subscriber_args.ret_id;

    mqd_t mq = open_mq_for_subscription(topic_name_, id_, mq_subscription_);

    /*
    auto node_base = node->get_node_base_interface();
    rclcpp::CallbackGroup::SharedPtr callback_group = get_valid_callback_group(node_base, options);
    */

    rclcpp::CallbackGroup::SharedPtr callback_group = options.callback_group;
    if (callback_group == nullptr) {
      // temporal workaround
      callback_group =
        rclcpp::CallbackGroup::make_shared(rclcpp::CallbackGroupType::MutuallyExclusive);
    }

    const bool is_transient_local = qos.durability() == rclcpp::DurabilityPolicy::TransientLocal;
    [[maybe_unused]] uint32_t callback_info_id = agnocast::register_callback<MessageT>(
      std::forward<Func>(callback), topic_name_, id_, is_transient_local, mq, callback_group);

    // We have to think about how to handle CARET logging without rclcpp::Node
    /*
    {
      uint64_t pid_ciid = (static_cast<uint64_t>(getpid()) << 32) | callback_info_id;
      TRACEPOINT(
        agnocast_subscription_init, static_cast<const void *>(this),
        static_cast<const void *>(node_base->get_shared_rcl_node_handle().get()),
        static_cast<const void *>(&callback), static_cast<const void *>(callback_group.get()),
        tracetools::get_symbol(callback), topic_name_.c_str(), qos.depth(), pid_ciid);
    }
    */
  }

  ~TmpSubscription() { remove_mq(mq_subscription_); }
};

template <typename MessageT, typename Func>
typename TmpSubscription<MessageT>::SharedPtr tmp_create_subscription(
  const std::string node_name, const std::string & topic_name, const size_t qos_history_depth,
  Func && callback, agnocast::SubscriptionOptions options)
{
  return std::make_shared<TmpSubscription<MessageT>>(
    node_name, topic_name, rclcpp::QoS(rclcpp::KeepLast(qos_history_depth)),
    std::forward<Func>(callback), options);
}

}  // namespace agnocast