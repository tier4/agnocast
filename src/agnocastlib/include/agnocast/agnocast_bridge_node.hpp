#pragma once

#include "agnocast/agnocast_bridge_utils.hpp"
#include "agnocast/agnocast_ioctl.hpp"  // ioctl定義(GID用)
#include "agnocast/agnocast_mq.hpp"
#include "agnocast/agnocast_publisher.hpp"
#include "agnocast/agnocast_subscription.hpp"
#include "rclcpp/rclcpp.hpp"

#include <dlfcn.h>
#include <mqueue.h>
#include <sys/ioctl.h>
#include <unistd.h>

#include <cstring>  // memcpy, memset
#include <memory>
#include <regex>
#include <string>
#include <vector>

namespace agnocast
{

// agnocast_utils.cpp 等で実体が定義されているファイルディスクリプタ
extern int agnocast_fd;

// 前方宣言: コマンド送信関数
template <typename MessageT>
void send_bridge_command(
  const std::string & topic_name, const rclcpp::QoS & qos, BridgeDirection dir, BridgeCommand cmd);

// =========================================================================
// GID Manager (Kernel Interface for Loop Prevention)
// カーネルモジュールと通信してGIDの登録・確認を行うシングルトン
// =========================================================================
class BridgeGidManager
{
public:
  static BridgeGidManager & get_instance()
  {
    static BridgeGidManager instance;
    return instance;
  }

  // 受信したメッセージのGIDが無視リスト(カーネル管理)に入っているか確認
  // true ならループバックなので破棄すべき
  bool is_ignored(const rmw_gid_t & gid)
  {
    // データが空ならチェック不要 (intra-process等)
    bool is_empty = true;
    for (auto b : gid.data) {
      if (b != 0) is_empty = false;
    }
    if (is_empty) return false;

    struct ioctl_bridge_args args;
    std::memset(&args, 0, sizeof(args));

    // GID照合用のデータをセット
    size_t copy_size = sizeof(gid.data) > MAX_GID_LEN ? MAX_GID_LEN : sizeof(gid.data);
    std::memcpy(args.info.gid, gid.data, copy_size);
    args.info.gid_len = copy_size;

    // カーネルへ問い合わせ (AGNOCAST_CHECK_GID_CMD)
    // カーネル側で登録済みリストと照合し、ret_is_ignored に結果が入る
    if (ioctl(agnocast_fd, AGNOCAST_CHECK_GID_CMD, &args) < 0) {
      // エラー時は安全側に倒して無視しない（ループのリスクはあるが通信断を防ぐ）
      // 必要ならログ出力
      return false;
    }

    return args.ret_is_ignored;
  }
};

// =========================================================================
// Request Policies
// ユーザーが利用する際に MQ 送信をトリガーするポリシー
// =========================================================================

// User側の Subscription が使うポリシー (ROS -> Agnocast を要求)
struct RosToAgnocastRequestPolicy
{
  template <typename MessageT>
  static void request_bridge(const std::string & topic_name, const rclcpp::QoS & qos)
  {
    // コンストラクタで作成リクエスト
    send_bridge_command<MessageT>(
      topic_name, qos, BridgeDirection::ROS2_TO_AGNOCAST, BridgeCommand::CREATE_BRIDGE);
  }

  template <typename MessageT>
  static void release_bridge(const std::string & topic_name)
  {
    // デストラクタで削除リクエスト
    send_bridge_command<MessageT>(
      topic_name, rclcpp::QoS(1), BridgeDirection::ROS2_TO_AGNOCAST, BridgeCommand::REMOVE_BRIDGE);
  }
};

// User側の Publisher が使うポリシー (Agnocast -> ROS を要求)
struct AgnocastToRosRequestPolicy
{
  template <typename MessageT>
  static void request_bridge(const std::string & topic_name, const rclcpp::QoS & qos)
  {
    send_bridge_command<MessageT>(
      topic_name, qos, BridgeDirection::AGNOCAST_TO_ROS2, BridgeCommand::CREATE_BRIDGE);
  }

  template <typename MessageT>
  static void release_bridge(const std::string & topic_name)
  {
    send_bridge_command<MessageT>(
      topic_name, rclcpp::QoS(1), BridgeDirection::AGNOCAST_TO_ROS2, BridgeCommand::REMOVE_BRIDGE);
  }
};

// ブリッジ内部で使うポリシー (連鎖防止のため何もしない)
struct NoBridgeRequestPolicy
{
  template <typename MessageT>
  static void request_bridge(const std::string &, const rclcpp::QoS &)
  {
  }

  template <typename MessageT>
  static void release_bridge(const std::string &)
  {
  }
};

// =========================================================================
// Class 1: ROS -> Agnocast Bridge (Receiver)
// =========================================================================
template <typename MessageT>
class RosToAgnocastBridge
{
private:
  using AgnoPub = agnocast::BasicPublisher<MessageT, NoBridgeRequestPolicy>;
  using RosSubPtr = typename rclcpp::Subscription<MessageT>::SharedPtr;

  typename AgnoPub::SharedPtr agnocast_pub_;
  RosSubPtr ros_sub_;
  rclcpp::CallbackGroup::SharedPtr ros_cb_group_;

  // ROSからのメッセージ受信コールバック
  void forward_to_agnocast(
    const typename MessageT::ConstSharedPtr ros_msg, const rclcpp::MessageInfo & msg_info)
  {
    auto gid = msg_info.get_rmw_message_info().publisher_gid;

    std::stringstream ss;
    ss << std::hex;
    for (size_t i = 0; i < 24; ++i) ss << (int)gid.data[i] << " ";
    RCLCPP_INFO(logger, "R2A Checking GID: [ %s]", ss.str().c_str());

    // ★重要: ループ防止フィルタ
    // カーネルに問い合わせて、身内のA2Rブリッジからの送信なら破棄する
    if (BridgeGidManager::get_instance().is_ignored(
          msg_info.get_rmw_message_info().publisher_gid)) {
      return;
    }

    auto loaned_msg = this->agnocast_pub_->borrow_loaned_message();
    *loaned_msg = *ros_msg;
    this->agnocast_pub_->publish(std::move(loaned_msg));
  }

public:
  // 親ノードを受け取ってリソースを生成
  explicit RosToAgnocastBridge(
    rclcpp::Node::SharedPtr parent_node, const std::string & topic_name,
    const rclcpp::QoS & sub_qos)
  {
    // [QoS] Agnocast Pub: Reliable + TransientLocal (固定)
    agnocast_pub_ = std::make_shared<AgnoPub>(
      parent_node.get(), topic_name, rclcpp::QoS(10).reliable().transient_local(),
      agnocast::PublisherOptions{});

    // Executor対策: MutuallyExclusiveグループ
    ros_cb_group_ =
      parent_node->create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive);

    rclcpp::SubscriptionOptions ros_opts;
    ros_opts.ignore_local_publications = true;  // プロセス内ループ防止の補助
    ros_opts.callback_group = ros_cb_group_;

    // [QoS] ROS Sub: ユーザー指定の sub_qos を使用
    // GID取得のために MessageInfo を受け取るコールバックにする
    ros_sub_ = parent_node->create_subscription<MessageT>(
      topic_name, sub_qos,
      [this](const typename MessageT::ConstSharedPtr msg, const rclcpp::MessageInfo & info) {
        this->forward_to_agnocast(msg, info);
      },
      ros_opts);

    RCLCPP_INFO(
      parent_node->get_logger(), "Attached ROS->Agno bridge for '%s'", topic_name.c_str());
  }
};

// =========================================================================
// Class 2: Agnocast -> ROS Bridge (Sender)
// =========================================================================
template <typename MessageT>
class AgnocastToRosBridge
{
private:
  using AgnoSub = agnocast::BasicSubscription<MessageT, NoBridgeRequestPolicy>;
  using RosPubPtr = typename rclcpp::Publisher<MessageT>::SharedPtr;

  RosPubPtr ros_pub_;
  typename AgnoSub::SharedPtr agnocast_sub_;
  rclcpp::CallbackGroup::SharedPtr agno_cb_group_;

  // GID登録管理用
  rmw_gid_t my_gid_;
  std::string unique_name_;
  bool gid_registered_ = false;

  void forward_to_ros(const agnocast::ipc_shared_ptr<MessageT> agno_msg)
  {
    if (this->ros_pub_->get_subscription_count() == 0) {
      return;
    }

    my_gid_ = ros_pub_->get_gid();

    std::stringstream ss;
    ss << std::hex;
    for (size_t i = 0; i < 24; ++i) ss << (int)my_gid_.data[i] << " ";
    RCLCPP_INFO(logger, "A2R Registering GID: [ %s]", ss.str().c_str());

    auto loaned_msg = this->ros_pub_->borrow_loaned_message();
    loaned_msg.get() = *agno_msg;
    this->ros_pub_->publish(std::move(loaned_msg));
  }

public:
  // コンストラクタ引数の pub_qos は使用せず、内部で固定QoSを使用する
  explicit AgnocastToRosBridge(
    rclcpp::Node::SharedPtr parent_node, const std::string & topic_name,
    [[maybe_unused]] const rclcpp::QoS & pub_qos)
  {
    // [QoS] ROS Pub: Depth(1) + Reliable + TransientLocal (固定)
    // 外部へ送る最強設定
    // auto bridge_qos = rclcpp::QoS(1).reliable().transient_local();
    auto bridge_qos = rclcpp::QoS(1).reliable().durability_volatile();  // ← 一旦これで様子見
    ros_pub_ = parent_node->create_publisher<MessageT>(topic_name, bridge_qos);

    // --- ★重要: カーネルへのGID登録 (ループ防止) ---
    my_gid_ = ros_pub_->get_gid();

    std::stringstream ss;
    ss << std::hex;
    for (size_t i = 0; i < 24; ++i) ss << (int)my_gid_.data[i] << " ";
    RCLCPP_INFO(parent_node->get_logger(), "A2R Registering GID: [ %s]", ss.str().c_str());

    unique_name_ = topic_name + "_A2R";  // 登録名

    struct ioctl_bridge_args args;
    std::memset(&args, 0, sizeof(args));

    // PIDとトピック名
    args.info.pid = getpid();
    safe_strncpy(args.info.topic_name, unique_name_.c_str(), MAX_TOPIC_NAME_LEN);

    // GID設定
    size_t copy_size = sizeof(my_gid_.data) > MAX_GID_LEN ? MAX_GID_LEN : sizeof(my_gid_.data);
    std::memcpy(args.info.gid, my_gid_.data, copy_size);
    args.info.gid_len = copy_size;

    // 登録実行
    // これにより、他のプロセスのR2AブリッジがこのGIDからのメッセージを無視できるようになる
    if (ioctl(agnocast_fd, AGNOCAST_REGISTER_BRIDGE_CMD, &args) == 0) {
      gid_registered_ = true;
    } else {
      RCLCPP_INFO(
        parent_node->get_logger(), "Failed to register A2R bridge GID for topic '%s'.",
        topic_name.c_str());
      // EEXISTの場合でも、カーネル側でGID情報が更新される実装になっていればOK
      // もしなっていなければ、unregister -> register する等のロジック検討が必要
      // 現状はGeneratorが名前だけ予約 -> ここでGID登録 という流れなので、
      // カーネル側の register_bridge が「名前一致ならGID更新」に対応している必要がある
      // （または Generator が登録せず、ここだけで登録する）
    }

    // --- Agnocast Sub 生成 ---
    agno_cb_group_ =
      parent_node->create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive);

    agnocast::SubscriptionOptions agno_opts;
    agno_opts.ignore_local_publications = true;
    agno_opts.callback_group = agno_cb_group_;

    // [QoS] Agnocast Sub: BestEffort + Volatile (固定)
    agnocast_sub_ = std::make_shared<AgnoSub>(
      parent_node.get(), topic_name, rclcpp::QoS(10).best_effort().durability_volatile(),
      [this](const agnocast::ipc_shared_ptr<MessageT> msg) { this->forward_to_ros(msg); },
      agno_opts);

    RCLCPP_INFO(
      parent_node->get_logger(), "Attached Agno->ROS bridge for '%s'", topic_name.c_str());
  }

  ~AgnocastToRosBridge()
  {
    if (gid_registered_) {
      // 終了時にGID登録を解除
      struct ioctl_bridge_args args;
      std::memset(&args, 0, sizeof(args));
      args.info.pid = getpid();
      safe_strncpy(args.info.topic_name, unique_name_.c_str(), MAX_TOPIC_NAME_LEN);

      ioctl(agnocast_fd, AGNOCAST_UNREGISTER_BRIDGE_CMD, &args);
    }
  }
};

// =========================================================================
// Factory Functions
// =========================================================================

template <typename MessageT>
std::shared_ptr<void> start_ros_to_agno_node(rclcpp::Node::SharedPtr node, const BridgeArgs & args)
{
  auto qos = reconstruct_qos_from_flat(args.qos);
  return std::make_shared<RosToAgnocastBridge<MessageT>>(node, args.topic_name, qos);
}

template <typename MessageT>
std::shared_ptr<void> start_agno_to_ros_node(rclcpp::Node::SharedPtr node, const BridgeArgs & args)
{
  auto qos = reconstruct_qos_from_flat(args.qos);
  return std::make_shared<AgnocastToRosBridge<MessageT>>(node, args.topic_name, qos);
}

// =========================================================================
// Helper: Send Command (MQ)
// =========================================================================

template <typename MessageT>
void send_bridge_command(
  const std::string & topic_name, const rclcpp::QoS & qos, BridgeDirection dir, BridgeCommand cmd)
{
  auto logger = rclcpp::get_logger("agnocast_bridge_requester");

  MqMsgBridge msg = {};
  msg.direction = dir;
  msg.command = cmd;

  BridgeFn fn = nullptr;
  if (dir == BridgeDirection::ROS2_TO_AGNOCAST) {
    fn = &start_ros_to_agno_node<MessageT>;
  } else {
    fn = &start_agno_to_ros_node<MessageT>;
  }

  Dl_info info{};
  if (dladdr(reinterpret_cast<void *>(fn), &info) == 0) {
    RCLCPP_ERROR(logger, "dladdr failed in send_command");
    return;
  }

  safe_strncpy(msg.shared_lib_path, info.dli_fname, MAX_NAME_LENGTH);
  const char * symbol_name = info.dli_sname ? info.dli_sname : "__MAIN_EXECUTABLE__";
  safe_strncpy(msg.symbol_name, symbol_name, MAX_NAME_LENGTH);
  msg.fn_ptr = reinterpret_cast<uintptr_t>(fn);

  safe_strncpy(msg.args.topic_name, topic_name.c_str(), sizeof(msg.args.topic_name));

  if (cmd == BridgeCommand::CREATE_BRIDGE) {
    msg.args.qos = flatten_qos(qos);
  }

  const std::string mq_name_str = create_mq_name_for_bridge(getpid());
  mqd_t mq = mq_open(mq_name_str.c_str(), O_WRONLY);

  if (mq == (mqd_t)-1) {
    return;
  }
  mq_send(mq, (const char *)&msg, sizeof(msg), 0);
  mq_close(mq);
}

}  // namespace agnocast
