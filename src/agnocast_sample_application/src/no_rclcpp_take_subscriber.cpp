#include "agnocast/agnocast.hpp"
#include "agnocast_sample_interfaces/msg/dynamic_size_array.hpp"

#include <chrono>

using namespace std::chrono_literals;

class NoRclcppTakeSubscriber : public agnocast::Node
{
  agnocast::PollingSubscriber<agnocast_sample_interfaces::msg::DynamicSizeArray>::SharedPtr sub_;
  agnocast::TimerBase::SharedPtr timer_;

public:
  // カバレッジテスト用に追加したコールバックグループ
  rclcpp::CallbackGroup::SharedPtr manual_group_;
  rclcpp::CallbackGroup::SharedPtr late_auto_group_;

  explicit NoRclcppTakeSubscriber() : agnocast::Node("no_rclcpp_take_subscriber")
  {
    sub_ = this->create_subscription<agnocast_sample_interfaces::msg::DynamicSizeArray>(
      "/my_topic", rclcpp::QoS(rclcpp::KeepLast(1)));

    timer_ = this->create_wall_timer(1s, std::bind(&NoRclcppTakeSubscriber::timer_callback, this));

    // 【テスト準備1】自動追加フラグを false にしてグループを作成
    manual_group_ =
      this->create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive, false);

    RCLCPP_INFO(get_logger(), "NoRclcppTakeSubscriber started");
  }

  void create_late_group()
  {
    // 【テスト準備2】ノードがExecutorに追加された後に作成
    late_auto_group_ = this->create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive);
  }

private:
  void timer_callback()
  {
    auto message = sub_->take_data();
    if (message) {
      RCLCPP_INFO(
        get_logger(), "I heard dynamic size array message with id: %ld, size: %zu", message->id,
        message->data.size());
    }
  }
};

// =========================================================
// 【追加】protectedなメソッドを呼び出すためのテスト用Executor
// =========================================================
class TestExecutor : public agnocast::AgnocastOnlyMultiThreadedExecutor
{
public:
  void trigger_add_groups()
  {
    // 子クラスの中であれば、protectedな親メソッドを呼び出せる
    this->add_callback_groups_from_nodes_associated_to_executor();
  }
};

int main(int argc, char ** argv)
{
  agnocast::init(argc, argv);

  // 通常のエグゼキュータではなく、作成したテスト用エグゼキュータを使用する
  TestExecutor executor;
  auto node = std::make_shared<NoRclcppTakeSubscriber>();

  // ---------------------------------------------------------
  // 既存のパス3: add_nodeによる自動追加
  // ---------------------------------------------------------
  executor.add_node(node);

  // ---------------------------------------------------------
  // 未網羅パス1: add_callback_group の直接呼び出し
  // ---------------------------------------------------------
  executor.add_callback_group(node->manual_group_, node->get_node_base_interface());

  // ---------------------------------------------------------
  // 未網羅パス2: テスト用エグゼキュータを経由して呼び出す
  // ---------------------------------------------------------
  node->create_late_group();
  executor.trigger_add_groups();

  executor.spin();
  return 0;
}
