# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## ブランチの目的: `apply_agnocast_for_thread_configurator`

`cie_thread_configurator` を Agnocast 通信に移行する。具体的なゴールは以下の4つ。

### 1. rclcpp::Node → agnocast::Node への置き換え

- `PrerunNode`, `ThreadConfiguratorNode` の基底クラスを `rclcpp::Node` から `agnocast::Node` に変更する
- `main.cpp` で `rclcpp::init` → `agnocast::init`、`rclcpp::executors::SingleThreadedExecutor` → `agnocast::AgnocastOnlySingleThreadedExecutor` に変更する
- `rclcpp::shutdown()` の呼び出しは不要になる（agnocast が処理する）

### 2. thread_configurator_node との全通信を agnocast 化

- `rclcpp::Subscription` → `agnocast::Subscription` に変更する
- コールバック引数を `const T::SharedPtr msg` から `const agnocast::ipc_shared_ptr<const T> & msg` に変更する
- publisher 側は `agnocast::create_publisher()` / `publish_callback_group_info()` を使用する
- ドメインノード（`rclcpp::Node`）はエグゼキュータに追加しない。agnocast サブスクリプションは agnocast インフラが自動的に処理する

### 3. agnocastlib → cie_thread_configurator のパッケージ依存を除去

- `agnocastlib/package.xml` から `<depend>cie_thread_configurator</depend>` を削除
- `agnocastlib/CMakeLists.txt` から `find_package(cie_thread_configurator)` と関連する `ament_target_dependencies` を削除
- 代わりに `cie_thread_configurator/package.xml` に `<depend>agnocastlib</depend>` を追加し、依存方向を逆転する
- `cie_thread_configurator/src/util.cpp` にあったユーティリティ関数（`create_callback_group_id`, `create_client_publisher`, `publish_callback_group_info`）を `agnocastlib` 側の新ファイル `agnocast_cie_utils.hpp/.cpp` に移動する

### 4. 変更の動作テスト

- agnocastlib のインテグレーションテスト: `colcon test --packages-select agnocastlib --event-handlers console_direct+`
- thread configurator の launch ファイル確認: `ros2 launch cie_thread_configurator thread_configurator.launch.xml prerun:=true`

## 変更対象ファイル

### agnocastlib（新規ユーティリティ + executor 拡張）

| ファイル | 変更内容 |
|---------|---------|
| `src/agnocastlib/include/agnocast/agnocast_cie_utils.hpp` | **新規** — CIE 用ユーティリティ関数の宣言 |
| `src/agnocastlib/src/agnocast_cie_utils.cpp` | **新規** — `create_callback_group_id`, `create_client_publisher`, `publish_callback_group_info` の実装 |
| `src/agnocastlib/include/agnocast/node/agnocast_only_executor.hpp` | `spin_once(timeout)` メソッド追加 |
| `src/agnocastlib/src/node/agnocast_only_executor.cpp` | `spin_once` の実装（epoll ベース） |
| `src/agnocastlib/CMakeLists.txt` | `cie_thread_configurator` 依存を削除、`agnocast_cie_utils.cpp` を追加 |
| `src/agnocastlib/package.xml` | `cie_thread_configurator` 依存を削除 |
| `src/agnocastlib/src/agnocast_callback_isolated_executor.cpp` | `agnocast_cie_utils` を使用するように変更 |
| `src/agnocastlib/src/agnocast_component_container_cie.cpp` | `agnocast_cie_utils` を使用するように変更 |

### cie_thread_configurator（agnocast 通信への移行）

| ファイル | 変更内容 |
|---------|---------|
| `src/cie_thread_configurator/include/cie_thread_configurator/prerun_node.hpp` | `rclcpp::Node` → `agnocast::Node`、サブスクリプション型変更 |
| `src/cie_thread_configurator/include/cie_thread_configurator/thread_configurator_node.hpp` | 同上 |
| `src/cie_thread_configurator/include/cie_thread_configurator/cie_thread_configurator.hpp` | ヘッダ整理 |
| `src/cie_thread_configurator/src/prerun_node.cpp` | agnocast サブスクリプション使用、`ipc_shared_ptr` コールバック |
| `src/cie_thread_configurator/src/thread_configurator_node.cpp` | 同上 |
| `src/cie_thread_configurator/src/main.cpp` | `agnocast::init`、`AgnocastOnlySingleThreadedExecutor` 使用 |
| `src/cie_thread_configurator/src/util.cpp` | ユーティリティ関数を agnocastlib 側に移動したため大幅削減 |
| `src/cie_thread_configurator/launch/thread_configurator.launch.xml` | **新規** — prerun/config モード対応の launch ファイル |
| `src/cie_thread_configurator/CMakeLists.txt` | `agnocastlib` 依存を追加、launch ファイルインストール追加 |
| `src/cie_thread_configurator/package.xml` | `agnocastlib` 依存を追加 |

### テスト修正

| ファイル | 変更内容 |
|---------|---------|
| `src/agnocastlib/test/integration/src/test_publisher_component.cpp` | 旧 util.cpp 依存の削除 |
| `src/agnocastlib/test/integration/test_agnocast_callback_isolated_executor.cpp` | QoS 設定変更 |
| `src/agnocastlib/test/integration/test_agnocast_component_container_cie_launch.py` | test_publisher_component 関連セットアップの削除 |

## ビルドとテスト

```bash
# ビルド
colcon build --symlink-install --cmake-args -DCMAKE_BUILD_TYPE=Release

# 単一パッケージビルド
colcon build --symlink-install --packages-select agnocastlib --cmake-args -DCMAKE_BUILD_TYPE=Release

# テスト実行（今回の変更で直接影響があるテストのみ）
colcon test --packages-select agnocastlib --event-handlers console_direct+ --ctest-args -R "test_integration_agnocastlib|test_agnocast_component_container_cie"
```

## コード規約

- pre-commit: `pre-commit install` で clang-format / markdownlint / KUnit フック有効化

## Agnocast の主要パターン（この変更で使う知識）

- `agnocast::Node` は `rclcpp::Node` を継承しつつ agnocast 機能を追加する
- コールバックは `const agnocast::ipc_shared_ptr<const T> &` を受け取る（`std::shared_ptr<T>` ではない）
- `AgnocastOnlySingleThreadedExecutor` は agnocast コールバックのみを処理する（rclcpp コールバックは処理しない）
- agnocast サブスクリプションは agnocast インフラが自動管理するため、ドメインノードをエグゼキュータに `add_node` する必要はない
