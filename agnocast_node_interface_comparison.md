# Agnocast::Node と rclcpp::Node のインターフェース比較

## エグゼクティブサマリー

本ドキュメントは、`agnocast::Node`と`rclcpp::Node`の包括的な比較を提供し、Agnocast実装でサポートされている機能、部分的にサポートされている機能、サポートされていない機能を詳述します。

**主な特徴**:
- `rclcpp::Node`は10個の異なるノードインターフェースを持つモジュラーアーキテクチャ
- `agnocast::Node`は、パラメータ管理とトピック名解決に特化した軽量実装
- **agnocastは独自のExecutor実装を提供** (SingleThreaded, MultiThreaded, CallbackIsolated)
- Publisherは`rclcpp::Node`が必要、Subscriptionは`agnocast::Node`でも作成可能

---

## 1. rclcpp::Nodeインターフェースアーキテクチャの概要

rclcpp::Nodeは10個のインターフェースコンポーネントで構成されています:

1. **NodeBaseInterface** - コアノードのアイデンティティとコールバック管理
2. **NodeTopicsInterface** - Publisher/Subscription管理
3. **NodeParametersInterface** - パラメータ管理
4. **NodeGraphInterface** - ROSグラフのイントロスペクション
5. **NodeServicesInterface** - サービスクライアント/サーバー管理
6. **NodeTimersInterface** - タイマー管理
7. **NodeLoggingInterface** - ロギング機能
8. **NodeClockInterface** - 時刻とクロック管理
9. **NodeWaitablesInterface** - カスタムwaitable管理
10. **NodeTimeSourceInterface** - タイムソース設定

各インターフェースは、`get_node_base_interface()`、`get_node_topics_interface()`などのgetterメソッドでアクセス可能です。

---

## 2. 詳細インターフェース比較

### 2.1 NodeBaseInterface

**目的**: コアノードのアイデンティティ、コンテキスト管理、コールバックグループ

| 機能 | agnocast::Node | サポートレベル | 備考 |
|------|----------------|---------------|------|
| `get_name()` | ✓ | **完全サポート** | agnocast_node.hpp:112 |
| `get_namespace()` | ✓ | **完全サポート** | agnocast_node.hpp:121 |
| `get_fully_qualified_name()` | ✓ | **完全サポート** | agnocast_node.hpp:130 |
| `get_context()` | ✗ | **未サポート** | agnocastはGlobalContextシングルトンを使用 |
| `get_rcl_node_handle()` | ✗ | **未サポート** | agnocastはrcl_node_tを作成しない |
| `get_shared_rcl_node_handle()` | ✗ | **未サポート** | agnocastはrcl_node_tを作成しない |
| `create_callback_group()` | ✗ | **未サポート** | デフォルトコールバックグループのみ存在 |
| `get_default_callback_group()` | ✓ | **完全サポート** | agnocast_node.hpp:137 |
| `callback_group_in_node()` | ✓ | **完全サポート** | agnocast_node.hpp:145, agnocast_node.cpp:709-720 |
| `for_each_callback_group()` | ✗ | **未サポート** | - |
| `get_notify_guard_condition()` | ✗ | **未サポート** | - |
| `resolve_topic_or_service_name()` | ✓ (トピックのみ) | **部分サポート** | agnocast_node.hpp:157, トピック解決のみ |
| `create_sub_node()` | ✗ | **未サポート** | サブノード作成機能なし |
| `get_sub_namespace()` | ✗ | **未サポート** | サブネームスペース機能なし |
| `get_effective_namespace()` | ✗ | **未サポート** | agnocastでは`get_namespace()`が実効ネームスペース |
| `get_node_options()` | ✗ | **未サポート** | NodeOptionsを使用しない |
| コンテキスト/rclハンドル管理 | ✗ | **未サポート** | agnocastはrclコンテキストを使用しない |
| Executor関連付け | ✗ | **未サポート** | - |
| プロセス内通信 | ✗ | **未サポート** | - |

**サマリー**:
- ✓ サポート: 5メソッド (name, namespace, FQN, デフォルトコールバックグループ, トピック解決)
- ⚠ 部分サポート: 1メソッド (resolve_topic_or_service_name - トピックのみ)
- ✗ 未サポート: 12機能 (コンテキスト, rclハンドル, コールバックグループ作成, guard condition, executor関連付け, プロセス内通信, サブノード関連4機能)

---

### 2.2 NodeTopicsInterface

**目的**: PublisherとSubscriptionの管理

| 機能 | agnocast::Node | サポートレベル | 備考 |
|------|----------------|---------------|------|
| `create_publisher()` | **✗** | **未サポート** | **rclcpp::Nodeが必要** |
| `create_subscription()` | ✓ | **完全サポート** | agnocast::Subscriptionテンプレートクラス経由 |
| `add_publisher()` | ✗ | **未サポート** | - |
| `add_subscription()` | ✗ | **未サポート** | - |
| `resolve_topic_name()` | ✓ | **完全サポート** | agnocast_node.hpp:157 |

**重要な制限**:
- **Publisherは`rclcpp::Node`が必要**: `agnocast::Publisher`のコンストラクタは`rclcpp::Node*`のみを受け取る（agnocast_publisher.hpp:70-111参照）
- **Subscriptionは両方サポート**: `agnocast::Subscription`は`rclcpp::Node*`と`agnocast::Node*`の両方のコンストラクタを持つ（agnocast_subscription.hpp:78-128参照）

**実装パターン**:
```cpp
// Publisher作成 - rclcpp::Nodeが必要
rclcpp::Node* rclcpp_node = /* ... */;
auto pub = agnocast::create_publisher<MsgType>(rclcpp_node, "topic", 10);

// Subscription作成 - agnocast::Nodeでも可能
agnocast::Node* agnocast_node = /* ... */;
auto sub = agnocast::create_subscription<MsgType>(
  agnocast_node, "topic", 10, callback);

// またはrclcpp::Nodeでも可能
auto sub2 = agnocast::create_subscription<MsgType>(
  rclcpp_node, "topic", 10, callback);
```

---

### 2.3 NodeParametersInterface

**目的**: パラメータの宣言、アクセス、管理

| 機能 | agnocast::Node | サポートレベル | 備考 |
|------|----------------|---------------|------|
| `declare_parameter()` | ✓ | **完全サポート** | agnocast_node.hpp:172-176 |
| `has_parameter()` | ✓ | **完全サポート** | agnocast_node.hpp:187 |
| `get_parameter()` | ✓ | **完全サポート** | agnocast_node.hpp:215-218 (bool, int64_t, double, string) |
| `get_parameter_or()` | ✗ | **未サポート** | デフォルト値付き取得の便利メソッド |
| `get_parameters()` | ✗ | **未サポート** | get_parameter()を使って実装可能 |
| `get_parameter_types()` | ✓ | **完全サポート** | agnocast_node.hpp:203 |
| `get_parameters_by_prefix()` | ✗ | **未サポート** | - |
| `set_parameter()` | ✗ | **未サポート** | パラメータは宣言後読み取り専用（単数形） |
| `set_parameters()` | ✗ | **未サポート** | パラメータは宣言後読み取り専用（複数形） |
| `set_parameters_atomically()` | ✗ | **未サポート** | - |
| `undeclare_parameter()` | ✗ | **未サポート** | - |
| `describe_parameters()` | ✗ | **未サポート** | - |
| `list_parameters()` | ✗ | **未サポート** | - |
| `add_on_set_parameters_callback()` | ✗ | **未サポート** | パラメータ変更コールバック登録 |
| `remove_on_set_parameters_callback()` | ✗ | **未サポート** | パラメータ変更コールバック削除 |
| パラメータイベントpublisher | ✗ | **未サポート** | - |
| パラメータサービス | ✗ | **未サポート** | - |
| パラメータディスクリプタ | ✓ | **部分サポート** | descriptionとread_onlyフィールドのみ |
| YAMLファイル読み込み | ✓ | **完全サポート** | agnocast_node.cpp:540-702 |
| コマンドライン上書き | ✓ | **部分サポート** | -pフラグ経由（制限あり、下記参照） |
| 配列型 | ✗ | **未サポート** | スカラー型のみ (bool, int64_t, double, string) |

**サマリー**:
- ✓ サポート: 6メソッド (declare, has, get, get_types, YAML読み込み, CLI上書き)
- ⚠ 部分サポート: 1機能 (パラメータディスクリプタ - 限定フィールド)
- ✗ 未サポート: 14機能 (get_parameter_or, set_parameter, set_parameters, set_parameters_atomically, undeclare, describe, list, get_parameters_by_prefix, コールバック登録/削除, イベント, サービス, 配列)

**主な制限事項**:
1. **宣言後は読み取り専用**: `declare_parameter()`後にパラメータを変更できない
2. **パラメータサービスなし**: ROSサービス経由でパラメータをリモートクエリ/設定できない
3. **配列型なし**: スカラー型のみサポート (PARAMETER_BOOL, PARAMETER_INTEGER, PARAMETER_DOUBLE, PARAMETER_STRING)
4. **コールバックなし**: パラメータ変更時のコールバック登録不可
5. **限定ディスクリプタ**: `description`と`read_only`フィールドのみサポート
6. **-p/--paramフラグの制限**:
   - **yaml parserなし**: 配列（例: `[1,2,3]`）は文字列として扱われる
   - **ノード名プレフィックス未対応**: `node_name:param_name:=value` 形式は未サポート

---

### 2.4 NodeGraphInterface

**目的**: ROSグラフのイントロスペクションと検出

| 機能 | agnocast::Node | サポートレベル | 備考 |
|------|----------------|---------------|------|
| すべてのグラフイントロスペクションAPI | ✗ | **未サポート** | - |

**理由**: AgnocastはDDS検出に参加せず、ROSグラフへのアクセスがありません。これは基本的なアーキテクチャの違いです。

---

### 2.5 その他のインターフェース

以下のインターフェースはすべて **未サポート** です。agnocast::Nodeはこれらのインターフェースを実装していません。

#### NodeLoggingInterface

| 機能 | agnocast::Node | サポートレベル | 備考 |
|------|----------------|---------------|------|
| `get_logger()` | ✗ | **未サポート** | 707回使用される重要なAPI |
| `get_logger_name()` | ✗ | **未サポート** | - |

**理由**: agnocast::Nodeはロギング機能を提供しません。ユーザーは標準C++ロギングまたはprintfを使用できます。

#### NodeServicesInterface, NodeTimersInterface, NodeClockInterface, NodeWaitablesInterface, NodeTimeSourceInterface

これらのインターフェースもすべて未サポートです。

---

## 3. コンテキストと初期化アーキテクチャ

### 3.1 グローバルコンテキスト (rclcpp::Context vs agnocast::GlobalContext)

| 機能 | agnocast::GlobalContext | サポートレベル |
|------|------------------------|---------------|
| シングルトンアクセス | ✓ (GlobalContext::instance()) | **完全サポート** |
| 初期化 | ✓ (init()) | **完全サポート** |
| 引数パース | ✓ | **部分サポート** |
| リマップルール保存 | ✓ | **完全サポート** |
| パラメータ上書き保存 | ✓ | **完全サポート** |
| シャットダウン/ライフサイクル | ✗ | **未サポート** |
| シグナルハンドリング | ✗ | **未サポート** |
| RCLコンテキストハンドル | ✗ | **未サポート** |

**主要ファイル**:
- rclcpp: `rclcpp/context.hpp`, `rclcpp/init_options.hpp`
- agnocast: `agnocast_context.hpp` (1-127行), `agnocast_context.cpp` (1-183行)

### 3.2 初期化関数

| 関数 | agnocast | サポートレベル | 備考 |
|------|----------|---------------|------|
| `init(argc, argv)` | ✓ | **完全サポート** | agnocast_context.cpp:175-180 |
| `shutdown()` | ✗ | **未サポート** | - |
| `ok()` | ✗ | **未サポート** | - |
| カスタムコンテキスト | ✗ | **未サポート** | agnocastはシングルトンのみ使用 |

---

## 4. 引数パースと名前解決

### 4.1 コマンドライン引数サポート

| 引数タイプ | agnocast | サポートレベル | 備考 |
|-----------|----------|---------------|------|
| `--ros-args` | ✓ | **完全サポート** | agnocast_node.cpp:249 |
| `-r topic:=new_topic` | ✓ | **完全サポート** | トピックリマップ |
| `-r __ns:=/namespace` | ✓ | **完全サポート** | ネームスペースリマップ |
| `-r __node:=name` | ✓ | **完全サポート** | ノード名リマップ |
| `-p param:=value` | ✓ | **完全サポート** | パラメータ上書き |
| `--params-file file.yaml` | ✓ | **完全サポート** | YAMLパラメータ読み込み |
| `--` (終了マーカー) | ✓ | **完全サポート** | ROS引数の終了 |
| `--log-level` | ✗ | **未サポート** | - |
| `--enable-rosout-logs` | ✗ | **未サポート** | - |
| `--disable-rosout-logs` | ✗ | **未サポート** | - |
| `-e` (enclave) | ✗ | **未サポート** | - |

**実装**: agnocast_node.cpp:224-293

### 4.2 トピック名解決

| 機能 | agnocast | サポートレベル | 備考 |
|------|----------|---------------|------|
| プライベートトピック (`~topic`) | ✓ | **完全サポート** | agnocast_node.cpp:112-121 |
| 相対トピック (`topic`) | ✓ | **完全サポート** | agnocast_node.cpp:152-159 |
| 絶対トピック (`/topic`) | ✓ | **完全サポート** | agnocast_node.cpp:108-110 |
| 置換 (`{node}`) | ✓ | **完全サポート** | agnocast_node.cpp:136 |
| 置換 (`{ns}`, `{namespace}`) | ✓ | **完全サポート** | agnocast_node.cpp:138-139 |
| トピックリマッピング | ✓ | **完全サポート** | agnocast_node.cpp:164-186 |
| サービスリマッピング | ✗ | **未サポート** | - |

**主要メソッド**:
- `resolve_topic_name()`: agnocast_node.cpp:68-72
- `expand_topic_name()`: agnocast_node.cpp:86-162
- `remap_name()`: agnocast_node.cpp:164-186

**RCL対応**:
- `rcl_expand_topic_name`: rcl/src/rcl/expand_topic_name.c:44-219
- `rcl_remap_name`: rcl/src/rcl/remap.c:167-231
- `rcl_node_resolve_name`: rcl/src/rcl/node_resolve_name.c:134-162

---

## 5. ノード構築パターン

### 5.1 argc/argvを使った構築

**rclcpp::Node**:
```cpp
rclcpp::init(argc, argv);
auto node = std::make_shared<rclcpp::Node>("node_name", "namespace");
```

**agnocast::Node**:
```cpp
// オプション1: グローバルコンテキストを使用
agnocast::init(argc, argv);
auto node = std::make_shared<agnocast::Node>("node_name", "namespace");

// オプション2: ローカルで引数をパース
auto node = std::make_shared<agnocast::Node>(argc, argv, "node_name", "namespace");
```

### 5.2 動作の違い

| 側面 | agnocast | 備考 |
|------|----------|------|
| グローバルコンテキスト必須 | ✗ (オプション) | agnocastはローカルで引数をパース可能 |
| NodeOptionsサポート | ✗ | agnocastにはNodeOptionsなし |
| サブノード | ✗ | agnocastはサブノード非サポート |
| ライフサイクルノード | ✗ | 該当なし |
| Publisherサポート | **✗** | **agnocast::NodeはPublisherを作成不可** |
| Subscriptionサポート | ✓ | agnocast::Nodeでも作成可能 |

---

## 6. Composable Nodeに関する考慮事項

### 6.1 コンポーネント読み込み

**agnocast::Node自体はコンポーザブルではない**が、以下のパターンでコンポーネント化可能:

**パターン: rclcpp::Node + agnocast::Node のハイブリッド**
```cpp
class MyComponent : public rclcpp::Node {
  agnocast::Node::SharedPtr agnocast_node_;
  agnocast::Subscription<MsgType>::SharedPtr subscription_;

public:
  explicit MyComponent(const rclcpp::NodeOptions& options)
    : Node("my_component", options) {
    // rclcpp::Node: コンポーネントインフラ、ライフサイクル管理用
    // agnocast::Node: パラメータ管理、トピック名解決用
    agnocast_node_ = std::make_shared<agnocast::Node>(
      "my_component", this->get_namespace());

    // パラメータ管理はagnocast::Nodeで
    agnocast_node_->declare_parameter("topic", std::string("default"));
    std::string topic;
    agnocast_node_->get_parameter("topic", topic);
    std::string resolved = agnocast_node_->resolve_topic_name(topic);

    // Subscriptionは rclcpp::Node (this) または agnocast::Node で作成可能
    subscription_ = agnocast::create_subscription<MsgType>(
      this,  // または agnocast_node_.get()
      resolved, 10, callback, options);
  }
};

RCLCPP_COMPONENTS_REGISTER_NODE(MyComponent)
```

### 6.2 動作の違い: Composable vs 実行ファイル

| シナリオ | rclcpp Composable | rclcpp 実行ファイル | agnocast | 備考 |
|---------|------------------|-------------------|----------|------|
| コンテキスト共有 | 共有 | 独立 | GlobalContextシングルトン | - |
| Executor | 共有または個別 | 独立 | AgnocastExecutor（共有可能） | - |
| プロセス内通信 | 利用可能 | 利用可能 | 利用不可 | - |
| 引数パース | NodeOptions経由 | argc/argv経由 | argc/argvまたはグローバル経由 | - |
| メモリオーバーヘッド | 低い (共有) | 高い (個別) | 非常に低い (共有メモリ直接アクセス) | - |
| `rclcpp::init()`必要性 | ✓ | ✓ | Publisherなら✓、Subscriptionのみなら✗ | - |

**重要**: `agnocast::Node`自体はコンポーネントとして読み込めませんが、`rclcpp::Node`を継承したクラスに`agnocast::Node`をメンバとして持たせることで、コンポーザブルノードの利点を得られます。

---

## 7. Publisher と Subscription の API

### 7.1 Publisher

| 機能 | agnocast::Publisher | サポートレベル | 備考 |
|------|---------------------|---------------|------|
| テンプレートベースAPI | ✓ | **完全サポート** | - |
| `publish(msg)` | ✓ | **完全サポート** | - |
| `borrow_loaned_message()` | ✓ | **完全サポート** | agnocast_publisher.hpp:176-181 |
| QoSパラメータ受け取り | ✓ | **部分サポート** | QoSオブジェクトは受け取るが、実際の使用は限定的 |
| `get_subscription_count()` | ✓ | **完全サポート** | agnocast_publisher.hpp:224-227 |
| トピック統計 | ✗ | **未サポート** | - |
| プロセス内通信 | ✗ | **未サポート** | 共有メモリ通信 |
| ローンメッセージ (DDS) | ✗ | **代替実装** | ipc_shared_ptrを使用 |
| **agnocast::Nodeサポート** | **✗** | **未サポート** | **rclcpp::Nodeが必要** |

**重要な制限**:
```cpp
// これは動作する
rclcpp::Node* node = /* ... */;
auto pub = agnocast::create_publisher<MsgType>(node, "topic", 10);

// これは動作しない！（コンストラクタが存在しない）
agnocast::Node* node = /* ... */;
auto pub = agnocast::create_publisher<MsgType>(node, "topic", 10);  // コンパイルエラー
```

### 7.2 Subscription

| 機能 | agnocast::Subscription | サポートレベル | 備考 |
|------|------------------------|---------------|------|
| テンプレートベースAPI | ✓ | **完全サポート** | - |
| コールバック実行 | ✓ | **完全サポート** | Executorが実行 |
| QoSパラメータ受け取り | ✓ | **部分サポート** | QoSオブジェクトは受け取る |
| トピック統計 | ✗ | **未サポート** | - |
| プロセス内通信 | ✗ | **未サポート** | 共有メモリ通信 |
| メッセージフィルタ | ✗ | **未サポート** | - |
| **agnocast::Nodeサポート** | **✓** | **完全サポート** | **rclcpp::NodeとagnocastNode両方OK** |
| **rclcpp::init()要否** | **Subscription単独なら不要** | **部分要** | 純粋agnocastなら`agnocast::init()`のみ |

**Subscriptionの柔軟性**:
```cpp
// パターン1: rclcpp::Nodeで作成
rclcpp::Node* rclcpp_node = /* ... */;
auto sub = agnocast::create_subscription<MsgType>(
  rclcpp_node, "topic", 10, callback);

// パターン2: agnocast::Nodeで作成（rclcpp::init()不要！）
agnocast::Node* agnocast_node = /* ... */;
auto sub = agnocast::create_subscription<MsgType>(
  agnocast_node, "topic", 10, callback);
```

### 7.3 TakeSubscription / PollingSubscriber

agnocastは追加で**ポーリングベースのサブスクリプション**も提供:

```cpp
// Autoware互換のポーリングサブスクライバー
auto sub = agnocast::create_subscription<MsgType>(rclcpp_node, "topic", 10);
// または
auto sub = std::make_shared<agnocast::PollingSubscriber<MsgType>>(
  rclcpp_node, "topic", rclcpp::QoS{10});

// ポーリングで取得
auto msg = sub->take_data();  // または takeData() (後方互換性)
if (msg) {
  // メッセージ処理
}
```

**注**: PollingSubscriberは`rclcpp::Node`のみサポート

---

## 8. 総合サポート状況サマリー

### 8.1 サポート機能 (✓)

1. **ノードのアイデンティティ**: name, namespace, fully qualified name
2. **トピック名解決**: 展開, 置換, リマッピング
3. **パラメータ管理**: declare, get, has, types, YAML読み込み
4. **Subscription作成**: rclcpp::NodeとagnocastNode両方で可能
5. **コマンドライン引数**: `--ros-args`, `-r`, `-p`, `--params-file`
6. **グローバルコンテキスト**: 初期化, リマップルール, パラメータ上書き
7. **コールバックグループ**: デフォルトコールバックグループアクセス
8. **Executor**: SingleThreaded, MultiThreaded, CallbackIsolated

### 8.2 部分サポート機能 (⚠)

1. **パラメータディスクリプタ**: `description`と`read_only`フィールドのみ
2. **名前解決**: トピックのみ (サービスは非対応)
3. **コールバックグループ**: デフォルトグループのみ (カスタムグループなし)
4. **QoS**: QoSオブジェクトは受け取るが、完全な機能は使用していない可能性

### 8.3 未サポート機能 (✗)

**コアインフラ**:
- RCLハンドルとコンテキスト（GlobalContext使用）
- カスタムコールバックグループ作成

**通信**:
- **Publisher作成（agnocast::Nodeから）** - rclcpp::Nodeが必要
- サービス (クライアント/サーバー)
- アクション
- 完全なQoSプロファイル制御
- プロセス内通信（共有メモリ使用）

**検出とイントロスペクション**:
- すべてのグラフイントロスペクションAPI
- ノード検出

**時刻とロギング**:
- ROSクロックと時刻
- Loggerインターフェース
- `/clock`トピック

**高度な機能**:
- タイマー
- Waitable
- ライフサイクルノード
- ネイティブなコンポーネントコンポジション（ハイブリッドパターンで対応可能）
- メッセージフィルタ
- パラメータサービスとコールバック
- パラメータイベント

---

## 9. ユースケース推奨

### 9.1 agnocast::Nodeを使うべき場合

✓ **推奨**:
- **Subscription専用アプリケーション**（Publisherが不要な場合）
- rclcpp依存を最小化したい
- パラメータ管理とトピック名解決だけが必要
- rclcpp::Nodeと併用してパラメータ管理を分離したい

✗ **非推奨**:
- Publisherが必要な場合（rclcpp::Nodeが必須）
- タイマーが必要な場合
- ロガーが必要な場合

### 9.2 ハイブリッドパターン (rclcpp::Node + agnocast::Node)

✓ **推奨**:
- PublisherとSubscriptionの両方が必要
- rclcpp::Nodeの機能（タイマー、ロガー等）を使いつつ、agnocastの軽量パラメータ管理も使いたい
- コンポーザブルノードが必要

### 9.3 純粋agnocastパターン (agnocast::Nodeのみ)

✓ **推奨**:
- Subscription専用
- 最小限の依存関係
- rclcpp::init()なしで動作させたい
- 組み込みシステムでリソースが限られている

---

## 10. ファイル別実装状況

### agnocast_node.hpp (328行)
- **79-327行**: Nodeクラス定義
- **85-103行**: コンストラクタ (2種類)
- **105-131行**: ノードアイデンティティメソッド
- **133-146行**: コールバックグループメソッド
- **148-158行**: トピック名解決
- **160-219行**: パラメータ管理
- **221-301行**: プライベートパースと解決メソッド
- **316-324行**: メンバ変数

### agnocast_node.cpp (723行)
- **14-54行**: コンストラクタ実装
- **56-72行**: ノードアイデンティティメソッド
- **74-186行**: 名前解決実装
- **188-222行**: グローバルコンテキストマージ
- **224-293行**: ROS引数パース
- **295-411行**: リマップルールとパラメータパース
- **413-538行**: パラメータ管理
- **540-702行**: YAMLファイル読み込み
- **704-720行**: コールバックグループメソッド

### agnocast_publisher.hpp (230行)
- **52-228行**: Publisherクラステンプレート
- **70-111行**: コンストラクタ（**rclcpp::Nodeのみ**）
- **176-181行**: borrow_loaned_message()
- **183-222行**: publish()
- **224-227行**: get_subscription_count()

### agnocast_subscription.hpp (219行)
- **71-131行**: Subscriptionクラステンプレート
- **78-106行**: rclcpp::Node用コンストラクタ
- **108-128行**: **agnocast::Node用コンストラクタ**
- **134-197行**: TakeSubscriptionクラス
- **200-217行**: PollingSubscriberクラス

### agnocast_executor.hpp (54行)
- **19-52行**: AgnocastExecutor基底クラス（rclcpp::Executorを継承）

### agnocast_single_threaded_executor.hpp (37行)
- **10-35行**: SingleThreadedAgnocastExecutor

### agnocast_multi_threaded_executor.hpp (39行)
- **11-37行**: MultiThreadedAgnocastExecutor

### agnocast_callback_isolated_executor.hpp (76行)
- **8-74行**: CallbackIsolatedAgnocastExecutor

### agnocast_context.hpp (127行)
- **20-113行**: GlobalContextクラス定義
- **116-124行**: init()関数

### agnocast_context.cpp (183行)
- **6-12行**: シングルトンインスタンス
- **14-80行**: init()実装
- **82-173行**: パースメソッド
- **175-180行**: agnocast::init()ラッパー

---

## 11. 互換性マトリクス

| 機能カテゴリ | rclcppメソッド数 | agnocastサポート数 | カバー率 |
|------------|----------------|-------------------|---------|
| ノードアイデンティティ | 3 | 3 | 100% |
| トピック解決 | 2 | 2 | 100% |
| パラメータ (基本) | 4 | 4 | 100% |
| パラメータ (高度) | 10 | 0 | 0% |
| Subscription作成 | 1 | 1 | 100% |
| Publisher作成 (agnocast::Node) | 1 | **0** | **0%** |
| Publisher作成 (rclcpp::Node) | 1 | 1 | 100% |
| Executor | 3種類 | 3種類 | 100% |
| グラフイントロスペクション | 13 | 0 | 0% |
| サービス | 3 | 0 | 0% |
| タイマー | 2 | 0 | 0% |
| ロギング | 2 | 0 | 0% |
| クロック | 1 | 0 | 0% |
| Waitable | 2 | 0 | 0% |
| コールバックグループ (基本) | 2 | 2 | 100% |
| コールバックグループ (高度) | 3 | 0 | 0% |

---

## 12. 既知の制限と回避策

### 12.1 Publisherにはrclcpp::Nodeが必要

**制限**: `agnocast::Node`から`agnocast::Publisher`を作成できない

**回避策**:
```cpp
// rclcpp::Nodeとagnocast::Nodeを併用
class MyNode : public rclcpp::Node {
  agnocast::Node::SharedPtr agnocast_node_;
  agnocast::Publisher<MsgType>::SharedPtr publisher_;

  MyNode() : Node("my_node") {
    agnocast_node_ = std::make_shared<agnocast::Node>("my_node");
    // agnocast::Nodeでパラメータ管理
    // rclcpp::Nodeでpublisher作成
    publisher_ = agnocast::create_publisher<MsgType>(this, "topic", 10);
  }
};
```

### 12.2 宣言後のパラメータ変更不可

**制限**: `declare_parameter()`後にパラメータは読み取り専用

**回避策**: デフォルト値で宣言し、ユーザーが`-p`やYAML経由で上書き

### 12.3 グラフイントロスペクションなし

**制限**: グラフ内のトピック、ノード、エンドポイントをクエリできない

**回避策**: `ros2` CLIツールを別途使用するか、手動設定を維持

### 12.4 配列パラメータなし

**制限**: スカラーパラメータ型のみサポート

**回避策**: 複数のスカラーパラメータを使用するか、文字列パラメータからパース

### 12.5 純粋agnocastではタイマー使用不可

**制限**: `agnocast::Node`のみではタイマーを作成できない

**回避策**:
- rclcpp::Nodeと併用してタイマーを使う
- std::threadやOSタイマーを使う

---

## 13. サンプルコード分析

### 13.1 minimal_publisher.cpp

**パターン**: rclcpp::Node + agnocast::Node ハイブリッド

```cpp
class MinimalPublisher : public rclcpp::Node {
  agnocast::Node::SharedPtr agnocast_node_;  // パラメータ管理用
  agnocast::Publisher<MsgType>::SharedPtr publisher_;  // rclcpp::Node必要
  rclcpp::TimerBase::SharedPtr timer_;  // rclcpp::Node機能

  MinimalPublisher() : Node("minimal_publisher") {
    agnocast_node_ = std::make_shared<agnocast::Node>("minimal_publisher");
    // agnocast::Nodeでパラメータ管理
    agnocast_node_->declare_parameter("topic_name", std::string("my_topic"));
    // rclcpp::Nodeでpublisher作成
    publisher_ = agnocast::create_publisher<MsgType>(this, resolved_topic, 1);
    // rclcpp::Nodeでタイマー作成
    timer_ = this->create_wall_timer(period, callback);
  }
};

int main(int argc, char* argv[]) {
  agnocast::init(argc, argv);  // グローバルコンテキスト
  rclcpp::init(argc, argv);    // rclcpp::Node用
  agnocast::SingleThreadedAgnocastExecutor executor;  // Agnocast executor!
  auto node = std::make_shared<MinimalPublisher>();
  executor.add_node(node);
  executor.spin();
  rclcpp::shutdown();
}
```

### 13.2 minimal_subscriber.cpp

**パターン1**: Composableノード（rclcpp::Node + agnocast::Node）
```cpp
class MinimalSubscriberComponent : public rclcpp::Node {
  agnocast::Node::SharedPtr agnocast_node_;
  agnocast::Subscription<MsgType>::SharedPtr sub_;

  explicit MinimalSubscriberComponent(const rclcpp::NodeOptions& options)
    : Node("minimal_subscriber", options) {
    agnocast_node_ = std::make_shared<agnocast::Node>("minimal_subscriber");
    // agnocast::Nodeでパラメータ管理
    // rclcpp::Nodeでsubscription作成（thisはrclcpp::Node*）
    sub_ = agnocast::create_subscription<MsgType>(this, topic, 1, callback);
  }
};
RCLCPP_COMPONENTS_REGISTER_NODE(MinimalSubscriberComponent)
```

**パターン2**: 純粋agnocast（agnocast::Nodeのみ）
```cpp
class MinimalSubscriber {  // rclcpp::Nodeを継承しない！
  agnocast::Node::SharedPtr node_;
  agnocast::Subscription<MsgType>::SharedPtr sub_;

  MinimalSubscriber() {
    node_ = std::make_shared<agnocast::Node>("minimal_subscriber");
    // agnocast::Nodeでsubscription作成
    sub_ = agnocast::create_subscription<MsgType>(
      node_.get(), resolved_topic, 1, callback);
  }
};

int main(int argc, char* argv[]) {
  agnocast::init(argc, argv);  // rclcpp::init()不要！
  agnocast::SingleThreadedAgnocastExecutor executor;
  auto subscriber = std::make_shared<MinimalSubscriber>();
  executor.spin();  // rclcpp::shutdown()不要！
}
```

---

## 結論

### agnocast::Nodeの位置付け

`agnocast::Node`は**rclcpp::Nodeの完全な代替ではなく、特定の用途に特化した補完的な実装**です:

**✓ 得意分野**:
1. **パラメータ管理**: YAML、CLI、リマッピングからの読み込み
2. **トピック名解決**: ROS 2名前解決ルールの完全実装
3. **Subscription専用ノード**: rclcpp::init()なしで動作可能
4. **軽量実装**: DDS非依存、最小限のオーバーヘッド

**✗ 制限事項**:
1. **Publisher作成不可**: rclcpp::Nodeが必要
2. **高度な機能なし**: タイマー、ロガー、サービス、グラフイントロスペクション等

**推奨使用パターン**:
- **ハイブリッド**: `rclcpp::Node`を継承し、`agnocast::Node`をメンバとして持つ（パラメータ管理用）
- **純粋agnocast**: Subscription専用で最小限の依存関係が必要な場合

**設計哲学**:
ROS 2互換性（パラメータ、トピック名解決）を保ちつつ、軽量で高性能な共有メモリ通信を実現。ただし、Publisherにはrclcpp::Nodeのインフラが必要という制約がある。

**Executorについて**:
agnocastは**独自のExecutor実装**を提供し、共有メモリメッセージとDDSメッセージの両方を効率的に処理できます。これにより、agnocastとROS 2の混在環境でも統一されたイベントループを使用できます。
