# Agnocast::Node と rclcpp::Node のインターフェース比較

## エグゼクティブサマリー

本ドキュメントは、`agnocast::Node`と`rclcpp::Node`の包括的な比較を提供し、Agnocast実装でサポートされている機能、部分的にサポートされている機能、サポートされていない機能を詳述します。

**主な特徴**:

- `rclcpp::Node`は10個の異なるノードインターフェースを持つモジュラーアーキテクチャ
- `agnocast::Node`は、**DDS participantを作成しない**ノード実装（パラメータ管理とトピック名解決に特化）
- **agnocastは独自のExecutor実装を提供** (SingleThreaded, MultiThreaded, CallbackIsolated)
- Publisherは`rclcpp::Node`が必要、Subscriptionは`agnocast::Node`でも作成可能
- **rclcpp互換のノードインターフェースを継承** (`NodeBaseInterface`, `NodeTopicsInterface`, `NodeParametersInterface`)
- **NodeOptionsをサポート** (parameter_overrides, context等)
- **`get_logger()`をサポート** (rclcpp::Loggerを返す)

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

**重要**: `agnocast::node_interfaces::NodeBase`は`rclcpp::node_interfaces::NodeBaseInterface`を**継承**しており、rclcppとの互換性が高い。

| 機能 | agnocast::Node | サポートレベル | 備考 |
|------|----------------|---------------|------|
| `get_name()` | ✓ | **完全サポート** | node_base.cpp:77-80 |
| `get_namespace()` | ✓ | **完全サポート** | node_base.cpp:82-85 |
| `get_fully_qualified_name()` | ✓ | **完全サポート** | node_base.cpp:87-90 |
| `get_context()` | ✓ | **完全サポート** | node_base.cpp:94-97, rclcpp::Context::SharedPtrを返す |
| `get_rcl_node_handle()` | ✗ | **例外スロー** | DDS不使用のため、呼び出すとstd::runtime_error |
| `get_shared_rcl_node_handle()` | ✗ | **例外スロー** | DDS不使用のため、呼び出すとstd::runtime_error |
| `create_callback_group()` | ✓ | **完全サポート** | node_base.cpp:131-140 |
| `get_default_callback_group()` | ✓ | **完全サポート** | node_base.cpp:142-145 |
| `callback_group_in_node()` | ✓ | **完全サポート** | node_base.cpp:147-157 |
| `for_each_callback_group()` | ✓ | **完全サポート** | node_base.cpp:159-168 |
| `get_notify_guard_condition()` | ✓ | **完全サポート** | node_base.cpp:185-195 |
| `get_associated_with_executor_atomic()` | ✓ | **完全サポート** | node_base.cpp:172-175 |
| `resolve_topic_or_service_name()` | ✓ (トピックのみ) | **部分サポート** | node_base.cpp:212-244, サービス解決はトピックと同じ |
| `get_use_intra_process_default()` | ✓ | **完全サポート** | 常にfalseを返す (agnocast独自IPC使用) |
| `get_enable_topic_statistics_default()` | ✓ | **完全サポート** | 常にfalseを返す |
| `create_sub_node()` | ✗ | **未サポート** | サブノード作成機能なし |
| `get_sub_namespace()` | ✗ | **未サポート** | サブネームスペース機能なし |
| `get_effective_namespace()` | ✗ | **未サポート** | agnocastでは`get_namespace()`が実効ネームスペース |

**サマリー**:

- ✓ サポート: 13メソッド (name, namespace, FQN, context, callback group系4つ, guard condition, executor atomic, resolve name, intra process, topic statistics)
- ⚠ 部分サポート: 1メソッド (resolve_topic_or_service_name - サービス固有の処理なし)
- ✗ 例外スロー: 4メソッド (rcl_node_handle系) - DDS不使用のため
- ✗ 未サポート: 3機能 (サブノード関連)

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

**重要**: `agnocast::node_interfaces::NodeParameters`は`rclcpp::node_interfaces::NodeParametersInterface`を**継承**しており、rclcppとの互換性が高い。

| 機能 | agnocast::Node | サポートレベル | 備考 |
|------|----------------|---------------|------|
| `declare_parameter()` | ✓ | **完全サポート** | 非テンプレート版とテンプレート版両方 (node_parameters.hpp:37-47) |
| `undeclare_parameter()` | ✓ | **完全サポート** | node_parameters.hpp:49 |
| `has_parameter()` | ✓ | **完全サポート** | node_parameters.hpp:51 |
| `set_parameter()` | ✓ | **完全サポート** | agnocast_node.hpp:107-111 |
| `set_parameters()` | ✓ | **完全サポート** | node_parameters.hpp:53-54 |
| `set_parameters_atomically()` | ✓ | **完全サポート** | node_parameters.hpp:56-57 |
| `get_parameter()` | ✓ | **完全サポート** | 複数オーバーロード (node_parameters.hpp:59-64) |
| `get_parameter_or()` | ✓ | **完全サポート** | agnocast_node.hpp:154-172 |
| `get_parameters()` | ✓ | **完全サポート** | node_parameters.hpp:59-60 |
| `get_parameter_types()` | ✓ | **完全サポート** | node_parameters.hpp:73 |
| `get_parameters_by_prefix()` | ✓ | **完全サポート** | node_parameters.hpp:66-68 |
| `describe_parameter()` | ✓ | **完全サポート** | agnocast_node.hpp:183-190 |
| `describe_parameters()` | ✓ | **完全サポート** | node_parameters.hpp:70-71 |
| `list_parameters()` | ✓ | **完全サポート** | node_parameters.hpp:75-76 |
| `add_on_set_parameters_callback()` | ✓ | **完全サポート** | node_parameters.hpp:78-79 |
| `remove_on_set_parameters_callback()` | ✓ | **完全サポート** | node_parameters.hpp:81-82 |
| `get_parameter_overrides()` | ✓ | **完全サポート** | node_parameters.hpp:84 |
| パラメータイベントpublisher | ✗ | **未サポート** | - |
| パラメータサービス | ✗ | **未サポート** | - |
| YAMLファイル読み込み | ✓ | **完全サポート** | agnocast_context.cpp:201-285 |
| コマンドライン上書き | ✓ | **部分サポート** | -pフラグ経由（制限あり、下記参照） |
| 配列型 | ✗ | **未サポート** | スカラー型のみ (bool, int64_t, double, string) |

**サマリー**:

- ✓ サポート: 18メソッド (declare, undeclare, has, set系3つ, get系4つ, describe系2つ, list, callback系2つ, get_parameter_overrides, get_parameters_by_prefix)
- ⚠ 部分サポート: 1機能 (CLI上書き - 配列未対応)
- ✗ 未サポート: 3機能 (パラメータイベント, パラメータサービス, 配列型)

**主な制限事項**:

1. **パラメータサービスなし**: ROSサービス経由でパラメータをリモートクエリ/設定できない
2. **配列型なし**: スカラー型のみサポート (PARAMETER_BOOL, PARAMETER_INTEGER, PARAMETER_DOUBLE, PARAMETER_STRING)
3. **-p/--paramフラグの制限**:
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
| `get_logger()` | ✓ | **完全サポート** | agnocast_node.hpp:49, rclcpp::Loggerを返す |
| `get_logger_name()` | ✗ | **未サポート** | - |

**備考**: `get_logger()`はノード名に基づいたrclcpp::Loggerを返します。RCLCPP_INFO等のマクロが使用可能です。

#### NodeServicesInterface, NodeTimersInterface, NodeClockInterface, NodeWaitablesInterface, NodeTimeSourceInterface

これらのインターフェースもすべて未サポートです。

---

## 3. コンテキストと初期化アーキテクチャ

### 3.1 グローバルコンテキスト (rclcpp::Context vs agnocast::Context)

| 機能 | agnocast::Context | サポートレベル |
|------|------------------------|---------------|
| シングルトンアクセス | ✓ (Context::instance()) | **完全サポート** |
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
| `-r node:old:=new` | ✓ | **完全サポート** | ノード固有リマッピング |
| `--log-level` | ✗ | **未サポート** | - |
| `--enable-rosout-logs` | ✗ | **未サポート** | - |
| `--disable-rosout-logs` | ✗ | **未サポート** | - |
| `-e` (enclave) | ✗ | **未サポート** | - |

**実装**: agnocast_node.cpp:224-293

#### `-r`/`--remap`の制限事項

| 制限 | 説明 |
|------|------|
| URL scheme未対応 | `rostopic://`、`rosservice://`プレフィックスによる明示的な型指定は未サポート |

**rclとの比較例**:

| 入力 | rcl | agnocast |
|------|-----|----------|
| `-r __node:=my_node` | ノード名を`my_node`に設定 | ノード名を`my_node`に設定 |
| `-r __ns:=/my_ns` | 名前空間を`/my_ns`に設定 | 名前空間を`/my_ns`に設定 |
| `-r /foo:=/bar` | トピックとサービスをリマップ | トピックとサービスをリマップ |
| `-r my_node:/foo:=/bar` | `my_node`のみにリマップ適用 | `my_node`のみにリマップ適用 |
| `-r rostopic:///foo:=/bar` | 明示的トピックリマップ | パースエラー |

#### `-p`/`--param`の制限事項

| 制限 | 説明 |
|------|------|
| yaml parserなし | 配列や複雑なYAML型は未サポート。スカラー値のみ対応 |
| ノード名プレフィックス未対応 | ノード固有パラメータ構文は未サポート |

**rclとの比較例**:

| 入力 | rcl | agnocast |
|------|-----|----------|
| `-p foo:=123` | int `123` | int `123` |
| `-p foo:=true` | bool `true` | bool `true` |
| `-p foo:=[1,2,3]` | int array `{1,2,3}` | string `"[1,2,3]"` |
| `-p /my_node:foo:=123` | `/my_node`のみに`foo=123` | パラメータ名が`/my_node:foo`になる |

### 4.2 トピック名解決

| 機能 | agnocast | サポートレベル | 備考 |
|------|----------|---------------|------|
| プライベートトピック (`~topic`) | ✓ | **完全サポート** | node_topics.cpp:128-137 |
| 相対トピック (`topic`) | ✓ | **完全サポート** | node_topics.cpp:181-191 |
| 絶対トピック (`/topic`) | ✓ | **完全サポート** | node_topics.cpp:121-124 |
| 置換 (`{node}`) | ✓ | **完全サポート** | node_topics.cpp:165-166 |
| 置換 (`{ns}`, `{namespace}`) | ✓ | **完全サポート** | node_topics.cpp:167-168 |
| トピックリマッピング | ✓ | **完全サポート** | node_topics.cpp:196-222 |
| カスタム置換 | ✗ | **未サポート** | TODO: rcutils_string_map_t対応 |
| サービスリマッピング | ✗ | **未サポート** | - |

**主要メソッド**:

- `resolve_topic_name()`: node_topics.cpp:16-24
- `expand_topic_name()`: node_topics.cpp:95-193
- `remap_name()`: node_topics.cpp:196-222

**RCL対応**:

- `rcl_expand_topic_name`: rcl/src/rcl/expand_topic_name.c:44-219
- `rcl_remap_name`: rcl/src/rcl/remap.c:167-231
- `rcl_node_resolve_name`: rcl/src/rcl/node_resolve_name.c:134-162

#### 4.2.1 expand_topic_name 詳細比較

**アーキテクチャの違い**:

| 項目 | rclcpp (RCL) | agnocast |
|------|-------------|----------|
| 関数シグネチャ | `rcl_expand_topic_name(input, node, ns, subs, alloc, out)` | `expand_topic_name(input)` (メンバ関数) |
| 実装場所 | rcl (C) + rclcpp (C++ラッパー) | NodeTopicsクラス内 |
| node_name/namespace取得 | 引数から | `node_base_->get_name()/get_namespace()` |

**機能比較**:

| 機能 | rclcpp | agnocast | 差分 |
|------|--------|----------|------|
| 絶対パス (`/foo`) | ✓ | ✓ | 同等 |
| 相対パス (`foo`) | ✓ | ✓ | 同等 |
| チルダ展開 (`~`) | ✓ | ✓ | 同等 |
| `{node}` substitution | ✓ | ✓ | 同等 |
| `{ns}` substitution | ✓ | ✓ | 同等 |
| `{namespace}` substitution | ✓ | ✓ | 同等 |
| カスタムsubstitution | ✓ (`rcutils_string_map_t`) | ✗ | **差分あり** |
| 入力バリデーション | ✓ (`rcl_validate_topic_name`) | △ (empty checkのみ) | **差分あり** |
| ノード名バリデーション | ✓ (`rmw_validate_node_name`) | ✗ | **差分あり** |
| namespace バリデーション | ✓ (`rmw_validate_namespace`) | ✗ | **差分あり** |

**具体的な入出力の差分**:

同等の動作をするケース:

| 入力 | node | namespace | 両方の出力 |
|------|------|-----------|------------|
| `/chatter` | my_node | /my_ns | `/chatter` |
| `chatter` | my_node | /my_ns | `/my_ns/chatter` |
| `{node}/chatter` | my_node | /my_ns | `/my_ns/my_node/chatter` |
| `/{node}` | my_node | /my_ns | `/my_node` |
| `{node}` | my_node | /my_ns | `/my_ns/my_node` |
| `{ns}` | my_node | /my_ns | `/my_ns` |
| `{namespace}/{node}/chatter` | my_node | /my_ns | `/my_ns/my_node/chatter` |
| `ping` | my_node | `/` | `/ping` |
| `~` | my_node | `/` | `/my_node` |
| `~` | my_node | /my_ns | `/my_ns/my_node` |
| `~/ping` | my_node | `/` | `/my_node/ping` |
| `~/ping` | my_node | /my_ns | `/my_ns/my_node/ping` |

差分があるケース:

| 入力 | rclcpp | agnocast | 説明 |
|------|--------|----------|------|
| `""` (空) | `RCL_RET_INVALID_ARGUMENT` | `std::invalid_argument` | 例外型は異なるがエラーになる |
| `"white space"` | `RCL_RET_TOPIC_NAME_INVALID` | **そのまま処理される** | agnocastはバリデーションなし |
| `{ping}` (カスタムsubs登録時) | 展開される (`/my_ns/pong`) | `std::invalid_argument` | agnocastは未サポート |
| `{unknown}` | `RCL_RET_UNKNOWN_SUBSTITUTION` | `std::invalid_argument` | エラー処理は同等 |
| 不正なノード名使用時 | `RCL_RET_NODE_INVALID_NAME` | **エラーなし** | agnocastはバリデーションなし |

**RCLとの変数名対応**:

| RCL (expand_topic_name.c) | agnocast (node_topics.cpp) |
|---------------------------|---------------------------|
| `node_namespace` | `node_namespace` |
| `has_a_substitution` | `has_a_substitution` |
| `has_a_namespace_tilde` | `has_a_namespace_tilde` |
| `is_absolute` | `is_absolute` |
| `local_output` | `local_output` |
| `next_opening_brace` | `next_opening_brace` |
| `next_closing_brace` | `next_closing_brace` |
| `substitution_substr_len` | `substitution_substr_len` |

**RCLとのコード構造対応**:

| 処理 | RCL (expand_topic_name.c) | agnocast (node_topics.cpp) |
|------|---------------------------|---------------------------|
| substitutionチェック | L98 | L117 |
| チルダチェック | L99 | L118 |
| 絶対パスチェック | L100 | L119 |
| チルダ展開 | L114-125 | L128-137 |
| substitution展開 | L127-194 | L139-178 |
| 絶対パス変換 | L196-215 | L181-191 |

**TODOコメント** (node_topics.cpp:104-107):

```cpp
// TODO: Support custom substitutions via rcutils_string_map_t (see rcl_expand_topic_name)
// TODO: Validate input_topic_name using rcl_validate_topic_name
// TODO: Validate node_name using rmw_validate_node_name
// TODO: Validate node_namespace using rmw_validate_namespace
```

---

## 5. ノード構築パターン

### 5.1 コンストラクタ

**agnocast::Node** は以下の2つのコンストラクタを提供:

```cpp
// コンストラクタ1: ノード名のみ（NodeOptionsオプション）
explicit Node(
  const std::string & node_name,
  const rclcpp::NodeOptions & options = rclcpp::NodeOptions());

// コンストラクタ2: ノード名 + 名前空間（NodeOptionsオプション）
explicit Node(
  const std::string & node_name,
  const std::string & namespace_,
  const rclcpp::NodeOptions & options = rclcpp::NodeOptions());
```

### 5.2 使用例

**rclcpp::Node**:

```cpp
rclcpp::init(argc, argv);
auto node = std::make_shared<rclcpp::Node>("node_name", "namespace");
```

**agnocast::Node**:

```cpp
// グローバルコンテキストを使用（リマップルール、パラメータ上書き等）
agnocast::init(argc, argv);
auto node = std::make_shared<agnocast::Node>("node_name", "namespace");

// NodeOptionsを使用（parameter_overrides, context等）
rclcpp::NodeOptions options;
options.parameter_overrides({rclcpp::Parameter("my_param", 42)});
auto node = std::make_shared<agnocast::Node>("node_name", options);
```

### 5.3 動作の違い

| 側面 | agnocast | 備考 |
|------|----------|------|
| グローバルコンテキスト必須 | ✗ (オプション) | agnocast::init()なしでも動作 |
| NodeOptionsサポート | ✓ | parameter_overrides, context等をサポート |
| サブノード | ✗ | agnocastはサブノード非サポート |
| ライフサイクルノード | ✗ | 該当なし |
| Publisherサポート | **✗** | **agnocast::NodeはPublisherを作成不可** |
| Subscriptionサポート | ✓ | agnocast::Nodeでも作成可能 |

---

## 6. Composable Nodeに関する考慮事項

### 6.1 コンポーネント読み込み

**agnocast::Node自体はコンポーザブルではない**が、以下のパターンでコンポーネント化可能:

#### パターン: rclcpp::Node + agnocast::Node のハイブリッド

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
| コンテキスト共有 | 共有 | 独立 | Contextシングルトン | - |
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
3. **パラメータ管理**: declare, undeclare, has, set, get, get_or, describe, list, types, YAML読み込み, callback
4. **パラメータ設定**: set_parameter, set_parameters, set_parameters_atomically
5. **Subscription作成**: rclcpp::NodeとagnocastNode両方で可能
6. **コマンドライン引数**: `--ros-args`, `-r`, `-p`, `--params-file`
7. **グローバルコンテキスト**: 初期化, リマップルール, パラメータ上書き
8. **コールバックグループ**: create_callback_group, get_default_callback_group, callback_group_in_node, for_each_callback_group
9. **Executor**: SingleThreaded, MultiThreaded, CallbackIsolated
10. **ロギング**: get_logger() - rclcpp::Loggerを返す
11. **NodeOptions**: parameter_overrides, context等をサポート
12. **rclcpp::Context**: get_context() - rclcpp::Context::SharedPtrを返す
13. **ノードインターフェース**: get_node_base_interface(), get_node_topics_interface(), get_node_parameters_interface()

### 8.2 部分サポート機能 (⚠)

1. **名前解決**: トピックのみ (サービス固有の処理なし)
2. **トピック名展開**: バリデーションなし、カスタム置換未対応 (TODO記録済み)
3. **QoS**: QoSオブジェクトは受け取るが、完全な機能は使用していない可能性
4. **CLI上書き**: 配列型パラメータ未対応

### 8.3 未サポート機能 (✗)

**コアインフラ**:

- RCLハンドル (get_rcl_node_handle() - 呼び出すと例外スロー)

**通信**:

- **Publisher作成（agnocast::Nodeから）** - rclcpp::Nodeが必要
- サービス (クライアント/サーバー)
- アクション
- 完全なQoSプロファイル制御
- プロセス内通信（共有メモリ使用）

**検出とイントロスペクション**:

- すべてのグラフイントロスペクションAPI
- ノード検出

**時刻**:

- ROSクロックと時刻
- `/clock`トピック

**高度な機能**:

- タイマー
- Waitable
- ライフサイクルノード
- ネイティブなコンポーネントコンポジション（ハイブリッドパターンで対応可能）
- メッセージフィルタ
- パラメータサービス
- パラメータイベント

---

## 9. ユースケース推奨

### 9.1 agnocast::Nodeを使うべき場合

✓ **推奨**:

- **Subscription専用アプリケーション**（Publisherが不要な場合）
- rclcpp依存を最小化したい
- パラメータ管理とトピック名解決だけが必要
- rclcpp::Nodeと併用してパラメータ管理を分離したい
- DDS participantを作成せずに軽量なノードが必要

✗ **非推奨**:

- Publisherが必要な場合（rclcpp::Nodeが必須）
- タイマーが必要な場合（rclcpp::Nodeが必須）
- ROSサービス/アクションが必要な場合

### 9.2 ハイブリッドパターン (rclcpp::Node + agnocast::Node)

✓ **推奨**:

- PublisherとSubscriptionの両方が必要
- rclcpp::Nodeの機能（タイマー、ロガー等）を使いつつ、agnocastの軽量パラメータ管理も使いたい
- コンポーザブルノードが必要

### 9.3 純粋agnocastパターン (agnocast::Nodeのみ)

✓ **推奨**:

- Subscription専用
- DDS participantを作成したくない
- rclcpp::init()なしで動作させたい
- DDSネットワークトラフィックを最小限に抑えたい

---

## 10. ファイル別実装状況

**ファイルパス**: `src/agnocastlib/include/agnocast/` および `src/agnocastlib/src/`

### agnocast_node.hpp

- Nodeクラス定義
- コンストラクタ (2種類: ノード名のみ, ノード名+名前空間)
- ノードアイデンティティメソッド (get_name, get_namespace, get_fully_qualified_name, get_logger)
- コールバックグループメソッド (create_callback_group, get_default_callback_group, callback_group_in_node)
- トピック名解決 (resolve_topic_name)
- パラメータ管理 (declare, undeclare, has, set, get, describe, list等)
- ノードインターフェースアクセサ (get_node_base_interface, get_node_topics_interface, get_node_parameters_interface)

### agnocast_node.cpp

- コンストラクタ実装
- initialize_node(): NodeBase, NodeTopics, NodeParameters の初期化
- グローバルコンテキストからのリマップルールとパラメータオーバーライド適用

### node_interfaces/node_base.hpp & node_base.cpp

- `rclcpp::node_interfaces::NodeBaseInterface`を継承
- ノードアイデンティティ (name, namespace, FQN)
- コールバックグループ管理 (create, get_default, callback_group_in_node, for_each)
- GuardCondition管理
- トピック/サービス名解決

### node_interfaces/node_parameters.hpp & node_parameters.cpp

- `rclcpp::node_interfaces::NodeParametersInterface`を継承
- パラメータのdeclare, undeclare, has, set, get, describe, list
- パラメータコールバック (add_on_set_parameters_callback, remove_on_set_parameters_callback)
- パラメータオーバーライド管理

### node_interfaces/node_topics.hpp & node_topics.cpp

- `rclcpp::node_interfaces::NodeTopicsInterface`を継承
- トピック名解決 (resolve_topic_name): node_topics.cpp:16-24
- トピック名展開 (expand_topic_name): node_topics.cpp:95-193
  - RCL準拠の変数名 (`node_namespace`, `next_opening_brace`, `next_closing_brace`, `substitution_substr_len`)
  - RCL準拠のコード構造（チルダ展開 → substitution展開 → 絶対パス変換）
  - TODOコメントでバリデーション対応を記録
- リマップ処理 (remap_name): node_topics.cpp:196-222
- リマップルール管理 (add_remap_rule): node_topics.cpp:86-91

### agnocast_publisher.hpp

- BasicPublisher, AgnocastOnlyPublisherクラステンプレート
- コンストラクタ（**rclcpp::Nodeのみ**）
- borrow_loaned_message(), publish(), get_subscription_count()

### agnocast_subscription.hpp

- BasicSubscription, TakeSubscription, PollingSubscriberクラス
- rclcpp::Node用コンストラクタ
- **agnocast::Node用コンストラクタ**

### agnocast_context.hpp & agnocast_context.cpp

- Contextシングルトンクラス
- init()関数
- parse_remap_rule(), parse_param_rule(), parse_yaml_file()
- get_param_overrides(): ノード固有パラメータ取得

### Executorファイル群

- agnocast_executor.hpp: AgnocastExecutor基底クラス
- agnocast_single_threaded_executor.hpp: SingleThreadedAgnocastExecutor
- agnocast_multi_threaded_executor.hpp: MultiThreadedAgnocastExecutor
- agnocast_callback_isolated_executor.hpp: CallbackIsolatedAgnocastExecutor

---

## 11. 互換性マトリクス

| 機能カテゴリ | rclcppメソッド数 | agnocastサポート数 | カバー率 |
|------------|----------------|-------------------|---------|
| ノードアイデンティティ | 3 | 3 | 100% |
| トピック解決 | 2 | 2 | 100% |
| パラメータ (基本) | 6 | 6 | 100% |
| パラメータ (高度) | 8 | 8 | 100% |
| パラメータ (コールバック) | 2 | 2 | 100% |
| Subscription作成 | 1 | 1 | 100% |
| Publisher作成 (agnocast::Node) | 1 | **0** | **0%** |
| Publisher作成 (rclcpp::Node) | 1 | 1 | 100% |
| Executor | 3種類 | 3種類 | 100% |
| グラフイントロスペクション | 13 | 0 | 0% |
| サービス | 3 | 0 | 0% |
| タイマー | 2 | 0 | 0% |
| ロギング | 2 | 1 | 50% |
| クロック | 1 | 0 | 0% |
| Waitable | 2 | 0 | 0% |
| コールバックグループ (基本) | 2 | 2 | 100% |
| コールバックグループ (高度) | 3 | 3 | 100% |
| ノードインターフェース取得 | 3 | 3 | 100% |
| Context | 1 | 1 | 100% |

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

### 12.2 グラフイントロスペクションなし

**制限**: グラフ内のトピック、ノード、エンドポイントをクエリできない

**回避策**: `ros2` CLIツールを別途使用するか、手動設定を維持

### 12.3 配列パラメータなし

**制限**: スカラーパラメータ型のみサポート

**回避策**: 複数のスカラーパラメータを使用するか、文字列パラメータからパース

### 12.4 純粋agnocastではタイマー使用不可

**制限**: `agnocast::Node`のみではタイマーを作成できない

**回避策**:

- rclcpp::Nodeと併用してタイマーを使う
- std::threadやOSタイマーを使う

### 12.5 サービス名解決の未対応

**制限**: `resolve_topic_or_service_name()`の`is_service`パラメータが無視される

**影響**:

- `node_base.cpp:220`で`(void)is_service;`として無視
- トピックとサービスで異なる名前解決ルールが適用されない
- サービスリマッピングが機能しない

**理由**: agnocast::Nodeはサービス機能を提供しないため、サービス名解決は優先度が低い

### 12.7 トピック名展開のバリデーション未対応

**制限**: `expand_topic_name()`で入力バリデーションが行われない

**影響**:

- 不正なトピック名（スペース含む等）がそのまま処理される
- 不正なノード名/namespaceでもエラーにならない

**RCLとの比較**:

| バリデーション | RCL | agnocast |
|--------------|-----|----------|
| トピック名 | `rcl_validate_topic_name` | なし (TODO) |
| ノード名 | `rmw_validate_node_name` | なし (TODO) |
| namespace | `rmw_validate_namespace` | なし (TODO) |

**TODOコメント** (node_topics.cpp:105-107):

```cpp
// TODO: Validate input_topic_name using rcl_validate_topic_name
// TODO: Validate node_name using rmw_validate_node_name
// TODO: Validate node_namespace using rmw_validate_namespace
```

### 12.8 カスタム置換の未対応

**制限**: `{node}`, `{ns}`, `{namespace}`以外のカスタム置換がサポートされていない

**影響**:

- `rcutils_string_map_t`でユーザー定義置換を登録できない
- カスタム置換を使用すると`std::invalid_argument`がスローされる

**RCLとの比較**:

```cpp
// RCLではカスタム置換が可能
rcutils_string_map_set(&subs, "ping", "pong");
// {ping} → pong に展開される

// agnocastでは未サポート
// {ping} → std::invalid_argument("unknown substitution: {ping}")
```

**TODOコメント** (node_topics.cpp:104):

```cpp
// TODO: Support custom substitutions via rcutils_string_map_t (see rcl_expand_topic_name)
```

### 12.6 RemapType::TOPIC_OR_SERVICE

**設計**: `RemapType`列挙型は`TOPIC_OR_SERVICE`を使用し、トピックとサービスの両方に適用

**RCLとの比較**:

```cpp
// RCL (rcl/src/rcl/remap_impl.h)
typedef enum rcl_remap_type_t {
  RCL_UNKNOWN_REMAP = 0,
  RCL_TOPIC_REMAP = 1u << 0,
  RCL_SERVICE_REMAP = 1u << 1,
  RCL_NODENAME_REMAP = 1u << 2,
  RCL_NAMESPACE_REMAP = 1u << 3
} rcl_remap_type_t;
// URL schemeなしの場合: RCL_TOPIC_REMAP | RCL_SERVICE_REMAP

// agnocast (agnocast_context.hpp)
enum class RemapType {
  NODENAME,
  NAMESPACE,
  TOPIC_OR_SERVICE  // トピックとサービス両方に適用
};
```

**動作**: `-r /foo:=/bar`形式のリマッピングはトピックとサービスの両方に適用される（RCLと同様）

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

1. **パラメータ管理**: YAML、CLI、リマッピングからの読み込み、コールバックサポート
2. **トピック名解決**: ROS 2名前解決ルールの完全実装
3. **Subscription専用ノード**: rclcpp::init()なしで動作可能
4. **DDS participant不使用**: DDS participantを作成しないため、DDSネットワークトラフィックを削減
5. **ロギング**: get_logger()をサポート（rclcpp::Loggerを返す）
6. **rclcpp互換インターフェース**: NodeBaseInterface, NodeTopicsInterface, NodeParametersInterfaceを継承
7. **NodeOptionsサポート**: parameter_overrides, context等

**✗ 制限事項**:

1. **Publisher作成不可**: rclcpp::Nodeが必要
2. **タイマー**: 未サポート
3. **サービス/アクション**: 未サポート
4. **グラフイントロスペクション**: 未サポート
5. **RCLハンドル**: 呼び出すと例外スロー（DDS不使用のため）

**推奨使用パターン**:

- **ハイブリッド**: `rclcpp::Node`を継承し、`agnocast::Node`をメンバとして持つ（パラメータ管理用）
- **純粋agnocast**: Subscription専用で最小限の依存関係が必要な場合

**設計哲学**:
ROS 2互換性（パラメータ、トピック名解決）を保ちつつ、**DDS participantを作成せずに**高性能な共有メモリ通信を実現。rclcppのノードインターフェースを継承することで、rclcpp APIとの互換性を最大化。ただし、Publisherにはrclcpp::Nodeのインフラが必要という制約がある。

**Executorについて**:
agnocastは**独自のExecutor実装**を提供し、共有メモリメッセージとDDSメッセージの両方を効率的に処理できます。これにより、agnocastとROS 2の混在環境でも統一されたイベントループを使用できます。
