# agnocast::message_filters 設計ドキュメント

## 概要

`agnocast::message_filters` は、複数のトピックからのメッセージを時刻同期して処理するためのライブラリです。ROS2の `message_filters` パッケージと互換性のあるAPIを提供しつつ、agnocast独自の `ipc_shared_ptr` を使用したゼロコピー通信に対応しています。

---

## 全体アーキテクチャ

```mermaid
graph TB
    subgraph UserCode["User Code"]
        UC[ユーザーコード]
    end

    subgraph Filters["Filters"]
        SUB1[Subscriber&lt;M0&gt;]
        SUB2[Subscriber&lt;M1&gt;]
        SF[SimpleFilter&lt;M&gt;<br/>基底クラス]
    end

    subgraph Synchronizer["Synchronizer&lt;Policy&gt;"]
        RC[registerCallback]
        CI[connectInput]
        ADD[add&lt;i&gt;]
        SIG[signal]
        GP[getPolicy]
        S9[Signal9<br/>callbacks管理]
    end

    subgraph Policies["Sync Policies"]
        ET[ExactTime<br/>実装済]
        AT[ApproximateTime<br/>未実装]
    end

    SUB1 --> SF
    SUB2 --> SF
    UC --> Synchronizer
    SUB1 --> CI
    SUB2 --> CI
    RC --> S9
    CI --> ADD
    ADD --> ET
    ET -->|全メッセージ揃った| SIG
    SIG --> S9
    S9 -->|コールバック呼び出し| UC
```

## クラス構成図

```mermaid
classDiagram
    class CallbackHelper9~M0...M8~ {
        <<abstract>>
        +Ptr = shared_ptr
        +call(e0...e8)*
    }

    class CallbackHelper9T~C,M0...M8~ {
        -C callback_
        +CallbackHelper9T(callback)
        +call(e0...e8)
    }

    class Signal9~M0...M8~ {
        -vector~CallbackHelper9Ptr~ callbacks_
        -mutex mutex_
        +addCallback(C&) Connection
        +addCallback(callback, T*) Connection
        +call(m0...m8)
        +removeCallback(helper)
    }

    class CallbackHelper1~M~ {
        <<abstract>>
        +Ptr = shared_ptr
        +call(msg)*
    }

    class CallbackHelper1T~P,M~ {
        -Callback callback_
        +CallbackHelper1T(callback)
        +call(msg)
    }

    class Signal1~M~ {
        -vector~CallbackHelper1Ptr~ callbacks_
        -mutex mutex_
        +addCallback(callback) CallbackHelper1Ptr
        +removeCallback(helper)
        +call(msg)
    }

    class SimpleFilter~M~ {
        -Signal1 signal_
        -string name_
        +registerCallback(C&) Connection
        +registerCallback(callback, T*) Connection
        +setName(string)
        +getName() string
        #signalMessage(MConstPtr&)
        #signalMessage(MPtr)
    }

    class Subscriber~M~ {
        -Subscription~M~::SharedPtr sub_
        +Subscriber()
        +Subscriber(node, topic, qos, options)
        +subscribe(node, topic, qos, options)
        +unsubscribe()
        +getTopic() string
    }

    class Synchronizer~Policy~ {
        -Signal9 signal_
        -Connection connections_[9]
        -string name_
        +Synchronizer()
        +Synchronizer(Policy)
        +Synchronizer(Policy, F0&, F1&, ...)
        +connectInput(F0&, F1&, ...)
        +registerCallback(C&) Connection
        +signal(m0...m8)
        +add~i~(msg)
        +getPolicy() Policy*
    }

    class ExactTime~M0...M8~ {
        -Sync* parent_
        -uint32_t queue_size_
        -map~Time,Tuple~ tuples_
        -Time last_signal_time_
        -Signal9 drop_signal_
        -mutex mutex_
        +ExactTime()
        +ExactTime(uint32_t queue_size)
        +initParent(Sync*)
        +registerDropCallback(C&) Connection
        +add~i~(msg)
        -checkTuple(Tuple&)
        -clearOldTuples()
    }

    class Connection {
        +disconnect()
    }

    CallbackHelper9T --|> CallbackHelper9
    CallbackHelper1T --|> CallbackHelper1
    Signal9 --> CallbackHelper9 : callbacks_
    Signal1 --> CallbackHelper1 : callbacks_
    SimpleFilter --> Signal1 : signal_
    Subscriber --|> SimpleFilter
    Synchronizer --> Signal9 : signal_
    Synchronizer --|> ExactTime : inherits Policy
    Synchronizer --> Connection : connections_[9]
    Signal9 --> Connection : returns
    Signal1 --> Connection : returns
    ExactTime --> Signal9 : drop_signal_
    ExactTime --> Synchronizer : parent_
```

---

## コンポーネントの役割

### CallbackHelper9 / CallbackHelper9T

**役割:** 型消去（Type Erasure）パターンによるコールバック抽象化

異なるパラメータ数のコールバック（2引数、3引数、...9引数）を同一のコンテナに格納するための基底クラスと派生クラスです。

| クラス | 役割 |
|--------|------|
| `CallbackHelper9<M0...M8>` | 純粋仮想基底クラス。`call()` メソッドを定義 |
| `CallbackHelper9T<C, M0...M8>` | 実際のコールバック `C` を保持する派生クラス |

**なぜ必要か:**
- 異なる型のコールバック（ラムダ、関数ポインタ、メンバ関数）を統一的に扱う
- `std::vector<CallbackHelper9::Ptr>` で異なる型のコールバックを格納可能
- ROS2 の `message_filters` と同じ設計パターン

---

### Signal9<M0...M8>

**役割:** 9メッセージ用シグナル/スロットパターンによるコールバック管理

複数のコールバックを登録・管理し、一括で呼び出す機能を提供します。`CallbackHelper9` を使った型消去により、異なるシグネチャのコールバックを統一的に扱います。

| メンバ/メソッド | 役割 |
|---------------|------|
| `callbacks_` | `CallbackHelper9Ptr` のベクタ（型消去されたコールバック） |
| `mutex_` | スレッドセーフなコールバック操作を保証 |
| `addCallback(C&)` | ラムダ/関数オブジェクトをコールバックとして登録 |
| `addCallback(callback, T*)` | メンバ関数をコールバックとして登録 |
| `call()` | 登録済みの全コールバックを順次呼び出し |
| `removeCallback()` | 特定のコールバックをリストから削除 |

---

### CallbackHelper1 / CallbackHelper1T

**役割:** 単一メッセージ用の型消去パターン

`Signal9` と同様の設計で、単一メッセージのコールバックを扱います。

| クラス | 役割 |
|--------|------|
| `CallbackHelper1<M>` | 純粋仮想基底クラス。`call(msg)` を定義 |
| `CallbackHelper1T<P, M>` | 実際のコールバックを保持する派生クラス |

---

### Signal1<M>

**役割:** 単一メッセージ用シグナル/スロットパターン

`SimpleFilter` の内部で使用され、単一メッセージのコールバック管理を行います。

| メンバ/メソッド | 役割 |
|---------------|------|
| `callbacks_` | `CallbackHelper1Ptr` のベクタ |
| `addCallback()` | コールバックを登録し、`CallbackHelper1Ptr` を返す |
| `removeCallback()` | コールバックを削除 |
| `call()` | 全コールバックを呼び出し |

---

### SimpleFilter<M>

**役割:** フィルターの基底クラス

`Subscriber` 等のフィルタークラスの基底となり、コールバック登録機能を提供します。ROS2 の `message_filters::SimpleFilter` と同じ API を持ちます。

| メンバ/メソッド | 役割 |
|---------------|------|
| `signal_` | `Signal1<M>` インスタンス |
| `registerCallback()` | コールバックを登録し `Connection` を返す |
| `signalMessage()` | 派生クラスから呼び出し、登録済みコールバックを発火 |
| `setName() / getName()` | デバッグ用の名前設定・取得 |

---

### Subscriber<M>

**役割:** agnocast サブスクリプションをフィルターとしてラップ

`agnocast::create_subscription` を内部で使用し、受信したメッセージを `SimpleFilter` 経由で `Synchronizer` に渡します。

| メンバ/メソッド | 役割 |
|---------------|------|
| `sub_` | `agnocast::Subscription<M>::SharedPtr` |
| `subscribe()` | サブスクリプションを開始 |
| `unsubscribe()` | サブスクリプションを停止 |
| `getTopic()` | トピック名を取得 |

**使用例:**
```cpp
agnocast::message_filters::Subscriber<sensor_msgs::msg::Imu> sub(
    node, "imu_topic", rclcpp::QoS(10));
```

---

### Synchronizer<Policy>

**役割:** メッセージ同期のファサード（窓口）クラス

ユーザーが直接操作するメインクラスです。ポリシーを継承し、シグナルを保持してメッセージの受信からコールバック呼び出しまでの全体フローを統括します。

| メンバ/メソッド | 役割 |
|---------------|------|
| `signal_` | 複数のユーザーコールバックを管理する Signal9 インスタンス |
| `connections_[9]` | フィルター（Subscriber等）との接続を管理 |
| `connectInput()` | 外部フィルターからのメッセージ受信を設定 |
| `registerCallback()` | 同期完了時に呼ばれるユーザーコールバックを登録 |
| `add<i>()` | i番目のメッセージを手動で追加（フィルター未使用時） |
| `signal()` | ポリシーから呼び出され、登録済みコールバックを発火 |
| `getPolicy()` | ポリシーへの直接アクセス（drop callback登録等） |

---

### ExactTime\<M0...M8\>

**役割:** 完全一致タイムスタンプによる同期ポリシー

全てのメッセージが**完全に同じタイムスタンプ**を持つ場合にのみコールバックを発火します。センサーフュージョン等、厳密な時刻同期が必要な場合に使用します。

| メンバ/メソッド | 役割 |
|---------------|------|
| `parent_` | 親Synchronizerへのポインタ（signal呼び出し用） |
| `queue_size_` | 保持する未完成タプルの最大数 |
| `tuples_` | タイムスタンプをキーとしたメッセージタプルのマップ |
| `drop_signal_` | キューオーバーフロー時のドロップコールバック管理 |
| `add<i>()` | i番目のメッセージを受け取り、タプルに格納 |
| `checkTuple()` | タプルが完成したかチェックし、完成なら signal 発火 |
| `clearOldTuples()` | 古い（処理済み時刻以前の）タプルを削除 |
| `registerDropCallback()` | メッセージドロップ時のコールバックを登録 |

**内部動作:**
1. メッセージ受信 → タイムスタンプで `tuples_` に格納
2. タプル内の全スロットが埋まったら `parent_->signal()` 呼び出し
3. キューサイズ超過時は古いタプルを削除し `drop_signal_` 発火

---

### Connection

**役割:** コールバック接続のライフサイクル管理

`registerCallback()` の戻り値として返され、`disconnect()` を呼ぶことでコールバックを解除できます。ROS2 の `message_filters::Connection` を再利用しています。

| メソッド | 役割 |
|---------|------|
| `disconnect()` | 関連付けられたコールバックを Signal から削除 |

**使用例:**
```cpp
auto conn = sync.registerCallback(myCallback);
// ... 処理 ...
conn.disconnect();  // コールバック解除
```

---

### NullFilter\<M\>

**役割:** 何もしないダミーフィルター

`connectInput()` で9個未満のフィルターを渡した場合、残りのスロットを埋めるために使用されます。`registerCallback()` は何もせず空の `Connection` を返します。ROS2 の実装を再利用しています。

---

## データフロー

```mermaid
sequenceDiagram
    participant Sub0 as Subscriber<M0>
    participant Sub1 as Subscriber<M1>
    participant SF as SimpleFilter
    participant Sync as Synchronizer
    participant Policy as ExactTime
    participant Sig as Signal9
    participant CB as User Callbacks

    Note over Sub0,CB: 初期化フェーズ
    Sync->>Sub0: registerCallback(cb<0>)
    Sub0->>SF: registerCallback via Signal1
    Sync->>Sub1: registerCallback(cb<1>)
    CB->>Sync: registerCallback(userCallback)
    Sync->>Sig: addCallback(userCallback)
    Sig-->>CB: Connection

    Note over Sub0,CB: メッセージ受信フェーズ
    Sub0->>SF: signalMessage(msg0)
    SF->>Sync: cb<0>(msg0)
    Sync->>Policy: add<0>(msg0)
    Policy->>Policy: tuples_[time][0] = msg0

    Sub1->>SF: signalMessage(msg1)
    SF->>Sync: cb<1>(msg1)
    Sync->>Policy: add<1>(msg1)
    Policy->>Policy: tuples_[time][1] = msg1
    Policy->>Policy: checkTuple() - 全揃った!

    Policy->>Sync: parent_->signal(m0, m1, ...)
    Sync->>Sig: call(m0, m1, ...)
    Sig->>CB: CallbackHelper9::call(m0, m1, ...)
```

## 型消去パターンの動作

```mermaid
flowchart TB
    subgraph UserCallback["ユーザーが渡すコールバック"]
        LAMBDA["lambda (2引数)"]
        FUNC["関数ポインタ (3引数)"]
        MEMBER["メンバ関数 (2引数)"]
    end

    subgraph Wrapping["ラムダでラップ (9引数化)"]
        W1["[cb](m0,m1,_,_,_,_,_,_,_){cb(m0,m1)}"]
        W2["[cb](m0,m1,m2,_,_,_,_,_,_){cb(m0,m1,m2)}"]
        W3["[cb,t](m0,m1,_,_,_,_,_,_,_){(t->*cb)(m0,m1)}"]
    end

    subgraph Helper["CallbackHelper9T"]
        H1["CallbackHelper9T&lt;Lambda&gt;"]
        H2["CallbackHelper9T&lt;Lambda&gt;"]
        H3["CallbackHelper9T&lt;Lambda&gt;"]
    end

    subgraph Storage["Signal9::callbacks_"]
        VEC["vector&lt;CallbackHelper9::Ptr&gt;"]
    end

    LAMBDA --> W1
    FUNC --> W2
    MEMBER --> W3
    W1 --> H1
    W2 --> H2
    W3 --> H3
    H1 --> VEC
    H2 --> VEC
    H3 --> VEC
```

## connectInput の動作

```mermaid
flowchart TB
    subgraph User["ユーザーコード"]
        CALL["sync.connectInput(sub0, sub1)"]
    end

    subgraph Chain["再帰的展開"]
        C2["connectInput(f0, f1)"]
        C3["connectInput(f0, f1, NullFilter)"]
        C4["connectInput(f0, f1, f2, NullFilter)"]
        CD["..."]
        C9["connectInput(f0...f8) - 9引数版"]
    end

    subgraph Register["コールバック登録"]
        R0["connections_[0] = f0.registerCallback(cb&lt;0&gt;)"]
        R1["connections_[1] = f1.registerCallback(cb&lt;1&gt;)"]
        RN["connections_[2..8] = NullFilter (何もしない)"]
    end

    CALL --> C2
    C2 -->|"NullFilterで埋める"| C3
    C3 --> C4
    C4 --> CD
    CD --> C9
    C9 --> R0
    C9 --> R1
    C9 --> RN
```

## Connection によるコールバック管理

```mermaid
stateDiagram-v2
    [*] --> Registered: registerCallback()

    state Registered {
        [*] --> Active
        Active: CallbackHelperがcallbacks_に存在
        Active: signal時にcall()が呼び出される
    }

    Registered --> Disconnected: connection.disconnect()

    state Disconnected {
        [*] --> Removed
        Removed: CallbackHelperがcallbacks_から削除
        Removed: signal時に呼び出されない
    }

    Disconnected --> [*]
```

## ExactTime ポリシーの内部動作

```mermaid
flowchart TB
    subgraph Input["メッセージ入力"]
        M0["msg0 (stamp=100)"]
        M1["msg1 (stamp=100)"]
        M2["msg2 (stamp=200)"]
    end

    subgraph Tuples["tuples_ マップ"]
        T100["tuples_[100]<br/>[msg0, msg1, null, ...]"]
        T200["tuples_[200]<br/>[null, null, msg2, ...]"]
    end

    subgraph Check["checkTuple()"]
        FULL{"全スロット<br/>埋まった?"}
        SIGNAL["parent_->signal()"]
        ERASE["tuples_.erase(time)"]
        CLEAR["clearOldTuples()"]
    end

    subgraph QueueMgmt["キュー管理"]
        QCHECK{"tuples_.size()<br/>> queue_size?"}
        DROP["drop_signal_.call()"]
        QERASE["oldest tuple削除"]
    end

    M0 --> T100
    M1 --> T100
    M2 --> T200

    T100 --> FULL
    FULL -->|Yes| SIGNAL
    SIGNAL --> ERASE
    ERASE --> CLEAR
    FULL -->|No| QCHECK

    QCHECK -->|Yes| DROP
    DROP --> QERASE
    QCHECK -->|No| END[終了]
```

## ros2/message_filters との API 対応表

```mermaid
graph LR
    subgraph ROS2["ros2/message_filters"]
        R_SYNC["Synchronizer"]
        R_ET["ExactTime"]
        R_AT["ApproximateTime"]
        R_SIG9["Signal9"]
        R_SIG1["Signal1"]
        R_SF["SimpleFilter"]
        R_SUB["Subscriber"]
        R_CH9["CallbackHelper9"]
        R_CH1["CallbackHelper1"]
        R_CONN["Connection"]
        R_PTR["std::shared_ptr"]
    end

    subgraph Agnocast["agnocast::message_filters"]
        A_SYNC["Synchronizer ✅"]
        A_ET["ExactTime ✅"]
        A_AT["ApproximateTime ❌"]
        A_SIG9["Signal9 ✅"]
        A_SIG1["Signal1 ✅"]
        A_SF["SimpleFilter ✅"]
        A_SUB["Subscriber ✅"]
        A_CH9["CallbackHelper9 ✅"]
        A_CH1["CallbackHelper1 ✅"]
        A_CONN["Connection ✅<br/>(ROS2再利用)"]
        A_PTR["ipc_shared_ptr"]
    end

    R_SYNC -.->|対応| A_SYNC
    R_ET -.->|対応| A_ET
    R_AT -.->|未実装| A_AT
    R_SIG9 -.->|対応| A_SIG9
    R_SIG1 -.->|対応| A_SIG1
    R_SF -.->|対応| A_SF
    R_SUB -.->|対応| A_SUB
    R_CH9 -.->|対応| A_CH9
    R_CH1 -.->|対応| A_CH1
    R_CONN -.->|再利用| A_CONN
    R_PTR -.->|型が異なる| A_PTR
```

## ファイル構成

```mermaid
graph TB
    subgraph Files["ファイル構成"]
        DIR["message_filters/"]
        SIG1["signal1.hpp<br/>(新規)"]
        SIG9["signal9.hpp<br/>(新規)"]
        SF["simple_filter.hpp<br/>(新規)"]
        SUB["subscriber.hpp<br/>(新規)"]
        SYNC["synchronizer.hpp<br/>(新規)"]
        POLICIES["sync_policies/"]
        ET["exact_time.hpp<br/>(新規)"]
    end

    DIR --> SIG1
    DIR --> SIG9
    DIR --> SF
    DIR --> SUB
    DIR --> SYNC
    DIR --> POLICIES
    POLICIES --> ET

    SF -->|includes| SIG1
    SUB -->|includes| SF
    SYNC -->|includes| SIG9
    ET -->|includes| SYNC
```

## 新規追加ファイル一覧

| ファイル | 内容 | 状態 |
|---------|------|------|
| `signal1.hpp` | CallbackHelper1, CallbackHelper1T, Signal1 | **新規** |
| `signal9.hpp` | CallbackHelper9, CallbackHelper9T, Signal9 | **新規** |
| `simple_filter.hpp` | SimpleFilter 基底クラス | **新規** |
| `subscriber.hpp` | Subscriber フィルター | **新規** |
| `synchronizer.hpp` | Synchronizer, PolicyBase | **新規** |
| `sync_policies/exact_time.hpp` | ExactTime ポリシー | **新規** |

---

## 使用例

### Subscriber を使った同期（推奨）

```cpp
#include "agnocast/message_filters/subscriber.hpp"
#include "agnocast/message_filters/sync_policies/exact_time.hpp"

using namespace agnocast::message_filters;

// 型定義
using Policy = sync_policies::ExactTime<
    sensor_msgs::msg::Imu,
    sensor_msgs::msg::Imu>;
using Sync = Synchronizer<Policy>;

class MyNode : public rclcpp::Node {
public:
    MyNode() : Node("my_node"),
        // Reentrant callback group（マルチスレッド対応）
        callback_group_(create_callback_group(rclcpp::CallbackGroupType::Reentrant)),
        // Subscriber 作成
        sub1_(this, "imu_topic1", rclcpp::QoS(10),
              agnocast::SubscriptionOptions{callback_group_}),
        sub2_(this, "imu_topic2", rclcpp::QoS(10),
              agnocast::SubscriptionOptions{callback_group_}),
        // Synchronizer 作成（コンストラクタで接続）
        sync_(Policy(10), sub1_, sub2_)
    {
        // コールバック登録
        sync_.registerCallback(
            std::bind(&MyNode::callback, this,
                      std::placeholders::_1, std::placeholders::_2));
    }

private:
    void callback(
        const agnocast::ipc_shared_ptr<const sensor_msgs::msg::Imu>& msg1,
        const agnocast::ipc_shared_ptr<const sensor_msgs::msg::Imu>& msg2)
    {
        RCLCPP_INFO(get_logger(), "Synchronized!");
    }

    rclcpp::CallbackGroup::SharedPtr callback_group_;
    Subscriber<sensor_msgs::msg::Imu> sub1_;
    Subscriber<sensor_msgs::msg::Imu> sub2_;
    Sync sync_;
};
```

### 手動メッセージ追加

```cpp
using Policy = sync_policies::ExactTime<
    sensor_msgs::msg::Image,
    sensor_msgs::msg::CameraInfo>;
using Sync = Synchronizer<Policy>;

// Synchronizer 作成
Sync sync{Policy(10)};  // queue_size = 10

// コールバック登録
sync.registerCallback([](
    const agnocast::ipc_shared_ptr<const sensor_msgs::msg::Image>& image,
    const agnocast::ipc_shared_ptr<const sensor_msgs::msg::CameraInfo>& info) {
    processImageWithInfo(image, info);
});

// メッセージを手動で追加
sync.add<0>(image_msg);
sync.add<1>(camera_info_msg);
```

### ドロップコールバックの使用

```cpp
Sync sync{Policy(2)};  // 小さいキューサイズ

sync.registerCallback(processCallback);

// キューオーバーフロー時のコールバック
sync.getPolicy()->registerDropCallback([](auto& img, auto& info) {
    RCLCPP_WARN(logger, "Message dropped due to queue overflow");
});
```

### Connection によるコールバック解除

```cpp
auto connection = sync.registerCallback(myCallback);

// ... 処理 ...

// コールバック解除
connection.disconnect();
```

---

## 設計上の考慮点

### ros2/message_filters との互換性

- **API互換:** 同じメソッド名・シグネチャを提供
- **型の違い:** `std::shared_ptr` → `ipc_shared_ptr`（ゼロコピー対応）
- **設計パターン:** `CallbackHelper` による型消去パターンを採用
- **未実装:** `ApproximateTime` ポリシー

### スレッドセーフティ

- `Signal1 / Signal9`: `mutex_` で保護されたコールバックリスト
- `ExactTime`: `mutex_` で保護されたタプルマップ
- 複数スレッドからの同時メッセージ追加に対応
- `Reentrant` callback group の使用を推奨

### メモリ管理

- `Connection` による明示的なコールバック解除
- `queue_size_` による未完成タプルの上限管理
- `clearOldTuples()` による古いデータの自動クリーンアップ
- `ipc_shared_ptr` によるゼロコピーメッセージ共有
