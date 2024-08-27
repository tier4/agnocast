## What is message queue in Linux?

See official man page: <https://man7.org/linux/man-pages/man7/mq_overview.7.html>

## How message queue is used in Agnocast?

### Basic usage

There are two different usages of message queue in Agnocast.

- To notify to subscriber processes that a new publisher is created.
- To notify to subscriber processes that a publisher has published a new topic.

### Detailed usage

#### Notification of a new publisher

The message queue is used in the following way:

- When Agnocast is initialized, a new message queue is opened as a receiver.
- When a publisher process calls `create_publisher` for a topic `T`, it gets information about subscribers for `T` through `AGNOCAST_PUBLISHER_ADD_CMD` ioctl, and opens an existing message queue to notify to the subscribers that a new publisher is created.
- When a subscriber process receives the notification, then it maps the sender's shared memory with a read-only privilege.

Thus, the definition of the message is the following.

```c
struct MqMsgNewPublisher {
  uint32_t publisher_pid; // The process id of the sender
  uint64_t shm_addr;      // The shared memory address which the sender has a writable privilege
};
```

#### Notification of a topic publish

The message queue is used in the following way:

- When a subscriber process calls `create_subscription` for a topic `T`, it opens a new message queue as a receiver.
- When a publisher process calls `publish` for `T`, it opens an existing message queue and sends a message to notify to the subscribers that a new topic is published.
- When a subscriber process receives the notification, then it gets the topic content through `AGNOCAST_RECEIVE_MSG_CMD` ioctl and executes the corresponding callback.

Thus, the definition of the message is the following.

```c
struct MqMsgAgnocast {
  uint32_t publisher_pid; // The process id of the sender
  uint64_t timestamp;     // The timestamp of the corresponding topic
};
```

### Naming rules and restrictions

Suppose that `pid` is the process id of the process who opens the message queue as a receiver and `topic_name` is the topic name corresponding to the message queue.

- The message queue name for the new publisher notification is `/new_publisher@pid`.
- The message queue name for the topic publish notification is `topic_name@pid`.

The restrictions of the naming are

- It must start with `/`
- It must not include `/` other than the beginning

The first rule is satisfied because all topic names start with `/`.
The satisfy the second rule, all the occurrence of `/` in topic names are replaced for `_`.

## Known issues

- When a subscriber process dies or is too slow to execute callbacks, the corresponding publisher processes will be blocked due to the message queue.
