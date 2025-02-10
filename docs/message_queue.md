## What is message queue in Linux?

See official man page: <https://man7.org/linux/man-pages/man7/mq_overview.7.html>

## How message queue is used in Agnocast?

The message queue is used to notify to subscriber processes that a publisher has published a new topic message. It is done in the following way:

- When a subscriber process calls `create_subscription` for a topic `T`, it opens a new message queue as a receiver.
- When a publisher process calls `publish` for `T`, it opens an existing message queue and sends a message to notify to the subscribers that a new topic message has been published.
- When a subscriber process receives the notification, then it gets the topic content through `AGNOCAST_RECEIVE_MSG_CMD` ioctl and executes the corresponding callback.

The definition of the message is as follows;

```c
struct MqMsgAgnocast {
  bool dummy;
};
```

This message only contains a boolean value, but the value itself is not relevant to the operation. The important fact for the subscriber is that a message has been received. Upon receiving this message, the subscriber needs to use an ioctl call to query the kernel module to check if there is anything that should be received.

### Naming rules and restrictions

The message_queue is named using topic_local_id. As implied by its name, topic_local_id exists in a topic-local namespace and represents IDs that are incrementally assigned from 0 to publishers/subscribers. This was introduced to distinguish between different publishers/subscribers that exist within the same process and participate in the same topic, and we use it here as well.
Suppose that `topic_local_id` is the topic_local_id of the subscriber who opens the message queue and `topic_name` is the topic name corresponding to the message queue.

- The message queue name for the topic publish notification is `topic_name@topic_local_id`.

The restrictions of the naming are

- It must start with `/`,
- and, it must not include `/` other than the beginning.

The first rule is satisfied because all topic names start with `/`.
To satisfy the second rule, all the occurrence of `/` in topic names are replaced for `_`.

## Known issues

- According to the man page for mq_send, it should be possible to send an empty message as an mq message. However, at the current time, attempts to do so have not been successful. As a workaround, we are using a dummy message instead. It's worth noting that this approach does not cause any issues in terms of functionality or performance.
