# ROS 2 Agnocast

True Zero Copy Communication Middleware for Undefined ROS 2 Message Types.

prototype: <https://github.com/sykwer/agnocast>

## Build

Setup.

```bash
bash scripts/setup
```

Build.

```bash
bash scripts/build_all
```

Check if there is a `libagnocast_heaphook.so` in `/usr/lib`.

```bash
$ ls /usr/lib | grep libagnocast_heaphook
libagnocast_heaphook.so
```

## Run

Insert kernel module.

```bash
cd kmod
sudo insmod agnocast.ko
sudo lsmod
```

Run sample app (different window for each script).
The order does not matter.

```bash
bash scripts/run_listener
bash scripts/run_listen_talker
bash scripts/run_talker
```

Stop applications and unload kernel module.

```bash
sudo rmmod agnocast
```

## Debug

Check the kernel log.

```bash
sudo dmesg -w
```

Check which process uses Agnocast and what kind of publishers/subscriptions it has.

```bash
sudo cat /sys/module/agnocast/status/process_list
```

Check which topic is passed through Agnocast and its publisher/subscription processes.

```bash
sudo cat /sys/module/agnocast/status/topic_list
```

Check the detail of a specific topic `/my_topic`.

```bash
echo "/my_topic" | sudo tee /sys/module/agnocast/status/topic_info
sudo cat /sys/module/agnocast/status/topic_info
```

To use dynamic_debug for dynamically outputting debug logs, please run the following command as super user:

```bash
sudo su
echo 'file agnocast.c +p' > /sys/kernel/debug/dynamic_debug/control
```

Check if dynamic_debug is enabled by running the following command. If the right side of the `=` is `p`, it is enabled. (If it's `_`, it is disabled.)

```bash
sudo cat /sys/kernel/debug/dynamic_debug/control | grep "agnocast.c"
/.../agnocast/kmod/agnocast.c:810 [agnocast]release_msgs_to_meet_depth =p "Release oldest message in the publisher_queue (publisher_pid=%d) of the topic (topic_name=%s) with qos_depth %d. (release_msgs_to_meet_depth)\012"
/.../agnocast/kmod/agnocast.c:367 [agnocast]insert_message_entry =p "Insert an entry (topic_name=%s publisher_pid=%d msg_virtual_address=%lld timestamp=%lld). (insert_message_entry)"
```

To use dynamic_debug, the Linux kernel configuration must have CONFIG_DYNAMIC_DEBUG set to `y`.
If CONFIG_DYNAMIC_DEBUG is not enabled in your environment, perform a debug build with:

```bash
make CFLAGS_agnocast.o="-DDEBUG"
```

Refer to the [Linux kernel documentation](https://www.kernel.org/doc/Documentation/kbuild/makefiles.txt) on kbuild for more information about compilation flags.

## (For developer) Test

You can build, test and generate the coverage report by following:

```bash
bash scripts/test_and_create_report
```

## (For developer) Setup pre-commit

The following command allows `clang-format` and `markdownlint` to be run before each commit.

```bash
bash scripts/setup
```

If you want to disable pre-commit, please execute `pre-commit uninstall`.

## Documents

- [shared memory](./docs/shared_memory.md)
- [message queue](./docs/message_queue.md)
- [Autoware integration](./docs/autoware_integration.md)
- [Memory format in heaphook](./docs/heaphook_alignment.md)
