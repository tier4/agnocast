# ROS 2 Agnocast
True Zero Copy Communication Middleware for Undefined ROS 2 Message Types.

prototype: https://github.com/sykwer/agnocast

## Build
```
source /opt/ros/humble/setup.bash
rosdep install -y --from-paths src --ignore-src --rosdistro $ROS_DISTRO
colcon build
cd kmod
make
```

## Run
Insert kernel module.
```
cd kmod
sudo insmod agnocast.ko
sudo lsmod
```

Run sample app (different window for each script).
The order does not matter.
```
bash scripts/run_listener
bash scripts/run_listen_talker
bash scripts/run_talker
```

Check kmod state.
```
cat /sys/module/agnocast/status/all
```

Unload kmod.
```
sudo rmmod agnocast
```

## Debug
To use dynamic_debug for dynamically outputting debug logs, please run the following command as super user:
```
sudo su
echo 'file agnocast.c +p' > /sys/kernel/debug/dynamic_debug/control
```

Check if dynamic_debug is enabled by running the following command. If the right side of the `=` is `p`, it is enabled. (If it's `_`, it is disabled.)
```
sudo cat /sys/kernel/debug/dynamic_debug/control | grep "agnocast.c"
/.../agnocast/kmod/agnocast.c:810 [agnocast]release_msgs_to_meet_depth =p "Release oldest message in the publisher_queue (publisher_pid=%d) of the topic (topic_name=%s) with qos_depth %d. (release_msgs_to_meet_depth)\012"
/.../agnocast/kmod/agnocast.c:367 [agnocast]insert_message_entry =p "Insert an entry (topic_name=%s publisher_pid=%d msg_virtual_address=%lld timestamp=%lld). (insert_message_entry)"
```

To use dynamic_debug, the Linux kernel configuration must have CONFIG_DYNAMIC_DEBUG set to `y`.
If CONFIG_DYNAMIC_DEBUG is not enabled in your environment, perform a debug build with:
```
make CFLAGS_agnocast.o="-DDEBUG"
```
Refer to the [Linux kernel documentation](https://www.kernel.org/doc/Documentation/kbuild/makefiles.txt) on kbuild for more information about compilation flags.

## (For developer) Setup pre-commit

The following command allows clang-format to be run before each commit.

```
bash scripts/setup_pre_commit
```

If you want to disable pre-commit, please execute `pre-commit uninstall`.

## Documents

 - [shared memory](./docs/shared_memory.md)