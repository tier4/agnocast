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
colcon build --symlink-install --cmake-args -DCMAKE_BUILD_TYPE=Release
```

## Run

Insert kernel module.

```bash
sudo modprobe agnocast
```

Run sample app (different window for each script).
The order does not matter.

```bash
bash scripts/run_listener
bash scripts/run_talker
```

Stop applications and unload kernel module.

```bash
sudo modprobe -r agnocast
```

## Debug

Check the kernel log.

```bash
sudo dmesg -w
```

To use dynamic_debug for dynamically outputting debug logs, please run the following command as super user:

```bash
sudo su
echo 'file agnocast_main.c +p' > /sys/kernel/debug/dynamic_debug/control
```

Check if dynamic_debug is enabled by running the following command. If the right side of the `=` is `p`, it is enabled. (If it's `_`, it is disabled.)

```bash
sudo cat /sys/kernel/debug/dynamic_debug/control | grep "agnocast_main.c"
/.../agnocast/agnocast_kmod/agnocast_main.c:810 [agnocast]release_msgs_to_meet_depth =p "Release oldest message in the publisher_queue (publisher_pid=%d) of the topic (topic_name=%s) with qos_depth %d. (release_msgs_to_meet_depth)\012"
/.../agnocast/agnocast_kmod/agnocast_main.c:367 [agnocast]insert_message_entry =p "Insert an entry (topic_name=%s publisher_pid=%d msg_virtual_address=%lld timestamp=%lld). (insert_message_entry)"
```

To use dynamic_debug, the Linux kernel configuration must have CONFIG_DYNAMIC_DEBUG set to `y`.
If CONFIG_DYNAMIC_DEBUG is not enabled in your environment, perform a debug build with:

```bash
make CFLAGS_agnocast.o="-DDEBUG"
```

Refer to the [Linux kernel documentation](https://www.kernel.org/doc/Documentation/kbuild/makefiles.txt) on kbuild for more information about compilation flags.

## Documents

- [shared memory](./docs/shared_memory.md)
- [message queue](./docs/message_queue.md)
- [Autoware integration](./docs/autoware_integration.md)
- [Memory format in heaphook](./docs/heaphook_alignment.md)
- [Clang-tidy Suppressions](./docs/clang_tidy_suppression.md)
- [How to set environment variables](./docs/how_to_set_environment_variables.md)
- [ros2 command extension](./docs/ros2_command_extension.md)

## Troubleshooting

Although Agnocast includes cleanup procedures for resources like shared memory and message queues, these resources may sometimes remain in the system. If you notice that available system memory decreases every time you run an Agnocast-enabled application, you'll need to remove leftover shared memory objects by running:

```bash
rm /dev/shm/agnocast@*
```

Additionally, if you encounter the error `mq_open failed: No space left on device`, it means that the system has reached the maximum number of message queues. In that case, you may need to remove leftover message queues by running:

```bash
rm /dev/mqueue/agnocast@*
rm /dev/mqueue/agnocast_to_ros2@*
```

---

## For developer

### Setup pre-commit

The following command allows `clang-format`, `markdownlint`, and [KUNIT Test](./agnocast_kmod/agnocast_kunit.c) to be run before each commit.

```bash
python3 -m pip install pre-commit
python3 -m pip install --upgrade pre-commit identify
pre-commit install
```

If you want to disable pre-commit, please run `pre-commit uninstall`.

### Build and insert kmod

> [!NOTE]
> If you have already installed `agnocast-heaphook` or `agnocast-kmod` via apt (i.e., `bash scripts/setup`), please remove them first.

Build.

```bash
bash scripts/build_all
```

Check if there is a `libagnocast_heaphook.so` in `install/agnocastlib/lib`.

```bash
$ ls install/agnocastlib/lib | grep libagnocast_heaphook
libagnocast_heaphook.so
```

Insert kernel module.

```bash
cd agnocast_kmod
sudo insmod agnocast.ko
sudo lsmod
```

### Test

You can build, test and generate the coverage report by following:

```bash
bash scripts/test_and_create_report
```

### Kernel Module Test

A custom kernel with the following CONFIG enabled is required to run KUnit Test and obtain the coverage report (sample custom kernel is placed [here](https://drive.google.com/drive/folders/1sd8ROusgxhnEDOO0hbze3F5y47qtIdcM?usp=drive_link)).

- `CONFIG_KUNIT=y`
- `CONFIG_GCOV_KERNEL=y`

If booting with the custom kernel, the following script can be used to run unit tests on kernel modules and generate coverage reports.

```bash
bash scripts/run_kunit
```

You can also use [pre-commit](#setup-pre-commit)
