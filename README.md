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

## (For developer) Setup pre-commit

The following command allows clang-format to be run before each commit.

```
bash scripts/setup_pre_commit
```

If you want to disable pre-commit, please execute `pre-commit uninstall`.
