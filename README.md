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
```
bash scripts/run_listener
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
