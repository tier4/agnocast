# ROS 2 Agnocast
True Zero Copy Communication Middleware for Undefined ROS 2 Message Types.

prototype: https://github.com/sykwer/agnocast

## Build
```
colcon build
cd kmod
make
```

## Run
Insert kernel module.
```
cd kmod
sudo insmod agnocast.kmod
sudo lsmod
```

Run sample app (different window for each script).
```
bash scripts/run_listener
bash scripts/run_talker
```

Check kmod state.
```
cat /sys/module/agnocast/state/all
```

Unload kmod.
```
sudo rmmod agnocast
```
