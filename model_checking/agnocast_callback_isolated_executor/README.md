# Model checking for CallbackIsolatedAgnocastExecutor

## Model checking for SingleThreadedAgnocastExecutor

The `CallbackIsolatedAgnocastExecutor` is regarded as a set of `SingleThreadedAgnocastExecutor`s. Therefore, we verify the `SingleThreadedAgnocastExecutor` in isolation as first step.

### Overall modeling policy

- The Agnocast-related part is modeled as accurately as possible, and only the kernel module part is simplified.
- The ROS-related part is roughly modeled.
- The topic names are not modeled and assumed to be same for all publishers and subscriptions (the name space is separated between ROS and Agnocast). This is because this case is most complex for the executor.
- The behavior of the MutuallyExclusive callback group is not modeled, because there is currently only one `SingleThreadedAgnocastExecutor`, and going forward, one `SingleThreadedAgnocastExecutor` will be provided per callback group, `callback_group.can_be_taken_from` will always be true.

### Setup

The verification is conducted under the following conditions:

- Only one `SingleThreadedAgnocastExecutor` exists (`NUM_EXECUTORS = 1`).
- For both ROS and Agnocast, there is one publisher and two subscriptions (`NUM_SUBSCRIPTIONS = 2`).
  - Subscriptions may join in the middle of execution.
- Each publisher sends just two messages (`NUM_PUBLISH = 2`).

Increasing `NUM_SUBSCRIPTIONS` or `NUM_PUBLISH` is difficult due to memory usage issues.

### Subjects to be verified

The model verifies the `ltl eventually_completed` which ensures all callbacks eventually complete.

### Result of enbug

#### Enbug 1

I commented out following line.

```c
inline prepare_epoll() {
...

d_step{
    // epoll_added[cb_info_i] = true;// epoll_ctl(epoll_fd_, EPOLL_CTL_ADD, ...); <- comment out
    expected_num_completed_cbs = expected_num_completed_cbs + NUM_PUBLISH - num_agnocast_published;
    printf("Agnocast | agnocast subscription is registered: callback_info_id = %d,num_agnocast_published = %d\n",cb_info_i,num_agnocast_published);
}

...
```

As shown in this output, registered agnocast subscriptions are not executed; thus, `ltl eventually_completed` is never satisfied.

```bash
ltl eventually_completed: [] (<> ((num_completed_cbs==expected_num_completed_cbs)))
Never claim moves to line 3     [(!((num_completed_cbs==expected_num_completed_cbs)))]
Never claim moves to line 8     [(!((num_completed_cbs==expected_num_completed_cbs)))]
                                  ROS | ros subscription is registered: cb_id = 0,num_ros_published = 0
                              ROS | ros subscription is registered: cb_id = 1,num_ros_published = 0
                                          Agnocast | agnocast subscription is registered: callback_info_id = 0,num_agnocast_published = 0
                                          Agnocast | agnocast subscription is registered: callback_info_id = 1,num_agnocast_published = 0
                                          ROS | start ros_timer_callback()
                                          ROS | finish ros_timer_callback()
                                          ROS | start ros_timer_callback()
                                          ROS | finish ros_timer_callback()
                                          Agnocast | start agnocast_timer_callback()
                                          Agnocast | finish agnocast_timer_callback()
                                          Agnocast | start agnocast_timer_callback()
                                          Agnocast | finish agnocast_timer_callback()
                                          ROS | subscription_callback(): cb_id = 0
                                          ROS | subscription_callback(): cb_id = 1
                                          ROS | subscription_callback(): cb_id = 0
                                          ROS | subscription_callback(): cb_id = 1
  <<<<<START OF CYCLE>>>>>
spin: trail ends after 866 steps
#processes: 9
                num_completed_cbs = 8
                num_ros_published = 2
                num_agnocast_published = 2
                expected_num_completed_cbs = 12
                consecutive_empty_executor_loop[0] = 0
                wait_for_weak_fairness[0] = 0
                queue 1 (resume_requests): 
                mutex_.is_locked = 0
                cur_ros_sub_cb_id = 2
                queue 2 (ready_executables): 
                registered_ros_subscriptions[0].id = 0
                registered_ros_subscriptions[0].type = SUBSCRIPTION
                registered_ros_subscriptions[1].id = 1
                registered_ros_subscriptions[1].type = SUBSCRIPTION
                next_callback_info_id = 2
                id2_callback_info_mtx.is_locked = 0
                id2_callback_info[0].callback_group = 1
                id2_callback_info[0].need_epoll_update = 0
                id2_callback_info[0].initialized = 1
                id2_callback_info[1].callback_group = 0
                id2_callback_info[1].need_epoll_update = 0
                id2_callback_info[1].initialized = 1
                need_epoll_updates = 0
                ready_agnocast_executables_mutex_.is_locked = 1
                entry_num[0] = 0
                entry_num[1] = 0
                epoll_added[0] = 0
                epoll_added[1] = 0
866:    proc  8 (SingleThreadedAgnocastExecutor:1) utility.pml:9 (state 66)
866:    proc  7 (RosPublisher:1) ros_pub_sub.pml:43 (state 21) <valid end state>
866:    proc  6 (RosSubscription:1) ros_pub_sub.pml:9 (state 7) <valid end state>
866:    proc  5 (RosSubscription:1) ros_pub_sub.pml:9 (state 7) <valid end state>
866:    proc  4 (AgnocastPublisher:1) agnocast_pub_sub.pml:67 (state 15) <valid end state>
866:    proc  3 (AgnocastSubscription:1) agnocast_pub_sub.pml:20 (state 15) <valid end state>
866:    proc  2 (AgnocastSubscription:1) agnocast_pub_sub.pml:20 (state 15) <valid end state>
866:    proc  1 (:init::1) main.pml:82 (state 30) <valid end state>
866:    proc  0 (timeout_handler:1) for_verification.pml:18 (state 14)
866:    proc  - (eventually_completed:1) _spin_nvr.tmp:7 (state 10)
9 processes created
```

#### Enbug 2

I commented out following lines.

```c
inline register_callback(callback_group_) {
...

// lock(id2_callback_info_mtx); <- comment out
id2_callback_info[callback_info_id].initialized = true;
id2_callback_info[callback_info_id].callback_group = callback_group_;
// unlock(id2_callback_info_mtx); <- comment out

...
```

The uninitialized `callback_group` causes assertion violation in `validate_callback_group()`.

```bash
ltl eventually_completed: [] (<> ((num_completed_cbs==expected_num_completed_cbs)))
Never claim moves to line 3     [(!((num_completed_cbs==expected_num_completed_cbs)))]
Never claim moves to line 8     [(!((num_completed_cbs==expected_num_completed_cbs)))]
                                  ROS | ros subscription is registered: cb_id = 0,num_ros_published = 0
                              ROS | ros subscription is registered: cb_id = 1,num_ros_published = 0
                                          Agnocast | start agnocast_timer_callback()
                                          Agnocast | finish agnocast_timer_callback()
                                          Agnocast | start agnocast_timer_callback()
                                          Agnocast | finish agnocast_timer_callback()
                                          ROS | start ros_timer_callback()
                                          ROS | finish ros_timer_callback()
                                          ROS | subscription_callback(): cb_id = 0
                                          ROS | subscription_callback(): cb_id = 1
                                          ROS | start ros_timer_callback()
                                          ROS | finish ros_timer_callback()
                                          ROS | subscription_callback(): cb_id = 0
                                          Agnocast | agnocast subscription is registered: callback_info_id = 0,num_agnocast_published = 2
spin: agnocast_pub_sub.pml:140, Error: assertion violated
spin: text of failed assertion: assert((id2_callback_info[cb_info_i].callback_group!=-(1)))
spin: trail ends after 607 steps
```

### Result of verification

```bash
$ make run
rm -f pan.* *.trail pan *.tmp
spin -a main.pml
ltl eventually_completed: [] (<> ((num_completed_cbs==expected_num_completed_cbs)))
gcc -O3 -DCOLLAPSE -o pan pan.c
rm -f *.trail
./pan -a -n -m30000
Depth=     930 States=    1e+06 Transitions= 2.43e+06 Memory=   161.536 t=     1.46 R=   7e+05
Depth=     943 States=    2e+06 Transitions= 4.71e+06 Memory=   193.665 t=     2.87 R=   7e+05
Depth=     943 States=    3e+06 Transitions= 7.01e+06 Memory=   226.184 t=     4.32 R=   7e+05
Depth=     943 States=    4e+06 Transitions= 9.26e+06 Memory=   257.727 t=     5.72 R=   7e+05
Depth=     943 States=    5e+06 Transitions= 1.15e+07 Memory=   288.294 t=     7.13 R=   7e+05
Depth=     943 States=    6e+06 Transitions= 1.36e+07 Memory=   318.762 t=     8.51 R=   7e+05
Depth=     943 States=    7e+06 Transitions= 1.62e+07 Memory=   350.696 t=     10.1 R=   7e+05
Depth=     943 States=    8e+06 Transitions= 1.88e+07 Memory=   382.141 t=     11.7 R=   7e+05
Depth=     943 States=    9e+06 Transitions= 2.12e+07 Memory=   414.270 t=     13.2 R=   7e+05
Depth=     943 States=    1e+07 Transitions= 2.38e+07 Memory=   446.302 t=     14.9 R=   7e+05
Depth=     943 States=  1.1e+07 Transitions= 2.63e+07 Memory=   477.747 t=     16.4 R=   7e+05
Depth=     943 States=  1.2e+07 Transitions= 2.87e+07 Memory=   508.313 t=       18 R=   7e+05
Depth=     943 States=  1.3e+07 Transitions=  3.1e+07 Memory=   538.782 t=     19.4 R=   7e+05
Depth=     943 States=  1.4e+07 Transitions= 3.36e+07 Memory=   569.348 t=       21 R=   7e+05
Depth=     943 States=  1.5e+07 Transitions= 3.64e+07 Memory=   599.915 t=     22.8 R=   7e+05
Depth=     943 States=  1.6e+07 Transitions= 3.92e+07 Memory=   630.384 t=     24.5 R=   7e+05
Depth=     943 States=  1.7e+07 Transitions= 4.17e+07 Memory=   660.950 t=     26.1 R=   7e+05
Depth=     943 States=  1.8e+07 Transitions= 4.45e+07 Memory=   692.298 t=     27.9 R=   6e+05
Depth=     943 States=  1.9e+07 Transitions= 4.76e+07 Memory=   723.255 t=     29.9 R=   6e+05
Depth=     943 States=    2e+07 Transitions= 5.02e+07 Memory=   755.091 t=     31.5 R=   6e+05
Depth=     943 States=  2.1e+07 Transitions= 5.29e+07 Memory=   786.829 t=     33.4 R=   6e+05
Depth=     943 States=  2.2e+07 Transitions= 5.54e+07 Memory=   817.591 t=       35 R=   6e+05
Depth=     943 States=  2.3e+07 Transitions= 5.81e+07 Memory=   848.157 t=     36.8 R=   6e+05
Depth=     943 States=  2.4e+07 Transitions= 6.07e+07 Memory=   879.212 t=     38.5 R=   6e+05
Depth=     943 States=  2.5e+07 Transitions= 6.31e+07 Memory=   909.680 t=     40.1 R=   6e+05
Depth=     943 States=  2.6e+07 Transitions= 6.57e+07 Memory=   940.345 t=     41.8 R=   6e+05
Depth=     943 States=  2.7e+07 Transitions= 6.81e+07 Memory=   971.887 t=     43.5 R=   6e+05
Depth=     943 States=  2.8e+07 Transitions= 7.04e+07 Memory=  1003.919 t=       45 R=   6e+05
Depth=     943 States=  2.9e+07 Transitions= 7.29e+07 Memory=  1034.778 t=     46.6 R=   6e+05
Depth=     943 States=    3e+07 Transitions= 7.52e+07 Memory=  1066.223 t=     48.3 R=   6e+05
Depth=     943 States=  3.1e+07 Transitions= 7.76e+07 Memory=  1097.864 t=       50 R=   6e+05
Depth=     956 States=  3.2e+07 Transitions= 7.99e+07 Memory=  1129.602 t=     51.5 R=   6e+05
Depth=    1016 States=  3.3e+07 Transitions= 8.22e+07 Memory=  1161.927 t=     53.1 R=   6e+05
Depth=    1059 States=  3.4e+07 Transitions= 8.45e+07 Memory=  1194.739 t=     54.8 R=   6e+05
pan: resizing hashtable to -w26..  done
Depth=    1076 States=  3.5e+07 Transitions= 8.67e+07 Memory=  1723.536 t=       59 R=   6e+05
Depth=    1076 States=  3.6e+07 Transitions= 8.89e+07 Memory=  1756.153 t=     60.5 R=   6e+05
Depth=    1076 States=  3.7e+07 Transitions= 9.14e+07 Memory=  1786.915 t=     62.1 R=   6e+05
Depth=    1076 States=  3.8e+07 Transitions= 9.35e+07 Memory=  1818.262 t=     63.5 R=   6e+05
Depth=    1076 States=  3.9e+07 Transitions= 9.58e+07 Memory=  1849.903 t=       65 R=   6e+05
Depth=    1076 States=    4e+07 Transitions= 9.81e+07 Memory=  1881.739 t=     66.5 R=   6e+05
Depth=    1076 States=  4.1e+07 Transitions=    1e+08 Memory=  1913.966 t=       68 R=   6e+05
Depth=    1076 States=  4.2e+07 Transitions= 1.03e+08 Memory=  1945.997 t=     69.3 R=   6e+05
Depth=    1076 States=  4.3e+07 Transitions= 1.05e+08 Memory=  1978.321 t=     70.8 R=   6e+05
Depth=    1076 States=  4.4e+07 Transitions= 1.07e+08 Memory=  2009.962 t=     72.3 R=   6e+05
Depth=    1076 States=  4.5e+07 Transitions=  1.1e+08 Memory=  2040.723 t=       74 R=   6e+05
Depth=    1076 States=  4.6e+07 Transitions= 1.12e+08 Memory=  2071.387 t=     75.4 R=   6e+05
Depth=    1076 States=  4.7e+07 Transitions= 1.14e+08 Memory=  2102.833 t=     76.9 R=   6e+05
Depth=    1076 States=  4.8e+07 Transitions= 1.17e+08 Memory=  2133.985 t=     78.4 R=   6e+05
Depth=    1076 States=  4.9e+07 Transitions= 1.19e+08 Memory=  2165.040 t=     79.9 R=   6e+05
Depth=    1076 States=    5e+07 Transitions= 1.21e+08 Memory=  2196.485 t=     81.3 R=   6e+05
Depth=    1076 States=  5.1e+07 Transitions= 1.23e+08 Memory=  2227.930 t=     82.7 R=   6e+05
Depth=    1076 States=  5.2e+07 Transitions= 1.26e+08 Memory=  2259.278 t=     84.2 R=   6e+05
Depth=    1076 States=  5.3e+07 Transitions= 1.28e+08 Memory=  2289.845 t=     85.8 R=   6e+05
Depth=    1076 States=  5.4e+07 Transitions= 1.31e+08 Memory=  2319.825 t=     87.5 R=   6e+05
Depth=    1076 States=  5.5e+07 Transitions= 1.33e+08 Memory=  2348.243 t=     89.1 R=   6e+05
Depth=    1076 States=  5.6e+07 Transitions= 1.35e+08 Memory=  2379.884 t=     90.5 R=   6e+05
Depth=    1076 States=  5.7e+07 Transitions= 1.37e+08 Memory=  2411.134 t=     91.9 R=   6e+05
Depth=    1076 States=  5.8e+07 Transitions=  1.4e+08 Memory=  2442.970 t=     93.4 R=   6e+05
Depth=    1076 States=  5.9e+07 Transitions= 1.42e+08 Memory=  2474.024 t=     94.9 R=   6e+05
Depth=    1076 States=    6e+07 Transitions= 1.45e+08 Memory=  2504.981 t=     96.6 R=   6e+05
Depth=    1076 States=  6.1e+07 Transitions= 1.47e+08 Memory=  2536.720 t=     98.2 R=   6e+05
Depth=    1076 States=  6.2e+07 Transitions=  1.5e+08 Memory=  2578.614 t=      100 R=   6e+05
Depth=    1076 States=  6.3e+07 Transitions= 1.54e+08 Memory=  2639.552 t=      103 R=   6e+05
Depth=    1076 States=  6.4e+07 Transitions= 1.57e+08 Memory=  2700.489 t=      106 R=   6e+05
Depth=    1076 States=  6.5e+07 Transitions= 1.61e+08 Memory=  2761.622 t=      109 R=   6e+05
Depth=    1076 States=  6.6e+07 Transitions= 1.65e+08 Memory=  2822.657 t=      112 R=   6e+05
Depth=    1076 States=  6.7e+07 Transitions= 1.69e+08 Memory=  2883.692 t=      115 R=   6e+05
Depth=    1076 States=  6.8e+07 Transitions= 1.73e+08 Memory=  2944.727 t=      118 R=   6e+05
Depth=    1076 States=  6.9e+07 Transitions= 1.77e+08 Memory=  3005.762 t=      121 R=   6e+05
Depth=    1076 States=    7e+07 Transitions= 1.81e+08 Memory=  3066.798 t=      125 R=   6e+05
Depth=    1076 States=  7.1e+07 Transitions= 1.86e+08 Memory=  3127.930 t=      128 R=   6e+05
Depth=    1076 States=  7.2e+07 Transitions=  1.9e+08 Memory=  3188.966 t=      132 R=   5e+05
Depth=    1076 States=  7.3e+07 Transitions= 1.95e+08 Memory=  3250.001 t=      135 R=   5e+05
Depth=    1076 States=  7.4e+07 Transitions= 1.99e+08 Memory=  3311.036 t=      138 R=   5e+05
Depth=    1076 States=  7.5e+07 Transitions= 2.03e+08 Memory=  3372.071 t=      141 R=   5e+05
Depth=    1076 States=  7.6e+07 Transitions= 2.07e+08 Memory=  3433.106 t=      144 R=   5e+05
Depth=    1076 States=  7.7e+07 Transitions=  2.1e+08 Memory=  3494.141 t=      147 R=   5e+05
Depth=    1076 States=  7.8e+07 Transitions= 2.14e+08 Memory=  3555.177 t=      150 R=   5e+05
Depth=    1094 States=  7.9e+07 Transitions= 2.17e+08 Memory=  3616.309 t=      153 R=   5e+05
Depth=    1094 States=    8e+07 Transitions= 2.21e+08 Memory=  3677.345 t=      156 R=   5e+05
Depth=    1094 States=  8.1e+07 Transitions= 2.25e+08 Memory=  3738.380 t=      159 R=   5e+05
Depth=    1094 States=  8.2e+07 Transitions= 2.28e+08 Memory=  3799.415 t=      162 R=   5e+05
Depth=    1094 States=  8.3e+07 Transitions= 2.31e+08 Memory=  3860.450 t=      165 R=   5e+05
Depth=    1094 States=  8.4e+07 Transitions= 2.35e+08 Memory=  3921.387 t=      168 R=   5e+05
Depth=    1094 States=  8.5e+07 Transitions= 2.39e+08 Memory=  3982.423 t=      171 R=   5e+05
Depth=    1094 States=  8.6e+07 Transitions= 2.43e+08 Memory=  4043.458 t=      174 R=   5e+05
Depth=    1094 States=  8.7e+07 Transitions= 2.46e+08 Memory=  4104.493 t=      177 R=   5e+05
Depth=    1094 States=  8.8e+07 Transitions=  2.5e+08 Memory=  4165.528 t=      180 R=   5e+05
Depth=    1094 States=  8.9e+07 Transitions= 2.54e+08 Memory=  4223.634 t=      183 R=   5e+05
Depth=    1094 States=    9e+07 Transitions= 2.57e+08 Memory=  4283.887 t=      186 R=   5e+05
Depth=    1094 States=  9.1e+07 Transitions= 2.61e+08 Memory=  4344.727 t=      189 R=   5e+05
Depth=    1094 States=  9.2e+07 Transitions= 2.65e+08 Memory=  4405.567 t=      193 R=   5e+05

(Spin Version 6.5.2 -- 6 December 2019)
        + Partial Order Reduction
        + Compression

Full statespace search for:
        never claim             + (eventually_completed)
        assertion violations    + (if within scope of claim)
        acceptance   cycles     + (fairness disabled)
        invalid end states      - (disabled by never claim)

State-vector 240 byte, depth reached 1094, errors: 0
 61658493 states, stored (9.24663e+07 visited)
1.7412776e+08 states, matched
2.6659408e+08 transitions (= visited+matched)
 18022118 atomic steps
hash conflicts:  64497685 (resolved)

Stats on memory usage (in Megabytes):
16229.385       equivalent memory usage for states (stored*(State-vector + overhead))
 3920.735       actual memory usage for states (compression: 24.16%)
                state-vector as stored = 31 byte + 36 byte overhead
  512.000       memory used for hash table (-w26)
    1.602       memory used for DFS stack (-m30000)
 4433.985       total actual memory usage


nr of templates: [ 0:globals 1:chans 2:procs ]
collapse counts: [ 0:591105 2:3 3:2 4:17 5:28 6:13 7:10615 8:24 9:2 ]

pan: elapsed time 194 seconds
pan: rate 476483.19 states/second
```
