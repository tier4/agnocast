# Model checking for CallbackIsolatedAgnocastExecutor

Currently, this model verifies a behavior or a single SingleThreadedAgnocastExecutor as first step.

## Setup

The verification is conducted under the following conditions:

- Only one SingleThreadedAgnocastExecutor exists (`NUM_EXECUTORS`).
- For both ROS and Agnocast, there is one publisher and two subscriptions (`NUM_SUBSCRIPTIONS = 2`).
  - Subscriptions may join in the middle of execution.
- Each publisher sends two messages (`NUM_PUBLISH = 2`).
- The behavior of the MutuallyExclusive callback group is not modeled for now.

Increasing `NUM_SUBSCRIPTIONS` or `NUM_PUBLISH` is difficult due to memory usage issues...

## Subjects to be verified

The model verifies the `ltl eventually_completed` which ensures all callbacks eventually complete.

## Result of enbug

I've commented out following line.

```c
inline prepare_epoll() {
	...
		
		d_step{
			// epoll_added[cb_info_i] = true; <- comment out
			expected_num_completed_cbs = expected_num_completed_cbs + NUM_PUBLISH - num_agnocast_published;
			printf("Agnocast | agnocast subscription is registered: callback_info_id = %d,topic_name = %d\n",cb_info_i,id2_callback_info[cb_info_i].topic_name);
		}
		
	...
```

As shown in this output, registered agnocast subscriptions are not executed and `ltl eventually_completed` is never satisfied.

```bash
spin -t main.pml
ltl eventually_completed: <> ((num_completed_cbs==expected_num_completed_cbs))
Never claim moves to line 4     [(!((num_completed_cbs==expected_num_completed_cbs)))]
                                  ROS | ros subscription is registered: cb_id = 0,topic_name = 82
                              ROS | ros subscription is registered: cb_id = 1,topic_name = 82
                                          Agnocast | agnocast subscription is registered: callback_info_id = 0,topic_name = 65
                                          Agnocast | agnocast subscription is registered: callback_info_id = 1,topic_name = 65
                                          ROS | start ros_timer_callback(): topic_name = 82
                                          ROS | finish ros_timer_callback(): topic_name = 82
                                          ROS | start ros_timer_callback(): topic_name = 82
                                          ROS | finish ros_timer_callback(): topic_name = 82
                                          Agnocast | start agnocast_timer_callback(): topic_name = 65
                                          Agnocast | finish agnocast_timer_callback(): topic_name = 65
                                          Agnocast | start agnocast_timer_callback(): topic_name = 65
                                          Agnocast | finish agnocast_timer_callback(): topic_name = 65
                                          ROS | subscription_callback(): cb_id = 0
                                          ROS | subscription_callback(): cb_id = 1
                                          ROS | subscription_callback(): cb_id = 0
                                          ROS | subscription_callback(): cb_id = 1
  <<<<<START OF CYCLE>>>>>
spin: trail ends after 1244 steps
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
                registered_ros_subscriptions[0].topic_name = 82
                registered_ros_subscriptions[1].id = 1
                registered_ros_subscriptions[1].type = SUBSCRIPTION
                registered_ros_subscriptions[1].topic_name = 82
                next_callback_info_id = 2
                id2_callback_info_mtx.is_locked = 0
                id2_callback_info[0].callback_group = 1
                id2_callback_info[0].topic_name = 65
                id2_callback_info[0].need_epoll_update = 0
                id2_callback_info[1].callback_group = 0
                id2_callback_info[1].topic_name = 65
                id2_callback_info[1].need_epoll_update = 0
                queue 3 (id2_callback_info_keys): [0][1]
                need_epoll_updates = 0
                ready_agnocast_executables_mutex_.is_locked = 0
                entry_num[0] = 0
                entry_num[1] = 0
                epoll_added[0] = 0
                epoll_added[1] = 0
1244:   proc  8 (SingleThreadedAgnocastExecutor:1) main.pml:52 (state 257)
1244:   proc  7 (RosPublisher:1) ros_pub_sub.pml:51 (state 22) <valid end state>
1244:   proc  6 (RosSubscription:1) ros_pub_sub.pml:10 (state 8) <valid end state>
1244:   proc  5 (RosSubscription:1) ros_pub_sub.pml:10 (state 8) <valid end state>
1244:   proc  4 (AgnocastPublisher:1) agnocast_pub_sub.pml:66 (state 16) <valid end state>
1244:   proc  3 (AgnocastSubscription:1) agnocast_pub_sub.pml:23 (state 17) <valid end state>
1244:   proc  2 (AgnocastSubscription:1) agnocast_pub_sub.pml:23 (state 17) <valid end state>
1244:   proc  1 (:init::1) main.pml:80 (state 30) <valid end state>
1244:   proc  0 (timeout_handler:1) for_verification.pml:18 (state 14)
1244:   proc  - (eventually_completed:1) _spin_nvr.tmp:3 (state 3)
9 processes created
```

## Result of verification

```bash
spin -a main.pml
ltl eventually_completed: <> ((num_completed_cbs==expected_num_completed_cbs))
gcc -O3 -DCOLLAPSE -DVECTORSZ=5000 -DNFAIR=3 -o pan pan.c
rm -f *.trail
./pan -a -n -m30000
Depth=    1357 States=    1e+06 Transitions= 2.23e+06 Memory=   165.365 t=     1.68 R=   6e+05
Depth=    1357 States=    2e+06 Transitions=  4.5e+06 Memory=   200.174 t=     3.36 R=   6e+05
Depth=    1370 States=    3e+06 Transitions= 6.69e+06 Memory=   232.599 t=     4.98 R=   6e+05
Depth=    1370 States=    4e+06 Transitions= 8.85e+06 Memory=   265.024 t=     6.56 R=   6e+05
Depth=    1370 States=    5e+06 Transitions=  1.1e+07 Memory=   296.972 t=     8.15 R=   6e+05
Depth=    1370 States=    6e+06 Transitions= 1.32e+07 Memory=   330.351 t=     9.85 R=   6e+05
Depth=    1370 States=    7e+06 Transitions= 1.54e+07 Memory=   362.776 t=     11.5 R=   6e+05
Depth=    1370 States=    8e+06 Transitions= 1.76e+07 Memory=   394.247 t=     13.2 R=   6e+05
Depth=    1370 States=    9e+06 Transitions= 1.98e+07 Memory=   424.765 t=     14.8 R=   6e+05
Depth=    1370 States=    1e+07 Transitions= 2.19e+07 Memory=   455.282 t=     16.4 R=   6e+05
Depth=    1370 States=  1.1e+07 Transitions=  2.4e+07 Memory=   485.800 t=       18 R=   6e+05
Depth=    1370 States=  1.2e+07 Transitions= 2.62e+07 Memory=   516.317 t=     19.7 R=   6e+05
Depth=    1370 States=  1.3e+07 Transitions= 2.84e+07 Memory=   546.835 t=     21.3 R=   6e+05
Depth=    1370 States=  1.4e+07 Transitions= 3.07e+07 Memory=   580.690 t=     23.1 R=   6e+05
Depth=    1370 States=  1.5e+07 Transitions= 3.29e+07 Memory=   614.546 t=     24.9 R=   6e+05
Depth=    1370 States=  1.6e+07 Transitions= 3.56e+07 Memory=   648.401 t=     26.9 R=   6e+05
Depth=    1370 States=  1.7e+07 Transitions= 3.81e+07 Memory=   681.303 t=     28.9 R=   6e+05
Depth=    1370 States=  1.8e+07 Transitions= 4.04e+07 Memory=   713.251 t=     30.6 R=   6e+05
Depth=    1370 States=  1.9e+07 Transitions= 4.27e+07 Memory=   745.199 t=     32.5 R=   6e+05
Depth=    1370 States=    2e+07 Transitions=  4.5e+07 Memory=   776.194 t=     34.2 R=   6e+05
Depth=    1370 States=  2.1e+07 Transitions= 4.75e+07 Memory=   809.095 t=     36.3 R=   6e+05
Depth=    1370 States=  2.2e+07 Transitions= 5.03e+07 Memory=   841.997 t=     38.5 R=   6e+05
Depth=    1370 States=  2.3e+07 Transitions= 5.28e+07 Memory=   873.468 t=     40.4 R=   6e+05
Depth=    1370 States=  2.4e+07 Transitions= 5.52e+07 Memory=   904.463 t=     42.4 R=   6e+05
Depth=    1370 States=  2.5e+07 Transitions= 5.75e+07 Memory=   934.980 t=     44.2 R=   6e+05
Depth=    1370 States=  2.6e+07 Transitions= 5.98e+07 Memory=   965.498 t=       46 R=   6e+05
Depth=    1370 States=  2.7e+07 Transitions= 6.21e+07 Memory=   996.015 t=     47.8 R=   6e+05
Depth=    1370 States=  2.8e+07 Transitions= 6.44e+07 Memory=  1026.533 t=     49.6 R=   6e+05
Depth=    1370 States=  2.9e+07 Transitions= 6.69e+07 Memory=  1057.051 t=     51.5 R=   6e+05
Depth=    1370 States=    3e+07 Transitions= 6.94e+07 Memory=  1087.568 t=     53.5 R=   6e+05
Depth=    1370 States=  3.1e+07 Transitions=  7.2e+07 Memory=  1118.563 t=     55.6 R=   6e+05
Depth=    1370 States=  3.2e+07 Transitions= 7.48e+07 Memory=  1149.080 t=     57.9 R=   6e+05
Depth=    1370 States=  3.3e+07 Transitions= 7.73e+07 Memory=  1179.598 t=     59.9 R=   6e+05
Depth=    1370 States=  3.4e+07 Transitions= 7.99e+07 Memory=  1210.115 t=       62 R=   5e+05
pan: resizing hashtable to -w26..  done
Depth=    1370 States=  3.5e+07 Transitions= 8.27e+07 Memory=  1736.897 t=       67 R=   5e+05
Depth=    1370 States=  3.6e+07 Transitions= 8.52e+07 Memory=  1767.415 t=     68.9 R=   5e+05
Depth=    1370 States=  3.7e+07 Transitions= 8.77e+07 Memory=  1797.932 t=     70.8 R=   5e+05
Depth=    1370 States=  3.8e+07 Transitions= 9.02e+07 Memory=  1828.450 t=     72.7 R=   5e+05
Depth=    1370 States=  3.9e+07 Transitions= 9.27e+07 Memory=  1858.968 t=     74.6 R=   5e+05
Depth=    1370 States=    4e+07 Transitions= 9.52e+07 Memory=  1889.485 t=     76.5 R=   5e+05
Depth=    1370 States=  4.1e+07 Transitions= 9.79e+07 Memory=  1921.433 t=     78.5 R=   5e+05
Depth=    1370 States=  4.2e+07 Transitions=    1e+08 Memory=  1953.858 t=     80.3 R=   5e+05
Depth=    1370 States=  4.3e+07 Transitions= 1.03e+08 Memory=  1985.806 t=     82.1 R=   5e+05
Depth=    1370 States=  4.4e+07 Transitions= 1.05e+08 Memory=  2018.708 t=     84.3 R=   5e+05
Depth=    1370 States=  4.5e+07 Transitions= 1.08e+08 Memory=  2051.133 t=     86.5 R=   5e+05
Depth=    1370 States=  4.6e+07 Transitions= 1.11e+08 Memory=  2083.081 t=     88.4 R=   5e+05
Depth=    1370 States=  4.7e+07 Transitions= 1.13e+08 Memory=  2114.075 t=     90.2 R=   5e+05
Depth=    1370 States=  4.8e+07 Transitions= 1.16e+08 Memory=  2145.547 t=       92 R=   5e+05
Depth=    1370 States=  4.9e+07 Transitions= 1.18e+08 Memory=  2177.018 t=     93.9 R=   5e+05
Depth=    1370 States=    5e+07 Transitions= 1.21e+08 Memory=  2208.012 t=     96.1 R=   5e+05
Depth=    1370 States=  5.1e+07 Transitions= 1.24e+08 Memory=  2239.960 t=     98.5 R=   5e+05
Depth=    1370 States=  5.2e+07 Transitions= 1.27e+08 Memory=  2271.432 t=      101 R=   5e+05
Depth=    1370 States=  5.3e+07 Transitions=  1.3e+08 Memory=  2302.903 t=      103 R=   5e+05
Depth=    1370 States=  5.4e+07 Transitions= 1.33e+08 Memory=  2333.421 t=      105 R=   5e+05
Depth=    1370 States=  5.5e+07 Transitions= 1.35e+08 Memory=  2363.938 t=      107 R=   5e+05
Depth=    1370 States=  5.6e+07 Transitions= 1.38e+08 Memory=  2394.456 t=      109 R=   5e+05
Depth=    1370 States=  5.7e+07 Transitions=  1.4e+08 Memory=  2424.973 t=      111 R=   5e+05
Depth=    1370 States=  5.8e+07 Transitions= 1.42e+08 Memory=  2455.491 t=      112 R=   5e+05
Depth=    1370 States=  5.9e+07 Transitions= 1.45e+08 Memory=  2486.008 t=      114 R=   5e+05
Depth=    1370 States=    6e+07 Transitions= 1.48e+08 Memory=  2516.526 t=      116 R=   5e+05
Depth=    1370 States=  6.1e+07 Transitions=  1.5e+08 Memory=  2547.044 t=      119 R=   5e+05
Depth=    1370 States=  6.2e+07 Transitions= 1.53e+08 Memory=  2578.515 t=      121 R=   5e+05
Depth=    1370 States=  6.3e+07 Transitions= 1.55e+08 Memory=  2609.032 t=      122 R=   5e+05
Depth=    1370 States=  6.4e+07 Transitions= 1.57e+08 Memory=  2639.550 t=      124 R=   5e+05
Depth=    1370 States=  6.5e+07 Transitions=  1.6e+08 Memory=  2670.068 t=      126 R=   5e+05
Depth=    1370 States=  6.6e+07 Transitions= 1.62e+08 Memory=  2700.585 t=      128 R=   5e+05
Depth=    1370 States=  6.7e+07 Transitions= 1.65e+08 Memory=  2731.103 t=      130 R=   5e+05
Depth=    1370 States=  6.8e+07 Transitions= 1.67e+08 Memory=  2761.620 t=      132 R=   5e+05
Depth=    1370 States=  6.9e+07 Transitions=  1.7e+08 Memory=  2792.138 t=      134 R=   5e+05
Depth=    1370 States=    7e+07 Transitions= 1.73e+08 Memory=  2823.132 t=      136 R=   5e+05
Depth=    1370 States=  7.1e+07 Transitions= 1.75e+08 Memory=  2853.650 t=      138 R=   5e+05
Depth=    1603 States=  7.2e+07 Transitions= 1.78e+08 Memory=  2887.029 t=      140 R=   5e+05
Depth=    1603 States=  7.3e+07 Transitions=  1.8e+08 Memory=  2918.500 t=      142 R=   5e+05
Depth=    1667 States=  7.4e+07 Transitions= 1.82e+08 Memory=  2951.402 t=      144 R=   5e+05
Depth=    1667 States=  7.5e+07 Transitions= 1.84e+08 Memory=  2984.780 t=      145 R=   5e+05
Depth=    1667 States=  7.6e+07 Transitions= 1.86e+08 Memory=  3018.159 t=      147 R=   5e+05
Depth=    1667 States=  7.7e+07 Transitions= 1.89e+08 Memory=  3049.153 t=      149 R=   5e+05
Depth=    1667 States=  7.8e+07 Transitions= 1.91e+08 Memory=  3080.624 t=      151 R=   5e+05
Depth=    1667 States=  7.9e+07 Transitions= 1.93e+08 Memory=  3114.480 t=      153 R=   5e+05
Depth=    1667 States=    8e+07 Transitions= 1.95e+08 Memory=  3148.335 t=      155 R=   5e+05
Depth=    1667 States=  8.1e+07 Transitions= 1.98e+08 Memory=  3181.237 t=      156 R=   5e+05
Depth=    1667 States=  8.2e+07 Transitions=    2e+08 Memory=  3214.616 t=      158 R=   5e+05
Depth=    1667 States=  8.3e+07 Transitions= 2.02e+08 Memory=  3246.087 t=      160 R=   5e+05
Depth=    1667 States=  8.4e+07 Transitions= 2.05e+08 Memory=  3277.558 t=      162 R=   5e+05
Depth=    1667 States=  8.5e+07 Transitions= 2.08e+08 Memory=  3310.460 t=      164 R=   5e+05
Depth=    1667 States=  8.6e+07 Transitions=  2.1e+08 Memory=  3342.408 t=      166 R=   5e+05
Depth=    1667 States=  8.7e+07 Transitions= 2.12e+08 Memory=  3373.879 t=      168 R=   5e+05
Depth=    1667 States=  8.8e+07 Transitions= 2.15e+08 Memory=  3405.351 t=      170 R=   5e+05
Depth=    1667 States=  8.9e+07 Transitions= 2.17e+08 Memory=  3436.822 t=      172 R=   5e+05
Depth=    1667 States=    9e+07 Transitions=  2.2e+08 Memory=  3468.293 t=      174 R=   5e+05
Depth=    1667 States=  9.1e+07 Transitions= 2.22e+08 Memory=  3499.287 t=      176 R=   5e+05
Depth=    1667 States=  9.2e+07 Transitions= 2.24e+08 Memory=  3532.189 t=      178 R=   5e+05
Depth=    1667 States=  9.3e+07 Transitions= 2.26e+08 Memory=  3565.091 t=      179 R=   5e+05
Depth=    1667 States=  9.4e+07 Transitions= 2.28e+08 Memory=  3599.900 t=      181 R=   5e+05
Depth=    1667 States=  9.5e+07 Transitions=  2.3e+08 Memory=  3634.232 t=      183 R=   5e+05
Depth=    1706 States=  9.6e+07 Transitions= 2.33e+08 Memory=  3668.088 t=      185 R=   5e+05
Depth=    1706 States=  9.7e+07 Transitions= 2.35e+08 Memory=  3702.420 t=      186 R=   5e+05
Depth=    1706 States=  9.8e+07 Transitions= 2.37e+08 Memory=  3739.137 t=      188 R=   5e+05
Depth=    1706 States=  9.9e+07 Transitions= 2.39e+08 Memory=  3771.085 t=      190 R=   5e+05
Depth=    1706 States=    1e+08 Transitions= 2.42e+08 Memory=  3802.079 t=      192 R=   5e+05
Depth=    1706 States= 1.01e+08 Transitions= 2.44e+08 Memory=  3833.550 t=      194 R=   5e+05
Depth=    1706 States= 1.02e+08 Transitions= 2.46e+08 Memory=  3866.452 t=      196 R=   5e+05
Depth=    1706 States= 1.03e+08 Transitions= 2.48e+08 Memory=  3901.261 t=      198 R=   5e+05
Depth=    1706 States= 1.04e+08 Transitions=  2.5e+08 Memory=  3936.070 t=      200 R=   5e+05
Depth=    1706 States= 1.05e+08 Transitions= 2.53e+08 Memory=  3969.449 t=      201 R=   5e+05
Depth=    1706 States= 1.06e+08 Transitions= 2.55e+08 Memory=  4002.827 t=      203 R=   5e+05
Depth=    1706 States= 1.07e+08 Transitions= 2.57e+08 Memory=  4037.637 t=      205 R=   5e+05
Depth=    1706 States= 1.08e+08 Transitions= 2.59e+08 Memory=  4073.399 t=      207 R=   5e+05
Depth=    1706 States= 1.09e+08 Transitions= 2.61e+08 Memory=  4104.871 t=      209 R=   5e+05
Depth=    1706 States=  1.1e+08 Transitions= 2.64e+08 Memory=  4135.865 t=      211 R=   5e+05
Depth=    1706 States= 1.11e+08 Transitions= 2.66e+08 Memory=  4166.383 t=      213 R=   5e+05
Depth=    1706 States= 1.12e+08 Transitions= 2.68e+08 Memory=  4196.900 t=      214 R=   5e+05
Depth=    1706 States= 1.13e+08 Transitions= 2.71e+08 Memory=  4227.418 t=      216 R=   5e+05
Depth=    1706 States= 1.14e+08 Transitions= 2.73e+08 Memory=  4258.412 t=      218 R=   5e+05
Depth=    1706 States= 1.15e+08 Transitions= 2.75e+08 Memory=  4291.791 t=      220 R=   5e+05
Depth=    1706 States= 1.16e+08 Transitions= 2.77e+08 Memory=  4325.169 t=      222 R=   5e+05
Depth=    1706 States= 1.17e+08 Transitions=  2.8e+08 Memory=  4357.594 t=      224 R=   5e+05
Depth=    1706 States= 1.18e+08 Transitions= 2.82e+08 Memory=  4390.019 t=      226 R=   5e+05
Depth=    1706 States= 1.19e+08 Transitions= 2.84e+08 Memory=  4421.014 t=      227 R=   5e+05
Depth=    1706 States=  1.2e+08 Transitions= 2.86e+08 Memory=  4452.962 t=      229 R=   5e+05
Depth=    1706 States= 1.21e+08 Transitions= 2.89e+08 Memory=  4485.387 t=      231 R=   5e+05
Depth=    1706 States= 1.22e+08 Transitions= 2.91e+08 Memory=  4517.335 t=      233 R=   5e+05
Depth=    1706 States= 1.23e+08 Transitions= 2.93e+08 Memory=  4547.852 t=      235 R=   5e+05
Depth=    1706 States= 1.24e+08 Transitions= 2.95e+08 Memory=  4579.800 t=      237 R=   5e+05
Depth=    1778 States= 1.25e+08 Transitions= 2.97e+08 Memory=  4612.702 t=      238 R=   5e+05
Depth=    1778 States= 1.26e+08 Transitions= 2.99e+08 Memory=  4645.127 t=      240 R=   5e+05
Depth=    1778 States= 1.27e+08 Transitions= 3.01e+08 Memory=  4676.598 t=      242 R=   5e+05
Depth=    1778 States= 1.28e+08 Transitions= 3.04e+08 Memory=  4709.023 t=      244 R=   5e+05
Depth=    1778 States= 1.29e+08 Transitions= 3.06e+08 Memory=  4740.971 t=      245 R=   5e+05
Depth=    1778 States=  1.3e+08 Transitions= 3.08e+08 Memory=  4773.873 t=      247 R=   5e+05
Depth=    1778 States= 1.31e+08 Transitions=  3.1e+08 Memory=  4804.391 t=      249 R=   5e+05
Depth=    1778 States= 1.32e+08 Transitions= 3.13e+08 Memory=  4834.908 t=      251 R=   5e+05
Depth=    1778 States= 1.33e+08 Transitions= 3.15e+08 Memory=  4865.426 t=      253 R=   5e+05
Depth=    1778 States= 1.34e+08 Transitions= 3.18e+08 Memory=  4895.943 t=      255 R=   5e+05
Depth=    1778 States= 1.35e+08 Transitions=  3.2e+08 Memory=  4926.461 t=      257 R=   5e+05
pan: resizing hashtable to -w28..  done
Depth=    1778 States= 1.36e+08 Transitions= 3.23e+08 Memory=  6974.461 t=      273 R=   5e+05
Depth=    1778 States= 1.37e+08 Transitions= 3.25e+08 Memory=  6974.461 t=      275 R=   5e+05
Depth=    1778 States= 1.38e+08 Transitions= 3.27e+08 Memory=  7002.118 t=      276 R=   5e+05
Depth=    1778 States= 1.39e+08 Transitions=  3.3e+08 Memory=  7035.019 t=      278 R=   5e+05
Depth=    1778 States=  1.4e+08 Transitions= 3.32e+08 Memory=  7070.305 t=      280 R=   5e+05
Depth=    1778 States= 1.41e+08 Transitions= 3.34e+08 Memory=  7105.114 t=      281 R=   5e+05
Depth=    1778 States= 1.42e+08 Transitions= 3.36e+08 Memory=  7140.400 t=      283 R=   5e+05
Depth=    1778 States= 1.43e+08 Transitions= 3.38e+08 Memory=  7171.872 t=      285 R=   5e+05
Depth=    1778 States= 1.44e+08 Transitions=  3.4e+08 Memory=  7204.773 t=      287 R=   5e+05
Depth=    1778 States= 1.45e+08 Transitions= 3.43e+08 Memory=  7235.291 t=      288 R=   5e+05
Depth=    1778 States= 1.46e+08 Transitions= 3.45e+08 Memory=  7267.239 t=      291 R=   5e+05
Depth=    1778 States= 1.47e+08 Transitions= 3.48e+08 Memory=  7299.664 t=      293 R=   5e+05
Depth=    1778 States= 1.48e+08 Transitions=  3.5e+08 Memory=  7333.996 t=      294 R=   5e+05
Depth=    1778 States= 1.49e+08 Transitions= 3.52e+08 Memory=  7367.375 t=      296 R=   5e+05
Depth=    1778 States=  1.5e+08 Transitions= 3.54e+08 Memory=  7399.800 t=      297 R=   5e+05
Depth=    1778 States= 1.51e+08 Transitions= 3.56e+08 Memory=  7432.225 t=      299 R=   5e+05
Depth=    1778 States= 1.52e+08 Transitions= 3.58e+08 Memory=  7465.603 t=      301 R=   5e+05
Depth=    1778 States= 1.53e+08 Transitions= 3.61e+08 Memory=  7499.459 t=      303 R=   5e+05
Depth=    1778 States= 1.54e+08 Transitions= 3.63e+08 Memory=  7532.361 t=      305 R=   5e+05
Depth=    1778 States= 1.55e+08 Transitions= 3.65e+08 Memory=  7564.309 t=      306 R=   5e+05
Depth=    1778 States= 1.56e+08 Transitions= 3.67e+08 Memory=  7596.734 t=      308 R=   5e+05
Depth=    1778 States= 1.57e+08 Transitions=  3.7e+08 Memory=  7629.635 t=      310 R=   5e+05
Depth=    1778 States= 1.58e+08 Transitions= 3.72e+08 Memory=  7660.153 t=      312 R=   5e+05
Depth=    1778 States= 1.59e+08 Transitions= 3.75e+08 Memory=  7690.670 t=      314 R=   5e+05
Depth=    1778 States=  1.6e+08 Transitions= 3.77e+08 Memory=  7721.188 t=      316 R=   5e+05
Depth=    1778 States= 1.61e+08 Transitions=  3.8e+08 Memory=  7751.706 t=      318 R=   5e+05
Depth=    1778 States= 1.62e+08 Transitions= 3.83e+08 Memory=  7784.607 t=      320 R=   5e+05
Depth=    1778 States= 1.63e+08 Transitions= 3.85e+08 Memory=  7816.079 t=      322 R=   5e+05
Depth=    1778 States= 1.64e+08 Transitions= 3.88e+08 Memory=  7847.550 t=      324 R=   5e+05
Depth=    1778 States= 1.65e+08 Transitions=  3.9e+08 Memory=  7879.021 t=      326 R=   5e+05
Depth=    1778 States= 1.66e+08 Transitions= 3.93e+08 Memory=  7910.492 t=      328 R=   5e+05
Depth=    1778 States= 1.67e+08 Transitions= 3.95e+08 Memory=  7943.394 t=      330 R=   5e+05
Depth=    1778 States= 1.68e+08 Transitions= 3.98e+08 Memory=  7973.912 t=      332 R=   5e+05
Depth=    1778 States= 1.69e+08 Transitions=    4e+08 Memory=  8005.860 t=      334 R=   5e+05
Depth=    1778 States=  1.7e+08 Transitions= 4.02e+08 Memory=  8037.331 t=      336 R=   5e+05
Depth=    1778 States= 1.71e+08 Transitions= 4.05e+08 Memory=  8069.279 t=      338 R=   5e+05
Depth=    1778 States= 1.72e+08 Transitions= 4.07e+08 Memory=  8100.750 t=      340 R=   5e+05
Depth=    1778 States= 1.73e+08 Transitions=  4.1e+08 Memory=  8132.222 t=      342 R=   5e+05
Depth=    1778 States= 1.74e+08 Transitions= 4.12e+08 Memory=  8164.647 t=      344 R=   5e+05
Depth=    1778 States= 1.75e+08 Transitions= 4.15e+08 Memory=  8195.641 t=      346 R=   5e+05
Depth=    1778 States= 1.76e+08 Transitions= 4.17e+08 Memory=  8227.112 t=      347 R=   5e+05

(Spin Version 6.5.2 -- 6 December 2019)
        + Partial Order Reduction
        + Compression

Full statespace search for:
        never claim             + (eventually_completed)
        assertion violations    + (if within scope of claim)
        acceptance   cycles     + (fairness disabled)
        invalid end states      - (disabled by never claim)

State-vector 476 byte, depth reached 1778, errors: 0
 88428148 states, stored (1.76856e+08 visited)
2.4212859e+08 states, matched
4.1898489e+08 transitions (= visited+matched)
 29048258 atomic steps
hash conflicts:  95250187 (resolved)

Stats on memory usage (in Megabytes):
43177.807       equivalent memory usage for states (stored*(State-vector + overhead))
 6206.695       actual memory usage for states (compression: 14.37%)
                state-vector as stored = 38 byte + 36 byte overhead
 2048.000       memory used for hash table (-w28)
    1.602       memory used for DFS stack (-m30000)
    1.564       memory lost to fragmentation
 8254.769       total actual memory usage


nr of templates: [ 0:globals 1:chans 2:procs ]
collapse counts: [ 0:1788301 2:2 3:2 4:17 5:24 6:13 7:59167 8:24 9:1 ]

pan: elapsed time 349 seconds
pan: rate 506737.04 states/second
```
