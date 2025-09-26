#define BYTE_MAX 255

Mutex mutex_[NUM_SINGLE_THREADED_EXECUTORS]// rclcpp::Executor mutex_

mtype:CallbackType = {ROS_TIMER,AGNOCAST_TIMER,SUBSCRIPTION}// The ROS 2 subscription and agnocast subscription are not distinguished.
typedef Callback {
	byte id// This is only used for debugging for now.
	byte callback_group
	mtype:CallbackType type
}

// === For ROS 2 ===
byte cur_ros_sub_cb_id = 0
// Simplification: ROS 2 publish/subscribe mechanism is simply modeled as follows, because it's not so important for the verification of Agnocast.
chan ready_executables[NUM_SINGLE_THREADED_EXECUTORS] = [MAX_COMPLETED_CBS] of {Callback}
Callback registered_ros_subscriptions[NUM_SUBSCRIPTIONS]

// === For Agnocast ===
// agnocast_callback_info.hpp | struct CallbackInfo
typedef CallbackInfo {
	short callback_group = -1
	bool need_epoll_update = true
	bool initialized = false// This is added for promela implementation.
}

byte next_callback_info_id = 0// agnocast_callback_info.hpp | next_callback_info_id

Mutex id2_callback_info_mtx// agnocast_callback_info.hpp | id2_callback_info_mtx
CallbackInfo id2_callback_info[NUM_SUBSCRIPTIONS]// agnocast_callback_info.hpp | id2_callback_info. index: callback_info_id

bool need_epoll_updates = false// agnocast_callback_info.hpp | need_epoll_updates

// Mutex ready_agnocast_executables_mutex_[NUM_SINGLE_THREADED_EXECUTORS]// agnocast_executor.hpp | AgnocastExecutor ready_agnocast_executables_mutex_
chan ready_agnocast_executables[NUM_SINGLE_THREADED_EXECUTORS] = [MAX_COMPLETED_CBS] of {Callback}// agnocast_executor.hpp | AgnocastExecutor ready_agnocast_executables

byte entry_num[NUM_SUBSCRIPTIONS] = 0// Simplification: This corresponds to `ioctl_receive_msg_args receive_args.ret_entry_num`. in AgnocastExecutor::receive_message(). index: callback_info_id. 
bool epoll_added[NUM_SUBSCRIPTIONS] = false// This possesses whether the corresponding callback_info.mqdes is added to epoll or not. index: callback_info_id
chan epoll[NUM_SINGLE_THREADED_EXECUTORS] = [MAX_COMPLETED_CBS] of {byte}// Simplification: This is directly used for publish / subscribe, and the corresponding mqueue is not modeled. msg: callback_info_id. 

bool is_dedicated_to_one_callback_group[NUM_SINGLE_THREADED_EXECUTORS] = false// agnocast_single_threaded_executor.hpp | AgnocastSingleThreadedExecutor is_dedicated_to_one_callback_group_. index: executor_id
byte dedicated_callback_group[NUM_SINGLE_THREADED_EXECUTORS]// agnocast_single_threaded_executor.hpp | AgnocastSingleThreadedExecutor dedicated_callback_group_. index: executor_id
bool spin_called[NUM_SINGLE_THREADED_EXECUTORS] = false// index: executor_id
byte node_callback_groups[NUM_CALLBACK_GROUPS]// Simplification: node->for_each_callback_group()
