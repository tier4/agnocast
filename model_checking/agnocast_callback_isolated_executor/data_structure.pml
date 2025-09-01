#define BYTE_MAX 255

Mutex mutex_// rclcpp::Executor mutex_

mtype:CallbackType = {ROS_TIMER,AGNOCAST_TIMER,SUBSCRIPTION}
typedef Callback {
	byte id// This is only used for debugging for now.
	mtype:CallbackType type
	int topic_name// This is redundant for now.
}

// === For ROS 2 ===
byte cur_ros_sub_cb_id = 0
// Abstraction: ROS 2 publish/subscribe mechanism is simply modeled as follows, because it's not so important for the verification of Agnocast.
chan ready_executables = [MAX_COMPLETED_CBS] of {Callback}
Callback registered_ros_subscriptions[NUM_SUBSCRIPTIONS]

// === For Agnocast ===
// agnocast_callback_info.hpp | struct CallbackInfo
typedef CallbackInfo {
	byte callback_group
	int topic_name = - 1
	bool need_epoll_update = true
}

byte next_callback_info_id = 0// agnocast_callback_info.hpp | next_callback_info_id

Mutex id2_callback_info_mtx// agnocast_callback_info.hpp | mutex for id2_callback_info
CallbackInfo id2_callback_info[NUM_SUBSCRIPTIONS]// agnocast_callback_info.hpp | id2_callback_info. index: callback_info_id
chan id2_callback_info_keys = [NUM_SUBSCRIPTIONS] of {byte}// The channel for preserving the registered callback_info_ids and the number of them. msg: callback_info_id.

bool need_epoll_updates = false// agnocast_callback_info.hpp | need_epoll_updates

Mutex ready_agnocast_executables_mutex_// agnocast_executor.hpp | AgnocastExecutor ready_agnocast_executables_mutex_
chan ready_agnocast_executables = [MAX_COMPLETED_CBS] of {Callback}// agnocast_executor.hpp | AgnocastExecutor ready_agnocast_executables

byte entry_num[NUM_SUBSCRIPTIONS] = 0// Abstraction: This corresponds to `ioctl_receive_msg_args receive_args.ret_entry_num`. in AgnocastExecutor::receive_message(). index: callback_info_id. 
bool epoll_added[NUM_SUBSCRIPTIONS] = false// This possesses whether the corresponding callback_info.mqdes is added to epoll or not. index: callback_info_id
chan epoll = [MAX_COMPLETED_CBS] of {byte}// Abstraction: This is directly used for publish / subscribe, and the corresponding mqueue is not modeled. msg: callback_info_id. 
