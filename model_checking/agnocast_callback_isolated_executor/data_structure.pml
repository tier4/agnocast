#define BYTE_MAX 255

Mutex mutex_// rclcpp::Executor mutex_

// === For ROS 2 ===
mtype:CallbackType = {TIMER,SUBSCRIPTION}
typedef RosCallback {
	byte id// NOTE: This is only used for debugging for now.
	mtype:CallbackType type
	int topic_name// NOTE: This is redundant for now.
}
chan ready_executables = [MAX_COMPLETED_CBS] of {RosCallback}
byte cur_ros_sub_cb_id = 0
RosCallback registered_subscriptions[NUM_SUBSCRIPTIONS]
