proctype RosSubscription(int topic_name) {
	d_step {
		registered_ros_subscriptions[cur_ros_sub_cb_id].id = cur_ros_sub_cb_id;
		registered_ros_subscriptions[cur_ros_sub_cb_id].type = SUBSCRIPTION;
		registered_ros_subscriptions[cur_ros_sub_cb_id].topic_name = topic_name;
		cur_ros_sub_cb_id++;
		expected_num_completed_cbs = expected_num_completed_cbs + NUM_PUBLISH - num_ros_published;
		printf("ROS | ros subscription is registered: cb_id = %d,topic_name = %d\n",cur_ros_sub_cb_id - 1,topic_name);
	}
}

inline ros_timer_callback(topic_name_) {
	byte sub_i;byte sub_num;
	d_step{
		sub_num = cur_ros_sub_cb_id;
		num_ros_published++;
		// The subscription callbacks registered after this line will not be triggered.
	}
	
	for (sub_i : 0 .. sub_num - 1) {
		if
		:: registered_ros_subscriptions[sub_i].topic_name == topic_name_ -> 
			d_step {
				ready_executables!registered_ros_subscriptions[sub_i]// Abstraction: This corresponds to the publish() and triggers subscription callbacks.
			}
		:: else
		fi
	}
	
	atomic {
		num_completed_cbs++;
		printf("ROS | finish ros_timer_callback(): topic_name = %d\n",topic_name_);
	}
}

proctype RosPublisher(int topic_name) {
	Callback timer_cb;
	d_step {
		timer_cb.id = BYTE_MAX;
		timer_cb.type = ROS_TIMER;
		timer_cb.topic_name = topic_name;
	}
	
	byte pub_i;
	for (pub_i : 0 .. NUM_PUBLISH - 1) {
		lock(mutex_);
		ready_executables!timer_cb;
		unlock(mutex_);
		skip// Simulate period
	}
}

// https://github.com/ros2/rclcpp/blob/76cdd45da31c7da87a9c2cbefff8e7437b47dae9/rclcpp/src/rclcpp/executor.cpp#L829
inline get_next_executable(ret_cb,ret_result) {
	lock(mutex_);
	if
	:: d_step {ready_executables?[ret_cb] -> ready_executables?ret_cb;} ret_result = true// Abstraction: simple FIFO
	:: else -> ret_result = false
	fi
	unlock(mutex_);
}

// https://github.com/ros2/rclcpp/blob/76cdd45da31c7da87a9c2cbefff8e7437b47dae9/rclcpp/src/rclcpp/executor.cpp#L509
inline execute_any_executable(cb) {
	if
	:: d_step{cb.type == ROS_TIMER -> printf("ROS | start ros_timer_callback(): topic_name = %d\n",cb.topic_name);} ros_timer_callback(cb.topic_name)
	:: d_step{cb.type == AGNOCAST_TIMER -> printf("Agnocast | start agnocast_timer_callback(): topic_name = %d\n",cb.topic_name);} agnocast_timer_callback(cb.topic_name)
	:: d_step{cb.type == SUBSCRIPTION -> printf("ROS | subscription_callback(): cb_id = %d\n",cb.id);} subscription_callback(cb.id)
	fi
}
