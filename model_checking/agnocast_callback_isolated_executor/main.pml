#define NUM_SUBSCRIPTIONS 3
#define NUM_PUBLISH 10
#define NUM_EXECUTORS 1

#include "utility.pml"
#include "for_verification.pml"
#include "data_structure.pml"

// === For ROS 2 ===

// NOTE: This is used for all RosSubscriptions.
inline subscription_callback(cb_id) {
	d_step {
		printf("subscription_callback(): cb_id = %d\n",cb_id);
		num_completed_cbs++
	}
}

// NOTE: `inline` is used instead of `proctype` to execute atomically.
inline RosSubscription(topic_name_) {
	d_step {
		registered_subscriptions[cur_ros_sub_cb_id].id = cur_ros_sub_cb_id;
		registered_subscriptions[cur_ros_sub_cb_id].type = SUBSCRIPTION;
		registered_subscriptions[cur_ros_sub_cb_id].topic_name = topic_name_;
		cur_ros_sub_cb_id++
	}
}

inline ros_timer_callback(topic_name_) {
	printf("ros_timer_callback(): topic_name_ = %d\n",topic_name_);
	byte sub_i;
	byte sub_num = cur_ros_sub_cb_id;// NOTE: The subscriber registered after the line will not receive the message.
	for (sub_i : 0 .. sub_num - 1) {
		if
		:: registered_subscriptions[sub_i].topic_name == topic_name_ -> ready_executables!registered_subscriptions[sub_i]// This corresponds to the publish() and triggers subscription callbacks.
		:: else
		fi
	}
	
	num_completed_cbs++
}

proctype RosPublisher(int topic_name) {
	RosCallback timer_cb;
	d_step {
		timer_cb.id = BYTE_MAX;
		timer_cb.type = TIMER;
		timer_cb.topic_name = topic_name;
	}
	
	byte pub_i;
	for (pub_i : 0 .. NUM_PUBLISH - 1) {
		ready_executables!timer_cb;
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
	:: cb.type == TIMER -> ros_timer_callback(cb.topic_name)
	:: cb.type == SUBSCRIPTION -> subscription_callback(cb.id)
	fi
}

proctype SingleThreadedAgnocastExecutor(byte executor_id) provided (!wait_for_weak_fairness[executor_id]) {
	RosCallback executable;bool ret_result;
	
	start:
	
    // For weak fairness
	atomic {
		consecutive_empty_executor_loop[executor_id]++;
		if
		:: consecutive_empty_executor_loop[executor_id] == MAX_CONSECUTIVE_EMPTY_EXECUTOR_LOOP -> 
			resume_requests!executor_id;
			wait_for_weak_fairness[executor_id] = true;
		:: else
		fi
	}

    get_next_executable(executable,ret_result);
    if 
    :: atomic {ret_result -> consecutive_empty_executor_loop[executor_id] = 0;} execute_any_executable(executable)
    :: else
    fi

    if
    :: num_completed_cbs < MAX_COMPLETED_CBS -> goto start
    :: else -> printf("All callbacks completed: %d\n",num_completed_cbs)
    fi

    end:
    }

init {
    byte init_i;
    int ros_topic_name = 'R';

    for (init_i : 0 .. NUM_SUBSCRIPTIONS - 1) {
        RosSubscription(ros_topic_name);
    }

    run RosPublisher(ros_topic_name);

    for (init_i : 0 .. NUM_EXECUTORS - 1) {
        run SingleThreadedAgnocastExecutor(init_i)
    }
}

#include "ltl.pml"
