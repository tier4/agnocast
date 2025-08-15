// Parameters
#define NUM_SUBSCRIPTIONS 2
#define NUM_PUBLISH 3
#define NUM_EXECUTORS 1

#include "utility.pml"
#include "for_verification.pml"
#include "data_structure.pml"
#include "ros_pub_sub.pml"
#include "agnocast_pub_sub.pml"

// This is used for both ROS and Agnocast.
inline subscription_callback(cb_id) {
	num_completed_cbs++
}

// agnocast_single_threaded_executor.hpp | class SingleThreadedAgnocastExecutor
proctype SingleThreadedAgnocastExecutor(byte executor_id) provided (!wait_for_weak_fairness[executor_id]) {
	Callback executable;bool ret_result;

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
	
	if
	:: need_epoll_updates -> prepare_epoll()
	:: else
	fi
	
	
	get_next_agnocast_executable(executable,ret_result);
	if
	:: atomic {ret_result -> consecutive_empty_executor_loop[executor_id] = 0;} execute_agnocast_executable(executable)
	:: else
	fi
	
	get_next_executable(executable,ret_result);
	if 
	:: atomic {ret_result -> consecutive_empty_executor_loop[executor_id] = 0;} execute_any_executable(executable)
	:: else
	fi
	
	if
	:: num_completed_cbs < expected_num_completed_cbs -> goto start
	:: else -> printf("All callbacks completed: %d\n",num_completed_cbs)
	fi
	
	end:
}

init {
	byte init_i;
	int agnocast_topic_name = 'A';
	int ros_topic_name = 'R';
	
	for (init_i : 0 .. NUM_SUBSCRIPTIONS - 1) {
		run AgnocastSubscription(agnocast_topic_name,init_i);// NOTE: Each subscription has a unique callback group for now.
	}
	
	run AgnocastPublisher(agnocast_topic_name);
	
	for (init_i : 0 .. NUM_SUBSCRIPTIONS - 1) {
		run RosSubscription(ros_topic_name);
	}
	
	run RosPublisher(ros_topic_name);
	
	for (init_i : 0 .. NUM_EXECUTORS - 1) {
		run SingleThreadedAgnocastExecutor(init_i)
	}
}

#include "ltl.pml"
