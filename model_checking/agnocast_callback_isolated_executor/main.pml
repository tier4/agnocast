// Parameters
#define NUM_SUBSCRIPTIONS 2
#define NUM_PUBLISH 2
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

	// For weak fairness
	d_step{
		if
		:: !ret_result -> consecutive_empty_executor_loop[executor_id]++
		:: else -> consecutive_empty_executor_loop[executor_id] = 0
		fi

		if
		:: consecutive_empty_executor_loop[executor_id] == MAX_CONSECUTIVE_EMPTY_EXECUTOR_LOOP -> 
			resume_requests!executor_id;
			wait_for_weak_fairness[executor_id] = true;
		:: else
		fi
	}
	
	if
	:: num_completed_cbs < expected_num_completed_cbs -> goto start
	:: else -> printf("All callbacks completed: %d\n",num_completed_cbs)
	fi
	
	end:
}

init {
	byte init_i;
	
	for (init_i : 0 .. NUM_SUBSCRIPTIONS - 1) {
		run AgnocastSubscription(init_i);// NOTE: Each subscription has a unique callback group for now.
	}

	run AgnocastPublisher();
	
	for (init_i : 0 .. NUM_SUBSCRIPTIONS - 1) {
		run RosSubscription();
	}
	
	run RosPublisher();
	
	for (init_i : 0 .. NUM_EXECUTORS - 1) {
		run SingleThreadedAgnocastExecutor(init_i)
	}
}

#include "ltl.pml"
