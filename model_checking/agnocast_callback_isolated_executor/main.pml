// Parameters
#define NUM_SUBSCRIPTIONS 2
#define NUM_PUBLISH 2
#define NUM_CALLBACK_GROUPS (2 + NUM_SUBSCRIPTIONS * 2)// Agnocast publisher, ROS publisher, and each subscription has its own callback group.
#define NUM_SINGLE_THREADED_EXECUTORS NUM_CALLBACK_GROUPS

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
proctype SingleThreadedAgnocastExecutor(byte executor_id) provided (spin_called[executor_id] && !wait_for_weak_fairness[executor_id]) {
	printf("Executor %d started\n",executor_id);
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

// agnocast_single_threaded_executor.cpp | SingleThreadedAgnocastExecutor::dedicate_to_callback_group()
inline dedicate_to_callback_group(executor_id,group) {
	assert(group != -1);

	is_dedicated_to_one_callback_group[executor_id] = true;
	dedicated_callback_group[executor_id] = group;
}

// agnocast_callback_isolated_executor.hpp | class CallbackIsolatedAgnocastExecutor
proctype CallbackIsolatedAgnocastExecutor() {
	byte executor_id;

	for (executor_id : 0 .. NUM_CALLBACK_GROUPS - 1) {
		run SingleThreadedAgnocastExecutor(executor_id);
		dedicate_to_callback_group(executor_id,node_callback_groups[executor_id]);
		spin_called[executor_id] = true;
	}
}

init {
	byte init_i,callback_group = 0;
	
	for (init_i : 0 .. NUM_SUBSCRIPTIONS - 1) {
		run AgnocastSubscription(callback_group);
		node_callback_groups[callback_group] = callback_group;
		callback_group++;
	}

	run AgnocastPublisher(callback_group);
	node_callback_groups[callback_group] = callback_group;
	callback_group++;
	
	for (init_i : 0 .. NUM_SUBSCRIPTIONS - 1) {
		run RosSubscription(callback_group);
		node_callback_groups[callback_group] = callback_group;
		callback_group++;
	}
	
	run RosPublisher(callback_group);
	node_callback_groups[callback_group] = callback_group;
	
	run CallbackIsolatedAgnocastExecutor();
}

#include "ltl.pml"
