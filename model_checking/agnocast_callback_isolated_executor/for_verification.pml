byte num_completed_cbs = 0
byte expected_num_completed_cbs = NUM_PUBLISH * 2// The expected number of completed subscription callbacks will be added later.

#define MAX_COMPLETED_CBS ((NUM_PUBLISH * (1 + NUM_SUBSCRIPTIONS)) * 2)

// === For weak fairness ===
#define MAX_CONSECUTIVE_EMPTY_EXECUTOR_LOOP 5
byte consecutive_empty_executor_loop[NUM_EXECUTORS] = 0
bool wait_for_weak_fairness[NUM_EXECUTORS] = false
chan resume_requests = [NUM_EXECUTORS] of { byte }// executor_id that requested to resume execution.

active proctype timeout_handler() {
	xr resume_requests;
	byte executor_id;
	
	do
	:: timeout -> 
		if
		:: num_completed_cbs == expected_num_completed_cbs -> break
		:: atomic{else -> 
				assert(nempty(resume_requests));
				resume_requests?executor_id;
				assert(wait_for_weak_fairness[executor_id]);
				wait_for_weak_fairness[executor_id] = false;
				assert(consecutive_empty_executor_loop[executor_id] == MAX_CONSECUTIVE_EMPTY_EXECUTOR_LOOP);
				consecutive_empty_executor_loop[executor_id] = 0;
			}
		fi
	od
}
