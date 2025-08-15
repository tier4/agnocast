// agnocast_callback_info.hpp | register_callback()
inline register_callback(topic_name_,callback_group_) {
	byte callback_info_id;
	d_step {
		callback_info_id = next_callback_info_id;
		next_callback_info_id++;
	}
	
	lock(id2_callback_info_mtx);
	d_step {
		id2_callback_info[callback_info_id].topic_name = topic_name_;
		id2_callback_info[callback_info_id].callback_group = callback_group_;
		id2_callback_info_keys!callback_info_id;
	}
	unlock(id2_callback_info_mtx);
	
	need_epoll_updates = true
}

// agnocast_subscription.hpp | class Subscription
proctype AgnocastSubscription(int topic_name;byte callback_group) {
	register_callback(topic_name,callback_group);
}

inline agnocast_timer_callback(topic_name_) {
	// agnocast_publisher.cpp | publish_core()
	byte loop_i;byte cb_info_i;byte len_id2_callback_info;
	d_step {
		len_id2_callback_info = len(id2_callback_info_keys);
		num_agnocast_published++;
		// The subscription callbacks registered after this line will not be triggered.
	}
	
	for (loop_i : 0 .. len_id2_callback_info) {
		d_step {id2_callback_info_keys?cb_info_i;id2_callback_info_keys!cb_info_i;}
		if
		:: id2_callback_info[cb_info_i].topic_name == topic_name_ && epoll_added[cb_info_i] -> // Abstraction: `id2_callback_info` is used instead of the return values of ioctl(2) for simplicity.
			entry_num[cb_info_i]++;// Abstraction: This corresponds to `ioctl(agnocast_fd,AGNOCAST_PUBLISH_MSG_CMD,&publish_msg_args)`.
			d_step{
				epoll!cb_info_i// mq_send() for publish
			}
		:: else
		fi
	}
	
	atomic {
		num_completed_cbs++
		printf("Agnocast | finish agnocast_timer_callback(): topic_name = %d\n",topic_name_);
	}
}

// agnocast_publisher.cpp | class Publisher
proctype AgnocastPublisher(int topic_name) {
	Callback timer_cb;
	d_step {
		timer_cb.id = BYTE_MAX;
		timer_cb.type = AGNOCAST_TIMER;
		timer_cb.topic_name = topic_name;
	}
	
	byte pub_i;
	for (pub_i : 0 .. NUM_PUBLISH - 1) {
		ready_executables!timer_cb;
		skip// Simulate period
	}
}

// agnocast_executor.cpp | AgnocastExecutor::receive_message()
inline receive_message(callback_info_id,callback_info) {
	byte ret_entry_num;
	d_step{
		ret_entry_num = entry_num[callback_info_id];
		entry_num[callback_info_id] = 0;
	}
	
	byte entry_i;
	for (entry_i : 0 .. ret_entry_num - 1) {
		Callback sub_cb;
		d_step {
			sub_cb.id = callback_info_id;
			sub_cb.type = SUBSCRIPTION;
			sub_cb.topic_name = callback_info.topic_name;
		}
		
		lock(ready_agnocast_executables_mutex_);
		ready_agnocast_executables!sub_cb;
		unlock(ready_agnocast_executables_mutex_);
	}
}

// agnocast_executor.cpp | AgnocastExecutor::wait_and_handle_epoll_event()
inline wait_and_handle_epoll_event() {
	byte callback_info_id;
	
	skip;// Simulate blocking with timeout
	if
	:: d_step {epoll?[callback_info_id] -> epoll?callback_info_id;}
	:: else -> goto finish_wait_and_handle_epoll_event// timeout
	fi
	
	CallbackInfo callback_info;
	lock(id2_callback_info_mtx);
	d_step {
		callback_info.callback_group = id2_callback_info[callback_info_id].callback_group;
		callback_info.topic_name = id2_callback_info[callback_info_id].topic_name;
		callback_info.need_epoll_update = id2_callback_info[callback_info_id].need_epoll_update;
	}
	unlock(id2_callback_info_mtx);
	
	receive_message(callback_info_id,callback_info);
	
	finish_wait_and_handle_epoll_event:
}

inline get_next_ready_agnocast_executable(ret_cb,ret_result) {
	lock(ready_agnocast_executables_mutex_);
	// TODO: add callback group mechanism
	if
	:: d_step {ready_agnocast_executables?[ret_cb] -> ready_agnocast_executables?ret_cb;} ret_result = true
	:: else -> ret_result = false
	fi
	unlock(ready_agnocast_executables_mutex_);
}

inline get_next_agnocast_executable(ret_cb,ret_result) {
	get_next_ready_agnocast_executable(ret_cb,ret_result);
	if
	:: ret_result -> goto finish_get_next_agnocast_executable
	:: else
	fi
	
	wait_and_handle_epoll_event();
	
	// Try again
	get_next_ready_agnocast_executable(ret_cb,ret_result);
	
	finish_get_next_agnocast_executable:
}

inline execute_agnocast_executable(cb) {
	if
	:: d_step{cb.type == SUBSCRIPTION -> printf("Agnocast | subscription_callback(): callback_info_id = %d\n",cb.id);} subscription_callback(cb.id)
	:: else -> assert(false)
	fi
}

// agnocast_executor.cpp | AgnocastExecutor::prepare_epoll()
inline prepare_epoll() {
	byte loop_i;byte cb_info_i;
	
	lock(id2_callback_info_mtx);
	for (loop_i : 0 .. len(id2_callback_info_keys) - 1) {
		d_step {id2_callback_info_keys?cb_info_i;id2_callback_info_keys!cb_info_i;}
		
		if
		:: id2_callback_info[cb_info_i].need_epoll_update == false -> goto continue_loop
		:: else
		fi
		
		// TODO(CIE): validate_callback_group();
		
		d_step{
			epoll_added[cb_info_i] = true;
			expected_num_completed_cbs = expected_num_completed_cbs + NUM_PUBLISH - num_agnocast_published;
			printf("Agnocast | agnocast subscription is registered: callback_info_id = %d,topic_name = %d\n",cb_info_i,id2_callback_info[cb_info_i].topic_name);
		}
		
		// Abstraction: The transient local is not modeled.
		
		id2_callback_info[cb_info_i].need_epoll_update = false;
		
		continue_loop:
	}
	
	bool all_updated = true;
	for (loop_i : 0 .. len(id2_callback_info_keys) - 1) {
		d_step {id2_callback_info_keys?cb_info_i;id2_callback_info_keys!cb_info_i;}
		if
		:: id2_callback_info[cb_info_i].need_epoll_update -> all_updated = false;break
		:: else
		fi
	}
	
	if
	:: all_updated -> need_epoll_updates = false// `all_updated` is always true for now.
	:: else
	fi
	
	unlock(id2_callback_info_mtx);
}
