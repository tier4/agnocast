typedef Mutex {
	bool is_locked = false
}

inline lock(mutex) {
	atomic {!mutex.is_locked -> mutex.is_locked = true}
}

inline unlock(mutex) {
	mutex.is_locked = false
}
