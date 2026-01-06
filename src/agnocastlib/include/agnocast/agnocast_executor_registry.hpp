#pragma once

namespace agnocast
{

void register_executor_notify_fd(int notify_fd);
void unregister_executor_notify_fd(int notify_fd);
void notify_executors();

}  // namespace agnocast
