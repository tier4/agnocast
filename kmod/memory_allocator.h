#pragma once

#include <linux/types.h>

void agnocast_init_memory_allocator(void);
uint64_t agnocast_assign_memory(const pid_t pid, const uint64_t size);
int agnocast_free_memory(const pid_t pid);
void agnocast_exit_memory_allocator(void);
