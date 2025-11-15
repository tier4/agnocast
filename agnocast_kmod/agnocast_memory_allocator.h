#pragma once

#include <linux/types.h>

// Maximum number of processes that can be mapped to a memory pool
#define MAX_PROCESS_NUM_PER_MEMPOOL 32

#define MEMPOOL_DEFAULT_SIZE 8589934592ULL  // 8GB
#define MEMPOOL_DEFAULT_NUM 1000

struct mempool_entry
{
  uint64_t addr;
  uint64_t pool_size;
  uint32_t mapped_num;
  pid_t mapped_pids[MAX_PROCESS_NUM_PER_MEMPOOL];
};

void init_memory_allocator(void);
struct mempool_entry * assign_memory(const pid_t pid, const uint64_t size);
int reference_memory(struct mempool_entry * mempool_entry, const pid_t pid);
void free_memory(const pid_t pid);

#ifdef KUNIT_BUILD
void exit_memory_allocator(void);
#endif
