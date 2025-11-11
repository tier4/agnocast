#include "agnocast_memory_allocator.h"

#include <linux/module.h>

MODULE_LICENSE("Dual BSD/GPL");

static struct mempool_entry mempool_entries[MEMPOOL_TOTAL_NUM];

void init_memory_allocator(void)
{
  uint64_t addr = 0x40000000000;

  for (int i = 0; i < MEMPOOL_DEFAULT_NUM; i++) {
    mempool_entries[i].addr = addr;
    mempool_entries[i].pool_size = MEMPOOL_DEFAULT_SIZE;
    mempool_entries[i].mapped_num = 0;
    for (int j = 0; j < MAX_PROCESS_NUM_PER_MEMPOOL; j++) {
      mempool_entries[i].mapped_pids[j] = -1;
    }
    addr += MEMPOOL_DEFAULT_SIZE;
  }

  for (int i = 0; i < MEMPOOL_DOUBLE_NUM; i++) {
    mempool_entries[i + MEMPOOL_DEFAULT_NUM].addr = addr;
    mempool_entries[i + MEMPOOL_DEFAULT_NUM].pool_size = MEMPOOL_DOUBLE_SIZE;
    mempool_entries[i + MEMPOOL_DEFAULT_NUM].mapped_num = 0;
    for (int j = 0; j < MAX_PROCESS_NUM_PER_MEMPOOL; j++) {
      mempool_entries[i + MEMPOOL_DEFAULT_NUM].mapped_pids[j] = -1;
    }
    addr += MEMPOOL_DOUBLE_SIZE;
  }
}

struct mempool_entry * assign_memory(const pid_t pid, const uint64_t size)
{
  if (size <= MEMPOOL_DEFAULT_SIZE) {
    for (int i = 0; i < MEMPOOL_DEFAULT_NUM; i++) {
      if (mempool_entries[i].mapped_num == 0) {
        mempool_entries[i].mapped_num = 1;
        mempool_entries[i].mapped_pids[0] = pid;
        return &mempool_entries[i];
      }
    }
  }

  if (size <= MEMPOOL_DOUBLE_SIZE) {
    for (int i = MEMPOOL_DEFAULT_NUM; i < MEMPOOL_DEFAULT_NUM + MEMPOOL_DOUBLE_NUM; i++) {
      if (mempool_entries[i].mapped_num == 0) {
        mempool_entries[i].mapped_num = 1;
        mempool_entries[i].mapped_pids[0] = pid;
        return &mempool_entries[i];
      }
    }
  }

  return NULL;
}

int reference_memory(struct mempool_entry * mempool_entry, const pid_t pid)
{
  if (mempool_entry->mapped_num == MAX_PROCESS_NUM_PER_MEMPOOL) {
    return -ENOBUFS;
  }

  for (int i = 0; i < mempool_entry->mapped_num; i++) {
    if (mempool_entry->mapped_pids[i] == pid) {
      return -EEXIST;
    }
  }

  mempool_entry->mapped_pids[mempool_entry->mapped_num] = pid;
  mempool_entry->mapped_num++;

  return 0;
}

void free_memory(const pid_t pid)
{
  for (int i = 0; i < MEMPOOL_TOTAL_NUM; i++) {
    for (int j = 0; j < mempool_entries[i].mapped_num; j++) {
      if (mempool_entries[i].mapped_pids[j] == pid) {
        for (int k = j; k < MAX_PROCESS_NUM_PER_MEMPOOL - 1; k++) {
          mempool_entries[i].mapped_pids[k] = mempool_entries[i].mapped_pids[k + 1];
        }
        mempool_entries[i].mapped_pids[MAX_PROCESS_NUM_PER_MEMPOOL - 1] = -1;
        mempool_entries[i].mapped_num--;
        break;
      }
    }
  }
}

#ifdef KUNIT_BUILD
void exit_memory_allocator(void)
{
  for (int i = 0; i < MEMPOOL_TOTAL_NUM; i++) {
    mempool_entries[i].mapped_num = 0;
    for (int j = 0; j < MAX_PROCESS_NUM_PER_MEMPOOL; j++) {
      mempool_entries[i].mapped_pids[j] = -1;
    }
  }
}
#endif
