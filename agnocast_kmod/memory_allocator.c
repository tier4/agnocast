#include "memory_allocator.h"

#include <linux/module.h>

MODULE_LICENSE("Dual BSD/GPL");

#define MEMPOOL_128MB_NUM 1000
#define MEMPOOL_1GB_NUM 100
#define MEMPOOL_8GB_NUM 10
#define MEMPOOL_TOTAL_NUM (MEMPOOL_128MB_NUM + MEMPOOL_1GB_NUM + MEMPOOL_8GB_NUM)

const uint64_t MEMPOOL_128MB_SIZE = 134217728;  // 128 * 1024 * 1024
const uint64_t MEMPOOL_1GB_SIZE = 1073741824;   // 1 * 1024 * 1024 * 1024
const uint64_t MEMPOOL_8GB_SIZE = 8589934592;   // 8 * 1024 * 1024 * 1024

static struct mempool_entry mempool_entries[MEMPOOL_TOTAL_NUM];

void agnocast_init_memory_allocator(void)
{
  // TODO(Ryuta Kambe): we assume that the address from 0x40000000000 to 0x8B000000000 is available
  uint64_t addr = 0x40000000000;

  for (int i = 0; i < MEMPOOL_128MB_NUM; i++) {
    mempool_entries[i].addr = addr;
    mempool_entries[i].pool_size = MEMPOOL_128MB_SIZE;
    mempool_entries[i].mapped_num = 0;
    for (int j = 0; j < MAX_MAP_NUM; j++) {
      mempool_entries[i].mapped_pids[j] = 0;
    }
    addr += MEMPOOL_128MB_SIZE;
  }

  for (int i = 0; i < MEMPOOL_1GB_NUM; i++) {
    mempool_entries[i + MEMPOOL_128MB_NUM].addr = addr;
    mempool_entries[i + MEMPOOL_128MB_NUM].pool_size = MEMPOOL_1GB_SIZE;
    mempool_entries[i + MEMPOOL_128MB_NUM].mapped_num = 0;
    for (int j = 0; j < MAX_MAP_NUM; j++) {
      mempool_entries[i + MEMPOOL_128MB_NUM].mapped_pids[j] = 0;
    }
    addr += MEMPOOL_1GB_SIZE;
  }

  for (int i = 0; i < MEMPOOL_8GB_NUM; i++) {
    mempool_entries[i + MEMPOOL_128MB_NUM + MEMPOOL_1GB_NUM].addr = addr;
    mempool_entries[i + MEMPOOL_128MB_NUM + MEMPOOL_1GB_NUM].pool_size = MEMPOOL_8GB_SIZE;
    mempool_entries[i + MEMPOOL_128MB_NUM + MEMPOOL_1GB_NUM].mapped_num = 0;
    for (int j = 0; j < MAX_MAP_NUM; j++) {
      mempool_entries[i + MEMPOOL_128MB_NUM + MEMPOOL_1GB_NUM].mapped_pids[j] = 0;
    }
    addr += MEMPOOL_8GB_SIZE;
  }
}

struct mempool_entry * agnocast_assign_memory(const pid_t pid, const uint64_t size)
{
  if (size <= MEMPOOL_128MB_SIZE) {
    for (int i = 0; i < MEMPOOL_128MB_NUM; i++) {
      if (mempool_entries[i].mapped_num == 0) {
        mempool_entries[i].mapped_num = 1;
        mempool_entries[i].mapped_pids[0] = pid;
        return &mempool_entries[i];
      }
    }
  }

  if (size <= MEMPOOL_1GB_SIZE) {
    for (int i = MEMPOOL_128MB_NUM; i < MEMPOOL_128MB_NUM + MEMPOOL_1GB_NUM; i++) {
      if (mempool_entries[i].mapped_num == 0) {
        mempool_entries[i].mapped_num = 1;
        mempool_entries[i].mapped_pids[0] = pid;
        return &mempool_entries[i];
      }
    }
  }

  if (size <= MEMPOOL_8GB_SIZE) {
    for (int i = MEMPOOL_128MB_NUM + MEMPOOL_1GB_NUM;
         i < MEMPOOL_128MB_NUM + MEMPOOL_1GB_NUM + MEMPOOL_8GB_NUM; i++) {
      if (mempool_entries[i].mapped_num == 0) {
        mempool_entries[i].mapped_num = 1;
        mempool_entries[i].mapped_pids[0] = pid;
        return &mempool_entries[i];
      }
    }
  }

  return NULL;
}

int agnocast_reference_memory(struct mempool_entry * mempool_entry, const pid_t pid)
{
  if (mempool_entry->mapped_num >= MAX_MAP_NUM) {
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

void agnocast_free_memory(const pid_t pid)
{
  for (int i = 0; i < MEMPOOL_TOTAL_NUM; i++) {
    for (int j = 0; j < mempool_entries[i].mapped_num; j++) {
      if (mempool_entries[i].mapped_pids[j] == pid) {
        for (int k = j; k < MAX_MAP_NUM - 1; k++) {
          mempool_entries[i].mapped_pids[k] = mempool_entries[i].mapped_pids[k + 1];
        }
        mempool_entries[i].mapped_pids[MAX_MAP_NUM - 1] = 0;
        mempool_entries[i].mapped_num--;
        break;
      }
    }
  }
}

#ifdef KUNIT_BUILD
void agnocast_exit_memory_allocator(void)
{
  for (int i = 0; i < MEMPOOL_TOTAL_NUM; i++) {
    mempool_entries[i].mapped_num = 0;
    for (int j = 0; j < MAX_MAP_NUM; j++) {
      mempool_entries[i].mapped_pids[j] = 0;
    }
  }
}
#endif