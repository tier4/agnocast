#include "memory_allocator.h"

#include <linux/module.h>

MODULE_LICENSE("Dual BSD/GPL");

#define MEMPOOL_128MB_NUM 1000
#define MEMPOOL_1GB_NUM 100
#define MEMPOOL_8GB_NUM 10
#define MEMPOOL_TOTAL_NUM (MEMPOOL_128MB_NUM + MEMPOOL_1GB_NUM + MEMPOOL_8GB_NUM)

static uint64_t mempool_size_128mb = 134217728;  // 128 * 1024 * 1024
static uint64_t mempool_size_1gb = 1073741824;   // 1 * 1024 * 1024 * 1024
static uint64_t mempool_size_8gb = 8589934592;   // 8 * 1024 * 1024 * 1024

struct mempool_entry
{
  pid_t pid;
  uint64_t addr;
  uint64_t size;
  uint64_t ref_count;
};

static struct mempool_entry mempool_entries[MEMPOOL_TOTAL_NUM];

void agnocast_init_memory_allocator(void)
{
  // TODO(Ryuta Kambe): we assume that the address from 0x40000000000 to 0x8B000000000 is available
  uint64_t addr = 0x40000000000;

  for (int i = 0; i < MEMPOOL_128MB_NUM; i++) {
    mempool_entries[i].pid = 0;
    mempool_entries[i].addr = addr;
    mempool_entries[i].size = mempool_size_128mb;
    mempool_entries[i].ref_count = 0;
    addr += mempool_size_128mb;
  }

  for (int i = 0; i < MEMPOOL_1GB_NUM; i++) {
    mempool_entries[i + MEMPOOL_128MB_NUM].pid = 0;
    mempool_entries[i + MEMPOOL_128MB_NUM].addr = addr;
    mempool_entries[i + MEMPOOL_128MB_NUM].size = mempool_size_1gb;
    mempool_entries[i + MEMPOOL_128MB_NUM].ref_count = 0;
    addr += mempool_size_1gb;
  }

  for (int i = 0; i < MEMPOOL_8GB_NUM; i++) {
    mempool_entries[i + MEMPOOL_128MB_NUM + MEMPOOL_1GB_NUM].pid = 0;
    mempool_entries[i + MEMPOOL_128MB_NUM + MEMPOOL_1GB_NUM].addr = addr;
    mempool_entries[i + MEMPOOL_128MB_NUM + MEMPOOL_1GB_NUM].size = mempool_size_8gb;
    mempool_entries[i + MEMPOOL_128MB_NUM + MEMPOOL_1GB_NUM].ref_count = 0;
    addr += mempool_size_8gb;
  }
}

uint64_t agnocast_assign_memory(const pid_t pid, const uint64_t size)
{
  for (int i = 0; i < MEMPOOL_TOTAL_NUM; i++) {
    if (size <= mempool_entries[i].size && mempool_entries[i].pid == 0) {
      mempool_entries[i].pid = pid;
      mempool_entries[i].ref_count = 1;
      return mempool_entries[i].addr;
    }
  }

  return 0;
}

int agnocast_reference_memory(const pid_t pid)
{
  for (int i = 0; i < MEMPOOL_TOTAL_NUM; i++) {
    if (mempool_entries[i].pid == pid) {
      mempool_entries[i].ref_count++;
    }
  }

  return -1;
}

int agnocast_free_memory(const pid_t pid)
{
  for (int i = 0; i < MEMPOOL_TOTAL_NUM; i++) {
    if (mempool_entries[i].pid == pid) {
      mempool_entries[i].ref_count--;
      if (mempool_entries[i].ref_count == 0) {
        mempool_entries[i].pid = 0;
      }
      return 0;
    }
  }

  return -1;
}

#ifdef KUNIT_BUILD
void agnocast_exit_memory_allocator(void)
{
  for (int i = 0; i < MEMPOOL_TOTAL_NUM; i++) {
    mempool_entries[i].pid = 0;
  }
}
#endif