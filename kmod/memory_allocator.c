#include "memory_allocator.h"

#include <linux/module.h>

MODULE_LICENSE("Dual BSD/GPL");

#define MEMPOOL_128MB_NUM 1000
#define MEMPOOL_1GB_NUM 100
#define MEMPOOL_8GB_NUM 10

static uint64_t mempool_size_128mb = 134217728;  // 128 * 1024 * 1024
static uint64_t mempool_size_1gb = 1073741824;   // 1 * 1024 * 1024 * 1024
static uint64_t mempool_size_8gb = 8589934592;   // 8 * 1024 * 1024 * 1024

static pid_t mempool_128mb_pid[MEMPOOL_128MB_NUM];
static pid_t mempool_1gb_pid[MEMPOOL_1GB_NUM];
static pid_t mempool_8gb_pid[MEMPOOL_8GB_NUM];

static uint64_t mempool_128mb_addr[MEMPOOL_128MB_NUM];
static uint64_t mempool_1gb_addr[MEMPOOL_1GB_NUM];
static uint64_t mempool_8gb_addr[MEMPOOL_8GB_NUM];

void agnocast_init_memory_allocator(void)
{
  // TODO(Ryuta Kambe): currently, we assume that the address from 0x40000000000 to 0x8B000000000 is
  // available
  uint64_t addr = 0x40000000000;

  for (int i = 0; i < MEMPOOL_128MB_NUM; i++) {
    mempool_128mb_pid[i] = 0;
    mempool_128mb_addr[i] = addr;
    addr += mempool_size_128mb;
  }

  for (int i = 0; i < MEMPOOL_1GB_NUM; i++) {
    mempool_1gb_pid[i] = 0;
    mempool_1gb_addr[i] = addr;
    addr += mempool_size_1gb;
  }

  for (int i = 0; i < MEMPOOL_8GB_NUM; i++) {
    mempool_8gb_pid[i] = 0;
    mempool_8gb_addr[i] = addr;
    addr += mempool_size_8gb;
  }
}

uint64_t agnocast_assign_memory(const pid_t pid, const uint64_t size)
{
  if (size <= mempool_size_128mb) {
    for (int i = 0; i < MEMPOOL_128MB_NUM; i++) {
      if (mempool_128mb_pid[i] == 0) {
        mempool_128mb_pid[i] = pid;
        return mempool_128mb_addr[i];
      }
    }
  }

  if (size <= mempool_size_1gb) {
    for (int i = 0; i < MEMPOOL_1GB_NUM; i++) {
      if (mempool_1gb_pid[i] == 0) {
        mempool_1gb_pid[i] = pid;
        return mempool_1gb_addr[i];
      }
    }
  }

  if (size <= mempool_size_8gb) {
    for (int i = 0; i < MEMPOOL_8GB_NUM; i++) {
      if (mempool_8gb_pid[i] == 0) {
        mempool_8gb_pid[i] = pid;
        return mempool_8gb_addr[i];
      }
    }
  }

  return 0;
}

int agnocast_free_memory(const pid_t pid)
{
  for (int i = 0; i < MEMPOOL_128MB_NUM; i++) {
    if (mempool_128mb_pid[i] == pid) {
      mempool_128mb_pid[i] = 0;
      return 0;
    }
  }

  for (int i = 0; i < MEMPOOL_1GB_NUM; i++) {
    if (mempool_1gb_pid[i] == pid) {
      mempool_1gb_pid[i] = 0;
      return 0;
    }
  }

  for (int i = 0; i < MEMPOOL_8GB_NUM; i++) {
    if (mempool_8gb_pid[i] == pid) {
      mempool_8gb_pid[i] = 0;
      return 0;
    }
  }

  return -1;
}

void agnocast_exit_memory_allocator(void)
{
  for (int i = 0; i < MEMPOOL_128MB_NUM; i++) {
    mempool_128mb_pid[i] = 0;
  }

  for (int i = 0; i < MEMPOOL_1GB_NUM; i++) {
    mempool_1gb_pid[i] = 0;
  }

  for (int i = 0; i < MEMPOOL_8GB_NUM; i++) {
    mempool_8gb_pid[i] = 0;
  }
}
