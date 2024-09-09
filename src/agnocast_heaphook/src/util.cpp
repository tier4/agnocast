
#include "agnocast_heaphook/util.hpp"

size_t memory_align(size_t mempool_size)
{
  if (mempool_size % ALIGNMENT != 0) {
    mempool_size += ALIGNMENT - (mempool_size % ALIGNMENT);
  }
  return mempool_size;
}