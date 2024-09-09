#ifndef AGNOCAST_HEAPHOOK__UTIL_HPP_
#define AGNOCAST_HEAPHOOK__UTIL_HPP_

#include <cstddef>

#define ALIGNMENT 102400  // 100kB

size_t memory_align(size_t mempool_size);

#endif  // AGNOCAST_HEAPHOOK__UTIL_HPP_
