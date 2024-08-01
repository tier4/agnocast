#pragma once

#include <cstdint>

void map_area(const char * shm_name, const uint64_t shm_addr, const bool writable);
void initialize_mempool(const char * shm_name, const uint64_t shm_addr);
