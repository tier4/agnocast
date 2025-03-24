#include <gtest/gtest.h>

// Mock
namespace agnocast
{
void * initialize_agnocast(const uint64_t shm_size)
{
  return nullptr;
}
}  // namespace agnocast

TEST(agnocast_heaphook, dummy)
{
  // Dummy test to avoid "No tests found in test_agnocast_heaphook.cpp" error
  SUCCEED();
}
