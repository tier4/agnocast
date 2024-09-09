
#include "agnocast_heaphook/util.hpp"

#include <gtest/gtest.h>

TEST(agnocast_heaphook, test_aligned)
{
  size_t address = 102400;
  size_t aligned_address = align_memory(address);
  EXPECT_EQ(aligned_address, 102400);
}

TEST(agnocast_heaphook, test_not_aligned)
{
  size_t address = 102401;
  size_t aligned_address = align_memory(address);
  EXPECT_EQ(aligned_address, 204800);
}

int main(int argc, char ** argv)
{
  testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
