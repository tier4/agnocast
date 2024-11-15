#include "agnocast_utils.hpp"

#include <gtest/gtest.h>

TEST(AgnocastUtilsTest, create_mq_name)
{
  std::string mq_name = agnocast::create_mq_name("/test", 0);
  EXPECT_EQ(mq_name, "/test@0");
}
