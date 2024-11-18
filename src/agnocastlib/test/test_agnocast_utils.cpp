#include "agnocast_utils.hpp"

#include <gtest/gtest.h>

TEST(AgnocastUtilsTest, create_mq_name_normal)
{
  EXPECT_EQ(agnocast::create_mq_name("/dummy", 0), "/dummy@0");
}

TEST(AgnocastUtilsTest, create_mq_name_slash_included)
{
  EXPECT_EQ(agnocast::create_mq_name("/dummy/dummy", 0), "/dummy_dummy@0");
}

TEST(AgnocastUtilsTest, create_mq_name_invalid_topic)
{
  EXPECT_EXIT(agnocast::create_mq_name("dummy", 0), ::testing::ExitedWithCode(EXIT_FAILURE), "");
}
