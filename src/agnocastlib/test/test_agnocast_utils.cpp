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

TEST(AgnocastUtilsTest, validate_ld_preload_normal)
{
  setenv("LD_PRELOAD", "libagnocast_heaphook.so", 1);
  EXPECT_NO_THROW(agnocast::validate_ld_preload());
  unsetenv("LD_PRELOAD");
}

TEST(AgnocastUtilsTest, validate_ld_preload_nothing)
{
  EXPECT_EXIT(
    agnocast::validate_ld_preload(), ::testing::ExitedWithCode(EXIT_FAILURE),
    "LD_PRELOAD is not set to libagnocast_heaphook.so");
}

TEST(AgnocastUtilsTest, validate_ld_preload_different)
{
  setenv("LD_PRELOAD", "dummy", 1);
  EXPECT_EXIT(
    agnocast::validate_ld_preload(), ::testing::ExitedWithCode(EXIT_FAILURE),
    "LD_PRELOAD is not set to libagnocast_heaphook.so");
  unsetenv("LD_PRELOAD");
}

TEST(AgnocastUtilsTest, validate_ld_preload_suffix)
{
  setenv("LD_PRELOAD", "libagnocast_heaphook.so_dummy", 1);
  EXPECT_EXIT(
    agnocast::validate_ld_preload(), ::testing::ExitedWithCode(EXIT_FAILURE),
    "LD_PRELOAD is not set to libagnocast_heaphook.so");
  unsetenv("LD_PRELOAD");
}

TEST(AgnocastUtilsTest, validate_ld_preload_prefix)
{
  setenv("LD_PRELOAD", "dummy_libagnocast_heaphook.so", 1);
  EXPECT_EXIT(
    agnocast::validate_ld_preload(), ::testing::ExitedWithCode(EXIT_FAILURE),
    "LD_PRELOAD is not set to libagnocast_heaphook.so");
  unsetenv("LD_PRELOAD");
}
