#include "agnocast/agnocast_context.hpp"

#include <gtest/gtest.h>

TEST(ParseParameterValueTest, parse_integer)
{
  auto result = agnocast::Context::parse_parameter_value("123");
  EXPECT_EQ(result.get_type(), rclcpp::ParameterType::PARAMETER_INTEGER);
  EXPECT_EQ(result.get<int64_t>(), 123);
}

TEST(ParseParameterValueTest, parse_negative_integer)
{
  auto result = agnocast::Context::parse_parameter_value("-456");
  EXPECT_EQ(result.get_type(), rclcpp::ParameterType::PARAMETER_INTEGER);
  EXPECT_EQ(result.get<int64_t>(), -456);
}

TEST(ParseParameterValueTest, parse_bool_true_lowercase)
{
  auto result = agnocast::Context::parse_parameter_value("true");
  EXPECT_EQ(result.get_type(), rclcpp::ParameterType::PARAMETER_BOOL);
  EXPECT_EQ(result.get<bool>(), true);
}

TEST(ParseParameterValueTest, parse_bool_false_uppercase)
{
  auto result = agnocast::Context::parse_parameter_value("FALSE");
  EXPECT_EQ(result.get_type(), rclcpp::ParameterType::PARAMETER_BOOL);
  EXPECT_EQ(result.get<bool>(), false);
}

TEST(ParseParameterValueTest, parse_double)
{
  auto result = agnocast::Context::parse_parameter_value("3.14");
  EXPECT_EQ(result.get_type(), rclcpp::ParameterType::PARAMETER_DOUBLE);
  EXPECT_DOUBLE_EQ(result.get<double>(), 3.14);
}

TEST(ParseParameterValueTest, parse_double_with_exponent)
{
  auto result = agnocast::Context::parse_parameter_value("1.5e10");
  EXPECT_EQ(result.get_type(), rclcpp::ParameterType::PARAMETER_DOUBLE);
  EXPECT_DOUBLE_EQ(result.get<double>(), 1.5e10);
}

TEST(ParseParameterValueTest, parse_string)
{
  auto result = agnocast::Context::parse_parameter_value("hello world");
  EXPECT_EQ(result.get_type(), rclcpp::ParameterType::PARAMETER_STRING);
  EXPECT_EQ(result.get<std::string>(), "hello world");
}

TEST(ParseParameterValueTest, parse_empty_string)
{
  auto result = agnocast::Context::parse_parameter_value("");
  EXPECT_EQ(result.get_type(), rclcpp::ParameterType::PARAMETER_STRING);
  EXPECT_EQ(result.get<std::string>(), "");
}

TEST(ParseParameterValueTest, parse_array_as_string)
{
  // Array syntax is not supported and treated as a plain string
  auto result = agnocast::Context::parse_parameter_value("[1,2,3]");
  EXPECT_EQ(result.get_type(), rclcpp::ParameterType::PARAMETER_STRING);
  EXPECT_EQ(result.get<std::string>(), "[1,2,3]");
}

TEST(ParseParameterValueTest, parse_node_prefix_as_string)
{
  // Node prefix syntax is not supported and treated as a plain string
  auto result = agnocast::Context::parse_parameter_value("/my_node:foo");
  EXPECT_EQ(result.get_type(), rclcpp::ParameterType::PARAMETER_STRING);
  EXPECT_EQ(result.get<std::string>(), "/my_node:foo");
}
