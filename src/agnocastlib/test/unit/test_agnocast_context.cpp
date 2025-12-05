#include "agnocast/agnocast_context.hpp"

#include <gtest/gtest.h>

class ParseParameterValueTest : public ::testing::Test
{
};

TEST_F(ParseParameterValueTest, parse_integer)
{
  auto result = agnocast::Context::parse_parameter_value("123");
  EXPECT_EQ(result.get_type(), rclcpp::ParameterType::PARAMETER_INTEGER);
  EXPECT_EQ(result.get<int64_t>(), 123);
}

TEST_F(ParseParameterValueTest, parse_negative_integer)
{
  auto result = agnocast::Context::parse_parameter_value("-456");
  EXPECT_EQ(result.get_type(), rclcpp::ParameterType::PARAMETER_INTEGER);
  EXPECT_EQ(result.get<int64_t>(), -456);
}

TEST_F(ParseParameterValueTest, parse_zero)
{
  auto result = agnocast::Context::parse_parameter_value("0");
  EXPECT_EQ(result.get_type(), rclcpp::ParameterType::PARAMETER_INTEGER);
  EXPECT_EQ(result.get<int64_t>(), 0);
}

TEST_F(ParseParameterValueTest, parse_bool_true_lowercase)
{
  auto result = agnocast::Context::parse_parameter_value("true");
  EXPECT_EQ(result.get_type(), rclcpp::ParameterType::PARAMETER_BOOL);
  EXPECT_EQ(result.get<bool>(), true);
}

TEST_F(ParseParameterValueTest, parse_bool_true_uppercase)
{
  auto result = agnocast::Context::parse_parameter_value("TRUE");
  EXPECT_EQ(result.get_type(), rclcpp::ParameterType::PARAMETER_BOOL);
  EXPECT_EQ(result.get<bool>(), true);
}

TEST_F(ParseParameterValueTest, parse_bool_true_mixedcase)
{
  auto result = agnocast::Context::parse_parameter_value("True");
  EXPECT_EQ(result.get_type(), rclcpp::ParameterType::PARAMETER_BOOL);
  EXPECT_EQ(result.get<bool>(), true);
}

TEST_F(ParseParameterValueTest, parse_bool_false_lowercase)
{
  auto result = agnocast::Context::parse_parameter_value("false");
  EXPECT_EQ(result.get_type(), rclcpp::ParameterType::PARAMETER_BOOL);
  EXPECT_EQ(result.get<bool>(), false);
}

TEST_F(ParseParameterValueTest, parse_bool_false_uppercase)
{
  auto result = agnocast::Context::parse_parameter_value("FALSE");
  EXPECT_EQ(result.get_type(), rclcpp::ParameterType::PARAMETER_BOOL);
  EXPECT_EQ(result.get<bool>(), false);
}

TEST_F(ParseParameterValueTest, parse_double)
{
  auto result = agnocast::Context::parse_parameter_value("3.14");
  EXPECT_EQ(result.get_type(), rclcpp::ParameterType::PARAMETER_DOUBLE);
  EXPECT_DOUBLE_EQ(result.get<double>(), 3.14);
}

TEST_F(ParseParameterValueTest, parse_negative_double)
{
  auto result = agnocast::Context::parse_parameter_value("-2.5");
  EXPECT_EQ(result.get_type(), rclcpp::ParameterType::PARAMETER_DOUBLE);
  EXPECT_DOUBLE_EQ(result.get<double>(), -2.5);
}

TEST_F(ParseParameterValueTest, parse_double_with_exponent)
{
  auto result = agnocast::Context::parse_parameter_value("1.5e10");
  EXPECT_EQ(result.get_type(), rclcpp::ParameterType::PARAMETER_DOUBLE);
  EXPECT_DOUBLE_EQ(result.get<double>(), 1.5e10);
}

TEST_F(ParseParameterValueTest, parse_string)
{
  auto result = agnocast::Context::parse_parameter_value("hello");
  EXPECT_EQ(result.get_type(), rclcpp::ParameterType::PARAMETER_STRING);
  EXPECT_EQ(result.get<std::string>(), "hello");
}

TEST_F(ParseParameterValueTest, parse_string_with_spaces)
{
  auto result = agnocast::Context::parse_parameter_value("hello world");
  EXPECT_EQ(result.get_type(), rclcpp::ParameterType::PARAMETER_STRING);
  EXPECT_EQ(result.get<std::string>(), "hello world");
}

TEST_F(ParseParameterValueTest, parse_empty_string)
{
  auto result = agnocast::Context::parse_parameter_value("");
  EXPECT_EQ(result.get_type(), rclcpp::ParameterType::PARAMETER_STRING);
  EXPECT_EQ(result.get<std::string>(), "");
}

// Arrays are NOT supported - they are parsed as strings (unlike rcl)
TEST_F(ParseParameterValueTest, parse_array_as_string)
{
  auto result = agnocast::Context::parse_parameter_value("[1,2,3]");
  EXPECT_EQ(result.get_type(), rclcpp::ParameterType::PARAMETER_STRING);
  EXPECT_EQ(result.get<std::string>(), "[1,2,3]");
}

TEST_F(ParseParameterValueTest, parse_string_array_as_string)
{
  auto result = agnocast::Context::parse_parameter_value("[\"a\",\"b\",\"c\"]");
  EXPECT_EQ(result.get_type(), rclcpp::ParameterType::PARAMETER_STRING);
  EXPECT_EQ(result.get<std::string>(), "[\"a\",\"b\",\"c\"]");
}

// Node name prefix is NOT supported - the whole string becomes the param name
TEST_F(ParseParameterValueTest, parse_value_with_node_prefix_style)
{
  // In rcl, "/my_node:foo:=123" would set foo=123 only for /my_node
  // In agnocast, the value "123" is just parsed as integer
  // The param name handling is done in parse_param_rule, not here
  auto result = agnocast::Context::parse_parameter_value("123");
  EXPECT_EQ(result.get_type(), rclcpp::ParameterType::PARAMETER_INTEGER);
  EXPECT_EQ(result.get<int64_t>(), 123);
}
