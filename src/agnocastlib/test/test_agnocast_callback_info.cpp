#include "agnocast_callback_info.hpp"

#include <gtest/gtest.h>

TEST(CallbackInfoTest, callback_first_arg)
{
  using FuncType = std::function<void(int, float)>;
  using FirstArgType = agnocast::callback_first_arg<FuncType>::type;
  EXPECT_TRUE((std::is_same<FirstArgType, int>::value));
}

TEST(CallbackInfoTest, get_erased_callback_normal)
{
  bool callback_called = false;
  int data = 0;
  agnocast::TypedMessagePtr<int> int_arg{agnocast::ipc_shared_ptr<int>(&data, "dummy", 0, 0)};
  auto int_callback = [&](const agnocast::ipc_shared_ptr<int> & /*unused_arg*/) {
    callback_called = true;
  };

  agnocast::TypeErasedCallback erased_callback = agnocast::get_erased_callback<int>(int_callback);
  erased_callback(int_arg);

  EXPECT_TRUE(callback_called);
}

TEST(CallbackInfoTest, get_erased_callback_invalid_type)
{
  int data = 0;
  agnocast::TypedMessagePtr<int> int_arg{agnocast::ipc_shared_ptr<int>(&data, "dummy", 0, 0)};
  auto float_callback = [&](agnocast::ipc_shared_ptr<float> /*unused_arg*/) {};

  agnocast::TypeErasedCallback erased_callback =
    agnocast::get_erased_callback<float>(float_callback);

  EXPECT_EXIT(
    erased_callback(int_arg), ::testing::ExitedWithCode(EXIT_FAILURE),
    "Agnocast internal implementation error: bad allocation when callback is called");
}
