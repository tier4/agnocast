#include "agnocast_smart_pointer.hpp"

#include <gmock-global/gmock-global.h>
#include <gmock/gmock.h>

MOCK_GLOBAL_FUNC3(decrement_rc, void(const std::string &, uint32_t, uint64_t));
MOCK_GLOBAL_FUNC3(increment_rc_core, void(const std::string &, uint32_t, uint64_t));

class AgnocastSmartPointerTest : public ::testing::Test
{
protected:
  void SetUp() override
  {
    dummy_tn = "dummy";
    dummy_pid = 0;
    dummy_ts = 0;
  }

  std::string dummy_tn;
  uint32_t dummy_pid;
  uint64_t dummy_ts;
};

TEST_F(AgnocastSmartPointerTest, reset_normal)
{
  EXPECT_GLOBAL_CALL(decrement_rc, decrement_rc(dummy_tn, dummy_pid, dummy_ts)).Times(1);
  agnocast::ipc_shared_ptr<int> sut{new int(0), dummy_tn, dummy_pid, dummy_ts, true};

  sut.reset();

  EXPECT_EQ(nullptr, sut.get());
}

TEST_F(AgnocastSmartPointerTest, reset_dont_need_rc_update)
{
  EXPECT_GLOBAL_CALL(decrement_rc, decrement_rc(dummy_tn, dummy_pid, dummy_ts)).Times(0);
  agnocast::ipc_shared_ptr<int> sut{new int(0), dummy_tn, dummy_pid, dummy_ts, false};

  sut.reset();

  EXPECT_EQ(nullptr, sut.get());
}

TEST_F(AgnocastSmartPointerTest, reset_nullptr)
{
  EXPECT_GLOBAL_CALL(decrement_rc, decrement_rc("", 0, 0)).Times(0);
  std::shared_ptr<agnocast::ipc_shared_ptr<int>> sut;
  sut.reset();
}

TEST_F(AgnocastSmartPointerTest, copy_constructor_normal)
{
  EXPECT_GLOBAL_CALL(increment_rc_core, increment_rc_core(dummy_tn, dummy_pid, dummy_ts)).Times(1);
  EXPECT_GLOBAL_CALL(decrement_rc, decrement_rc(dummy_tn, dummy_pid, dummy_ts)).Times(2);
  agnocast::ipc_shared_ptr<int> sut{new int(0), dummy_tn, dummy_pid, dummy_ts, true};

  agnocast::ipc_shared_ptr<int> sut2 = sut;

  EXPECT_EQ(sut.get(), sut2.get());
  EXPECT_EQ(sut.get_topic_name(), sut2.get_topic_name());
  EXPECT_EQ(sut.get_timestamp(), sut2.get_timestamp());
}

TEST_F(AgnocastSmartPointerTest, copy_constructor_dont_need_rc_update)
{
  EXPECT_GLOBAL_CALL(increment_rc_core, increment_rc_core(dummy_tn, dummy_pid, dummy_ts)).Times(0);
  EXPECT_GLOBAL_CALL(decrement_rc, decrement_rc(dummy_tn, dummy_pid, dummy_ts)).Times(0);
  agnocast::ipc_shared_ptr<int> sut{new int(0), dummy_tn, dummy_pid, dummy_ts, false};

  agnocast::ipc_shared_ptr<int> sut2 = sut;

  EXPECT_EQ(sut.get(), sut2.get());
  EXPECT_EQ(sut.get_topic_name(), sut2.get_topic_name());
  EXPECT_EQ(sut.get_timestamp(), sut2.get_timestamp());
}

TEST_F(AgnocastSmartPointerTest, move_constructor_normal)
{
  int * ptr = new int(0);
  EXPECT_GLOBAL_CALL(increment_rc_core, increment_rc_core(dummy_tn, dummy_pid, dummy_ts)).Times(0);
  EXPECT_GLOBAL_CALL(decrement_rc, decrement_rc(dummy_tn, dummy_pid, dummy_ts)).Times(1);
  agnocast::ipc_shared_ptr<int> sut{ptr, dummy_tn, dummy_pid, dummy_ts, true};

  agnocast::ipc_shared_ptr<int> sut2 = std::move(sut);

  EXPECT_EQ(nullptr, sut.get());
  EXPECT_EQ(ptr, sut2.get());
  EXPECT_EQ(dummy_tn, sut2.get_topic_name());
  EXPECT_EQ(dummy_ts, sut2.get_timestamp());
}

TEST_F(AgnocastSmartPointerTest, move_assignment_normal)
{
  int * ptr = new int(0);
  EXPECT_GLOBAL_CALL(increment_rc_core, increment_rc_core(dummy_tn, dummy_pid, dummy_ts)).Times(0);
  EXPECT_GLOBAL_CALL(decrement_rc, decrement_rc(dummy_tn, dummy_pid, dummy_ts)).Times(1);
  agnocast::ipc_shared_ptr<int> sut{ptr, dummy_tn, dummy_pid, dummy_ts, true};

  agnocast::ipc_shared_ptr<int> sut2;
  sut2 = std::move(sut);

  EXPECT_EQ(nullptr, sut.get());
  EXPECT_EQ(ptr, sut2.get());
  EXPECT_EQ(dummy_tn, sut2.get_topic_name());
  EXPECT_EQ(dummy_ts, sut2.get_timestamp());
}

TEST_F(AgnocastSmartPointerTest, move_assignment_self)
{
  int * ptr = new int(0);
  EXPECT_GLOBAL_CALL(increment_rc_core, increment_rc_core(dummy_tn, dummy_pid, dummy_ts)).Times(0);
  EXPECT_GLOBAL_CALL(decrement_rc, decrement_rc(dummy_tn, dummy_pid, dummy_ts)).Times(1);
  agnocast::ipc_shared_ptr<int> sut{ptr, dummy_tn, dummy_pid, dummy_ts, true};

  sut = std::move(sut);

  EXPECT_EQ(ptr, sut.get());
  EXPECT_EQ(dummy_tn, sut.get_topic_name());
  EXPECT_EQ(dummy_ts, sut.get_timestamp());
}

TEST_F(AgnocastSmartPointerTest, dereference_operator)
{
  int * ptr = new int(0);
  EXPECT_GLOBAL_CALL(decrement_rc, decrement_rc(dummy_tn, dummy_pid, dummy_ts)).Times(1);
  agnocast::ipc_shared_ptr<int> sut{ptr, dummy_tn, dummy_pid, dummy_ts, true};

  int & result = *sut;

  EXPECT_EQ(ptr, &result);
}

TEST_F(AgnocastSmartPointerTest, arrow_operator)
{
  EXPECT_GLOBAL_CALL(decrement_rc, decrement_rc(dummy_tn, dummy_pid, dummy_ts)).Times(1);
  agnocast::ipc_shared_ptr<std::vector<int>> sut{
    new std::vector<int>{0}, dummy_tn, dummy_pid, dummy_ts, true};

  size_t result = sut->size();

  EXPECT_EQ(1, result);
}

TEST_F(AgnocastSmartPointerTest, bool_operator_true)
{
  EXPECT_GLOBAL_CALL(decrement_rc, decrement_rc(dummy_tn, dummy_pid, dummy_ts)).Times(1);
  agnocast::ipc_shared_ptr<int> sut{new int(0), dummy_tn, dummy_pid, dummy_ts, true};

  bool result = static_cast<bool>(sut);

  EXPECT_TRUE(result);
}

TEST_F(AgnocastSmartPointerTest, bool_operator_false)
{
  agnocast::ipc_shared_ptr<int> sut;

  bool result = static_cast<bool>(sut);

  EXPECT_FALSE(result);
}
