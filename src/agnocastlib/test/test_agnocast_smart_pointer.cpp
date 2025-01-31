#include "agnocast_smart_pointer.hpp"

#include <gmock-global/gmock-global.h>
#include <gmock/gmock.h>

using namespace agnocast;
using testing::_;

MOCK_GLOBAL_FUNC4(
  decrement_rc_mock,
  void(const std::string &, const topic_local_id_t, const topic_local_id_t, const uint64_t));
MOCK_GLOBAL_FUNC4(
  increment_rc_core_mock,
  void(const std::string &, const topic_local_id_t, const topic_local_id_t, const uint64_t));

namespace agnocast {
  void decrement_rc(const std::string & tn, const topic_local_id_t pub_id, const topic_local_id_t sub_id, const uint64_t ts) {
    decrement_rc_mock(tn, pub_id, sub_id, ts);
  }
  void increment_rc_core(const std::string & tn, const topic_local_id_t pub_id, const topic_local_id_t sub_id, const uint64_t ts) {
    increment_rc_core_mock(tn, pub_id, sub_id, ts);
  }
}

class AgnocastSmartPointerTest : public ::testing::Test
{
protected:
  void SetUp() override
  {
    dummy_tn = "dummy";
    dummy_pub_id = 1;
    dummy_sub_id = 2;
    dummy_ts = 3;
  }

  std::string dummy_tn;
  topic_local_id_t dummy_pub_id;
  topic_local_id_t dummy_sub_id;
  uint64_t dummy_ts;
};

TEST_F(AgnocastSmartPointerTest, reset_normal)
{
  EXPECT_GLOBAL_CALL(decrement_rc_mock, decrement_rc_mock(dummy_tn, dummy_pub_id, dummy_sub_id, dummy_ts))
    .Times(1);
  agnocast::ipc_shared_ptr<int> sut{new int(0), dummy_tn, dummy_pub_id, dummy_sub_id, dummy_ts};

  sut.reset();

  EXPECT_EQ(nullptr, sut.get());
}

TEST_F(AgnocastSmartPointerTest, reset_isnt_created_by_sub)
{
  EXPECT_GLOBAL_CALL(decrement_rc_mock, decrement_rc_mock(dummy_tn, dummy_pub_id, dummy_sub_id, dummy_ts))
    .Times(0);
  agnocast::ipc_shared_ptr<int> sut{new int(0), dummy_tn, dummy_pub_id, dummy_ts};

  sut.reset();

  EXPECT_EQ(nullptr, sut.get());
}

TEST_F(AgnocastSmartPointerTest, reset_nullptr)
{
  EXPECT_GLOBAL_CALL(decrement_rc_mock, decrement_rc_mock("", 0, 0, 0)).Times(0);
  std::shared_ptr<agnocast::ipc_shared_ptr<int>> sut;
  sut.reset();
}

TEST_F(AgnocastSmartPointerTest, copy_constructor_normal)
{
  EXPECT_GLOBAL_CALL(
    increment_rc_core_mock, increment_rc_core_mock(dummy_tn, dummy_pub_id, dummy_sub_id, dummy_ts))
    .Times(1);
  EXPECT_GLOBAL_CALL(decrement_rc_mock, decrement_rc_mock(dummy_tn, dummy_pub_id, dummy_sub_id, dummy_ts))
    .Times(2);
  agnocast::ipc_shared_ptr<int> sut{new int(0), dummy_tn, dummy_pub_id, dummy_sub_id, dummy_ts};

  agnocast::ipc_shared_ptr<int> sut2 = sut;

  EXPECT_EQ(sut.get(), sut2.get());
  EXPECT_EQ(sut.get_topic_name(), sut2.get_topic_name());
  EXPECT_EQ(sut.get_timestamp(), sut2.get_timestamp());
}

TEST_F(AgnocastSmartPointerTest, copy_constructor_isnt_created_by_sub)
{
  agnocast::ipc_shared_ptr<int> sut{new int(0), dummy_tn, dummy_pub_id, dummy_ts};

  EXPECT_EXIT(
    agnocast::ipc_shared_ptr<int> sut2{sut}, ::testing::ExitedWithCode(EXIT_FAILURE),
    "Copying an ipc_shared_ptr is not allowed if it was created by borrow_loaned_message().");
}

TEST_F(AgnocastSmartPointerTest, copy_constructor_empty)
{
  EXPECT_GLOBAL_CALL(increment_rc_core_mock, increment_rc_core_mock(_, _, _, _)).Times(0);
  EXPECT_GLOBAL_CALL(decrement_rc_mock, decrement_rc_mock(_, _, _, _)).Times(0);

  agnocast::ipc_shared_ptr<int> sut;
  EXPECT_NO_THROW(agnocast::ipc_shared_ptr<int> sut2{sut});
}

TEST_F(AgnocastSmartPointerTest, move_constructor_normal)
{
  int * ptr = new int(0);
  EXPECT_GLOBAL_CALL(
    increment_rc_core_mock, increment_rc_core_mock(dummy_tn, dummy_pub_id, dummy_sub_id, dummy_ts))
    .Times(0);
  EXPECT_GLOBAL_CALL(decrement_rc_mock, decrement_rc_mock(dummy_tn, dummy_pub_id, dummy_sub_id, dummy_ts))
    .Times(1);
  agnocast::ipc_shared_ptr<int> sut{ptr, dummy_tn, dummy_pub_id, dummy_sub_id, dummy_ts};

  agnocast::ipc_shared_ptr<int> sut2 = std::move(sut);

  EXPECT_EQ(nullptr, sut.get());
  EXPECT_EQ(ptr, sut2.get());
  EXPECT_EQ(dummy_tn, sut2.get_topic_name());
  EXPECT_EQ(dummy_ts, sut2.get_timestamp());
}

TEST_F(AgnocastSmartPointerTest, move_assignment_normal)
{
  int * ptr = new int(0);
  EXPECT_GLOBAL_CALL(
    increment_rc_core_mock, increment_rc_core_mock(dummy_tn, dummy_pub_id, dummy_sub_id, dummy_ts))
    .Times(0);
  EXPECT_GLOBAL_CALL(decrement_rc_mock, decrement_rc_mock(dummy_tn, dummy_pub_id, dummy_sub_id, dummy_ts))
    .Times(1);
  agnocast::ipc_shared_ptr<int> sut{ptr, dummy_tn, dummy_pub_id, dummy_sub_id, dummy_ts};

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
  EXPECT_GLOBAL_CALL(
    increment_rc_core_mock, increment_rc_core_mock(dummy_tn, dummy_pub_id, dummy_sub_id, dummy_ts))
    .Times(0);
  EXPECT_GLOBAL_CALL(decrement_rc_mock, decrement_rc_mock(dummy_tn, dummy_pub_id, dummy_sub_id, dummy_ts))
    .Times(1);
  agnocast::ipc_shared_ptr<int> sut{ptr, dummy_tn, dummy_pub_id, dummy_sub_id, dummy_ts};

  sut = std::move(sut);

  EXPECT_EQ(ptr, sut.get());
  EXPECT_EQ(dummy_tn, sut.get_topic_name());
  EXPECT_EQ(dummy_ts, sut.get_timestamp());
}

TEST_F(AgnocastSmartPointerTest, dereference_operator)
{
  int * ptr = new int(0);
  EXPECT_GLOBAL_CALL(decrement_rc_mock, decrement_rc_mock(dummy_tn, dummy_pub_id, dummy_sub_id, dummy_ts))
    .Times(1);
  agnocast::ipc_shared_ptr<int> sut{ptr, dummy_tn, dummy_pub_id, dummy_sub_id, dummy_ts};

  int & result = *sut;

  EXPECT_EQ(ptr, &result);
}

TEST_F(AgnocastSmartPointerTest, arrow_operator)
{
  EXPECT_GLOBAL_CALL(decrement_rc_mock, decrement_rc_mock(dummy_tn, dummy_pub_id, dummy_sub_id, dummy_ts))
    .Times(1);
  agnocast::ipc_shared_ptr<std::vector<int>> sut{
    new std::vector<int>{0}, dummy_tn, dummy_pub_id, dummy_sub_id, dummy_ts};

  size_t result = sut->size();

  EXPECT_EQ(1, result);
}

TEST_F(AgnocastSmartPointerTest, bool_operator_true)
{
  EXPECT_GLOBAL_CALL(decrement_rc_mock, decrement_rc_mock(dummy_tn, dummy_pub_id, dummy_sub_id, dummy_ts))
    .Times(1);
  agnocast::ipc_shared_ptr<int> sut{new int(0), dummy_tn, dummy_pub_id, dummy_sub_id, dummy_ts};

  bool result = static_cast<bool>(sut);

  EXPECT_TRUE(result);
}

TEST_F(AgnocastSmartPointerTest, bool_operator_false)
{
  agnocast::ipc_shared_ptr<int> sut;

  bool result = static_cast<bool>(sut);

  EXPECT_FALSE(result);
}
