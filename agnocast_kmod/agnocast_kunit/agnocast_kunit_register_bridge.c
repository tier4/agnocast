#include "agnocast_kunit_register_bridge.h"

#include "../agnocast.h"
#include "../agnocast_memory_allocator.h"

static pid_t reg_pid_cnt = 8000;

void test_case_register_bridge_normal(struct kunit * test)
{
  pid_t pid = reg_pid_cnt++;
  char * topic_name = "/kunit_reg_bridge_normal";

  int ret = register_bridge(pid, topic_name, current->nsproxy->ipc_ns);

  KUNIT_EXPECT_EQ(test, ret, 0);

  unregister_bridge(pid, topic_name, current->nsproxy->ipc_ns);
}

void test_case_register_bridge_duplicate(struct kunit * test)
{
  pid_t pid = reg_pid_cnt++;
  char * topic_name = "/kunit_reg_bridge_dup";

  int ret = register_bridge(pid, topic_name, current->nsproxy->ipc_ns);
  KUNIT_ASSERT_EQ(test, ret, 0);

  ret = register_bridge(pid, topic_name, current->nsproxy->ipc_ns);
  KUNIT_EXPECT_EQ(test, ret, -EEXIST);

  unregister_bridge(pid, topic_name, current->nsproxy->ipc_ns);
}

void test_case_register_bridge_multi_topic(struct kunit * test)
{
  pid_t pid = reg_pid_cnt++;
  char * topic1 = "/kunit_reg_bridge_multi_1";
  char * topic2 = "/kunit_reg_bridge_multi_2";

  int ret1 = register_bridge(pid, topic1, current->nsproxy->ipc_ns);
  KUNIT_EXPECT_EQ(test, ret1, 0);

  int ret2 = register_bridge(pid, topic2, current->nsproxy->ipc_ns);
  KUNIT_EXPECT_EQ(test, ret2, 0);

  unregister_bridge(pid, topic1, current->nsproxy->ipc_ns);
  unregister_bridge(pid, topic2, current->nsproxy->ipc_ns);
}