#include "agnocast_kunit_unregister_bridge.h"

#include "../agnocast.h"
#include "../agnocast_memory_allocator.h"

static pid_t unreg_pid_cnt = 9000;

void test_case_unregister_bridge_normal(struct kunit * test)
{
  pid_t pid = unreg_pid_cnt++;
  char * topic_name = "/kunit_unreg_bridge_normal";

  register_bridge(pid, topic_name, current->nsproxy->ipc_ns);

  int ret = unregister_bridge(pid, topic_name, current->nsproxy->ipc_ns);
  KUNIT_EXPECT_EQ(test, ret, 0);

  ret = unregister_bridge(pid, topic_name, current->nsproxy->ipc_ns);
  KUNIT_EXPECT_EQ(test, ret, -ENOENT);
}

void test_case_unregister_bridge_not_exist(struct kunit * test)
{
  pid_t pid = unreg_pid_cnt++;
  char * topic_name = "/kunit_unreg_bridge_phantom";

  int ret = unregister_bridge(pid, topic_name, current->nsproxy->ipc_ns);
  KUNIT_EXPECT_EQ(test, ret, -ENOENT);
}