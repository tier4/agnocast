#include "agnocast_kunit_add_bridge.h"

#include "../agnocast.h"

#include <kunit/test.h>

static const char * TOPIC_NAME = "/kunit_test_bridge_topic";
static const pid_t BRIDGE_OWNER_PID = 1000;
static const pid_t OTHER_PID = 1001;

void test_case_add_bridge_normal(struct kunit * test)
{
  // Arrange
  struct ioctl_add_bridge_args args = {0};

  // Act
  int ret = add_bridge(TOPIC_NAME, BRIDGE_OWNER_PID, current->nsproxy->ipc_ns, &args);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, 0);
  KUNIT_EXPECT_TRUE(test, is_in_bridge_htable(TOPIC_NAME, current->nsproxy->ipc_ns));
  KUNIT_EXPECT_EQ(
    test, get_bridge_owner_pid(TOPIC_NAME, current->nsproxy->ipc_ns), BRIDGE_OWNER_PID);
}

void test_case_add_bridge_already_exists_same_pid(struct kunit * test)
{
  // Arrange
  struct ioctl_add_bridge_args args = {0};
  add_bridge(TOPIC_NAME, BRIDGE_OWNER_PID, current->nsproxy->ipc_ns, &args);

  // Act
  int ret = add_bridge(TOPIC_NAME, BRIDGE_OWNER_PID, current->nsproxy->ipc_ns, &args);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, 0);
  KUNIT_EXPECT_EQ(
    test, get_bridge_owner_pid(TOPIC_NAME, current->nsproxy->ipc_ns), BRIDGE_OWNER_PID);
}

void test_case_add_bridge_already_exists_diff_pid(struct kunit * test)
{
  // Arrange
  struct ioctl_add_bridge_args args = {0};
  add_bridge(TOPIC_NAME, BRIDGE_OWNER_PID, current->nsproxy->ipc_ns, &args);

  // Act
  int ret = add_bridge(TOPIC_NAME, OTHER_PID, current->nsproxy->ipc_ns, &args);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, -EEXIST);
  KUNIT_EXPECT_EQ(
    test, get_bridge_owner_pid(TOPIC_NAME, current->nsproxy->ipc_ns), BRIDGE_OWNER_PID);
}
