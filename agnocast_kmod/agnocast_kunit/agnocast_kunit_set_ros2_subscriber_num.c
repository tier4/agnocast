#include "agnocast_kunit_set_ros2_subscriber_num.h"

#include "../agnocast.h"

static char * node_name = "/kunit_test_node";
static uint32_t qos_depth = 10;
static bool qos_is_transient_local = false;
static bool qos_is_reliable = true;
static pid_t subscriber_pid = 1000;
static pid_t publisher_pid = 2000;
static bool is_take_sub = false;
static bool ignore_local_publications = false;

static void setup_one_subscriber(struct kunit * test, char * topic_name)
{
  subscriber_pid++;

  union ioctl_add_process_args add_process_args;
  int ret1 = add_process(subscriber_pid, current->nsproxy->ipc_ns, &add_process_args);

  union ioctl_add_subscriber_args add_subscriber_args;
  int ret2 = add_subscriber(
    topic_name, current->nsproxy->ipc_ns, node_name, subscriber_pid, qos_depth,
    qos_is_transient_local, qos_is_reliable, is_take_sub, ignore_local_publications,
    &add_subscriber_args);

  KUNIT_ASSERT_EQ(test, ret1, 0);
  KUNIT_ASSERT_EQ(test, ret2, 0);
}

static void setup_one_publisher(struct kunit * test, char * topic_name)
{
  publisher_pid++;

  union ioctl_add_process_args add_process_args;
  int ret1 = add_process(publisher_pid, current->nsproxy->ipc_ns, &add_process_args);

  union ioctl_add_publisher_args add_publisher_args;
  int ret2 = add_publisher(
    topic_name, current->nsproxy->ipc_ns, node_name, publisher_pid, qos_depth,
    qos_is_transient_local, &add_publisher_args);

  KUNIT_ASSERT_EQ(test, ret1, 0);
  KUNIT_ASSERT_EQ(test, ret2, 0);
}

void test_case_set_ros2_subscriber_num_normal(struct kunit * test)
{
  char * topic_name = "/kunit_test_topic";
  setup_one_subscriber(test, topic_name);

  int ret = set_ros2_subscriber_num(topic_name, current->nsproxy->ipc_ns, 5);
  KUNIT_EXPECT_EQ(test, ret, 0);

  // Verify the value was set correctly using get_subscriber_num with include_ros2=true
  union ioctl_get_subscriber_num_args subscriber_num_args;
  int ret2 = get_subscriber_num(topic_name, current->nsproxy->ipc_ns, true, &subscriber_num_args);
  KUNIT_EXPECT_EQ(test, ret2, 0);
  KUNIT_EXPECT_EQ(test, subscriber_num_args.ret_subscriber_num, 6);  // 1 agnocast + 5 ros2
}

void test_case_set_ros2_subscriber_num_topic_not_exist(struct kunit * test)
{
  char * topic_name = "/kunit_nonexistent_topic";

  int ret = set_ros2_subscriber_num(topic_name, current->nsproxy->ipc_ns, 5);
  KUNIT_EXPECT_EQ(test, ret, -ENOENT);
}

void test_case_set_ros2_subscriber_num_update(struct kunit * test)
{
  char * topic_name = "/kunit_test_topic";
  setup_one_subscriber(test, topic_name);

  // Set initial value
  int ret1 = set_ros2_subscriber_num(topic_name, current->nsproxy->ipc_ns, 3);
  KUNIT_EXPECT_EQ(test, ret1, 0);

  // Verify initial value
  union ioctl_get_subscriber_num_args subscriber_num_args;
  int ret2 = get_subscriber_num(topic_name, current->nsproxy->ipc_ns, true, &subscriber_num_args);
  KUNIT_EXPECT_EQ(test, ret2, 0);
  KUNIT_EXPECT_EQ(test, subscriber_num_args.ret_subscriber_num, 4);  // 1 agnocast + 3 ros2

  // Update to new value
  int ret3 = set_ros2_subscriber_num(topic_name, current->nsproxy->ipc_ns, 7);
  KUNIT_EXPECT_EQ(test, ret3, 0);

  // Verify updated value
  int ret4 = get_subscriber_num(topic_name, current->nsproxy->ipc_ns, true, &subscriber_num_args);
  KUNIT_EXPECT_EQ(test, ret4, 0);
  KUNIT_EXPECT_EQ(test, subscriber_num_args.ret_subscriber_num, 8);  // 1 agnocast + 7 ros2
}

void test_case_set_ros2_subscriber_num_zero(struct kunit * test)
{
  char * topic_name = "/kunit_test_topic";
  setup_one_subscriber(test, topic_name);

  // Set to non-zero first
  int ret1 = set_ros2_subscriber_num(topic_name, current->nsproxy->ipc_ns, 5);
  KUNIT_EXPECT_EQ(test, ret1, 0);

  // Then set to zero
  int ret2 = set_ros2_subscriber_num(topic_name, current->nsproxy->ipc_ns, 0);
  KUNIT_EXPECT_EQ(test, ret2, 0);

  // Verify it's back to agnocast-only count
  union ioctl_get_subscriber_num_args subscriber_num_args;
  int ret3 = get_subscriber_num(topic_name, current->nsproxy->ipc_ns, true, &subscriber_num_args);
  KUNIT_EXPECT_EQ(test, ret3, 0);
  KUNIT_EXPECT_EQ(test, subscriber_num_args.ret_subscriber_num, 1);  // 1 agnocast + 0 ros2
}

void test_case_set_ros2_subscriber_num_with_publisher_topic(struct kunit * test)
{
  char * topic_name = "/kunit_test_topic";
  setup_one_publisher(test, topic_name);

  // Should succeed even if topic only has publishers (no agnocast subscribers)
  int ret = set_ros2_subscriber_num(topic_name, current->nsproxy->ipc_ns, 3);
  KUNIT_EXPECT_EQ(test, ret, 0);

  // Verify: 0 agnocast subscribers + 3 ros2 subscribers
  union ioctl_get_subscriber_num_args subscriber_num_args;
  int ret2 = get_subscriber_num(topic_name, current->nsproxy->ipc_ns, true, &subscriber_num_args);
  KUNIT_EXPECT_EQ(test, ret2, 0);
  KUNIT_EXPECT_EQ(test, subscriber_num_args.ret_subscriber_num, 3);  // 0 agnocast + 3 ros2
}
