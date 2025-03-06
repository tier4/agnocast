#include "agnocast.h"
#include "agnocast_kunit/agnocast_kunit_decrement_rc.h"
#include "agnocast_kunit/agnocast_kunit_get_subscriber_num.h"
#include "agnocast_kunit/agnocast_kunit_get_topic_list.h"
#include "agnocast_kunit/agnocast_kunit_increment_rc.h"
#include "agnocast_kunit/agnocast_kunit_new_shm.h"
#include "agnocast_kunit/agnocast_kunit_publish_msg.h"
#include "agnocast_kunit/agnocast_kunit_publisher_add.h"
#include "agnocast_kunit/agnocast_kunit_receive_msg.h"
#include "agnocast_kunit/agnocast_kunit_subscriber_add.h"
#include "agnocast_kunit/agnocast_kunit_take_msg.h"
#include "agnocast_memory_allocator.h"

#include <kunit/test.h>

MODULE_LICENSE("Dual BSD/GPL");

struct kunit_case agnocast_test_cases[] = {
  TEST_CASES_SUBSCRIBER_ADD,
  TEST_CASES_PUBLISHER_ADD,
  TEST_CASES_INCREMENT_RC,
  TEST_CASES_DECREMENT_RC,
  TEST_CASES_RECEIVE_MSG,
  TEST_CASES_PUBLISH_MSG,
  TEST_CASES_TAKE_MSG,
  TEST_CASES_NEW_SHM,
  TEST_CASES_GET_SUBSCRIBER_NUM,
  TEST_CASES_GET_TOPIC_LIST,
  {},
};

static int agnocast_test_init(struct kunit * test)
{
  return 0;
}

static void agnocast_test_exit(struct kunit * test)
{
  agnocast_exit_free_data();
}

static int agnocast_test_suite_init(struct kunit_suite * test_suite)
{
  int ret;

  agnocast_init_mutexes();

  ret = agnocast_init_sysfs();
  if (ret < 0) return ret;

  agnocast_init_device();

  ret = agnocast_init_kthread();
  if (ret < 0) return ret;

  ret = agnocast_init_kprobe();
  if (ret < 0) return ret;

  init_memory_allocator();

  return 0;
}

static void agnocast_test_suite_exit(struct kunit_suite * test_suite)
{
  agnocast_exit_sysfs();
  agnocast_exit_kthread();
  agnocast_exit_kprobe();
  agnocast_exit_device();
  exit_memory_allocator();
}

struct kunit_suite agnocast_test_suite = {
  .name = "agnocast_test_suite",
  .init = agnocast_test_init,
  .exit = agnocast_test_exit,
  .suite_init = agnocast_test_suite_init,
  .suite_exit = agnocast_test_suite_exit,
  .test_cases = agnocast_test_cases,
};

kunit_test_suite(agnocast_test_suite);
