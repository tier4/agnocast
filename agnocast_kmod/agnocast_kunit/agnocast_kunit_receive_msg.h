#pragma once
#include <kunit/test.h>

#define TEST_CASES_RECEIVE_MSG                                                                      \
  KUNIT_CASE(test_case_receive_msg_no_topic_when_receive),                                          \
    KUNIT_CASE(test_case_receive_msg_no_subscriber_when_receive),                                   \
    KUNIT_CASE(test_case_receive_msg_no_publish_no_receive),                                        \
    KUNIT_CASE(test_case_receive_msg_receive_one),                                                  \
    KUNIT_CASE(                                                                                     \
      test_case_receive_msg_sub_qos_depth_smaller_than_publish_num_smaller_than_pub_qos_depth),     \
    KUNIT_CASE(                                                                                     \
      test_case_receive_msg_publish_num_smaller_than_sub_qos_depth_smaller_than_pub_qos_depth),     \
    KUNIT_CASE(                                                                                     \
      test_case_receive_msg_sub_qos_depth_smaller_than_pub_qos_depth_smaller_than_publish_num),     \
    KUNIT_CASE(                                                                                     \
      test_case_receive_msg_publish_num_and_sub_qos_depth_and_pub_qos_depth_are_all_max_qos_depth), \
    KUNIT_CASE(test_case_receive_msg_too_many_rc), KUNIT_CASE(test_case_receive_msg_one_new_pub),   \
    KUNIT_CASE(test_case_receive_msg_pubsub_in_same_process),                                       \
    KUNIT_CASE(test_case_receive_msg_2pub_in_same_process),                                         \
    KUNIT_CASE(test_case_receive_msg_2sub_in_same_process),                                         \
    KUNIT_CASE(test_case_receive_msg_too_many_mapping_processes)

void test_case_receive_msg_no_topic_when_receive(struct kunit * test);
void test_case_receive_msg_no_subscriber_when_receive(struct kunit * test);
void test_case_receive_msg_no_publish_no_receive(struct kunit * test);
void test_case_receive_msg_receive_one(struct kunit * test);
void test_case_receive_msg_sub_qos_depth_smaller_than_publish_num_smaller_than_pub_qos_depth(
  struct kunit * test);
void test_case_receive_msg_publish_num_smaller_than_sub_qos_depth_smaller_than_pub_qos_depth(
  struct kunit * test);
void test_case_receive_msg_sub_qos_depth_smaller_than_pub_qos_depth_smaller_than_publish_num(
  struct kunit * test);
void test_case_receive_msg_publish_num_and_sub_qos_depth_and_pub_qos_depth_are_all_max_qos_depth(
  struct kunit * test);
void test_case_receive_msg_too_many_rc(struct kunit * test);
void test_case_receive_msg_one_new_pub(struct kunit * test);
void test_case_receive_msg_pubsub_in_same_process(struct kunit * test);
void test_case_receive_msg_2pub_in_same_process(struct kunit * test);
void test_case_receive_msg_2sub_in_same_process(struct kunit * test);
void test_case_receive_msg_too_many_mapping_processes(struct kunit * test);
