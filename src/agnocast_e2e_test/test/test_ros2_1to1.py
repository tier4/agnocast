import os
import unittest

import launch_testing
import launch_testing.asserts
import launch_testing.markers
import yaml
from launch import LaunchDescription
from launch.actions import SetEnvironmentVariable, TimerAction
from launch_ros.actions import ComposableNodeContainer
from launch_ros.descriptions import ComposableNode

CONFIG_PATH = os.path.join(os.path.dirname(__file__), 'config_test_ros2_1to1.yaml')

EXPECT_INIT_ROS2_PUB_NUM: int
EXPECT_ROS2_PUB_NUM: int
EXPECT_INIT_ROS2_SUB_NUM: int
EXPECT_ROS2_SUB_NUM: int

TIMEOUT = os.environ.get('STRESS_TEST_TIMEOUT')
FOREVER = True if (os.environ.get('STRESS_TEST_TIMEOUT')) else False

def calc_expect_pub_sub_num(config: dict) -> None:
    global EXPECT_ROS2_PUB_NUM, EXPECT_INIT_ROS2_PUB_NUM, EXPECT_INIT_ROS2_SUB_NUM, EXPECT_ROS2_SUB_NUM

    EXPECT_INIT_ROS2_PUB_NUM = config['pub_qos_depth'] if (
        config['launch_pub_before_sub'] and config['pub_transient_local']) else 0
    EXPECT_ROS2_PUB_NUM = config['pub_qos_depth']

    EXPECT_ROS2_SUB_NUM = min(EXPECT_ROS2_PUB_NUM, config['sub_qos_depth'])

    if config['sub_transient_local']:
        EXPECT_INIT_ROS2_SUB_NUM = min(
            EXPECT_INIT_ROS2_PUB_NUM, config['sub_qos_depth']) if config['pub_transient_local'] else 0
    else:
        EXPECT_INIT_ROS2_SUB_NUM = 0

def calc_action_delays(config: dict) -> tuple:
    unit_delay = 1.0
    pub_delay = 0.0 if config['launch_pub_before_sub'] else unit_delay
    sub_delay = 0.01 * EXPECT_INIT_ROS2_PUB_NUM + unit_delay if config['launch_pub_before_sub'] else 0.0
    ready_delay = float(TIMEOUT) if TIMEOUT else pub_delay + sub_delay + 10.0
    return pub_delay, sub_delay, ready_delay

def generate_test_description():
    with open(CONFIG_PATH, 'r') as f:
        config = yaml.safe_load(f)
    
    calc_expect_pub_sub_num(config)
    pub_delay, sub_delay, ready_delay = calc_action_delays(config)

    pub_node = TimerAction(
        period=pub_delay,
        actions=[
            ComposableNodeContainer(
                name='test_ros2_talker_container',
                namespace='',
                package='rclcpp_components',
                executable='component_container',
                composable_node_descriptions=[
                    ComposableNode(
                        package='agnocast_e2e_test',
                        plugin='TestROS2Publisher',
                        name='test_ros2_talker_node',
                        parameters=[
                            {
                                "qos_depth": config['pub_qos_depth'],
                                "transient_local": config['pub_transient_local'],
                                "init_pub_num": EXPECT_INIT_ROS2_PUB_NUM,
                                "pub_num": EXPECT_ROS2_PUB_NUM,
                                "forever": FOREVER
                            }
                        ],
                    )
                ],
                output='screen',
            )
        ]
    )

    sub_node = TimerAction(
        period=sub_delay,
        actions=[
            ComposableNodeContainer(
                name='test_ros2_listener_container',
                namespace='',
                package='rclcpp_components',
                executable='component_container',
                composable_node_descriptions=[
                    ComposableNode(
                        package='agnocast_e2e_test',
                        plugin='TestROS2Subscriber',
                        name='test_ros2_subscriber_node',
                        parameters=[
                            {
                                "qos_depth": config['sub_qos_depth'],
                                "transient_local": config['sub_transient_local'],
                                "sub_num": EXPECT_INIT_ROS2_SUB_NUM + EXPECT_ROS2_SUB_NUM,
                                "forever": FOREVER
                            }
                        ],
                    )
                ],
                output='screen',
            )
        ]
    )

    return (
        LaunchDescription(
        [
            SetEnvironmentVariable('RCUTILS_LOGGING_BUFFERED_STREAM', '0'),
            pub_node,
            sub_node,
            TimerAction(period=ready_delay, actions=[launch_testing.actions.ReadyToTest()])
        ]
        ),
        {
            'test_ros2_pub': pub_node.actions[0],
            'test_ros2_sub': sub_node.actions[0],
        }
    )

class TestParameterizedPubSub(unittest.TestCase):
    def test_ros2_pub(self, proc_output, test_ros2_pub):
        with launch_testing.asserts.assertSequentialStdout(proc_output, process=test_ros2_pub) as cm:
            proc_output = "".join(cm._output)

            # The display order is not guaranteed, so the message order is not checked.
            for i in range(EXPECT_INIT_ROS2_PUB_NUM + EXPECT_ROS2_PUB_NUM):
                self.assertEqual(proc_output.count(f"Publishing {i}."), 1)
            self.assertEqual(proc_output.count("All messages published. Shutting down."), 1)

    def test_ros2_sub(self, proc_output, test_ros2_sub):
        with launch_testing.asserts.assertSequentialStdout(proc_output, process=test_ros2_sub) as cm:
            proc_output = "".join(cm._output)

            # The display order is not guaranteed, so the message order is not checked.
            for i in range(EXPECT_INIT_ROS2_PUB_NUM - EXPECT_INIT_ROS2_SUB_NUM, EXPECT_ROS2_SUB_NUM):
                self.assertEqual(proc_output.count(f"Receiving {i}."), 1)
            self.assertEqual(proc_output.count("All messages received. Shutting down."), 1)