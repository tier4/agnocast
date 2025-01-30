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

CONFIG_PATH = os.path.join(os.path.dirname(__file__), 'config_test_1to1_with_ros2sub.yaml')

EXPECT_INIT_PUB_NUM: int
EXPECT_PUB_NUM: int
EXPECT_INIT_SUB_NUM: int
EXPECT_SUB_NUM: int
EXPECT_INIT_ROS2_SUB_NUM: int
EXPECT_ROS2_SUB_NUM: int


def calc_expect_pub_sub_num(config: dict) -> None:
    global EXPECT_PUB_NUM, EXPECT_INIT_PUB_NUM, EXPECT_INIT_SUB_NUM, EXPECT_SUB_NUM, EXPECT_INIT_ROS2_SUB_NUM, EXPECT_ROS2_SUB_NUM

    EXPECT_INIT_PUB_NUM = config['pub_qos_depth'] if (
        config['launch_pub_before_sub'] and config['pub_transient_local']) else 0
    EXPECT_PUB_NUM = config['pub_qos_depth']

    EXPECT_ROS2_SUB_NUM = min(EXPECT_PUB_NUM, config['sub_qos_depth'])
    EXPECT_SUB_NUM = min(EXPECT_PUB_NUM, config['sub_qos_depth'])
    if config['sub_transient_local']:
        EXPECT_INIT_ROS2_SUB_NUM = min(
            EXPECT_INIT_PUB_NUM, config['sub_qos_depth']) if config['pub_transient_local'] else 0
        EXPECT_INIT_SUB_NUM = 0 if config['use_take_sub'] else min(
            EXPECT_INIT_PUB_NUM, config['sub_qos_depth'])
    else:
        EXPECT_INIT_ROS2_SUB_NUM = 0
        EXPECT_INIT_SUB_NUM = 0


def calc_action_delays(config: dict) -> tuple:
    unit_delay = 1.0
    pub_delay = 0.0 if config['launch_pub_before_sub'] else unit_delay
    sub_delay = 0.01 * EXPECT_INIT_PUB_NUM + unit_delay if config['launch_pub_before_sub'] else 0.0
    ready_delay = pub_delay + sub_delay + 5.0
    return pub_delay, sub_delay, ready_delay


@launch_testing.markers.keep_alive
def generate_test_description():
    with open(CONFIG_PATH, 'r') as f:
        config = yaml.safe_load(f)
    calc_expect_pub_sub_num(config)
    pub_delay, sub_delay, ready_delay = calc_action_delays(config)

    pub_node = TimerAction(
        period=pub_delay,
        actions=[
            ComposableNodeContainer(
                name='test_talker_container',
                namespace='',
                package='agnocastlib',
                executable='agnocast_component_container',
                composable_node_descriptions=[
                    ComposableNode(
                        package='e2e_test',
                        plugin='TestPublisher',
                        name='test_talker_node',
                        parameters=[
                            {
                                "qos_depth": config['pub_qos_depth'],
                                "transient_local": config['pub_transient_local'],
                                "init_pub_num": EXPECT_INIT_PUB_NUM,
                                "pub_num": EXPECT_PUB_NUM
                            }
                        ],
                    )
                ],
                output='screen',
                additional_env={
                    'LD_PRELOAD': f"libagnocast_heaphook.so:{os.getenv('LD_PRELOAD', '')}",
                    'MEMPOOL_SIZE': '134217728',
                }
            )
        ]
    )

    sub_nodes_actions = [
        ComposableNodeContainer(
            name='test_ros2_lister_container',
            namespace='',
            package='agnocastlib',
            executable='agnocast_component_container',
            composable_node_descriptions=[
                    ComposableNode(
                        package='e2e_test',
                        plugin='TestROS2Subscriber',
                        name='test_ros2_listener_node',
                        parameters=[
                            {"qos_depth": config['sub_qos_depth'],
                             "transient_local": config
                             ['sub_transient_local']
                             if config['pub_transient_local'] else False,
                             "sub_num": EXPECT_INIT_ROS2_SUB_NUM + EXPECT_ROS2_SUB_NUM}
                        ],
                    )
            ],
            output='screen',
        )
    ]
    if config['use_take_sub']:
        sub_nodes_actions.append(
            ComposableNodeContainer(
                name='test_taker_container',
                namespace='',
                package='agnocastlib',
                executable='agnocast_component_container',
                composable_node_descriptions=[
                    ComposableNode(
                        package='e2e_test',
                        plugin='TestTakeSubscriber',
                        name='test_taker_node',
                        parameters=[
                            {
                                "qos_depth": config['sub_qos_depth'],
                                "transient_local": config['sub_transient_local'],
                                "sub_num": EXPECT_INIT_SUB_NUM + EXPECT_SUB_NUM
                            }
                        ],
                    )
                ],
                output='screen',
                additional_env={
                    'LD_PRELOAD': f"libagnocast_heaphook.so:{os.getenv('LD_PRELOAD', '')}",
                    'MEMPOOL_SIZE': '134217728',
                }
            )
        )
    else:
        sub_nodes_actions.append(
            ComposableNodeContainer(
                name='test_lister_container',
                namespace='',
                package='agnocastlib',
                executable='agnocast_component_container',
                composable_node_descriptions=[
                    ComposableNode(
                        package='e2e_test',
                        plugin='TestSubscriber',
                        name='test_listener_node',
                        parameters=[
                            {
                                "qos_depth": config['sub_qos_depth'],
                                "transient_local": config['sub_transient_local'],
                                "sub_num": EXPECT_INIT_SUB_NUM + EXPECT_SUB_NUM
                            }
                        ],
                    )
                ],
                output='screen',
                additional_env={
                    'LD_PRELOAD': f"libagnocast_heaphook.so:{os.getenv('LD_PRELOAD', '')}",
                    'MEMPOOL_SIZE': '134217728',
                }
            )
        )

    sub_nodes = TimerAction(
        period=sub_delay,
        actions=sub_nodes_actions
    )

    return (
        LaunchDescription(
            [
                SetEnvironmentVariable('RCUTILS_LOGGING_BUFFERED_STREAM', '0'),
                pub_node,
                sub_nodes,
                TimerAction(period=ready_delay, actions=[launch_testing.actions.ReadyToTest()])
            ]
        ),
        {
            'test_pub': pub_node.actions[0],
            'test_ros2_sub': sub_nodes.actions[0],
            'test_sub': sub_nodes.actions[1],
        }
    )


@launch_testing.post_shutdown_test()
class Test1To1(unittest.TestCase):

    def test_pub(self, proc_output, test_pub):
        with launch_testing.asserts.assertSequentialStdout(proc_output, process=test_pub) as cm:
            for i in range(EXPECT_INIT_PUB_NUM + EXPECT_PUB_NUM):
                cm.assertInStdout(f"Publishing {i}.")
            cm.assertInStdout("All messages published. Shutting down.")

    def test_sub(self, proc_output, test_sub):
        with launch_testing.asserts.assertSequentialStdout(proc_output, process=test_sub) as cm:
            # Check the order of messages received
            for i in range(EXPECT_INIT_PUB_NUM - EXPECT_INIT_SUB_NUM, EXPECT_SUB_NUM):
                cm.assertInStdout(f"Receiving {i}.")
            cm.assertInStdout("All messages received. Shutting down.")

            # Check the number of messages received
            sub_count = "".join(cm._output).count("Receiving ")
            self.assertEqual(sub_count, EXPECT_INIT_SUB_NUM + EXPECT_SUB_NUM)

    def test_ros2_sub(self, proc_output, test_ros2_sub):
        with launch_testing.asserts.assertSequentialStdout(proc_output, process=test_ros2_sub) as cm:
            # Check the order of messages received
            for i in range(EXPECT_INIT_PUB_NUM - EXPECT_INIT_ROS2_SUB_NUM, EXPECT_ROS2_SUB_NUM):
                cm.assertInStdout(f"Receiving {i}.")
            cm.assertInStdout("All messages received. Shutting down.")

            # Check the number of messages received
            sub_count = "".join(cm._output).count("Receiving ")
            self.assertEqual(sub_count, EXPECT_INIT_ROS2_SUB_NUM + EXPECT_ROS2_SUB_NUM)
