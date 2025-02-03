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

CONFIG_PATH = os.path.join(os.path.dirname(__file__), 'config_test_2to2.yaml')
with open(CONFIG_PATH, 'r') as f:
    CONFIG = yaml.safe_load(f)
QOS_DEPTH = 10
PUB_NUM = int(QOS_DEPTH / 2)


@launch_testing.markers.keep_alive
def generate_test_description():
    pub_i = 0
    sub_i = 0
    containers = []
    testing_processes = {}
    for i, nodes in enumerate(CONFIG.values()):
        composable_nodes = []
        for node in nodes:
            if node == 'p':
                composable_nodes.append(
                    ComposableNode(
                        package='e2e_test',
                        plugin='TestPublisher',
                        name=f'test_talker_node_{pub_i}',
                        parameters=[
                            {
                                "qos_depth": QOS_DEPTH,
                                "transient_local": False,
                                "init_pub_num": 0,
                                "pub_num": PUB_NUM,
                                "planned_pub_count": 2,
                                "planned_sub_count": 2
                            }
                        ],
                    )
                )
                pub_i += 1
            else:  # s
                composable_nodes.insert(
                    0,
                    ComposableNode(
                        package='e2e_test',
                        plugin='TestSubscriber',
                        name=f'test_listener_node_{sub_i}',
                        parameters=[
                            {
                                "qos_depth": QOS_DEPTH,
                                "transient_local": False,
                                "sub_num": QOS_DEPTH,
                            }
                        ],
                    )
                )
                sub_i += 1

        container = ComposableNodeContainer(
            name=f'test_container_{i}',
            namespace='',
            package='agnocastlib',
            executable='agnocast_component_container_mt',
            composable_node_descriptions=composable_nodes,
            output='screen',
            additional_env={
                'LD_PRELOAD': f"libagnocast_heaphook.so:{os.getenv('LD_PRELOAD', '')}",
                'MEMPOOL_SIZE': '134217728',
            }
        )
        containers.append(container)
        testing_processes[f'container{i}'] = container

    return (
        LaunchDescription(
            [
                SetEnvironmentVariable('RCUTILS_LOGGING_BUFFERED_STREAM', '0'),
                *containers,
                TimerAction(period=8.0, actions=[launch_testing.actions.ReadyToTest()])
            ]
        ), testing_processes
    )


@launch_testing.post_shutdown_test()
class Test1To1(unittest.TestCase):
    pub_i_ = 0
    sub_i_ = 0

    def common_assert(self, proc_output, container_proc, nodes):
        if not nodes:
            return

        for node in nodes:
            if node == 'p':
                with launch_testing.asserts.assertSequentialStdout(proc_output, process=container_proc) as cm:
                    prefix = f"[test_talker_node_{self.pub_i_}]: "
                    for i in range(PUB_NUM):
                        cm.assertInStdout(f"{prefix}Publishing {i}.")
                    cm.assertInStdout(f"{prefix}All messages published. Shutting down.")
                    self.pub_i_ += 1
            else:  # s
                with launch_testing.asserts.assertSequentialStdout(proc_output, process=container_proc) as cm:
                    prefix = f"[test_listener_node_{self.sub_i_}]: "
                    # Not checking the order of the messages from the different publishers
                    for i in range(PUB_NUM):
                        cm.assertInStdout(f"{prefix}Receiving {i}.")
                    cm.assertInStdout(f"{prefix}All messages received. Shutting down.")

                    # Check the number of messages received
                    sub_count = "".join(cm._output).count(f"{prefix}Receiving ")
                    self.assertEqual(sub_count, PUB_NUM*2)

                    self.sub_i_ += 1

    def test_all_container(self, proc_output, container0, container1, container2, container3):
        nodes = CONFIG['container0']
        self.common_assert(proc_output, container0, nodes)

        nodes = CONFIG['container1']
        self.common_assert(proc_output, container1, nodes)

        nodes = CONFIG['container2']
        self.common_assert(proc_output, container2, nodes)

        nodes = CONFIG['container3']
        self.common_assert(proc_output, container3, nodes)
