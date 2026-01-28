import os
import unittest
import yaml
import launch_testing
import launch_testing.asserts
import launch_testing.markers
from launch import LaunchDescription
from launch.actions import SetEnvironmentVariable, TimerAction
from launch_ros.actions import ComposableNodeContainer
from launch_ros.descriptions import ComposableNode

CONFIG_PATH = os.path.join(os.path.dirname(__file__), 'config_test_1to1_ros2_to_agnocast.yaml')

EXPECT_INIT_PUB_NUM: int = 0
EXPECT_PUB_NUM: int = 0
EXPECT_INIT_SUB_NUM: int = 0
EXPECT_SUB_NUM: int = 0

TIMEOUT = os.environ.get('STRESS_TEST_TIMEOUT')
FOREVER = True if (os.environ.get('STRESS_TEST_TIMEOUT')) else False

def calc_expect_pub_sub_num(config: dict) -> None:
    global EXPECT_PUB_NUM, EXPECT_INIT_PUB_NUM, EXPECT_INIT_SUB_NUM, EXPECT_SUB_NUM
    
    EXPECT_INIT_PUB_NUM = config['pub_qos_depth'] if (
        config['launch_pub_before_sub'] and config['pub_transient_local']) else 0
    EXPECT_PUB_NUM = config['pub_qos_depth']

    is_pub_volatile = not config['pub_transient_local']
    is_sub_transient_local = config['sub_transient_local']

    if is_pub_volatile and is_sub_transient_local:
        EXPECT_SUB_NUM = 0
        EXPECT_INIT_SUB_NUM = 0
    else:
        EXPECT_SUB_NUM = min(EXPECT_PUB_NUM, config['sub_qos_depth'])
        
        if config['launch_pub_before_sub'] and not is_pub_volatile and is_sub_transient_local:
            EXPECT_INIT_SUB_NUM = min(EXPECT_INIT_PUB_NUM, config['sub_qos_depth'])
        else:
            EXPECT_INIT_SUB_NUM = 0

def calc_action_delays(config: dict) -> tuple:
    unit_delay = 1.0
    pub_delay = 0.0 if config['launch_pub_before_sub'] else unit_delay
    sub_delay = 0.01 * EXPECT_INIT_PUB_NUM + unit_delay if config['launch_pub_before_sub'] else 0.0
    buffer_time = 10.0
    ready_delay = float(TIMEOUT) if TIMEOUT else pub_delay + sub_delay + buffer_time
    return pub_delay, sub_delay, ready_delay

def generate_test_description():
    with open(CONFIG_PATH, 'r') as f:
        config = yaml.safe_load(f)
    calc_expect_pub_sub_num(config)
    pub_delay, sub_delay, ready_delay = calc_action_delays(config)

    # ROS 2 Publisher Node
    pub_node = TimerAction(
        period=pub_delay,
        actions=[
            ComposableNodeContainer(
                name='test_ros2_pub_container',
                namespace='',
                package='rclcpp_components',
                executable='component_container',
                composable_node_descriptions=[
                    ComposableNode(
                        package='agnocast_e2e_test',
                        plugin='TestROS2Publisher',
                        name='test_ros2_publisher',
                        parameters=[{
                            "qos_depth": config['pub_qos_depth'],
                            "transient_local": config['pub_transient_local'],
                            "init_pub_num": EXPECT_INIT_PUB_NUM,
                            "pub_num": EXPECT_PUB_NUM,
                            "planned_sub_count": 1 if EXPECT_SUB_NUM > 0 else 0,
                            "forever": FOREVER
                        }],
                    )
                ],
                output='screen',
            )
        ]
    )

    # Agnocast Subscriber
    plugin_name = 'TestTakeSubscriber' if config.get('use_take_sub') else 'TestSubscriber'
    sub_nodes = TimerAction(
        period=sub_delay,
        actions=[
            ComposableNodeContainer(
                name='test_agno_sub_container',
                namespace='',
                package='agnocastlib',
                executable='agnocast_component_container',
                composable_node_descriptions=[
                    ComposableNode(
                        package='agnocast_e2e_test',
                        plugin=plugin_name,
                        name='test_agnocast_subscriber',
                        parameters=[{
                            "qos_depth": config['sub_qos_depth'],
                            "transient_local": config['sub_transient_local'],
                            "sub_num": EXPECT_INIT_SUB_NUM + EXPECT_SUB_NUM,
                            "forever": FOREVER
                        }],
                    )
                ],
                output='screen',
                additional_env={
                    'LD_PRELOAD': f"libagnocast_heaphook.so:{os.getenv('LD_PRELOAD', '')}",
                    'AGNOCAST_MEMPOOL_SIZE': '134217728',
                }
            )
        ]
    )

    return (
        LaunchDescription([
            SetEnvironmentVariable('RCUTILS_LOGGING_BUFFERED_STREAM', '0'),
            pub_node,
            sub_nodes,
            TimerAction(period=ready_delay, actions=[launch_testing.actions.ReadyToTest()])
        ]),
        {
            'test_pub': pub_node.actions[0],
            'test_agno_sub': sub_nodes.actions[0],
        }
    )

class Test1To1WithRos2Pub(unittest.TestCase):

    def test_pub_log(self, proc_output, test_pub):
        with launch_testing.asserts.assertSequentialStdout(proc_output, process=test_pub) as cm:
            output = "".join(cm._output)
            total_expected = EXPECT_INIT_PUB_NUM + EXPECT_PUB_NUM
            for i in range(total_expected):
                self.assertEqual(output.count(f"Publishing {i}."), 1)
            self.assertEqual(output.count("All messages published. Shutting down."), 1)

    def test_agno_sub_log(self, proc_output, test_agno_sub):
        with launch_testing.asserts.assertSequentialStdout(proc_output, process=test_agno_sub) as cm:
            output = "".join(cm._output)
            expected_total = EXPECT_INIT_SUB_NUM + EXPECT_SUB_NUM
            start_index = EXPECT_INIT_PUB_NUM - EXPECT_INIT_SUB_NUM
            
            # The R2A bridge's ROS 2 Subscriber inherits QoS settings from the Agnocast Subscriber.
            # Consequently, incompatible settings (e.g., Volatile Pub vs. Transient Local Sub) result in no communication.
            # This check confirms that the connection is correctly rejected.
            if expected_total == 0:
                self.assertEqual(output.count("Receiving"), 0)

                # Startup timing determines which node logs the warning, so we scan the full log output.
                full_log = "".join([
                    line.text.decode() if isinstance(line.text, bytes) else line.text 
                    for line in proc_output
                ])
                self.assertIn("incompatible QoS", full_log)
            else:
                for i in range(start_index, start_index + expected_total):
                    self.assertEqual(output.count(f"Receiving {i}."), 1)
                self.assertEqual(output.count("All messages received. Shutting down."), 1)
