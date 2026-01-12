import unittest

import launch
import launch.actions
import launch_ros.actions
import launch_testing
import launch_testing.actions
import launch_testing.asserts


def generate_test_description():
    thread_configurator_node = launch_ros.actions.Node(
        package='cie_thread_configurator',
        executable='thread_configurator_node',
        name='thread_configurator_node',
        output='screen',
        arguments=['--prerun']
    )

    test_publisher_node = launch_ros.actions.Node(
        package='agnocast_e2e_test',
        executable='test_agnocast_only_publisher_node',
        name='test_agnocast_only_publisher',
        output='screen',
        additional_env={
            'LD_PRELOAD': 'libagnocast_heaphook.so',
            'AGNOCAST_MEMPOOL_SIZE': '134217728',
        }
    )

    test_subscriber_node = launch_ros.actions.Node(
        package='agnocast_e2e_test',
        executable='test_agnocast_only_subscriber_node',
        name='test_agnocast_only_subscriber',
        output='screen',
        additional_env={
            'LD_PRELOAD': 'libagnocast_heaphook.so',
            'AGNOCAST_MEMPOOL_SIZE': '134217728',
        }
    )

    return (
        launch.LaunchDescription([
            launch.actions.SetEnvironmentVariable('RCUTILS_LOGGING_BUFFERED_STREAM', '0'),
            thread_configurator_node,
            launch.actions.TimerAction(
                period=3.0,
                actions=[test_publisher_node, test_subscriber_node]
            ),
            launch.actions.TimerAction(
                period=6.0,
                actions=[launch_testing.actions.ReadyToTest()]
            )
        ]),
        {
            'thread_configurator': thread_configurator_node,
            'test_publisher': test_publisher_node,
            'test_subscriber': test_subscriber_node
        }
    )


class TestAgnocastOnlyCallbackIsolatedExecutor(unittest.TestCase):

    def test_publisher_publishes(self, proc_output, test_publisher):
        proc_output.assertWaitFor(
            'Publishing:',
            timeout=10.0,
            process=test_publisher
        )

    def test_subscriber_receives(self, proc_output, test_subscriber):
        proc_output.assertWaitFor(
            'Received:',
            timeout=10.0,
            process=test_subscriber
        )

    def test_thread_configurator_receives_callback_info(self, proc_output, thread_configurator):
        with launch_testing.asserts.assertSequentialStdout(proc_output, process=thread_configurator) as cm:
            output_text = "".join(cm._output)
            callback_info_count = output_text.count('Received CallbackGroupInfo:')

            self.assertEqual(
                callback_info_count, 3,
                f"Expected at least 3 'Received CallbackGroupInfo:' messages, but got {callback_info_count}"
            )


@launch_testing.post_shutdown_test()
class TestAgnocastOnlyCallbackIsolatedExecutorShutdown(unittest.TestCase):

    def test_exit_code(self, proc_info):
        # Accept SIGINT (-2) and SIGKILL (-9) for test nodes
        launch_testing.asserts.assertExitCodes(proc_info, allowable_exit_codes=[0, -2, -9])

    def test_cleanup(self):
        import os
        template_yaml = os.path.join(os.path.expanduser("~"), "agnocast", "template.yaml")
        if os.path.exists(template_yaml):
            os.remove(template_yaml)
