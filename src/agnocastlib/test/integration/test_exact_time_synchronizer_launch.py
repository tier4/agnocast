# Copyright 2025 The Autoware Contributors
# SPDX-License-Identifier: Apache-2.0

import os
import unittest

import launch
import launch_testing
import launch_testing.actions
import launch_testing.asserts
from launch_ros.actions import ComposableNodeContainer
from launch_ros.descriptions import ComposableNode


def generate_test_description():
    publisher_container = ComposableNodeContainer(
        name='publisher_container',
        namespace='',
        package='agnocastlib',
        executable='agnocast_component_container_mt',
        composable_node_descriptions=[
            ComposableNode(
                package='agnocastlib',
                plugin='agnocastlib_test::TestExactTimePublisherComponent',
                name='test_exact_time_publisher',
            ),
        ],
        output='screen',
        additional_env={
            'LD_PRELOAD': f"libagnocast_heaphook.so:{os.getenv('LD_PRELOAD', '')}",
            'AGNOCAST_MEMPOOL_SIZE': '134217728',
        }
    )

    # Test all callback interface types
    subscriber_plugins = [
        ('agnocastlib_test::TestMemberFunctionCallback', 'test_member_function'),
        ('agnocastlib_test::TestFreeFunctionCallback', 'test_free_function'),
        ('agnocastlib_test::TestLambda9ArgsCallback', 'test_lambda_9args'),
        ('agnocastlib_test::TestStdFunctionCallback', 'test_std_function'),
        ('agnocastlib_test::TestStdBindCallback', 'test_std_bind'),
        ('agnocastlib_test::TestConnectInputCallback', 'test_connect_input'),
        ('agnocastlib_test::TestSubscriberDirectCallback', 'test_subscriber_direct'),
    ]

    subscriber_container = ComposableNodeContainer(
        name='subscriber_container',
        namespace='',
        package='agnocastlib',
        executable='agnocast_component_container_mt',
        composable_node_descriptions=[
            ComposableNode(
                package='agnocastlib',
                plugin=plugin,
                name=name,
            )
            for plugin, name in subscriber_plugins
        ],
        output='screen',
        additional_env={
            'LD_PRELOAD': f"libagnocast_heaphook.so:{os.getenv('LD_PRELOAD', '')}",
            'AGNOCAST_MEMPOOL_SIZE': '134217728',
        }
    )

    return (
        launch.LaunchDescription([
            subscriber_container,
            launch.actions.TimerAction(period=1.0, actions=[publisher_container]),
            launch_testing.actions.ReadyToTest()
        ]),
        {
            'subscriber_container': subscriber_container
        }
    )


class TestExactTimeSynchronizer(unittest.TestCase):

    def test_member_function_callback(self, proc_output, subscriber_container):
        proc_output.assertWaitFor(
            'MemberFunction: Synchronized',
            timeout=30.0,
            process=subscriber_container
        )

    def test_free_function_callback(self, proc_output, subscriber_container):
        proc_output.assertWaitFor(
            'FreeFunction: Synchronized',
            timeout=30.0,
            process=subscriber_container
        )

    def test_lambda_9args_callback(self, proc_output, subscriber_container):
        proc_output.assertWaitFor(
            'Lambda9Args: Synchronized',
            timeout=30.0,
            process=subscriber_container
        )

    def test_std_function_callback(self, proc_output, subscriber_container):
        proc_output.assertWaitFor(
            'StdFunction: Synchronized',
            timeout=30.0,
            process=subscriber_container
        )

    def test_std_bind_callback(self, proc_output, subscriber_container):
        proc_output.assertWaitFor(
            'StdBind: Synchronized',
            timeout=30.0,
            process=subscriber_container
        )

    def test_connect_input_callback(self, proc_output, subscriber_container):
        proc_output.assertWaitFor(
            'ConnectInput: Synchronized',
            timeout=30.0,
            process=subscriber_container
        )

    def test_signal1_subscriber_direct_callback(self, proc_output, subscriber_container):
        proc_output.assertWaitFor(
            'Signal1-Sub1: Received',
            timeout=30.0,
            process=subscriber_container
        )
        proc_output.assertWaitFor(
            'Signal1-Sub2: Received',
            timeout=30.0,
            process=subscriber_container
        )
