import ctypes
import sys

import rclpy
from rclpy.qos import QoSDurabilityPolicy
from rclpy.qos import QoSHistoryPolicy
from rclpy.qos import QoSProfile
from rclpy.qos import QoSReliabilityPolicy
from ros2cli.node.strategy import add_arguments as add_strategy_node_arguments
from ros2cli.node.strategy import NodeStrategy
from ros2topic.api import get_msg_class
from ros2topic.api import TopicNameCompleter
from ros2topic.verb import VerbExtension
from rosidl_runtime_py import message_to_yaml


class TopicInfoRet(ctypes.Structure):
    _fields_ = [
        ("node_name", ctypes.c_char * 256),
        ("qos_depth", ctypes.c_uint32),
        ("qos_is_transient_local", ctypes.c_bool),
        ("qos_is_reliable", ctypes.c_bool),
        ("is_bridge", ctypes.c_bool),
    ]


class EchoAgnocastVerb(VerbExtension):
    """Echo messages from a topic (Agnocast enabled)."""

    def add_arguments(self, parser, cli_name):
        add_strategy_node_arguments(parser)
        arg = parser.add_argument(
            'topic_name',
            help="Name of the ROS topic to echo (e.g. '/chatter')")
        arg.completer = TopicNameCompleter(
            include_hidden_topics_key='include_hidden_topics')
        parser.add_argument(
            '--once',
            action='store_true',
            help='Print the first message received and then exit')
        parser.add_argument(
            '--timeout',
            metavar='N',
            type=float,
            default=None,
            help='Maximum time to wait for a message (in seconds)')
        parser.add_argument(
            '--no-agnocast-check',
            action='store_true',
            help='Skip checking if topic has Agnocast publishers')
        parser.add_argument(
            '--qos-depth',
            metavar='N',
            type=int,
            default=10,
            help='QoS history depth (default: 10)')
        parser.add_argument(
            '--qos-reliability',
            choices=['reliable', 'best_effort'],
            default='best_effort',
            help='QoS reliability (default: best_effort)')
        parser.add_argument(
            '--qos-durability',
            choices=['volatile', 'transient_local'],
            default='volatile',
            help='QoS durability (default: volatile)')

    def get_agnocast_pub_count(self, topic_name):
        """Get the count of Agnocast publishers for a topic."""
        try:
            lib = ctypes.CDLL("libagnocast_ioctl_wrapper.so")
            lib.get_agnocast_pub_nodes.argtypes = [ctypes.c_char_p, ctypes.POINTER(ctypes.c_int)]
            lib.get_agnocast_pub_nodes.restype = ctypes.POINTER(TopicInfoRet)
            lib.free_agnocast_topic_info_ret.argtypes = [ctypes.POINTER(TopicInfoRet)]
            lib.free_agnocast_topic_info_ret.restype = None

            topic_name_byte = topic_name.encode('utf-8')
            pub_count = ctypes.c_int()
            pub_array = lib.get_agnocast_pub_nodes(topic_name_byte, ctypes.byref(pub_count))

            if pub_count.value != 0 and pub_array is not None:
                lib.free_agnocast_topic_info_ret(pub_array)

            return pub_count.value
        except OSError:
            return 0

    def get_agnocast_sub_count(self, topic_name):
        """Get the count of Agnocast subscribers for a topic."""
        try:
            lib = ctypes.CDLL("libagnocast_ioctl_wrapper.so")
            lib.get_agnocast_sub_nodes.argtypes = [ctypes.c_char_p, ctypes.POINTER(ctypes.c_int)]
            lib.get_agnocast_sub_nodes.restype = ctypes.POINTER(TopicInfoRet)
            lib.free_agnocast_topic_info_ret.argtypes = [ctypes.POINTER(TopicInfoRet)]
            lib.free_agnocast_topic_info_ret.restype = None

            topic_name_byte = topic_name.encode('utf-8')
            sub_count = ctypes.c_int()
            sub_array = lib.get_agnocast_sub_nodes(topic_name_byte, ctypes.byref(sub_count))

            if sub_count.value != 0 and sub_array is not None:
                lib.free_agnocast_topic_info_ret(sub_array)

            return sub_count.value
        except OSError:
            return 0

    def main(self, *, args):
        topic_name = args.topic_name
        if not topic_name.startswith('/'):
            topic_name = '/' + topic_name

        # Check for Agnocast publishers unless disabled
        if not args.no_agnocast_check:
            agnocast_pub_count = self.get_agnocast_pub_count(topic_name)
            agnocast_sub_count = self.get_agnocast_sub_count(topic_name)

            if agnocast_pub_count > 0:
                print(f"Topic '{topic_name}' has {agnocast_pub_count} Agnocast publisher(s)")
            if agnocast_sub_count > 0:
                print(f"Topic '{topic_name}' has {agnocast_sub_count} Agnocast subscriber(s)")
            if agnocast_pub_count == 0 and agnocast_sub_count == 0:
                print(f"Note: Topic '{topic_name}' has no Agnocast publishers or subscribers",
                      file=sys.stderr)
            print()

        return self.subscribe_and_echo(args, topic_name)

    def subscribe_and_echo(self, args, topic_name):
        with NodeStrategy(args) as node:
            # Determine message type
            msg_class = get_msg_class(node, topic_name, blocking=True, include_hidden_topics=True)
            if msg_class is None:
                return f"Could not determine message type for topic: {topic_name}"

            # Build QoS profile
            reliability = (QoSReliabilityPolicy.RELIABLE if args.qos_reliability == 'reliable'
                           else QoSReliabilityPolicy.BEST_EFFORT)
            durability = (QoSDurabilityPolicy.TRANSIENT_LOCAL if args.qos_durability == 'transient_local'
                          else QoSDurabilityPolicy.VOLATILE)
            qos_profile = QoSProfile(
                depth=args.qos_depth,
                reliability=reliability,
                durability=durability,
                history=QoSHistoryPolicy.KEEP_LAST
            )

            # Use future for --once mode
            future = None
            if args.once:
                future = rclpy.task.Future()

            def callback(msg):
                # Check if we should still process messages (for --once mode)
                if future is not None and future.done():
                    return
                print('---')
                print(message_to_yaml(msg))
                if future is not None and not future.done():
                    future.set_result(True)

            # Create subscription
            node.create_subscription(
                msg_class,
                topic_name,
                callback,
                qos_profile)

            # Spin with appropriate mode
            try:
                if args.timeout is not None:
                    timeout_future = rclpy.task.Future()
                    _timer = node.create_timer(args.timeout, lambda: timeout_future.set_result(True)
                                               if not timeout_future.done() else None)

                    if future is not None:
                        # Wait for either message or timeout
                        def check_done():
                            return future.done() or timeout_future.done()

                        while not check_done():
                            rclpy.spin_once(node, timeout_sec=0.1)

                        if timeout_future.done() and not future.done():
                            return f"Timeout: No message received within {args.timeout} seconds"
                    else:
                        # Wait for timeout
                        rclpy.spin_until_future_complete(node, timeout_future)
                elif future is not None:
                    # Wait for first message
                    rclpy.spin_until_future_complete(node, future)
                else:
                    # Continuous spinning
                    rclpy.spin(node)
            except KeyboardInterrupt:
                pass
