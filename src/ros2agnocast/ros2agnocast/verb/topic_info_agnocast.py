import ctypes
import sys
from ros2cli.node.strategy import add_arguments as add_strategy_node_arguments
from ros2cli.node.strategy import NodeStrategy
from ros2topic.api import get_topic_names_and_types
from ros2topic.api import TopicNameCompleter
from ros2node.verb import VerbExtension

class TopicInfoRet(ctypes.Structure):
    _fields_ = [
        ("node_name", ctypes.c_char * 256),
        ("qos_depth", ctypes.c_uint32),
        ("qos_is_transient_local", ctypes.c_bool),
    ]

class TopicInfoAgnocastVerb(VerbExtension):
    """Print information about a topic including Agnocast."""

    def add_arguments(self, parser, cli_name):
        add_strategy_node_arguments(parser)
        arg = parser.add_argument(
            'topic_name',
            help="Name of the ROS topic to get info (e.g. '/chatter') including Agnocast.")
        parser.add_argument(
            '--verbose',
            '-v',
            action='store_true',
            help='Prints detailed information like the node name, node namespace, topic type, '
                 'topic type hash, GUID, and QoS Profile of the publishers and subscribers to '
                 'this topic. In case of Agnocast, only the supported QoS parameters are '
                 'displayed')
        arg.completer = TopicNameCompleter(
            include_hidden_topics_key='include_hidden_topics')

    def split_full_node_name(self, full_node_name):
        full_node_name = full_node_name.rstrip("/") if full_node_name != "/" else full_node_name
        namespace, _, node_name = full_node_name.rpartition("/")
        namespace = namespace if namespace else "/"
        return namespace, node_name

    def print_publishers_info(self, node, topic_name, pub_topic_info_rets, args, line_end):
        agnocast_pub_count = len(pub_topic_info_rets)
        print('ROS 2 Publisher count: %d' % node.count_publishers(topic_name))
        print('Agnocast Publisher count: %d' % agnocast_pub_count, end=line_end)

        if args.verbose:
            try:
                for info in node.get_publishers_info_by_topic(topic_name):
                    full_node_name = f"{info.node_namespace.rstrip('/')}/{info.node_name.lstrip('/')}"
                    print('Node name: %s' % info.node_name)
                    print('Node namespace: %s' % info.node_namespace)
                    print('Topic type: %s' % info.topic_type)
                    if full_node_name in [info['node_name'] for info in pub_topic_info_rets]:
                        print('Endpoint type: %s (Agnocast enabled)' % info.endpoint_type.name)
                    else:
                        print('Endpoint type: %s' % info.endpoint_type.name)
                    print('GID: %s' % '.'.join(format(b, '02x') for b in info.endpoint_gid))
                    print('QoS profile:')
                    print('  Reliability: %s' % info.qos_profile.reliability.name)
                    print('  History (Depth): %s (%d)' % (info.qos_profile.history.name, info.qos_profile.depth))
                    print('  Durability: %s' % info.qos_profile.durability.name)
                    print('  Lifespan: %s' % info.qos_profile.lifespan)
                    print('  Deadline: %s' % info.qos_profile.deadline)
                    print('  Liveliness: %s' % info.qos_profile.liveliness.name)
                    print('  Liveliness lease duration: %s' % info.qos_profile.liveliness_lease_duration, end=line_end)
            except NotImplementedError as e:
                return str(e)

    def print_subscribers_info(self, node, topic_name, topic_types, sub_topic_info_rets, args, line_end):
        agnocast_sub_count = len(sub_topic_info_rets)
        print('ROS 2 Subscription count: %d' % node.count_subscribers(topic_name))
        print('Agnocast Subscription count: %d' % agnocast_sub_count, end=line_end)

        if args.verbose:
            try:
                for info in node.get_subscriptions_info_by_topic(topic_name):
                    print(info, end=line_end)
                for info in sub_topic_info_rets:
                    nodespace, node_name = self.split_full_node_name(info['node_name'])
                    print('Node name: %s' % node_name)
                    print('Node namespace: %s' % nodespace)
                    print('Topic type: %s' % topic_types)
                    print('Endpoint type: SUBSCRIPTION (Agnocast enabled)')
                    print('QoS profile:')
                    print('  History (Depth): KEEP_LAST (%d)' % info['qos_depth'])
                    if info['qos_is_transient_local']:
                        print('  Durability: TRANSIENT_LOCAL', end=line_end)
                    else:
                        print('  Durability: VOLATILE', end=line_end)
            except NotImplementedError as e:
                return str(e)

    def main(self, *, args):
        with NodeStrategy(None) as node:
            lib = ctypes.CDLL("libagnocast_ioctl_wrapper.so")
            lib.get_agnocast_sub_nodes.argtypes = [ctypes.c_char_p, ctypes.POINTER(ctypes.c_int)]
            lib.get_agnocast_sub_nodes.restype = ctypes.POINTER(TopicInfoRet)
            lib.get_agnocast_pub_nodes.argtypes = [ctypes.c_char_p, ctypes.POINTER(ctypes.c_int)]
            lib.get_agnocast_pub_nodes.restype = ctypes.POINTER(TopicInfoRet)          
            lib.free_agnocast_topic_info_ret.argtypes = [ctypes.POINTER(TopicInfoRet)]
            lib.free_agnocast_topic_info_ret.restype = None

            topic_name = args.topic_name
            topic_name_byte = topic_name.encode('utf-8')

            # get agnocast sub node list
            sub_topic_info_ret_count = ctypes.c_int()
            sub_topic_info_ret_array = lib.get_agnocast_sub_nodes(topic_name_byte, ctypes.byref(sub_topic_info_ret_count))
            sub_topic_info_rets = []
            for i in range(sub_topic_info_ret_count.value):
                sub_topic_info_rets.append({
                    "node_name": sub_topic_info_ret_array[i].node_name.decode('utf-8'),
                    "qos_depth": sub_topic_info_ret_array[i].qos_depth,
                    "qos_is_transient_local": sub_topic_info_ret_array[i].qos_is_transient_local,
                })
            if sub_topic_info_ret_count.value != 0 and sub_topic_info_ret_array is not None:
                lib.free_agnocast_topic_info_ret(sub_topic_info_ret_array)

            # get agnocast pub node list
            pub_topic_info_ret_count = ctypes.c_int()
            pub_topic_info_ret_array = lib.get_agnocast_pub_nodes(topic_name_byte, ctypes.byref(pub_topic_info_ret_count))
            pub_topic_info_rets = []
            for i in range(pub_topic_info_ret_count.value):
                pub_topic_info_rets.append({
                    "node_name": pub_topic_info_ret_array[i].node_name.decode('utf-8'),
                    "qos_depth": pub_topic_info_ret_array[i].qos_depth,
                    "qos_is_transient_local": pub_topic_info_ret_array[i].qos_is_transient_local,
                })
            if pub_topic_info_ret_count.value != 0 and pub_topic_info_ret_array is not None:
                lib.free_agnocast_topic_info_ret(pub_topic_info_ret_array)

            # get ros2 topic list
            topic_names_and_types = get_topic_names_and_types(node=node, include_hidden_topics=True)

            topic_types = None
            for (t_name, t_types) in topic_names_and_types:
                if t_name == topic_name:
                    topic_types = t_types
                    break

            # check if topic exists
            if topic_types is None:
                if sub_topic_info_ret_count.value == 0 and pub_topic_info_ret_count.value == 0:
                    return 'Unkown topic: %s' % topic_name
                else:
                    topic_types = '<UNKNOWN>'

            ########################################################################
            # print topic info
            ########################################################################
            line_end = '\n'
            if args.verbose:
                line_end = '\n\n'
            type_str = topic_types[0] if len(topic_types) == 1 else topic_types
            print('Type: %s' % type_str, end=line_end)

            print_publishers_info_ret = self.print_publishers_info(node, topic_name, pub_topic_info_rets, args, line_end)
            if print_publishers_info_ret:
                return print_publishers_info_ret
            print_subscribers_info_ret = self.print_subscribers_info(node, topic_name, type_str, sub_topic_info_rets, args, line_end)
            if print_subscribers_info_ret:
                return print_subscribers_info_ret
            ########################################################################
