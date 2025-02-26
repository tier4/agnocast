import ctypes
import sys
from ros2cli.node.strategy import add_arguments as add_strategy_node_arguments
from ros2cli.node.strategy import NodeStrategy
from ros2topic.api import get_topic_names_and_types
from ros2topic.api import TopicNameCompleter
from ros2node.verb import VerbExtension

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

    def main(self, *, args):
        with NodeStrategy(None) as node:
            lib = ctypes.CDLL("libagnocast_ioctl_wrapper.so")
            lib.get_agnocast_topic_list.argtype = [ctypes.POINTER(ctypes.c_int)]
            lib.get_agnocast_topic_list.restype = ctypes.POINTER(ctypes.POINTER(ctypes.c_char))
            lib.get_agnocast_sub_nodes.argtypes = [ctypes.c_char_p, ctypes.POINTER(ctypes.c_int)]
            lib.get_agnocast_sub_nodes.restype = ctypes.POINTER(ctypes.POINTER(ctypes.c_char))
            lib.get_agnocast_pub_nodes.argtypes = [ctypes.c_char_p, ctypes.POINTER(ctypes.c_int)]
            lib.get_agnocast_pub_nodes.restype = ctypes.POINTER(ctypes.POINTER(ctypes.c_char))           
            lib.free_agnocast_nodes_and_topics.argtypes = [ctypes.POINTER(ctypes.POINTER(ctypes.c_char)), ctypes.c_int]
            lib.free_agnocast_nodes_and_topics.restype = None

            # get agnocast topic list
            agnocast_topic_count = ctypes.c_int()
            agnocast_topic_names_array = lib.get_agnocast_topic_list(ctypes.byref(agnocast_topic_count))
            agnocast_topic_names = []
            for i in range(agnocast_topic_count.value):
                topic_ptr = ctypes.cast(agnocast_topic_names_array[i], ctypes.c_char_p)
                agnocast_topic_names.append(topic_ptr.value.decode('utf-8'))
            if agnocast_topic_count.value != 0:
                lib.free_agnocast_nodes_and_topics(agnocast_topic_names_array, agnocast_topic_count)

            # get ros2 topic list
            topic_names_and_types = get_topic_names_and_types(node=node, include_hidden_topics=True)

            topic_name = args.topic_name
            topic_name_byte = topic_name.encode('utf-8')
            for (t_name, t_types) in topic_names_and_types:
                if t_name == topic_name:
                    topic_types = t_types
                    break
            else:
                if topic_name in agnocast_topic_names:
                    topic_types = '<UNKOWN>'
                else:
                    return "Unknown topic '%s'" % topic_name

            line_end = '\n'
            if args.verbose:
                line_end = '\n\n'

            # get agnocast sub node list
            sub_node_count = ctypes.c_int()
            sub_node_array = lib.get_agnocast_sub_nodes(topic_name_byte, ctypes.byref(sub_node_count))
            sub_nodes = []
            for i in range(sub_node_count.value):
                node_ptr = ctypes.cast(sub_node_array[i], ctypes.c_char_p)
                sub_nodes.append(node_ptr.value.decode('utf-8'))
            if sub_node_count.value != 0:
                lib.free_agnocast_topics(sub_node_array, sub_node_count)

            # get agnocast pub node list
            pub_node_count = ctypes.c_int()
            pub_node_array = lib.get_agnocast_pub_nodes(topic_name_byte, ctypes.byref(pub_node_count))
            pub_nodes = []
            for i in range(pub_node_count.value):
                node_ptr = ctypes.cast(pub_node_array[i], ctypes.c_char_p)
                pub_nodes.append(node_ptr.value.decode('utf-8'))
            if pub_node_count.value != 0:
                lib.free_agnocast_topics(pub_node_array, pub_node_count)


            ########################################################################
            # Temp Code: existing ros2 topic info functionality
            ########################################################################
            type_str = topic_types[0] if len(topic_types) == 1 else topic_types
            print('Type: %s' % type_str, end=line_end)

            agnocast_pub_count = len(pub_nodes)
            print('Publisher count: %d' %
                  node.count_publishers(topic_name))
            print('(Include Agnocast Publisher count: %d)' %
                  agnocast_pub_count, end=line_end)
            if args.verbose:
                try:
                    for info in node.get_publishers_info_by_topic(topic_name):
                        full_node_name = f"{info.node_namespace.rstrip('/')}/{info.node_name.lstrip('/')}"
                        print('Node name: %s' % info.node_name)
                        print('Node namespace: %s' % info.node_namespace)
                        print('Topic type: %s' % info.topic_type)
                        if full_node_name in pub_nodes:
                            print('Endpoint type: %s (Agnocast enabled))' % info.endpoint_type.name)
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

            agnocast_sub_count = len(sub_nodes)
            print('Subscription count: %d' %
                  (int(node.count_subscribers(topic_name)) + agnocast_sub_count))
            print('(Include Agnocast Subscription count: %d)' %
                  agnocast_sub_count, end=line_end)
            if args.verbose:
                try:
                    for info in node.get_subscriptions_info_by_topic(topic_name):
                        print(info, end=line_end)
                    for info in sub_nodes:
                        nodespace, node_name = self.split_full_node_name(info)
                        print('Node name: %s' % node_name)
                        print('Node namespace: %s' % nodespace)
                        print('Topic type: %s' % type_str)
                        print('Endpoint type: SUBSCROPTION (Agnocast enabled)')
                        print('QoS profile:', end=line_end)
                except NotImplementedError as e:
                    return str(e)
            ########################################################################
