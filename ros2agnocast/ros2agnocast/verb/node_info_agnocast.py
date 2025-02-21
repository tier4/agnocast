import ctypes
import sys
from ros2cli.node.strategy import NodeStrategy
from ros2node.api import (
    get_action_client_info, get_action_server_info, get_node_names,
    get_publisher_info, get_service_client_info, get_service_server_info, get_subscriber_info
)
from ros2node.verb import VerbExtension

class NodeInfoAgnocastVerb(VerbExtension):
    "Output information about a node including Agnocast"

    def add_arguments(self, parser, cli_name):
        parser.add_argument(
            'node_name',
            help='Fully qualified node name to request information with Agnocast topics')

    def main(self, *, args):
        node_name = args.node_name

        with NodeStrategy(None) as node:
            node_names = [n.full_name for n in get_node_names(node=node)]
            if node_name not in node_names:
                print(f"Error: The node '{node_name}' does not exist.")
                return


            lib = ctypes.CDLL("libagnocast_ioctl_wrapper.so")
            lib.get_agnocast_sub_topics.argtypes = [ctypes.c_char_p, ctypes.POINTER(ctypes.c_int)]
            lib.get_agnocast_sub_topics.restype = ctypes.POINTER(ctypes.POINTER(ctypes.c_char))
            lib.get_agnocast_pub_topics.argtypes = [ctypes.c_char_p, ctypes.POINTER(ctypes.c_int)]
            lib.get_agnocast_pub_topics.restype = ctypes.POINTER(ctypes.POINTER(ctypes.c_char))           
            lib.free_agnocast_topics.argtypes = [ctypes.POINTER(ctypes.POINTER(ctypes.c_char)), ctypes.c_int]
            lib.free_agnocast_topics.restype = None

            node_name_bytes = args.node_name.encode('utf-8')

            sub_topic_count = ctypes.c_int()
            sub_topic_array = lib.get_agnocast_sub_topics(node_name_bytes, ctypes.byref(sub_topic_count))
            sub_topics = []
            for i in range(sub_topic_count.value):
                topic_ptr = ctypes.cast(sub_topic_array[i], ctypes.c_char_p)
                sub_topics.append(topic_ptr.value.decode('utf-8'))
            
            ########################################################################
            # Temp Code: to print sub Agnocast topics
            ########################################################################
            print("Agnocast Subscription topics:")
            for topic in sub_topics:
                print(topic)
            ########################################################################
            lib.free_agnocast_topics(sub_topic_array, sub_topic_count)

            pub_topic_count = ctypes.c_int()
            pub_topic_array = lib.get_agnocast_pub_topics(node_name_bytes, ctypes.byref(pub_topic_count))
            pub_topics = []
            for i in range(pub_topic_count.value):
                topic_ptr = ctypes.cast(pub_topic_array[i], ctypes.c_char_p)
                pub_topics.append(topic_ptr.value.decode('utf-8'))
            
            ########################################################################
            # Temp Code: print sub Agnocast topics
            ########################################################################
            print("Agnocast Publisher topics:")
            for topic in pub_topics:
                print(topic)
            ########################################################################
            lib.free_agnocast_topics(pub_topic_array, pub_topic_count)


            ########################################################################
            # Temp Code: existing ros2 node info functionality
            ########################################################################
            print("  Subscribers :")
            subscribers = get_subscriber_info(node=node, remote_node_name=node_name)
            for sub in subscribers:
                print(f"    {sub.name}: {', '.join(sub.types)}")

            print("  Publishers :")
            publishers = get_publisher_info(node=node, remote_node_name=node_name)
            for pub in publishers:
                print(f"    {pub.name}: {', '.join(pub.types)}")

            print("  Service Servers :")
            service_servers = get_service_server_info(node=node, remote_node_name=node_name)
            for service in service_servers:
                print(f"    {service.name}: {', '.join(service.types)}")

            print("  Service Clients :")
            service_clients = get_service_client_info(node=node, remote_node_name=node_name)
            for client in service_clients:
                print(f"    {client.name}: {', '.join(client.types)}")

            print("  Action Servers :")
            action_servers = get_action_server_info(node=node, remote_node_name=node_name)
            for action in action_servers:
                print(f"    {action.name}: {', '.join(action.types)}")

            print("  Action Clients :")
            action_clients = get_action_client_info(node=node, remote_node_name=node_name)
            for action in action_clients:
                print(f"    {action.name}: {', '.join(action.types)}")
            ########################################################################
