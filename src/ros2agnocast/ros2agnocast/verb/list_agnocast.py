import ctypes
from ros2cli.node.strategy import NodeStrategy
from ros2topic.api import get_topic_names_and_types
from ros2topic.verb import VerbExtension

class TopicInfoRet(ctypes.Structure):
    _fields_ = [
        ("node_name", ctypes.c_char * 256),
        ("qos_depth", ctypes.c_uint32),
        ("qos_is_transient_local", ctypes.c_bool),
        # Agnocast does not natively support reliability configuration,
        # but this field is required to pass the QoS profile to the ROS 2 bridge.
        ("qos_is_reliable", ctypes.c_bool),
        ("is_bridge", ctypes.c_bool),
    ]
class ListAgnocastVerb(VerbExtension):
    "Output a list of available topics including Agnocast"

    def main(self, *, args):
        with NodeStrategy(None) as node:
            lib = ctypes.CDLL("libagnocast_ioctl_wrapper.so")
            lib.get_agnocast_topics.argtypes = [ctypes.POINTER(ctypes.c_int)]
            lib.get_agnocast_topics.restype = ctypes.POINTER(ctypes.POINTER(ctypes.c_char))
            lib.free_agnocast_topics.argtypes = [ctypes.POINTER(ctypes.POINTER(ctypes.c_char)), ctypes.c_int]
            lib.free_agnocast_topics.restype = None

            # For bridge detection, we need to get nodes by topic
            lib.get_agnocast_sub_nodes.argtypes = [ctypes.c_char_p, ctypes.POINTER(ctypes.c_int)]
            lib.get_agnocast_sub_nodes.restype = ctypes.POINTER(TopicInfoRet)
            lib.get_agnocast_pub_nodes.argtypes = [ctypes.c_char_p, ctypes.POINTER(ctypes.c_int)]
            lib.get_agnocast_pub_nodes.restype = ctypes.POINTER(TopicInfoRet)
            lib.free_agnocast_topic_info_ret.argtypes = [ctypes.POINTER(TopicInfoRet)]
            lib.free_agnocast_topic_info_ret.restype = None

            def is_topic_bridged(topic_name):
                topic_name_bytes = topic_name.encode('utf-8')

                # Check Agnocast subscribers
                sub_count = ctypes.c_int()
                sub_array = lib.get_agnocast_sub_nodes(topic_name_bytes, ctypes.byref(sub_count))
                
                try:
                    if any(sub_array[i].is_bridge for i in range(sub_count.value)):
                        return True
                finally:
                    if sub_count.value > 0 and sub_array:
                        lib.free_agnocast_topic_info_ret(sub_array)

                # Check Agnocast publishers
                pub_count = ctypes.c_int()
                pub_array = lib.get_agnocast_pub_nodes(topic_name_bytes, ctypes.byref(pub_count))
                
                try:
                    if any(pub_array[i].is_bridge for i in range(pub_count.value)):
                        return True
                finally:
                    if pub_count.value > 0 and pub_array:
                        lib.free_agnocast_topic_info_ret(pub_array)

                return False
            
            # Get Agnocast topics
            topic_count = ctypes.c_int()
            agnocast_topic_array = lib.get_agnocast_topics(ctypes.byref(topic_count))
            agnocast_topics = []
            for i in range(topic_count.value):
                topic_ptr = ctypes.cast(agnocast_topic_array[i], ctypes.c_char_p)
                topic_name = topic_ptr.value.decode('utf-8')
                agnocast_topics.append(topic_name)
            if topic_count.value != 0:
                lib.free_agnocast_topics(agnocast_topic_array, topic_count)
            
            # Get ros2 topics
            ros2_topics_data = get_topic_names_and_types(node=node)
            ros2_topics = [name for name, _ in ros2_topics_data]

            ########################################################################
            # Print topic list
            ########################################################################
            agnocast_topics_set = set(agnocast_topics)
            ros2_topics_set = set(ros2_topics)

            for topic in sorted(agnocast_topics_set | ros2_topics_set):
                if topic in agnocast_topics_set and topic not in ros2_topics_set:
                    suffix = " (Agnocast enabled)"
                elif topic in ros2_topics_set and topic not in agnocast_topics_set:
                    suffix = ""
                else:
                    if is_topic_bridged(topic):
                        suffix = " (Agnocast enabled, bridged)"
                    else:
                        suffix = " (ERROR: Agnocast ros2 mismatch)"
                print(f"{topic}{suffix}")
