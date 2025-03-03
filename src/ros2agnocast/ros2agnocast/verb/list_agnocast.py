import ctypes
from ros2topic.verb import VerbExtension

class ListAgnocastVerb(VerbExtension):
    "Output a list of available topics including Agnocast"

    def main(self, *, args):
        lib = ctypes.CDLL("libagnocast_ioctl_wrapper.so")
        lib.topic_list.argtypes = []
        lib.topic_list.restype = ctypes.c_int
        lib.topic_list()
