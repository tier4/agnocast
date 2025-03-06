## How to use ros2 command for Agnocast

Currently, Agnocast supports the following `ros2` commands:

- `ros2 topic list`
- `ros2 topic info /topic_name`
- `ros2 node info /node_name`

### Topic List

To list all topics including Agnocast, use `ros2 topic list_agnocast`.

If a topic is Agnocast enabled, it will be shown with a "(Agnocast enabled)" suffix.

```bash
$ ros2 topic list_agnocast
/topic_name1
/topic_name2 (Agnocast enabled)
/topic_name3
```

If you want to get only Agnocast related topics, use `ros2 topic list_agnocast | grep Agnocast`:

```bash
$ ros2 topic list_agnocast | grep Agnocast
/topic_name2 (Agnocast enabled)
```

### Topic Info

To show the topic info including Agnocast, use `ros2 topic info_agnocast /topic_name`.

```bash
$ ros2 topic info_agnocast -v /my_topic
Type: agnocast_sample_interfaces/msg/DynamicSizeArray

ROS 2 Publisher count: 1
Agnocast Publisher count: 1
ROS 2 Subscription count: 0
Agnocast Subscription count: 1
```

For more details, use `--verbose` or `-v`.

```bash
$ ros2 topic info_agnocast -v /my_topic
Type: agnocast_sample_interfaces/msg/DynamicSizeArray

ROS 2 Publisher count: 1
Agnocast Publisher count: 1

Node name: talker_node
Node namespace: /
Topic type: agnocast_sample_interfaces/msg/DynamicSizeArray
Endpoint type: PUBLISHER (Agnocast enabled)
GID: 01.10.6f.78.ef.cc.19.22.6a.d5.d6.8a.00.00.15.03.00.00.00.00.00.00.00.00
QoS profile:
  Reliability: RELIABLE
  History (Depth): KEEP_LAST (1)
  Durability: VOLATILE
  Lifespan: Infinite
  Deadline: Infinite
  Liveliness: AUTOMATIC
  Liveliness lease duration: Infinite

ROS 2 Subscription count: 0
Agnocast Subscription count: 1

Node name: listener_node
Node namespace: /
Topic type: agnocast_sample_interfaces/msg/DynamicSizeArray
Endpoint type: SUBSCRIPTION (Agnocast enabled)
QoS profile:
  History (Depth): KEEP_LAST (1)
  Durability: VOLATILE
```

### Node Info

To show the node info including Agnocast, use `ros2 node info_agnocast /node_name`.

```bash
$ ros2 node info_agnocast /listener_node
  Subscribers :
    /parameter_events: rcl_interfaces/msg/ParameterEvent
    /my_topic: sample_interfaces/msg/DynamicSizeArray (Agnocast enabled)
  Publishers :
    /my_topic2: sample_interfaces/msg/DynamicSizeArray (Agnocast enabled)
    /parameter_events: rcl_interfaces/msg/ParameterEvent
    /rosout: rcl_interfaces/msg/Log
  Service Servers :
    /listener_node/describe_parameters: rcl_interfaces/srv/DescribeParameters
    /listener_node/get_parameter_types: rcl_interfaces/srv/GetParameterTypes
    /listener_node/get_parameters: rcl_interfaces/srv/GetParameters
    /listener_node/list_parameters: rcl_interfaces/srv/ListParameters
    /listener_node/set_parameters: rcl_interfaces/srv/SetParameters
    /listener_node/set_parameters_atomically: rcl_interfaces/srv/SetParametersAtomically
  Service Clients :
  Action Servers :
  Action Clients :
```
