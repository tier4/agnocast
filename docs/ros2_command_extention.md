## How to use ros2 command for Agnocast

Currently, Agnocast partially supports `ros2` command to analyze Agnocast related topics.

### List Agnocast topics

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
