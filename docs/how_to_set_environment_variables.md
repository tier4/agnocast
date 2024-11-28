# How to set environment variables

## Introduction

Agnocast uses the `LD_PRELOAD` to replace the following memory allocation/deallocation functions:

- `malloc`
- `free`
- `calloc`
- `realloc`
- `posix_memalign`
- `aligned_alloc`
- `memalign`

The hook library is generated as `libagnocast_heaphook.so`, so Agnocast requires to set `LD_PRELOAD` to `libagnocast_heaphook.so`. In addition, you have to specify appropriate `MEMPOOL_SIZE` as an environment variable because of [this](./shared_memory.md#how-virtual-addresses-are-decided).

## Integrate with ROS 2 launch

You can set environment variables through ROS 2 launch file systems as follows.

```xml
<node pkg="..." exec="..." name="...">
  <env name="LD_PRELOAD" value="libagnocast_heaphook.so" />
  <env name="MEMPOOL_SIZE" value="..." />
</node>
```

```xml
<node_container pkg="agnocastlib" exec="agnocast_component_container" name="...">
  <env name="LD_PRELOAD" value="libagnocast_heaphook.so"/>
  <env name="MEMPOOL_SIZE" value="..." />
</node_container>
```

```python
container = ComposableNodeContainer(
    ...,
    additional_env={
        "LD_PRELOAD": "libagnocast_heaphook.so",
        "MEMPOOL_SIZE": "...",
    },
)
```

## Co-operation with application using LD_PRELOAD

If you want to run the other application using `LD_PRELOAD` with Agnocast, you have to leave the contents of it when setting the environment variables.

```xml
<arg name="CURR_LD_PRELOAD" default="$(env LD_PRELOAD)" />
<node_container pkg="agnocastlib" exec="agnocast_component_container" name="...">
  <env name="LD_PRELOAD" value="libagnocast_heaphook.so:$(var CURR_LD_PRELOAD)" />
  <env name="MEMPOOL_SIZE" value="..." />
</node_container>
```

```python
import os

container = ComposableNodeContainer(
    ...,
    additional_env={
        'LD_PRELOAD': f"libagnocast_heaphook.so:{os.getenv('LD_PRELOAD')}",
        "MEMPOOL_SIZE": "...",
    },
)
```

> [!WARNING]
> If the other application hooks [memory allocation/deallocation functions that are hooked by Agnocast](#introduction), it is impossible to cooperate with it.
