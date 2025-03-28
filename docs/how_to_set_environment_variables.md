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

The hook library is generated as `libagnocast_heaphook.so`, so Agnocast requires to set `LD_PRELOAD` to `libagnocast_heaphook.so`. In addition, you have to specify appropriate `AGNOCAST_MEMPOOL_SIZE` as an environment variable because of [this](./shared_memory.md#how-virtual-addresses-are-decided).

## Integrate with ROS 2 launch

You can set environment variables through ROS 2 launch file systems as follows. To run the other application using `LD_PRELOAD` with Agnocast, you must add "libagnocast_heaphook.so" to the existing 'LD_PRELOAD' contents without modifying the libraries already specified there.

```xml
<node pkg="..." exec="..." name="...">
  <env name="LD_PRELOAD" value="libagnocast_heaphook.so:$(env LD_PRELOAD '')" />
  <env name="AGNOCAST_MEMPOOL_SIZE" value="..." />
</node>
```

```xml
<node_container pkg="agnocastlib" exec="agnocast_component_container" name="...">
  <env name="LD_PRELOAD" value="libagnocast_heaphook.so:$(env LD_PRELOAD '')" />
  <env name="AGNOCAST_MEMPOOL_SIZE" value="..." />
</node_container>
```

```python
import os

container = ComposableNodeContainer(
    ...,
    additional_env={
        'LD_PRELOAD': f"libagnocast_heaphook.so:{os.getenv('LD_PRELOAD', '')}",
        "AGNOCAST_MEMPOOL_SIZE": "...",
    },
)
```

> [!WARNING]
> If the other applications hooks [memory allocation/deallocation functions that are hooked by Agnocast](#introduction), it cannot be used together with Agnocast.
