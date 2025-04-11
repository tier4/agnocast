
## What is shared memory in Linux?

See official man page: <https://man7.org/linux/man-pages/man7/shm_overview.7.html>

## How shared memory is used in Agnocast?

### Basic usage

- A publisher opens a shared memory with a writable privilege.
- A subscriber opens the shared memory with a read-only privilege which the corresponding publisher opened.

### Detailed usage

There are three invocations for shared memory related procedures.

#### Initialization of a process

Each process linked with Agnocast opens a shared memory, which is writable only for the process.
When a process first calls malloc or other memory related functions, Agnocast starts and the shared memory is opened in the following steps:

1. get an allocatable area through `AGNOCAST_ADD_PROCESS_CMD` ioctl.
2. open a writable shared memory on the allocatable area, with `shm_open`, `ftruncate` and `mmap` system calls.
3. create a thread and open a message queue so that the process can recognize a emergence of a new publisher later.

#### Creation of a publisher

When a process calls `create_publisher` for a topic `T`, the shared memory of the process should be mapped by processes which have a subscription for `T`.
Thus the following procedures are executed:

1. The publisher process gets the information about subscribers already registered for the topic `T` through `AGNOCAST_ADD_PUBLISHER_CMD` ioctl.
2. The publisher process opens a message queue and send the shared memory information in order to notify the subscribers already created for the topic `T` that a new publisher is registered.
3. The subscriber process receives the message and maps the publisher's shared memory area with a read-only privilege.

#### Creation of a subscriber

When a process calls `create_subscription` for topic `T`, then the process maps the corresponding publisher's shared memory area with a read-only privilege in the following steps:

1. get the information about the publishers for the topic `T` through `AGNOCAST_ADD_SUBSCRIBER_CMD` ioctl.
2. map the publisher's shared memories with a read-only privilege.

### Naming rule and restrictions

In Agnocast, there is exactly one writable process and there are some read-only processes for a shared memory.
Suppose the writable process's id is `pid`, then the shared memory is named as "/agnocast@pid".
The name should start with '/' and should not include '/' any more.

Message queue is also created for each process.
Suppose the process's id is `pid`, then the message queue is named as "/new_publisher@pid".
The restriction for the name is the same as the shared memory.

## How virtual addresses are decided?

Any process which joins Agnocast has to set `AGNOCAST_MEMPOOL_SIZE` as an environment variable.
The passed value is aligned to 100kB.

## Known issues

- When a heaphook fails to allocate a memory due to the lack of enough memory pool, heaphook tries to add a new memory. However, the added area will not be mapped by the subscribers in the current implementation and in turn Agnocast will not work well.
- The current implementation suppose that the memory after 0x40000000000 is always allocatable, though it is not investigated in detail.
