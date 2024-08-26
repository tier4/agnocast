
## What is shared memory in Linux?

See official man page: https://github.com/autowarefoundation/autoware/blob/b35b75ccbd122c82be4a6dde870640646066058f/.clang-tidy-ci#L163


## How shared memory is used in Agnocast?

### Basic usage

 - A publisher opens a shared memory with a writable privilege.
 - A subscriber opens the shared memory with an only readable privilege which the corresponsing publisher opened.


### Detailed usage

There are three invocations for shared meomry related procedures.

#### Initialization of a process

All processes linked with Agnocast open a shared memory, which is writable only for the process.
When a process first calls malloc or other memory related functions, Agnocast starts and the shared memory is opened in the following steps:

1. get an allocatable area through `AGNOCAST_NEW_SHM_CMD` ioctl.
2. open a writable shared memory on the allocatable area, with `shm_open`, `ftruncate` and `mmap` system calls.
3. create a thread and open a message queue so that the process can recognize a emergence of a new publisher later.

#### Creattion of a publisher

When a process calls `create_publisher` for topic `T`, then the shared memory of the process should be mapped by processes which has a subscription for `T`.
Thus in the `create_publisher`, the following procedures are executed:

1. The publisher process gets the infomation about subscribers already registerd for the topic `T` through `AGNOCAST_PUBLISHER_ADD_CMD` ioctl.
2. The publisher process opens a message queue and send the sahred memory infomation in order to notify the subscribers already created for the topic `T` that a publisher is registered.
3. The subscriber process receives the message and maps the publisher's shared memory area with a read-only privilege.

##### Creation of a subscriber

When a process calls `create_subscription` for topic `T`, then the process maps the corresponding publisher's shared memory area with a read-only privilege in the following steps:

1. get the information about the publishers for the topic `T` through `AGNOCAST_SUBSCRIBER_ADD_CMD` ioctl.
2. map the publisher's shared memories with a read-only privilege.


### Naming rule and restrictions

In Agnocast, there is exactly one writable process and there are some read-only processes for a shared memory.
Suppose the writable process's id is `pid`, then the shared memory is named as "/agnocast@pid".
The name should start with '/' and should not include '/' any more.

Message queue is created also for each process.
Suppose the process's id is `pid`, then the message queue is named as "/new_publisher@pid".
The restriction for the name is the same as the shared memory one.


## Known issues
 - The `INITIAL_MEMPOOL_SIZE` is fixed to 100MB, but the size of it is configured for each process based on the computational cost.
 - When a heaphook fails to allocate a new memory due to the lack of enough mempool, heaphook tries to add a new memory. However, the added area will not be mapped by the subscribers in the current implementation and in turn Agnocast will not work well.