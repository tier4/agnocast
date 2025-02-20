obj-m := agnocast.o
CFLAGS_agnocast.o := -Wall -Werror
CFLAGS_agnocast_kunit.o := -Wall -Werror -DKUNIT_BUILD

KERNEL_VERSION := $(shell uname -r)
KERNEL_MAJOR := $(shell echo $(KERNEL_VERSION) | cut -d '.' -f 1)
KERNEL_MINOR := $(shell echo $(KERNEL_VERSION) | cut -d '.' -f 2)

# In Linux kernel v5.17 and earlier, the top-level Linux Makefile specifies -std=gnu89,
# so it is necessary to declare the variable used as the iterator in the for loop beforehand.
# For example:
#   int i;
#   for (i = 0; i < n; i++) {
#       ...
#   }
# Therefore, add -std=gnu11 to suppress this error.
ifeq ($(shell expr $(KERNEL_MAJOR) \< 5 \| $(KERNEL_MAJOR) = 5 \& $(KERNEL_MINOR) \<= 17), 1)
  CFLAGS_agnocast.o += -std=gnu11
  CFLAGS_agnocast_tmp_copied.o += -std=gnu11
  CFLAGS_agnocast_kunit.o += -std=gnu11
endif


# In Linux kernel versions v6.4 and earlier, the top-level Makefile includes
# -Wdeclaration-after-statement, which requires all variables used within
# a function to be declared at the beginning of the function. To suppress
# this, we should add -Wno-declaration-after-statement.
ifeq ($(shell expr $(KERNEL_MAJOR) \< 6 \| $(KERNEL_MAJOR) = 6 \& $(KERNEL_MINOR) \<= 4), 1)
  CFLAGS_agnocast.o += -Wno-declaration-after-statement
  CFLAGS_agnocast_tmp_copied.o += -Wno-declaration-after-statement
  CFLAGS_agnocast_kunit.o += -Wno-declaration-after-statement
endif

ifeq ($(CONFIG_KUNIT),y)
  obj-m += agnocast_kunit.o
	agnocast_kunit-m := agnocast_kunit_main.o agnocast_tmp_copied.o \
		agnocast_kunit/agnocast_kunit_subscriber_add.o \
		agnocast_kunit/agnocast_kunit_publisher_add.o \
		agnocast_kunit/agnocast_kunit_increment_rc.o \
		agnocast_kunit/agnocast_kunit_decrement_rc.o \
		agnocast_kunit/agnocast_kunit_receive_msg.o \
		agnocast_kunit/agnocast_kunit_publish_msg.o \
		agnocast_kunit/agnocast_kunit_take_msg.o \
		agnocast_kunit/agnocast_kunit_new_shm.o \
		agnocast_kunit/agnocast_kunit_get_subscriber_num.o \
		agnocast_kunit/agnocast_kunit_get_topic_list.o
	CFLAGS_agnocast_tmp_copied.o := -DKUNIT_BUILD
endif

ifeq ($(CONFIG_GCOV_KERNEL),y)
  CFLAGS_agnocast.o += -fprofile-arcs -ftest-coverage
  CFLAGS_agnocast_tmp_copied.o += -fprofile-arcs -ftest-coverage
  CFLAGS_agnocast_kunit.o += -fprofile-arcs -ftest-coverage
endif

all:
	# In order to build with different build options (KUNIT_BUILD),
	# we need to temporarily copy the kernel module source.
	cp agnocast.c agnocast_tmp_copied.c
	make -C /lib/modules/$(shell uname -r)/build M=$(PWD) modules

clean:
	rm -f agnocast_tmp_copied.c
	make -C /lib/modules/$(shell uname -r)/build M=$(PWD) clean
