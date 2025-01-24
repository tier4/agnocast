obj-m := agnocast.o
CFLAGS_agnocast.o := -Wall -Werror

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
endif


# In Linux kernel versions v6.4 and earlier, the top-level Makefile includes
# -Wdeclaration-after-statement, which requires all variables used within
# a function to be declared at the beginning of the function. To suppress
# this, we should add -Wno-declaration-after-statement.
ifeq ($(shell expr $(KERNEL_MAJOR) \< 6 \| $(KERNEL_MAJOR) = 6 \& $(KERNEL_MINOR) \<= 4), 1)
  CFLAGS_agnocast.o += -Wno-declaration-after-statement
endif

# For KUnit
ifeq ($(CONFIG_KUNIT),y)
  obj-m += agnocast_kunit.o
endif
ifeq ($(CONFIG_GCOV_KERNEL),y)
  CFLAGS_agnocast.o += -fprofile-arcs -ftest-coverage
  CFLAGS_agnocast_kunit.o += -fprofile-arcs -ftest-coverage
endif

all:
	make -C /lib/modules/$(shell uname -r)/build M=$(PWD) modules

clean:
	make -C /lib/modules/$(shell uname -r)/build M=$(PWD) clean
