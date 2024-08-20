obj-m := agnocast.o
CFLAGS_agnocast.o :=

KERNEL_VERSION := $(shell uname -r)
KERNEL_MAJOR := $(shell echo $(KERNEL_VERSION) | cut -d '.' -f 1)
KERNEL_MINOR := $(shell echo $(KERNEL_VERSION) | cut -d '.' -f 2)

ifeq ($(shell expr $(KERNEL_MAJOR) \< 5), 1)
  CFLAGS_agnocast.o += -std=gnu11
else ifeq ($(shell expr $(KERNEL_MAJOR) = 5), 1)
  ifeq ($(shell expr $(KERNEL_MINOR) \<= 17), 1)
    CFLAGS_agnocast.o += -std=gnu11
  endif
endif

ifeq ($(shell expr $(KERNEL_MAJOR) \< 6), 1)
  CFLAGS_agnocast.o += -Wno-declaration-after-statement
else ifeq ($(shell expr $(KERNEL_MAJOR) = 6), 1)
  ifeq ($(shell expr $(KERNEL_MINOR) \<= 4), 1)
    CFLAGS_agnocast.o += -Wno-declaration-after-statement
  endif
endif





all:
	make -C /lib/modules/$(shell uname -r)/build M=$(PWD) modules

clean:
	make -C /lib/modules/$(shell uname -r)/build M=$(PWD) clean
