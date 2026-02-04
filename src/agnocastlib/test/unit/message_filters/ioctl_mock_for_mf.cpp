#include <cstdarg>
#include <cstdio>
#include <sys/ioctl.h>

// Simple ioctl mock for message_filters tests
// This mock just returns success for all ioctl calls
extern "C" int ioctl(int fd, unsigned long request, ...)
{
  (void)fd;
  (void)request;
  // Return success for all ioctl calls
  return 0;
}
