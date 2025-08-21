#include "agnocast/agnocast_subscription.hpp"

#include <unistd.h>

#include <cerrno>
#include <cstring>
#include <iostream>
#include <string>

void bridge_daemon_main(int read_pipe_fd)
{
  if (setsid() == -1) {
    std::cerr << "setsid failed for daemon: " << strerror(errno) << std::endl;
    exit(EXIT_FAILURE);
  }

  std::cout << "[Bridge Daemon] PID: " << getpid() << ". Waiting for notifications..." << std::endl;

  while (true) {
    char buffer[256];
    ssize_t bytes_read = read(read_pipe_fd, buffer, sizeof(buffer) - 1);

    if (bytes_read > 0) {
      buffer[bytes_read] = '\0';
      std::cout << "[Bridge Daemon] Received notification: " << buffer << std::endl;

      agnocast::commonFunction();

    } else if (bytes_read == 0) {
      std::cout << "[Bridge Daemon] Parent process closed the pipe. Shutting down." << std::endl;
      break;

    } else {
      if (errno == EINTR) {
        continue;
      }
      std::cerr << "[Bridge Daemon] read failed: " << strerror(errno) << std::endl;
      break;
    }
  }

  close(read_pipe_fd);
  std::cout << "[Bridge Daemon] Daemon has finished." << std::endl;

  exit(EXIT_SUCCESS);
}