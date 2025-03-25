#include <fcntl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>

#include <cerrno>
#include <cstdint>
#include <string>

int shm_fd;

namespace agnocast
{

extern "C" void * initialize_agnocast(const uint64_t shm_size)
{
  const std::string shm_name = "/heaphook_test@" + std::to_string(getpid());

  int oflag = O_CREAT | O_RDWR;
  const int shm_mode = 0666;
  shm_fd = shm_open(shm_name.c_str(), oflag, shm_mode);
  if (shm_fd == -1) {
    return nullptr;
  }

  if (ftruncate(shm_fd, static_cast<off_t>(shm_size)) == -1) {
    return nullptr;
  }

  int prot = PROT_READ | PROT_WRITE;
  void * ret = mmap(
    reinterpret_cast<void *>(0x40000000000), shm_size, prot, MAP_SHARED | MAP_FIXED_NOREPLACE,
    shm_fd, 0);

  if (ret == MAP_FAILED) {
    return nullptr;
  }

  return ret;
}

void shutdown_agnocast()
{
  close(shm_fd);
  shm_unlink(("/heaphook_test@" + std::to_string(getpid())).c_str());
}

}  // namespace agnocast
