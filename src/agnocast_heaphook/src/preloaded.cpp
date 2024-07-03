#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif
#include <dlfcn.h>

#include <stdio.h>
#include <unistd.h>
#include <pthread.h>
#include <sys/mman.h>
#include <string.h>
#include <malloc.h>
#include <fcntl.h>

#include <cstdint>
#include <unordered_map>
#include <string>

#include "tlsf/tlsf.h"

using malloc_type = void * (*)(size_t);
using free_type = void (*)(void *);
using calloc_type = void * (*)(size_t, size_t);
using realloc_type = void * (*)(void *, size_t);

// Aligned allocation
using posix_memalign_type = int (*)(void **, size_t, size_t);
using memalign_type = void * (*)(size_t, size_t);
using aligned_alloc_type = void * (*)(size_t, size_t);
using valloc_type = void * (*)(size_t);
using pvalloc_type = void * (*)(size_t);

using malloc_usable_size_type = size_t (*)(void *);

static char * mempool_ptr;
static size_t INITIAL_MEMPOOL_SIZE = 100 * 1000 * 1000; // default: 100MB
static size_t ADDITIONAL_MEMPOOL_SIZE = 100 * 1000 * 1000; // default: 100MB
static std::unordered_map<void *, void *> * aligned2orig;

static pthread_mutex_t init_mtx = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t init_cond = PTHREAD_COND_INITIALIZER; // mempool_initialized == true
static bool mempool_initialized = false;
static bool mempool_init_started = false; // guarded by init_mtx

static pthread_mutex_t tlsf_mtx = PTHREAD_MUTEX_INITIALIZER;

static void map_area(const char *area_name_env, const char *addr_str_env, bool writable = false) {
  const char *shm_name = std::getenv(area_name_env);
  int shm_fd = shm_open(shm_name, O_CREAT | O_RDWR, 0666);
  if (shm_fd == -1) {
    fprintf(stderr, "shm_open failed on READ_ONLY_AREA0\n");
    exit(EXIT_FAILURE);
  }

  if (ftruncate(shm_fd, INITIAL_MEMPOOL_SIZE) == -1) {
    fprintf(stderr, "ftruncate fail on READ_ONLY_AREA0\n");
    exit(EXIT_FAILURE);
  }

  const char * addr_str = std::getenv(addr_str_env);
  char *end;
  errno = 0;
  uint64_t addr = std::strtoull(addr_str, &end, 16);
  /*
  if (errno != 0 || *end != '\0') // error handling
  */

  int prot = PROT_READ | MAP_FIXED;
  if (writable) prot |= PROT_WRITE;

  void* ret = mmap(reinterpret_cast<void*>(addr), INITIAL_MEMPOOL_SIZE, prot, MAP_SHARED | MAP_FIXED, shm_fd, 0);

  if (ret == MAP_FAILED) {
    fprintf(stderr, "mmap failed\n");
    exit(EXIT_FAILURE);
  }

  if (writable) {
    mempool_ptr = reinterpret_cast<char*>(ret);
  }
}

static void initialize_mempool()
{
  if (const char * env_p = std::getenv("INITIAL_MEMPOOL_SIZE")) {
    INITIAL_MEMPOOL_SIZE = std::stoull(std::string(env_p));
  }

  if (const char * env_p = std::getenv("ADDITIONAL_MEMPOOL_SIZE")) {
    ADDITIONAL_MEMPOOL_SIZE = std::stoull(std::string(env_p));
  }

  map_area("READ_ONLY_AREA0_NAME", "READ_ONLY_AREA0_START");
  map_area("READ_ONLY_AREA1_NAME", "READ_ONLY_AREA1_START");
  map_area("WRITABLE_AREA_NAME", "WRITABLE_AREA_START", true);

  memset(mempool_ptr, 0, INITIAL_MEMPOOL_SIZE);
  init_memory_pool(INITIAL_MEMPOOL_SIZE, mempool_ptr); // tlsf library function

  // aligned2orig.reserve(10000000);
}

// Do not use printf
void check_mempool_initialized()
{
  if (mempool_initialized) {return;}

  pthread_mutex_lock(&init_mtx);

  if (!mempool_init_started) {
    mempool_init_started = true;
    pthread_mutex_unlock(&init_mtx);

    initialize_mempool();

    aligned2orig = new std::unordered_map<void *, void *>();

    mempool_initialized = true;
    pthread_cond_signal(&init_cond);
  } else {
    while (!mempool_initialized) {
      pthread_cond_wait(&init_cond, &init_mtx);
    }

    pthread_mutex_unlock(&init_mtx);
  }
}

template<class F>
static void * tlsf_allocate_internal(F allocate)
{
  pthread_mutex_lock(&tlsf_mtx);

  void * ret = allocate();

  size_t multiplier = 1;
  while (ret == NULL) {
    char * addr = (char *) mmap(
      NULL, multiplier * ADDITIONAL_MEMPOOL_SIZE, PROT_READ | PROT_WRITE,
      MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    add_new_area(addr, multiplier * ADDITIONAL_MEMPOOL_SIZE, mempool_ptr); // tlsf library function
    fprintf(
      stderr, "TLSF memory pool exhausted: %lu bytes additionally mmaped.\n",
      multiplier * ADDITIONAL_MEMPOOL_SIZE);

    ret = allocate();
    multiplier *= 2;
  }

  pthread_mutex_unlock(&tlsf_mtx);
  return ret;
}

static void * tlsf_malloc_wrapped(size_t size)
{
  return tlsf_allocate_internal([size] {return tlsf_malloc(size);});
}

static void * tlsf_calloc_wrapped(size_t num, size_t size)
{
  return tlsf_allocate_internal([num, size] {return tlsf_calloc(num, size);});
}

static void * tlsf_realloc_wrapped(void * ptr, size_t new_size)
{
  return tlsf_allocate_internal([ptr, new_size] {return tlsf_realloc(ptr, new_size);});
}

static void tlsf_free_wrapped(void * ptr)
{
  pthread_mutex_lock(&tlsf_mtx);
  tlsf_free(ptr);
  pthread_mutex_unlock(&tlsf_mtx);
}

static void * tlsf_aligned_malloc(size_t alignment, size_t size)
{
  void * addr = tlsf_malloc_wrapped(alignment + size);
  void * aligned =
    reinterpret_cast<void *>(reinterpret_cast<uint64_t>(addr) + alignment -
    reinterpret_cast<uint64_t>(addr) % alignment);
  (*aligned2orig)[aligned] = addr;

  //printf("In tlsf_aligned_malloc: orig=%p -> aligned=%p\n", addr, aligned);

  return aligned;
}

extern "C" {

void * malloc(size_t size)
{
  static malloc_type original_malloc = reinterpret_cast<malloc_type>(dlsym(RTLD_NEXT, "malloc"));
  static __thread bool malloc_no_hook = false;

  if (malloc_no_hook) {
    if (mempool_initialized) {
      return tlsf_malloc_wrapped(size);
    } else {
      return original_malloc(size);
    }
  }

  malloc_no_hook = true;
  check_mempool_initialized();
  void * ret = tlsf_malloc_wrapped(size);
  malloc_no_hook = false;
  return ret;
}

void free(void * ptr)
{
  static free_type original_free = reinterpret_cast<free_type>(dlsym(RTLD_NEXT, "free"));
  static __thread bool free_no_hook = false;

  if (free_no_hook) {
    if (mempool_initialized) {
      tlsf_free_wrapped(ptr);
    } else {
      original_free(ptr);
    }

    return;
  }

  free_no_hook = true;
  check_mempool_initialized();

  auto it = aligned2orig->find(ptr);
  if (it != aligned2orig->end()) {
    ptr = it->second;
    aligned2orig->erase(it);
  }

  tlsf_free_wrapped(ptr);
  free_no_hook = false;
}

void * calloc(size_t num, size_t size)
{
  static calloc_type original_calloc = reinterpret_cast<calloc_type>(dlsym(RTLD_NEXT, "calloc"));
  static __thread bool calloc_no_hook = false;

  if (calloc_no_hook) {
    if (mempool_initialized) {
      return tlsf_calloc_wrapped(num, size);
    } else {
      return original_calloc(num, size);
    }
  }

  calloc_no_hook = true;
  check_mempool_initialized();
  void * ret = tlsf_calloc_wrapped(num, size);
  calloc_no_hook = false;

  return ret;
}

void * realloc(void * ptr, size_t new_size)
{
  static realloc_type original_realloc =
    reinterpret_cast<realloc_type>(dlsym(RTLD_NEXT, "realloc"));
  static __thread bool realloc_no_hook = false;

  if (realloc_no_hook) {
    if (mempool_initialized) {
      return tlsf_realloc_wrapped(ptr, new_size);
    } else {
      return original_realloc(ptr, new_size);
    }
  }

  realloc_no_hook = true;
  check_mempool_initialized();

  auto it = aligned2orig->find(ptr);
  if (it != aligned2orig->end()) {
    ptr = it->second;
    aligned2orig->erase(ptr);
  }

  void * ret = tlsf_realloc_wrapped(ptr, new_size);
  realloc_no_hook = false;
  return ret;
}

int posix_memalign(void ** memptr, size_t alignment, size_t size)
{
  static posix_memalign_type original_posix_memalign =
    reinterpret_cast<posix_memalign_type>(dlsym(RTLD_NEXT, "posix_memalign"));
  static __thread bool posix_memalign_no_hook = false;

  if (posix_memalign_no_hook) {
    if (mempool_initialized) {
      *memptr = tlsf_aligned_malloc(alignment, size);
      return 0;
    } else {
      return original_posix_memalign(memptr, alignment, size);
    }
  }

  posix_memalign_no_hook = true;
  check_mempool_initialized();

  *memptr = tlsf_aligned_malloc(alignment, size);

  posix_memalign_no_hook = false;
  return 0;
}

void * memalign(size_t alignment, size_t size)
{
  static memalign_type original_memalign =
    reinterpret_cast<memalign_type>(dlsym(RTLD_NEXT, "memalign"));
  static __thread bool memalign_no_hook = false;

  if (memalign_no_hook) {
    if (mempool_initialized) {return tlsf_aligned_malloc(alignment, size);} else {
      return original_memalign(alignment, size);
    }
  }

  memalign_no_hook = true;
  check_mempool_initialized();
  void * ret = tlsf_aligned_malloc(alignment, size);
  memalign_no_hook = false;
  return ret;
}

void * aligned_alloc(size_t alignment, size_t size)
{
  static aligned_alloc_type original_aligned_alloc =
    reinterpret_cast<aligned_alloc_type>(dlsym(RTLD_NEXT, "aligned_alloc"));
  static __thread bool aligned_alloc_no_hook = false;

  if (aligned_alloc_no_hook /*|| pthread_self() == logging_thread*/) {
    if (mempool_initialized) {return tlsf_aligned_malloc(alignment, size);} else {
      return original_aligned_alloc(alignment, size);
    }
  }

  aligned_alloc_no_hook = true;
  check_mempool_initialized();
  void * ret = tlsf_aligned_malloc(alignment, size);
  aligned_alloc_no_hook = false;
  return ret;
}

void * valloc(size_t size)
{
  static valloc_type original_valloc = reinterpret_cast<valloc_type>(dlsym(RTLD_NEXT, "valloc"));
  static __thread bool valloc_no_hook = false;
  static size_t page_size = sysconf(_SC_PAGESIZE);

  if (valloc_no_hook) {
    if (mempool_initialized) {return tlsf_aligned_malloc(page_size, size);} else {
      return original_valloc(size);
    }
  }

  valloc_no_hook = true;
  check_mempool_initialized();
  void * ret = tlsf_aligned_malloc(page_size, size);
  valloc_no_hook = false;

  return ret;
}

// pvalloc() rounds the size of the allocation up to the next multiple of the system page size.
void * pvalloc(size_t size)
{
  static pvalloc_type original_pvalloc =
    reinterpret_cast<pvalloc_type>(dlsym(RTLD_NEXT, "pvalloc"));
  static __thread bool pvalloc_no_hook = false;
  static size_t page_size = sysconf(_SC_PAGESIZE);
  size_t rounded_up = size + (page_size - size % page_size) % page_size;

  if (pvalloc_no_hook) {
    if (mempool_initialized) {return tlsf_aligned_malloc(page_size, rounded_up);}
    return original_pvalloc(size);
  }

  pvalloc_no_hook = true;
  check_mempool_initialized();
  void * ret = tlsf_aligned_malloc(page_size, rounded_up);
  return ret;
}

size_t malloc_usable_size(void * ptr)
{
  static malloc_usable_size_type original_malloc_usable_size = \
    reinterpret_cast<malloc_usable_size_type>(dlsym(RTLD_NEXT, "malloc_usable_size"));

  check_mempool_initialized();

  printf("hoge: malloc_usable_size called\n");

  size_t ret = original_malloc_usable_size(ptr);
  return ret;
}

using mallinfo_type = struct mallinfo (*)( void);
struct mallinfo mallinfo()
{
  static mallinfo_type orig = reinterpret_cast<mallinfo_type>(dlsym(RTLD_NEXT, "mallinfo")); printf(
    "hoge: mallinfo called\n");
  printf("hoge: mallinfo called\n");
  return orig();
}

#ifdef HAVE_MALLINFO2
using mallinfo2_type = struct mallinfo2 (*)( void);
struct mallinfo2 mallinfo2()
{
  static mallinfo2_type orig = reinterpret_cast<mallinfo2_type>(dlsym(RTLD_NEXT, "mallinfo2"));
  printf("hoge: mallinfo2 called\n");
  return orig();
}
#endif

using mallopt_type = int (*)(int, int);
int mallopt(int param, int value)
{
  static mallopt_type orig = reinterpret_cast<mallopt_type>(dlsym(RTLD_NEXT, "mallopt"));
  printf("hoge: mallopt called\n");
  return orig(param, value);
}

using malloc_trim_type = int (*)(size_t);
int malloc_trim(size_t pad)
{
  static malloc_trim_type orig =
    reinterpret_cast<malloc_trim_type>(dlsym(RTLD_NEXT, "malloc_trim"));
  printf("hoge: malloc_trim called\n");
  return orig(pad);
}

using malloc_stats_type = void (*)(void);
void malloc_stats(void)
{
  static malloc_stats_type orig =
    reinterpret_cast<malloc_stats_type>(dlsym(RTLD_NEXT, "malloc_stats"));
  printf("hoge: malloc_stats\n");
  orig();
  return;
}

using malloc_info_type = int (*)(int, FILE *);
int malloc_info(int options, FILE * stream)
{
  static malloc_info_type orig =
    reinterpret_cast<malloc_info_type>(dlsym(RTLD_NEXT, "malloc_info"));
  printf("malloc_info called\n");
  return orig(options, stream);
}

} // extern "C"
