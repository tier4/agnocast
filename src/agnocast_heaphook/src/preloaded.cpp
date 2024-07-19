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

#include <unordered_map>
#include <string>

#include "tlsf/tlsf.h"

#include "preloaded.hpp"

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
static bool mempool_initialized = false;

static pthread_mutex_t tlsf_mtx = PTHREAD_MUTEX_INITIALIZER;

void map_area(const char * shm_name, const uint64_t shm_addr, const bool writable) {
  int shm_fd = shm_open(shm_name, O_CREAT | O_RDWR, 0666);
  if (shm_fd == -1) {
    fprintf(stderr, "heaphook: shm_open failed in map_area\n");
    exit(EXIT_FAILURE);
  }

  if (ftruncate(shm_fd, INITIAL_MEMPOOL_SIZE) == -1) {
    fprintf(stderr, "heaphook: ftruncate failed in map_area\n");
    exit(EXIT_FAILURE);
  }

  int prot = PROT_READ | MAP_FIXED;
  if (writable) prot |= PROT_WRITE;

  void* ret = mmap(reinterpret_cast<void*>(shm_addr), INITIAL_MEMPOOL_SIZE, prot, MAP_SHARED | MAP_FIXED, shm_fd, 0);

  if (ret == MAP_FAILED) {
    fprintf(stderr, "heaphook: mmap failed in map_area\n");
    exit(EXIT_FAILURE);
  }

  if (writable) {
    mempool_ptr = reinterpret_cast<char*>(ret);
  }
}

void initialize_mempool(const char * shm_name, const uint64_t shm_addr) {
  pthread_mutex_lock(&init_mtx);

  if (mempool_initialized) {
    pthread_mutex_unlock(&init_mtx);
    return;
  }

  if (const char * env_p = std::getenv("INITIAL_MEMPOOL_SIZE")) {
    INITIAL_MEMPOOL_SIZE = std::stoull(std::string(env_p));
  }

  if (const char * env_p = std::getenv("ADDITIONAL_MEMPOOL_SIZE")) {
    ADDITIONAL_MEMPOOL_SIZE = std::stoull(std::string(env_p));
  }

  map_area(shm_name, shm_addr, true);

  memset(mempool_ptr, 0, INITIAL_MEMPOOL_SIZE);
  init_memory_pool(INITIAL_MEMPOOL_SIZE, mempool_ptr); // tlsf library function

  aligned2orig = new std::unordered_map<void *, void *>();
  // aligned2orig.reserve(10000000);

  mempool_initialized = true;
  pthread_mutex_unlock(&init_mtx);
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

    // TODO: printf cannot be used
    // fprintf(
    //   stderr, "TLSF memory pool exhausted: %lu bytes additionally mmaped.\n",
    //   multiplier * ADDITIONAL_MEMPOOL_SIZE);

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

  if (!mempool_initialized || malloc_no_hook) {
    return original_malloc(size);
  }

  malloc_no_hook = true;
  void * ret = tlsf_malloc_wrapped(size);
  malloc_no_hook = false;
  return ret;
}

void free(void * ptr)
{
  static free_type original_free = reinterpret_cast<free_type>(dlsym(RTLD_NEXT, "free"));
  static __thread bool free_no_hook = false;

  if (!mempool_initialized || free_no_hook) {
    original_free(ptr);
    return;
  }

  free_no_hook = true;

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

  if (!mempool_initialized || calloc_no_hook) {
    return original_calloc(num, size);
  }

  calloc_no_hook = true;
  void * ret = tlsf_calloc_wrapped(num, size);
  calloc_no_hook = false;
  return ret;
}

void * realloc(void * ptr, size_t new_size)
{
  static realloc_type original_realloc =
    reinterpret_cast<realloc_type>(dlsym(RTLD_NEXT, "realloc"));
  static __thread bool realloc_no_hook = false;

  if (!mempool_initialized || realloc_no_hook) {
    return original_realloc(ptr, new_size);
  }

  realloc_no_hook = true;

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

  if (!mempool_initialized || posix_memalign_no_hook) {
    return original_posix_memalign(memptr, alignment, size);
  }

  posix_memalign_no_hook = true;
  *memptr = tlsf_aligned_malloc(alignment, size);
  posix_memalign_no_hook = false;
  return 0;
}

void * memalign(size_t alignment, size_t size)
{
  static memalign_type original_memalign =
    reinterpret_cast<memalign_type>(dlsym(RTLD_NEXT, "memalign"));
  static __thread bool memalign_no_hook = false;

  if (!mempool_initialized || memalign_no_hook) {
    return original_memalign(alignment, size);
  }

  memalign_no_hook = true;
  void * ret = tlsf_aligned_malloc(alignment, size);
  memalign_no_hook = false;
  return ret;
}

void * aligned_alloc(size_t alignment, size_t size)
{
  static aligned_alloc_type original_aligned_alloc =
    reinterpret_cast<aligned_alloc_type>(dlsym(RTLD_NEXT, "aligned_alloc"));
  static __thread bool aligned_alloc_no_hook = false;

  if (!mempool_initialized || aligned_alloc_no_hook) {
    return original_aligned_alloc(alignment, size);
  }

  aligned_alloc_no_hook = true;
  void * ret = tlsf_aligned_malloc(alignment, size);
  aligned_alloc_no_hook = false;
  return ret;
}

void * valloc(size_t size)
{
  static valloc_type original_valloc = reinterpret_cast<valloc_type>(dlsym(RTLD_NEXT, "valloc"));
  static __thread bool valloc_no_hook = false;
  static size_t page_size = sysconf(_SC_PAGESIZE);

  if (!mempool_initialized || valloc_no_hook) {
    return original_valloc(size);
  }

  valloc_no_hook = true;
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

  if (!mempool_initialized || pvalloc_no_hook) {
    return original_pvalloc(size);
  }

  pvalloc_no_hook = true;
  void * ret = tlsf_aligned_malloc(page_size, rounded_up);
  pvalloc_no_hook = false;
  return ret;
}

size_t malloc_usable_size(void * ptr)
{
  static malloc_usable_size_type original_malloc_usable_size = \
    reinterpret_cast<malloc_usable_size_type>(dlsym(RTLD_NEXT, "malloc_usable_size"));
  size_t ret = original_malloc_usable_size(ptr);
  return ret;
}

using mallinfo_type = struct mallinfo (*)( void);
struct mallinfo mallinfo()
{
  static mallinfo_type orig = reinterpret_cast<mallinfo_type>(dlsym(RTLD_NEXT, "mallinfo"));
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
  return orig(param, value);
}

using malloc_trim_type = int (*)(size_t);
int malloc_trim(size_t pad)
{
  static malloc_trim_type orig =
    reinterpret_cast<malloc_trim_type>(dlsym(RTLD_NEXT, "malloc_trim"));
  return orig(pad);
}

using malloc_stats_type = void (*)(void);
void malloc_stats(void)
{
  static malloc_stats_type orig =
    reinterpret_cast<malloc_stats_type>(dlsym(RTLD_NEXT, "malloc_stats"));
  orig();
  return;
}

using malloc_info_type = int (*)(int, FILE *);
int malloc_info(int options, FILE * stream)
{
  static malloc_info_type orig =
    reinterpret_cast<malloc_info_type>(dlsym(RTLD_NEXT, "malloc_info"));
  return orig(options, stream);
}

} // extern "C"
