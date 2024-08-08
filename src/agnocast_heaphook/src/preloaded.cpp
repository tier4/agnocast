#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif

#include "agnocast.hpp"
#include "tlsf/tlsf.h"

#include <dlfcn.h>
#include <fcntl.h>
#include <malloc.h>
#include <pthread.h>
#include <stdio.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

#include <atomic>
#include <string>
#include <unordered_map>

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
static size_t INITIAL_MEMPOOL_SIZE = 100 * 1000 * 1000;     // default: 100MB
static size_t ADDITIONAL_MEMPOOL_SIZE = 100 * 1000 * 1000;  // default: 100MB
static std::unordered_map<void *, void *> * aligned2orig;

static pthread_mutex_t init_mtx = PTHREAD_MUTEX_INITIALIZER;
static std::atomic<bool> mempool_initialized = false;

static pthread_mutex_t tlsf_mtx = PTHREAD_MUTEX_INITIALIZER;

__thread bool is_in_hooked_call = false;

void initialize_mempool()
{
  if (mempool_initialized) return;

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

  void * ret = agnocast::initialize_agnocast();

  mempool_ptr = reinterpret_cast<char *>(ret);

  memset(mempool_ptr, 0, INITIAL_MEMPOOL_SIZE);
  init_memory_pool(INITIAL_MEMPOOL_SIZE, mempool_ptr);  // tlsf library function

  aligned2orig = new std::unordered_map<void *, void *>();
  // aligned2orig.reserve(10000000);

  mempool_initialized = true;

  pthread_mutex_unlock(&init_mtx);
}

template <class F>
static void * tlsf_allocate_internal(F allocate)
{
  pthread_mutex_lock(&tlsf_mtx);

  void * ret = allocate();

  size_t multiplier = 1;
  while (ret == NULL) {
    void * addr = mmap(
      NULL, multiplier * ADDITIONAL_MEMPOOL_SIZE, PROT_READ | PROT_WRITE,
      MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    add_new_area(addr, multiplier * ADDITIONAL_MEMPOOL_SIZE, mempool_ptr);  // tlsf library function

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
  return tlsf_allocate_internal([size] { return tlsf_malloc(size); });
}

static void * tlsf_calloc_wrapped(size_t num, size_t size)
{
  return tlsf_allocate_internal([num, size] { return tlsf_calloc(num, size); });
}

static void * tlsf_realloc_wrapped(void * ptr, size_t new_size)
{
  return tlsf_allocate_internal([ptr, new_size] { return tlsf_realloc(ptr, new_size); });
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
  void * aligned = reinterpret_cast<void *>(
    reinterpret_cast<uint64_t>(addr) + alignment - reinterpret_cast<uint64_t>(addr) % alignment);
  (*aligned2orig)[aligned] = addr;

  // printf("In tlsf_aligned_malloc: orig=%p -> aligned=%p\n", addr, aligned);

  return aligned;
}

extern "C" {

void * malloc(size_t size)
{
  static malloc_type original_malloc = reinterpret_cast<malloc_type>(dlsym(RTLD_NEXT, "malloc"));

  if (is_in_hooked_call) {
    return original_malloc(size);
  }

  is_in_hooked_call = true;
  initialize_mempool();
  void * ret = tlsf_malloc_wrapped(size);
  is_in_hooked_call = false;

  return ret;
}

void free(void * ptr)
{
  static free_type original_free = reinterpret_cast<free_type>(dlsym(RTLD_NEXT, "free"));

  if (is_in_hooked_call) {
    original_free(ptr);
    return;
  }

  is_in_hooked_call = true;
  initialize_mempool();

  auto it = aligned2orig->find(ptr);
  if (it != aligned2orig->end()) {
    ptr = it->second;
    aligned2orig->erase(it);
  }

  tlsf_free_wrapped(ptr);
  is_in_hooked_call = false;
}

void * calloc(size_t num, size_t size)
{
  static calloc_type original_calloc = reinterpret_cast<calloc_type>(dlsym(RTLD_NEXT, "calloc"));

  if (is_in_hooked_call) {
    return original_calloc(num, size);
  }

  is_in_hooked_call = true;
  initialize_mempool();
  void * ret = tlsf_calloc_wrapped(num, size);
  is_in_hooked_call = false;
  return ret;
}

void * realloc(void * ptr, size_t new_size)
{
  static realloc_type original_realloc =
    reinterpret_cast<realloc_type>(dlsym(RTLD_NEXT, "realloc"));

  if (is_in_hooked_call) {
    return original_realloc(ptr, new_size);
  }

  is_in_hooked_call = true;
  initialize_mempool();

  auto it = aligned2orig->find(ptr);
  if (it != aligned2orig->end()) {
    ptr = it->second;
    aligned2orig->erase(ptr);
  }

  void * ret = tlsf_realloc_wrapped(ptr, new_size);
  is_in_hooked_call = false;
  return ret;
}

int posix_memalign(void ** memptr, size_t alignment, size_t size)
{
  static posix_memalign_type original_posix_memalign =
    reinterpret_cast<posix_memalign_type>(dlsym(RTLD_NEXT, "posix_memalign"));

  if (is_in_hooked_call) {
    return original_posix_memalign(memptr, alignment, size);
  }

  is_in_hooked_call = true;
  initialize_mempool();
  *memptr = tlsf_aligned_malloc(alignment, size);
  is_in_hooked_call = false;
  return 0;
}

void * memalign(size_t alignment, size_t size)
{
  static memalign_type original_memalign =
    reinterpret_cast<memalign_type>(dlsym(RTLD_NEXT, "memalign"));

  if (is_in_hooked_call) {
    return original_memalign(alignment, size);
  }

  is_in_hooked_call = true;
  initialize_mempool();
  void * ret = tlsf_aligned_malloc(alignment, size);
  is_in_hooked_call = false;
  return ret;
}

void * aligned_alloc(size_t alignment, size_t size)
{
  static aligned_alloc_type original_aligned_alloc =
    reinterpret_cast<aligned_alloc_type>(dlsym(RTLD_NEXT, "aligned_alloc"));

  if (is_in_hooked_call) {
    return original_aligned_alloc(alignment, size);
  }

  is_in_hooked_call = true;
  initialize_mempool();
  void * ret = tlsf_aligned_malloc(alignment, size);
  is_in_hooked_call = false;
  return ret;
}

void * valloc(size_t size)
{
  static valloc_type original_valloc = reinterpret_cast<valloc_type>(dlsym(RTLD_NEXT, "valloc"));
  static size_t page_size = sysconf(_SC_PAGESIZE);

  if (is_in_hooked_call) {
    return original_valloc(size);
  }

  is_in_hooked_call = true;
  initialize_mempool();
  void * ret = tlsf_aligned_malloc(page_size, size);
  is_in_hooked_call = false;
  return ret;
}

// pvalloc() rounds the size of the allocation up to the next multiple of the system page size.
void * pvalloc(size_t size)
{
  static pvalloc_type original_pvalloc =
    reinterpret_cast<pvalloc_type>(dlsym(RTLD_NEXT, "pvalloc"));
  static size_t page_size = sysconf(_SC_PAGESIZE);
  size_t rounded_up = size + (page_size - size % page_size) % page_size;

  if (is_in_hooked_call) {
    return original_pvalloc(size);
  }

  is_in_hooked_call = true;
  initialize_mempool();
  void * ret = tlsf_aligned_malloc(page_size, rounded_up);
  is_in_hooked_call = false;
  return ret;
}

size_t malloc_usable_size(void * ptr)
{
  static malloc_usable_size_type original_malloc_usable_size =
    reinterpret_cast<malloc_usable_size_type>(dlsym(RTLD_NEXT, "malloc_usable_size"));
  initialize_mempool();
  size_t ret = original_malloc_usable_size(ptr);
  return ret;
}

using mallinfo_type = struct mallinfo (*)(void);
struct mallinfo mallinfo()
{
  static mallinfo_type orig = reinterpret_cast<mallinfo_type>(dlsym(RTLD_NEXT, "mallinfo"));
  return orig();
}

#ifdef HAVE_MALLINFO2
using mallinfo2_type = struct mallinfo2 (*)(void);
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

}  // extern "C"
