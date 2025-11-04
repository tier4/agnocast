use core::panic;
use std::{
    alloc::Layout,
    ffi::CStr,
    mem::size_of,
    os::raw::{c_int, c_void},
    ptr::{self, NonNull},
    sync::{
        atomic::{AtomicBool, Ordering},
        OnceLock,
    },
};

use crate::tlsf::TLSFAllocator;

mod tlsf;

// See: https://doc.rust-lang.org/src/std/sys/alloc/mod.rs.html
#[allow(clippy::if_same_then_else)]
const MIN_ALIGN: usize = if cfg!(target_arch = "x86_64") {
    16
} else {
    // Architectures other than x64 are not officially supported yet.
    // This value might need to be changed.
    16
};

type LibcStartMainType = unsafe extern "C" fn(
    main: unsafe extern "C" fn(c_int, *const *const u8) -> c_int,
    argc: c_int,
    argv: *const *const u8,
    init: unsafe extern "C" fn(),
    fini: unsafe extern "C" fn(),
    rtld_fini: unsafe extern "C" fn(),
    stack_end: *const c_void,
) -> c_int;
static ORIGINAL_LIBC_START_MAIN: OnceLock<LibcStartMainType> = OnceLock::new();

fn init_original_libc_start_main() -> LibcStartMainType {
    let symbol: &CStr = CStr::from_bytes_with_nul(b"__libc_start_main\0").unwrap();
    unsafe {
        let start_main_ptr: *mut c_void = libc::dlsym(libc::RTLD_NEXT, symbol.as_ptr());
        std::mem::transmute::<*mut c_void, LibcStartMainType>(start_main_ptr)
    }
}

type MallocType = unsafe extern "C" fn(usize) -> *mut c_void;
static ORIGINAL_MALLOC: OnceLock<MallocType> = OnceLock::new();

fn init_original_malloc() -> MallocType {
    let symbol: &CStr = CStr::from_bytes_with_nul(b"malloc\0").unwrap();
    unsafe {
        let malloc_ptr: *mut c_void = libc::dlsym(libc::RTLD_NEXT, symbol.as_ptr());
        std::mem::transmute::<*mut c_void, MallocType>(malloc_ptr)
    }
}

type FreeType = unsafe extern "C" fn(*mut c_void) -> ();
static ORIGINAL_FREE: OnceLock<FreeType> = OnceLock::new();

fn init_original_free() -> FreeType {
    let symbol: &CStr = CStr::from_bytes_with_nul(b"free\0").unwrap();
    unsafe {
        let free_ptr: *mut c_void = libc::dlsym(libc::RTLD_NEXT, symbol.as_ptr());
        std::mem::transmute::<*mut c_void, FreeType>(free_ptr)
    }
}

type CallocType = unsafe extern "C" fn(usize, usize) -> *mut c_void;
static ORIGINAL_CALLOC: OnceLock<CallocType> = OnceLock::new();

fn init_original_calloc() -> CallocType {
    let symbol: &CStr = CStr::from_bytes_with_nul(b"calloc\0").unwrap();
    unsafe {
        let calloc_ptr: *mut c_void = libc::dlsym(libc::RTLD_NEXT, symbol.as_ptr());
        std::mem::transmute::<*mut c_void, CallocType>(calloc_ptr)
    }
}

type ReallocType = unsafe extern "C" fn(*mut c_void, usize) -> *mut c_void;
static ORIGINAL_REALLOC: OnceLock<ReallocType> = OnceLock::new();

fn init_original_realloc() -> ReallocType {
    let symbol: &CStr = CStr::from_bytes_with_nul(b"realloc\0").unwrap();
    unsafe {
        let realloc_ptr: *mut c_void = libc::dlsym(libc::RTLD_NEXT, symbol.as_ptr());
        std::mem::transmute::<*mut c_void, ReallocType>(realloc_ptr)
    }
}

type PosixMemalignType = unsafe extern "C" fn(&mut *mut c_void, usize, usize) -> i32;
static ORIGINAL_POSIX_MEMALIGN: OnceLock<PosixMemalignType> = OnceLock::new();

fn init_original_posix_memalign() -> PosixMemalignType {
    let symbol: &CStr = CStr::from_bytes_with_nul(b"posix_memalign\0").unwrap();
    unsafe {
        let posix_memalign_ptr: *mut c_void = libc::dlsym(libc::RTLD_NEXT, symbol.as_ptr());
        std::mem::transmute(posix_memalign_ptr)
    }
}

type AlignedAllocType = unsafe extern "C" fn(usize, usize) -> *mut c_void;
static ORIGINAL_ALIGNED_ALLOC: OnceLock<AlignedAllocType> = OnceLock::new();

fn init_original_aligned_alloc() -> AlignedAllocType {
    let symbol: &CStr = CStr::from_bytes_with_nul(b"aligned_alloc\0").unwrap();
    unsafe {
        let aligned_alloc_ptr: *mut c_void = libc::dlsym(libc::RTLD_NEXT, symbol.as_ptr());
        std::mem::transmute(aligned_alloc_ptr)
    }
}

type MemalignType = unsafe extern "C" fn(usize, usize) -> *mut c_void;
static ORIGINAL_MEMALIGN: OnceLock<MemalignType> = OnceLock::new();

fn init_original_memalign() -> MemalignType {
    let symbol: &CStr = CStr::from_bytes_with_nul(b"memalign\0").unwrap();
    unsafe {
        let memalign_ptr: *mut c_void = libc::dlsym(libc::RTLD_NEXT, symbol.as_ptr());
        std::mem::transmute(memalign_ptr)
    }
}

static IS_FORKED_CHILD: AtomicBool = AtomicBool::new(false);

#[cfg(not(test))]
extern "C" fn post_fork_handler_in_child() {
    IS_FORKED_CHILD.store(true, Ordering::Relaxed);
}

struct AgnocastSharedMemory {
    start: usize,
    end: usize,
}

impl AgnocastSharedMemory {
    #[cfg(not(test))]
    /// Initializes shared memory.
    ///
    /// # Safety
    /// - After this function returns, the range from `start` to `end` must be mapped and accessible.
    unsafe fn new() -> Self {
        use std::{ffi::CString, os::raw::c_char};

        extern "C" {
            fn initialize_agnocast(
                size: usize,
                version: *const c_char,
                version_str_length: usize,
            ) -> *mut c_void;
        }

        let result = unsafe { libc::pthread_atfork(None, None, Some(post_fork_handler_in_child)) };

        if result != 0 {
            panic!(
                "[ERROR] [Agnocast] agnocast_heaphook internal error: pthread_atfork failed: {}",
                std::io::Error::from_raw_os_error(result)
            )
        }

        let mempool_size_env = std::env::var("AGNOCAST_MEMPOOL_SIZE").unwrap_or_else(|error| {
            panic!("[ERROR] [Agnocast] {}: AGNOCAST_MEMPOOL_SIZE", error);
        });

        let mempool_size = mempool_size_env.parse::<usize>().unwrap_or_else(|error| {
            panic!("[ERROR] [Agnocast] {}: AGNOCAST_MEMPOOL_SIZE", error);
        });

        let page_size = unsafe { libc::sysconf(libc::_SC_PAGESIZE) as usize };
        let aligned_size = (mempool_size + page_size - 1) & !(page_size - 1);

        let version = env!("CARGO_PKG_VERSION");
        let c_version = CString::new(version).unwrap();

        let mempool_ptr = unsafe {
            initialize_agnocast(aligned_size, c_version.as_ptr(), c_version.as_bytes().len())
        };

        let start = mempool_ptr as usize;
        let end = start + mempool_size;

        Self { start, end }
    }

    #[cfg(test)]
    /// Initializes shared memory.
    ///
    /// # Safety
    /// - After this function returns, the range from `start` to `end` must be mapped and accessible.
    unsafe fn new() -> Self {
        let mempool_size = 1024 * 1024;
        let mempool_ptr = 0x121000000000 as *mut c_void;

        let shm_fd = unsafe {
            libc::shm_open(
                CStr::from_bytes_with_nul(b"/agnocast_test\0")
                    .unwrap()
                    .as_ptr(),
                libc::O_CREAT | libc::O_RDWR,
                0o600,
            )
        };
        assert!(shm_fd != -1);

        let result = unsafe { libc::ftruncate(shm_fd, mempool_size as libc::off_t) };
        assert!(result != -1);

        let mmap_ptr = unsafe {
            libc::mmap(
                mempool_ptr,
                mempool_size,
                libc::PROT_READ | libc::PROT_WRITE,
                libc::MAP_SHARED | libc::MAP_FIXED_NOREPLACE,
                shm_fd,
                0,
            )
        };
        assert!(mmap_ptr != libc::MAP_FAILED);

        let result = unsafe {
            libc::shm_unlink(
                CStr::from_bytes_with_nul(b"/agnocast_test\0")
                    .unwrap()
                    .as_ptr(),
            )
        };
        assert!(result != -1);

        let start = mempool_ptr as usize;
        let end = start + mempool_size;

        Self { start, end }
    }

    #[inline]
    fn is_shared(&self, ptr: *const u8) -> bool {
        let addr = ptr as usize;
        self.start <= addr && addr <= self.end
    }

    #[inline]
    fn len(&self) -> usize {
        self.end - self.start
    }

    #[inline]
    fn as_ptr(&self) -> *const u8 {
        self.start as *const u8
    }
}

static AGNOCAST_SHARED_MEMORY: OnceLock<AgnocastSharedMemory> = OnceLock::new();

struct AgnocastSharedMemoryAllocator<A: SharedMemoryAllocator> {
    inner: A,
}

impl<A: SharedMemoryAllocator> AgnocastSharedMemoryAllocator<A> {
    #[inline]
    fn new(shm: &'static AgnocastSharedMemory) -> Self {
        Self { inner: A::new(shm) }
    }
}

static AGNOCAST_SHARED_MEMORY_ALLOCATOR: OnceLock<AgnocastSharedMemoryAllocator<TLSFAllocator>> =
    OnceLock::new();

#[inline]
fn is_shared(ptr: *const u8) -> bool {
    if let Some(shm) = AGNOCAST_SHARED_MEMORY.get() {
        shm.is_shared(ptr)
    } else {
        false
    }
}

/// A memory allocator that manages shared memory.
///
/// # Safety
///
/// The `SharedMemoryAllocator` is an `unsafe` trait for a number of reasons, and implementors must ensure that they adhere to these contracts:
///
/// * The memory allocator must not unwind. A panic in any of its functions may lead to memory unsafety.
unsafe trait SharedMemoryAllocator {
    /// Initializes the allocator with the given `shm`.
    fn new(shm: &'static AgnocastSharedMemory) -> Self;

    /// Attempts to allocate a block of memory as described by the given `layout`.
    ///
    /// # Safety
    ///
    /// * If this returns `Some`, then the returned pointer must be within the range of `shm` passed to `SharedMemoryAllocator::new`
    /// and satisfy the requirements of `layout`.
    fn allocate(&self, layout: Layout) -> Option<NonNull<u8>>;

    /// Attempts to reallocate the block of memory at the given `ptr` to fit the `new_layout`.
    ///
    /// # Safety
    ///
    /// * `ptr` must denote a block of memory currently allocated via this allocator.
    /// * If this returns `Some`, then the returned pointer must be within the range of `shm` passed to `SharedMemoryAllocator::new`
    /// and satisfy the requirements of `new_layout`.
    fn reallocate(&self, ptr: NonNull<u8>, new_layout: Layout) -> Option<NonNull<u8>>;

    /// Deallocates the block of memory at the given `ptr`.
    ///
    /// # Safety
    ///
    /// * `ptr` must denote a block of memory currently allocated via this allocator.
    fn deallocate(&self, ptr: NonNull<u8>);
}

/// Determines when to use the heap.
///
/// We must use the heap when any of the following conditions hold:
/// * When the shared memory allocator is not initialized.
/// * When in a forked process (since we do not expect forked processes to operate on shared memory).
/// * When `agnocast_get_borrowed_publisher_num` returns 0, i.e., when the publisher is not using shared memory.
#[cfg(not(test))]
fn should_use_heap() -> bool {
    extern "C" {
        fn agnocast_get_borrowed_publisher_num() -> u32;
    }

    if IS_FORKED_CHILD.load(Ordering::Relaxed) {
        return true;
    }

    unsafe {
        if agnocast_get_borrowed_publisher_num() == 0 {
            return true;
        }
    }

    // We do not need to explicitly check whether the shared memory allocator is initialized,
    // because it is initialized in `__libc_start_main`, and when `agnocast_get_borrowed_publisher_num` returns a non-zero value,
    // meaning that the `main` function is running, we can assume the allocator is already initialized.
    false
}

#[cfg(test)]
fn should_use_heap() -> bool {
    // In tests, we use the heap only when the allocator is uninitialized.
    AGNOCAST_SHARED_MEMORY_ALLOCATOR.get().is_none()
}

/// # Safety
///
#[no_mangle]
pub unsafe extern "C" fn __libc_start_main(
    main: unsafe extern "C" fn(c_int, *const *const u8) -> c_int,
    argc: c_int,
    argv: *const *const u8,
    init: unsafe extern "C" fn(),
    fini: unsafe extern "C" fn(),
    rtld_fini: unsafe extern "C" fn(),
    stack_end: *const c_void,
) -> c_int {
    if AGNOCAST_SHARED_MEMORY
        .set(AgnocastSharedMemory::new())
        .is_err()
    {
        panic!("[ERROR] [Agnocast] Shared memory has already been initialized.");
    }

    if AGNOCAST_SHARED_MEMORY_ALLOCATOR
        .set(AgnocastSharedMemoryAllocator::new(
            AGNOCAST_SHARED_MEMORY.get().unwrap(),
        ))
        .is_err()
    {
        panic!("[ERROR] [Agnocast] The memory allocator has already been initialized.");
    }

    (*ORIGINAL_LIBC_START_MAIN.get_or_init(init_original_libc_start_main))(
        main, argc, argv, init, fini, rtld_fini, stack_end,
    )
}

#[no_mangle]
pub extern "C" fn malloc(size: usize) -> *mut c_void {
    if should_use_heap() {
        return unsafe { (*ORIGINAL_MALLOC.get_or_init(init_original_malloc))(size) };
    }

    // The default global allocator assumes `malloc` returns 16-byte aligned address (on x64 platforms).
    // See: https://doc.rust-lang.org/beta/src/std/sys/alloc/unix.rs.html#13-15
    let layout = match Layout::from_size_align(size, MIN_ALIGN) {
        Ok(layout) => layout,
        Err(_) => return ptr::null_mut(),
    };

    match AGNOCAST_SHARED_MEMORY_ALLOCATOR
        .get()
        .unwrap()
        .inner
        .allocate(layout)
    {
        Some(non_null_ptr) => non_null_ptr.as_ptr().cast(),
        None => ptr::null_mut(),
    }
}

/// # Safety
///
#[no_mangle]
pub unsafe extern "C" fn free(ptr: *mut c_void) {
    if ptr.is_null() {
        return;
    }

    if !is_shared(ptr.cast()) {
        return (*ORIGINAL_FREE.get_or_init(init_original_free))(ptr);
    }

    if IS_FORKED_CHILD.load(Ordering::Relaxed) {
        // Ignore unexpected calls to `free`.
        return;
    }

    let non_null_ptr = unsafe { NonNull::new_unchecked(ptr.cast()) };

    AGNOCAST_SHARED_MEMORY_ALLOCATOR
        .get()
        .unwrap()
        .inner
        .deallocate(non_null_ptr);
}

#[no_mangle]
pub extern "C" fn calloc(num: usize, size: usize) -> *mut c_void {
    if should_use_heap() {
        return unsafe { (*ORIGINAL_CALLOC.get_or_init(init_original_calloc))(num, size) };
    }

    // The default global allocator assumes `calloc` returns 16-byte aligned address (on x64 platforms).
    // See: https://doc.rust-lang.org/beta/src/std/sys/alloc/unix.rs.html#35-36
    let size = num * size;
    let layout = match Layout::from_size_align(size, MIN_ALIGN) {
        Ok(layout) => layout,
        Err(_) => return ptr::null_mut(),
    };

    match AGNOCAST_SHARED_MEMORY_ALLOCATOR
        .get()
        .unwrap()
        .inner
        .allocate(layout)
    {
        Some(non_null_ptr) => {
            let ptr = non_null_ptr.as_ptr();
            unsafe {
                ptr::write_bytes(ptr, 0, size);
            }
            ptr.cast()
        }
        None => ptr::null_mut(),
    }
}

/// # Safety
///
#[no_mangle]
pub unsafe extern "C" fn realloc(ptr: *mut c_void, new_size: usize) -> *mut c_void {
    // If `ptr` is NULL, then the call is equivalent to `malloc(size)`.
    if ptr.is_null() {
        return malloc(new_size);
    }

    if !is_shared(ptr.cast()) {
        return (*ORIGINAL_REALLOC.get_or_init(init_original_realloc))(ptr, new_size);
    }

    if should_use_heap() {
        // Ignore unexpected calls to `realloc`.
        return ptr::null_mut();
    }

    let non_null_ptr = unsafe { NonNull::new_unchecked(ptr.cast()) };

    // The default global allocator assumes `realloc` returns 16-byte aligned address (on x64 platforms).
    // See: https://doc.rust-lang.org/beta/src/std/sys/alloc/unix.rs.html#53-54
    let new_layout = match Layout::from_size_align(new_size, MIN_ALIGN) {
        Ok(layout) => layout,
        Err(_) => return ptr::null_mut(),
    };

    match AGNOCAST_SHARED_MEMORY_ALLOCATOR
        .get()
        .unwrap()
        .inner
        .reallocate(non_null_ptr, new_layout)
    {
        Some(non_null_ptr) => non_null_ptr.as_ptr().cast(),
        None => ptr::null_mut(),
    }
}

#[no_mangle]
pub extern "C" fn posix_memalign(memptr: &mut *mut c_void, alignment: usize, size: usize) -> i32 {
    if should_use_heap() {
        return unsafe {
            (*ORIGINAL_POSIX_MEMALIGN.get_or_init(init_original_posix_memalign))(
                memptr, alignment, size,
            )
        };
    }

    // `alignment` must be a power of two and a multiple of `sizeof(void *)`.
    if !alignment.is_power_of_two() || alignment & (size_of::<*mut c_void>() - 1) != 0 {
        return libc::EINVAL;
    }

    let layout = match Layout::from_size_align(size, alignment) {
        Ok(layout) => layout,
        Err(_) => return libc::ENOMEM,
    };

    match AGNOCAST_SHARED_MEMORY_ALLOCATOR
        .get()
        .unwrap()
        .inner
        .allocate(layout)
    {
        Some(non_null_ptr) => {
            *memptr = non_null_ptr.as_ptr().cast();
            0
        }
        None => libc::ENOMEM,
    }
}

#[no_mangle]
pub extern "C" fn aligned_alloc(alignment: usize, size: usize) -> *mut c_void {
    if should_use_heap() {
        return unsafe {
            (*ORIGINAL_ALIGNED_ALLOC.get_or_init(init_original_aligned_alloc))(alignment, size)
        };
    }

    // `alignment` should be a power of two and `size` should be a multiple of `alignment`.
    if !alignment.is_power_of_two() || size & (alignment - 1) != 0 {
        return ptr::null_mut();
    }

    let layout = match Layout::from_size_align(size, alignment.max(MIN_ALIGN)) {
        Ok(layout) => layout,
        Err(_) => return ptr::null_mut(),
    };

    match AGNOCAST_SHARED_MEMORY_ALLOCATOR
        .get()
        .unwrap()
        .inner
        .allocate(layout)
    {
        Some(non_null_ptr) => non_null_ptr.as_ptr().cast(),
        None => std::ptr::null_mut(),
    }
}

#[no_mangle]
pub extern "C" fn memalign(alignment: usize, size: usize) -> *mut c_void {
    if should_use_heap() {
        return unsafe {
            (*ORIGINAL_MEMALIGN.get_or_init(init_original_memalign))(alignment, size)
        };
    }

    // `alignment` must be a power of two.
    let layout = match Layout::from_size_align(size, alignment) {
        Ok(layout) => layout,
        Err(_) => return ptr::null_mut(),
    };

    match AGNOCAST_SHARED_MEMORY_ALLOCATOR
        .get()
        .unwrap()
        .inner
        .allocate(layout)
    {
        Some(non_null_ptr) => non_null_ptr.as_ptr().cast(),
        None => std::ptr::null_mut(),
    }
}

#[no_mangle]
pub extern "C" fn valloc(_size: usize) -> *mut c_void {
    panic!("[ERROR] [Agnocast] valloc is not supported");
}

#[no_mangle]
pub extern "C" fn pvalloc(_size: usize) -> *mut c_void {
    panic!("[ERROR] [Agnocast] pvalloc is not supported");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_malloc_normal() {
        let sizes = (1..=MIN_ALIGN * 2).filter(|x| x.is_power_of_two());

        for size in sizes {
            let ptr = unsafe { libc::malloc(size) } as *mut u8;

            assert!(!ptr.is_null());
            assert!(is_shared(ptr.cast()));

            let alignment = if size <= MIN_ALIGN { size } else { MIN_ALIGN };
            assert!(
                ptr as usize % alignment == 0,
                "the pointer must be suitably aligned so that it can store any object whose size is less than or equal to the requested size and has fundamental alignment."
            );
        }
    }

    #[test]
    fn test_malloc_with_zero_size() {
        // If the size is 0, the behavior is implementation-defined. It must not panic.
        let _ = unsafe { libc::malloc(0) };
    }

    #[test]
    fn test_malloc_with_excessive_size() {
        assert!(
            unsafe { libc::malloc(usize::MAX) }.is_null(),
            "malloc should return NULL if the requested size is excessively large."
        );
    }

    #[test]
    fn test_calloc_normal() {
        let obj_sizes = (1..=MIN_ALIGN).filter(|x| x.is_power_of_two());
        let obj_nums = [1, 2];

        for obj_size in obj_sizes {
            for obj_num in obj_nums {
                let total_size = obj_size * obj_num;

                let ptr = unsafe { libc::calloc(obj_num, obj_size) };
                assert!(!ptr.is_null());
                assert!(is_shared(ptr.cast()));

                // Is it possible to relax the constraint by replacing `total_size` with `obj_size`?
                let alignment = if total_size <= MIN_ALIGN {
                    total_size
                } else {
                    MIN_ALIGN
                };

                assert!(
                    ptr as usize % alignment == 0,
                    "the pointer must be suitably aligned so that it can store any object whose size is less than or equal to the requested size and has fundamental alignment."
                );

                for i in 0..total_size {
                    let val = unsafe { *(ptr as *mut u8).byte_add(i) };
                    assert!(val == 0, "The allocated memory must be zero-initialized.");
                }
            }
        }
    }

    #[test]
    fn test_calloc_with_zero_size() {
        // If the size is 0, the behavior is implementation-defined. It must not panic.
        let _ = unsafe { libc::calloc(0, 1) };
        let _ = unsafe { libc::calloc(1, 0) };
    }

    #[test]
    fn test_calloc_with_overflow_size() {
        assert!(
            unsafe { libc::calloc(usize::MAX, 2) }.is_null(),
            "calloc should return NULL if the total size does not fit in size_t."
        );
        assert!(
            unsafe { libc::calloc(usize::MAX, 2) }.is_null(),
            "calloc should return NULL if the total size does not fit in size_t."
        );
    }

    #[test]
    fn test_realloc_normal() {
        let old_size = MIN_ALIGN;
        let new_size = old_size * 2;

        let old_ptr = unsafe { libc::malloc(old_size) };
        assert!(!old_ptr.is_null());
        assert!(is_shared(old_ptr.cast()));

        for i in 0..old_size {
            unsafe { *((old_ptr as *mut u8).byte_add(i)) = i as u8 };
        }

        let new_ptr = unsafe { libc::realloc(old_ptr, new_size) };
        assert!(!new_ptr.is_null());
        assert!(is_shared(new_ptr.cast()));

        let copy_size = new_size.min(old_size);
        for i in 0..copy_size {
            let val = unsafe { *(new_ptr as *mut u8).byte_add(i) };
            assert!(val == i as u8, "The contents of the new object shall be the same as that of the old object up to the lesser of the new and old sizes.");
        }
    }

    #[test]
    fn test_realloc_with_null_pointer() {
        // If the pointer with `NULL`, `realloc` bahaves like `malloc`.

        // If the size is 0, the behavior is implementation-defined. It must not panic.
        let _ = unsafe { libc::realloc(ptr::null_mut(), 0) };

        let sizes = (1..=MIN_ALIGN * 2).filter(|x| x.is_power_of_two());

        for size in sizes {
            let ptr = unsafe { libc::malloc(size) } as *mut u8;

            assert!(!ptr.is_null());
            assert!(is_shared(ptr.cast()));

            let alignment = if size <= MIN_ALIGN { size } else { MIN_ALIGN };
            assert!(
                ptr as usize % alignment == 0,
                "the pointer must be suitably aligned so that it can store any object whose size is less than or equal to the requested size and has fundamental alignment."
            );
        }
    }

    #[test]
    fn test_realloc_with_excessive_size() {
        assert!(
            unsafe { libc::realloc(ptr::null_mut(), usize::MAX) }.is_null(),
            "realloc should return NULL if the requested size is excessively large."
        );

        let ptr = unsafe { libc::malloc(1) };
        assert!(!ptr.is_null());
        assert!(
            unsafe { libc::realloc(ptr, usize::MAX) }.is_null(),
            "realloc should return NULL if the requested size is excessively large."
        );
    }

    #[test]
    fn test_posix_memalign_normal() {
        let alignment = size_of::<*mut c_void>();
        let sizes = (1..=MIN_ALIGN).filter(|x| x.is_power_of_two());

        // NOTE:
        // Unlike `aligned_alloc`, `posix_memalign` only needs to satisfy the specified alignment requirement.
        // That is, for example, when the size is 16 and the alignment is 8, it is allowed to return an 8 byte-aligned pointer.
        // `aligned_alloc`, on the other hand, must return a 16-byte aligned pointer even in this case.
        for size in sizes {
            let mut ptr = ptr::null_mut();
            let result = unsafe { libc::posix_memalign(&mut ptr, alignment, size) };
            assert!(result == 0);
            assert!(!ptr.is_null());
            assert!(is_shared(ptr.cast()));
            assert!(
                ptr as usize % alignment == 0,
                "The pointer must satisfy the specified alignment requirement."
            );
        }
    }

    #[test]
    fn test_posix_memalign_with_zero_size() {
        // If the size is 0, the behavior is implementation-defined. It must not panic.
        let mut ptr: *mut c_void = ptr::null_mut();
        let _ = unsafe { libc::posix_memalign(&mut ptr, size_of::<*mut c_void>(), 0) };
    }

    #[test]
    fn test_posix_memalign_with_invalid_alignment() {
        let mut ptr: *mut c_void = ptr::null_mut();

        assert_eq!(
            unsafe { libc::posix_memalign(&mut ptr, 0, 1) },
            libc::EINVAL,
            "posix_memalign should return EINVAL if the alignment is not a power of two"
        );
        assert!(ptr.is_null(), "If posix_memalign fails, the value of the pointer must eihter remain unchanged or be NULL.");

        assert_eq!(
            unsafe {libc::posix_memalign(&mut ptr, size_of::<*mut c_void>() / 2, 1)},
            libc::EINVAL,
            "posix_memalign should return EINVAL if the alignment is not a multiple of `sizeof(void *)`"
        );
        assert!(ptr.is_null(), "If posix_memalign fails, the value of the pointer must eihter remain unchanged or be NULL.");
    }

    #[test]
    fn test_posix_memalign_with_excessive_size() {
        let mut ptr: *mut c_void = ptr::null_mut();
        assert_eq!(
            unsafe { libc::posix_memalign(&mut ptr, size_of::<*mut c_void>(), usize::MAX) },
            libc::ENOMEM,
            "posix_memalign should return ENOMEM if the requested size is excessively large."
        );
        assert!(ptr.is_null(), "If posix_memalign fails, the value of the pointer must eihter remain unchanged or be NULL.");
    }

    #[test]
    fn test_aligned_alloc_with_fundamental_alignments() {
        let alignments = (1..=MIN_ALIGN).filter(|x| x.is_power_of_two());
        let size = MIN_ALIGN;
        for alignment in alignments {
            let ptr = unsafe { libc::aligned_alloc(alignment, size) };
            assert!(!ptr.is_null());
            assert!(is_shared(ptr.cast()));
            assert!(
                ptr as usize % MIN_ALIGN == 0,
                "the pointer must be suitably aligned so that it can store any object whose size is less than or equal to the requested size and has fundamental alignment."
            );
        }
    }

    #[test]
    fn test_aligned_alloc_with_extended_alignments() {
        // Assume that alignmets up to 2048 are supported. This assumption may change in the future.
        let alignments = (MIN_ALIGN + 1..4096).filter(|x| x.is_power_of_two());

        for alignment in alignments {
            let size = alignment;
            let ptr = unsafe { libc::aligned_alloc(alignment, size) };
            assert!(!ptr.is_null());
            assert!(is_shared(ptr.cast()));
            assert!(
                ptr as usize % alignment == 0,
                "the pointer must be aligned to the requested alignment."
            );
        }
    }

    #[test]
    fn test_aligned_alloc_with_zero_size() {
        // If the size is 0, the behavior is implementation-defined. It must not panic.
        let _ = unsafe { libc::aligned_alloc(1, 0) };
    }

    #[test]
    fn test_aligned_alloc_with_invalid_alignment() {
        assert!(
            unsafe { libc::aligned_alloc(0, 8) }.is_null(),
            "aligned_alloc should return NULL if the alignment is not a power of two"
        );

        assert!(
            unsafe { libc::aligned_alloc(2, 7) }.is_null(),
            "aligned_alloc should return NULL if the size is not a multiple of the alignment"
        );
    }

    #[test]
    fn test_aligned_alloc_with_excessive_size() {
        assert!(
            unsafe { libc::aligned_alloc(1, usize::MAX) }.is_null(),
            "aligned_alloc should return NULL if the requested size is excessively large."
        );
    }

    #[test]
    fn test_memalign_normal() {
        // Assume that alignmets up to 2048 are supported. This assumption may change in the future.
        let alignments = (1..4096usize).filter(|x| x.is_power_of_two());
        let size = MIN_ALIGN;

        // NOTE:
        // `memalign` is already obsolute, and C23 does not define its behavior.
        // Therefore, it is unclear wheter `memalign` should satisfy the same alignment constaints as `aligned_alloc`.
        // Currently, this constraint is not required, and `memalign` only checks that the alignment is a power of two.
        // This behavior may change in the future.
        for alignment in alignments {
            let ptr = unsafe { libc::memalign(alignment, size) };
            assert!(!ptr.is_null());
            assert!(is_shared(ptr.cast()));
            assert!(
                ptr as usize % alignment == 0,
                "the pointer must be aligned to the requested alignment."
            );
        }
    }

    #[test]
    fn test_memalign_with_invalid_alignment() {
        assert!(
            unsafe { libc::memalign(0, 8) }.is_null(),
            "memalign should return NULL if the alignment is not a power of two"
        );
    }

    #[test]
    fn test_memalign_with_excessive_size() {
        assert!(
            unsafe { libc::memalign(1, usize::MAX) }.is_null(),
            "memalign should return NULL if the requested size is excessively large."
        );
    }
}
