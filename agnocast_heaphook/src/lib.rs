use rlsf::Tlsf;
use std::{
    alloc::Layout,
    ffi::{CStr, CString},
    mem::{size_of, MaybeUninit},
    os::raw::{c_char, c_int, c_void},
    ptr::{self, NonNull},
    sync::{
        atomic::{AtomicBool, AtomicUsize, Ordering},
        Mutex, OnceLock,
    },
};

extern "C" {
    fn initialize_agnocast(
        size: usize,
        version: *const c_char,
        version_str_length: usize,
    ) -> *mut c_void;
    fn agnocast_get_borrowed_publisher_num() -> u32;
}

const POINTER_SIZE: usize = std::mem::size_of::<&usize>();
const POINTER_ALIGN: usize = std::mem::align_of::<&usize>();
const LAYOUT_ALIGN: usize = 1; // Minimun value that is a power of 2.

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

static MEMPOOL_START: AtomicUsize = AtomicUsize::new(0);
static MEMPOOL_END: AtomicUsize = AtomicUsize::new(0);
static IS_FORKED_CHILD: AtomicBool = AtomicBool::new(false);

extern "C" fn post_fork_handler_in_child() {
    IS_FORKED_CHILD.store(true, Ordering::Relaxed);
}

const FLLEN: usize = 28; // The maximum block size is (32 << 28) - 1 = 8_589_934_591 (nearly 8GiB)
const SLLEN: usize = 64; // The worst-case internal fragmentation is ((32 << 28) / 64 - 2) = 134_217_726 (nearly 128MiB)
type FLBitmap = u32; // FLBitmap should contain at least FLLEN bits
type SLBitmap = u64; // SLBitmap should contain at least SLLEN bits
type TlsfType = Tlsf<'static, FLBitmap, SLBitmap, FLLEN, SLLEN>;
static TLSF: OnceLock<Mutex<TlsfType>> = OnceLock::new();

#[cfg(not(test))]
fn init_tlsf() {
    let result = unsafe { libc::pthread_atfork(None, None, Some(post_fork_handler_in_child)) };

    if result != 0 {
        panic!(
            "[ERROR] [Agnocast] agnocast_heaphook internal error: pthread_atfork failed: {}",
            std::io::Error::from_raw_os_error(result)
        )
    }

    let mempool_size_env: String = std::env::var("AGNOCAST_MEMPOOL_SIZE").unwrap_or_else(|error| {
        panic!("[ERROR] [Agnocast] {}: AGNOCAST_MEMPOOL_SIZE", error);
    });

    let mempool_size: usize = mempool_size_env.parse::<usize>().unwrap_or_else(|error| {
        panic!("[ERROR] [Agnocast] {}: AGNOCAST_MEMPOOL_SIZE", error);
    });

    let page_size: usize = unsafe { libc::sysconf(libc::_SC_PAGESIZE) as usize };
    let aligned_size: usize = (mempool_size + page_size - 1) & !(page_size - 1);

    let version = env!("CARGO_PKG_VERSION");
    let c_version = CString::new(version).unwrap();

    let mempool_ptr: *mut c_void = unsafe {
        initialize_agnocast(aligned_size, c_version.as_ptr(), c_version.as_bytes().len())
    };

    let pool: &mut [MaybeUninit<u8>] = unsafe {
        std::slice::from_raw_parts_mut(mempool_ptr as *mut MaybeUninit<u8>, mempool_size)
    };

    MEMPOOL_START.store(mempool_ptr as usize, Ordering::Relaxed);
    MEMPOOL_END.store(mempool_ptr as usize + mempool_size, Ordering::Relaxed);

    let mut tlsf: TlsfType = Tlsf::new();
    tlsf.insert_free_block(pool);

    if TLSF.set(Mutex::new(tlsf)).is_err() {
        panic!("[ERROR] [Agnocast] TLSF is already initialized.");
    }
}

fn tlsf_allocate_wrapped(layout: Layout) -> Option<NonNull<u8>> {
    // `alignment` must be at least `POINTER_ALIGN` to ensure that `aligned_ptr` is properly aligned to store a pointer.
    let alignment = layout.align().max(POINTER_ALIGN);
    let size = layout.size();
    let layout = Layout::from_size_align(POINTER_SIZE + size + alignment, LAYOUT_ALIGN).ok()?;

    // the original pointer returned by the internal allocator
    let mut tlsf = TLSF.get().unwrap().lock().unwrap();
    let original_ptr = tlsf.allocate(layout)?;
    let original_addr = original_ptr.as_ptr() as usize;

    // the aligned pointer returned to the user
    //
    // It is our responsibility to satisfy alignment constraints.
    // We avoid using `Layout::align` because doing so requires us to remember the alignment.
    // This is because `Tlsf::{reallocate, deallocate}` functions require the same alignment.
    // See: https://docs.rs/rlsf/latest/rlsf/struct.Tlsf.html
    let aligned_addr = (original_addr + POINTER_SIZE + alignment - 1) & !(alignment - 1);

    // SAFETY: `aligned_addr` must be non-zero.
    debug_assert!(aligned_addr % alignment == 0 && aligned_addr != 0);
    let aligned_ptr = unsafe { NonNull::new_unchecked(aligned_addr as *mut u8) };

    // store the original pointer
    unsafe { *aligned_ptr.as_ptr().byte_sub(POINTER_SIZE).cast() = original_ptr };

    Some(aligned_ptr)
}

fn tlsf_reallocate_wrapped(ptr: NonNull<u8>, new_layout: Layout) -> Option<NonNull<u8>> {
    // `alignment` must be at least `POINTER_ALIGN` to ensure that `aligned_ptr` is properly aligned to store a pointer.
    let alignment = new_layout.align().max(POINTER_ALIGN);
    let size = new_layout.size();
    let new_layout = Layout::from_size_align(POINTER_SIZE + size + alignment, LAYOUT_ALIGN).ok()?;

    // get the original pointer
    // SAFETY: `ptr` must have been allocated by `tlsf_allocate_wrapped`.
    let old_original_ptr = unsafe { *ptr.as_ptr().byte_sub(POINTER_SIZE).cast() };

    // the original pointer returned by the internal allocator
    let mut tlsf = TLSF.get().unwrap().lock().unwrap();
    let new_original_ptr = unsafe { tlsf.reallocate(old_original_ptr, new_layout) }?;
    let new_original_addr = new_original_ptr.as_ptr() as usize;

    // the aligned pointer returned to the user
    //
    // It is our responsibility to satisfy alignment constraints.
    // We avoid using `Layout::align` because doing so requires us to remember the alignment.
    // This is because `Tlsf::{reallocate, deallocate}` functions require the same alignment.
    // See: https://docs.rs/rlsf/latest/rlsf/struct.Tlsf.html
    let new_aligned_addr = (new_original_addr + POINTER_SIZE + alignment - 1) & !(alignment - 1);

    // SAFETY: `new_aligned_addr` must be non-zero.
    debug_assert!(new_aligned_addr % alignment == 0 && new_aligned_addr != 0);
    let new_aligned_ptr = unsafe { NonNull::new_unchecked(new_aligned_addr as *mut u8) };

    // store the original pointer
    unsafe { *new_aligned_ptr.as_ptr().byte_sub(POINTER_SIZE).cast() = new_original_ptr };

    Some(new_aligned_ptr)
}

fn tlsf_deallocate_wrapped(ptr: NonNull<u8>) {
    // get the original pointer
    // SAFETY: `ptr` must have been allocated by `tlsf_{allocate, reallocate}_wrapped`.
    let original_ptr = unsafe { *ptr.as_ptr().byte_sub(POINTER_SIZE).cast() };

    let mut tlsf = TLSF.get().unwrap().lock().unwrap();
    unsafe { tlsf.deallocate(original_ptr, LAYOUT_ALIGN) }
}

#[cfg(not(test))]
fn should_use_original_func() -> bool {
    if IS_FORKED_CHILD.load(Ordering::Relaxed) {
        return true;
    }

    unsafe {
        if agnocast_get_borrowed_publisher_num() == 0 {
            return true;
        }
    }

    false
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
    init_tlsf();

    (*ORIGINAL_LIBC_START_MAIN.get_or_init(init_original_libc_start_main))(
        main, argc, argv, init, fini, rtld_fini, stack_end,
    )
}

#[no_mangle]
pub extern "C" fn malloc(size: usize) -> *mut c_void {
    if should_use_original_func() {
        return unsafe { (*ORIGINAL_MALLOC.get_or_init(init_original_malloc))(size) };
    }

    // The default global allocator assumes `malloc` returns 16-byte aligned address (on x64 platforms).
    // See: https://doc.rust-lang.org/beta/src/std/sys/alloc/unix.rs.html#13-15
    let layout = match Layout::from_size_align(size, MIN_ALIGN) {
        Ok(layout) => layout,
        Err(_) => return ptr::null_mut(),
    };

    match tlsf_allocate_wrapped(layout) {
        Some(non_null_ptr) => non_null_ptr.as_ptr().cast(),
        None => ptr::null_mut(),
    }
}

#[inline]
fn is_shared(ptr: *mut u8) -> bool {
    let addr = ptr as usize;
    MEMPOOL_START.load(Ordering::Relaxed) <= addr && addr <= MEMPOOL_END.load(Ordering::Relaxed)
}

/// # Safety
///
#[no_mangle]
pub unsafe extern "C" fn free(ptr: *mut c_void) {
    if ptr.is_null() {
        return;
    }

    // SAFETY: `ptr` must be non-null.
    let non_null_ptr = unsafe { NonNull::new_unchecked(ptr.cast()) };
    let is_shared = is_shared(ptr.cast());
    let is_forked_child = IS_FORKED_CHILD.load(Ordering::Relaxed);

    match (is_shared, is_forked_child) {
        (true, true) => (), // In the child processes, ignore the free operation to the shared memory
        (true, false) => tlsf_deallocate_wrapped(non_null_ptr),
        (false, _) => (*ORIGINAL_FREE.get_or_init(init_original_free))(ptr),
    }
}

#[no_mangle]
pub extern "C" fn calloc(num: usize, size: usize) -> *mut c_void {
    if should_use_original_func() {
        return unsafe { (*ORIGINAL_CALLOC.get_or_init(init_original_calloc))(num, size) };
    }

    // The default global allocator assumes `calloc` returns 16-byte aligned address (on x64 platforms).
    // See: https://doc.rust-lang.org/beta/src/std/sys/alloc/unix.rs.html#35-36
    let size = num * size;
    let layout = match Layout::from_size_align(size, MIN_ALIGN) {
        Ok(layout) => layout,
        Err(_) => return ptr::null_mut(),
    };

    match tlsf_allocate_wrapped(layout) {
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
    let is_shared = is_shared(ptr.cast());
    let should_use_original = should_use_original_func();

    match (is_shared, should_use_original) {
        (true, true) => {
            // In the child processes, ignore the free operation to the shared memory.
            (*ORIGINAL_MALLOC.get_or_init(init_original_malloc))(new_size)
        }
        (true, false) => {
            // The default global allocator assumes `realloc` returns 16-byte aligned address (on x64 platforms).
            // See: https://doc.rust-lang.org/beta/src/std/sys/alloc/unix.rs.html#53-54
            let new_layout = match Layout::from_size_align(new_size, MIN_ALIGN) {
                Ok(layout) => layout,
                Err(_) => return ptr::null_mut(),
            };

            match NonNull::new(ptr.cast()) {
                Some(non_null_ptr) => {
                    // If `new_size` is equal to zero, and `ptr` is not NULL, then the call is equivalent to `free(ptr)`.
                    if new_layout.size() == 0 {
                        tlsf_deallocate_wrapped(non_null_ptr);
                        return ptr::null_mut();
                    }

                    match tlsf_reallocate_wrapped(non_null_ptr, new_layout) {
                        Some(non_null_ptr) => non_null_ptr.as_ptr().cast(),
                        None => ptr::null_mut(),
                    }
                }
                None => {
                    // If `ptr` is NULL, then the call is equivalent to `malloc(size)`.
                    match tlsf_allocate_wrapped(new_layout) {
                        Some(non_null_ptr) => non_null_ptr.as_ptr().cast(),
                        None => ptr::null_mut(),
                    }
                }
            }
        }
        (false, _) => (*ORIGINAL_REALLOC.get_or_init(init_original_realloc))(ptr, new_size),
    }
}

#[no_mangle]
pub extern "C" fn posix_memalign(memptr: &mut *mut c_void, alignment: usize, size: usize) -> i32 {
    if should_use_original_func() {
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

    match tlsf_allocate_wrapped(layout) {
        Some(non_null_ptr) => {
            *memptr = non_null_ptr.as_ptr().cast();
            0
        }
        None => libc::ENOMEM,
    }
}

#[no_mangle]
pub extern "C" fn aligned_alloc(alignment: usize, size: usize) -> *mut c_void {
    if should_use_original_func() {
        return unsafe {
            (*ORIGINAL_ALIGNED_ALLOC.get_or_init(init_original_aligned_alloc))(alignment, size)
        };
    }

    // `alignment` should be a power of two and `size` should be a multiple of `alignment`.
    if !alignment.is_power_of_two() || size & (alignment - 1) != 0 {
        return ptr::null_mut();
    }

    let layout = match Layout::from_size_align(size, alignment) {
        Ok(layout) => layout,
        Err(_) => return ptr::null_mut(),
    };

    match tlsf_allocate_wrapped(layout) {
        Some(non_null_ptr) => non_null_ptr.as_ptr().cast(),
        None => std::ptr::null_mut(),
    }
}

#[no_mangle]
pub extern "C" fn memalign(alignment: usize, size: usize) -> *mut c_void {
    if should_use_original_func() {
        return unsafe {
            (*ORIGINAL_MEMALIGN.get_or_init(init_original_memalign))(alignment, size)
        };
    }

    // `alignment` must be a power of two.
    let layout = match Layout::from_size_align(size, alignment) {
        Ok(layout) => layout,
        Err(_) => return ptr::null_mut(),
    };

    match tlsf_allocate_wrapped(layout) {
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
fn init_tlsf() {
    let mempool_size: usize = 1024 * 1024;
    let mempool_ptr: *mut c_void = 0x121000000000 as *mut c_void;
    let pool: &mut [MaybeUninit<u8>] = unsafe {
        std::slice::from_raw_parts_mut(mempool_ptr as *mut MaybeUninit<u8>, mempool_size)
    };

    let shm_fd = unsafe {
        libc::shm_open(
            CStr::from_bytes_with_nul(b"/agnocast_test\0")
                .unwrap()
                .as_ptr(),
            libc::O_CREAT | libc::O_RDWR,
            0o600,
        )
    };

    unsafe { libc::ftruncate(shm_fd, mempool_size as libc::off_t) };

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

    unsafe {
        libc::shm_unlink(
            CStr::from_bytes_with_nul(b"/agnocast_test\0")
                .unwrap()
                .as_ptr(),
        )
    };

    MEMPOOL_START.store(mmap_ptr as usize, Ordering::Relaxed);
    MEMPOOL_END.store(mmap_ptr as usize + mempool_size, Ordering::Relaxed);

    let mut tlsf: TlsfType = Tlsf::new();
    tlsf.insert_free_block(pool);

    TLSF.set(Mutex::new(tlsf));
}

#[cfg(test)]
fn should_use_original_func() -> bool {
    false
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_malloc_normal() {
        // Arrange
        let start = MEMPOOL_START.load(Ordering::SeqCst);
        let end = MEMPOOL_END.load(Ordering::SeqCst);
        let malloc_size = 1024;

        // Act
        let ptr = unsafe { libc::malloc(malloc_size) };

        // Assert
        assert!(!ptr.is_null(), "allocated memory should not be null");
        assert!(
            ptr as usize >= start,
            "allocated memory should be within pool bounds"
        );
        assert!(
            ptr as usize + malloc_size <= end,
            "allocated memory should be within pool bounds"
        );

        unsafe { libc::free(ptr) };
    }

    #[test]
    fn test_calloc_normal() {
        // Arrange
        let start = MEMPOOL_START.load(Ordering::SeqCst);
        let end = MEMPOOL_END.load(Ordering::SeqCst);
        let elements = 4;
        let element_size = 256;
        let calloc_size = elements * element_size;

        // Act
        let ptr = unsafe { libc::calloc(elements, element_size) };

        // Assert
        assert!(!ptr.is_null(), "calloc must not return NULL");
        assert!(
            ptr as usize >= start,
            "calloc returned memory below the memory pool start address"
        );
        assert!(
            ptr as usize + calloc_size <= end,
            "calloc allocated memory exceeds the memory pool end address"
        );

        unsafe {
            for i in 0..calloc_size {
                let byte = *((ptr as *const u8).add(i));
                assert_eq!(byte, 0, "memory should be zero-initialized");
            }
        }

        unsafe { libc::free(ptr) };
    }

    #[test]
    fn test_realloc_normal() {
        // Arrange
        let start = MEMPOOL_START.load(Ordering::SeqCst);
        let end = MEMPOOL_END.load(Ordering::SeqCst);
        let malloc_size = 512;
        let realloc_size = 1024;

        let ptr = unsafe { libc::malloc(malloc_size) };
        assert!(!ptr.is_null(), "allocated memory should not be null");

        unsafe {
            for i in 0..malloc_size {
                *((ptr as *mut u8).add(i)) = (i % 255) as u8;
            }
        }

        // Act
        let new_ptr = unsafe { libc::realloc(ptr, realloc_size) };

        // Assert
        assert!(!new_ptr.is_null(), "realloc must not return NULL");
        assert!(
            new_ptr as usize >= start,
            "realloc returned memory below the memory pool start address"
        );
        assert!(
            new_ptr as usize + realloc_size <= end,
            "realloc allocated memory exceeds the memory pool end address"
        );

        unsafe {
            for i in 0..malloc_size {
                assert_eq!(
                    *((new_ptr as *const u8).add(i)),
                    (i % 255) as u8,
                    "realloc should preserve original data"
                );
            }
        }

        unsafe { libc::free(new_ptr) };
    }

    #[test]
    fn test_posix_memalign_normal() {
        // Arrange
        let start = MEMPOOL_START.load(Ordering::SeqCst);
        let end = MEMPOOL_END.load(Ordering::SeqCst);
        let alignment = 64;
        let size = 512;
        let mut ptr: *mut c_void = std::ptr::null_mut();

        // Act
        let r = unsafe { libc::posix_memalign(&mut ptr, alignment, size) };

        // Assert
        assert_eq!(r, 0, "posix_memalign should return 0 on success");

        assert!(!ptr.is_null(), "posix_memalign must not return NULL");
        assert!(
            ptr as usize >= start,
            "posix_memalign returned memory below the memory pool start address"
        );
        assert!(
            ptr as usize + size <= end,
            "posix_memalign allocated memory exceeds the memory pool end address"
        );
        assert_eq!(
            ptr as usize % alignment,
            0,
            "posix_memalign memory should be aligned to the specified boundary"
        );

        unsafe { libc::free(ptr) };
    }

    #[test]
    fn test_aligned_alloc_normal() {
        // Arrange
        let start = MEMPOOL_START.load(Ordering::SeqCst);
        let end = MEMPOOL_END.load(Ordering::SeqCst);
        let alignments = [8, 16, 32, 64, 128, 256, 512, 1024, 2048];

        for &alignment in &alignments {
            let sizes = [
                alignment,
                alignment * 2,
                alignment * 4,
                alignment * 8,
                alignment * 16,
            ];

            for &size in &sizes {
                // Act
                let ptr = unsafe { libc::aligned_alloc(alignment, size) };

                // Assert
                assert!(!ptr.is_null(), "aligned_alloc must not return NULL");
                assert!(
                    ptr as usize >= start,
                    "aligned_alloc returned memory below the memory pool start address"
                );
                assert!(
                    ptr as usize + size <= end,
                    "aligned_alloc allocated memory exceeds the memory pool end address"
                );
                assert_eq!(
                    ptr as usize % alignment,
                    0,
                    "aligned_alloc memory should be aligned to the specified boundary"
                );
                unsafe { libc::free(ptr) };
            }
        }
    }
    #[test]
    fn test_memalign_normal() {
        // Arrange
        let start = MEMPOOL_START.load(Ordering::SeqCst);
        let end = MEMPOOL_END.load(Ordering::SeqCst);
        let alignments = [8, 16, 32, 64, 128, 256, 512, 1024, 2048];
        let sizes = [10, 32, 100, 512, 1000, 4096];

        for &alignment in &alignments {
            for &size in &sizes {
                // Act
                let ptr = unsafe { libc::memalign(alignment, size) };

                // Assert
                assert!(!ptr.is_null(), "memalign must not return NULL");

                assert!(
                    ptr as usize >= start,
                    "memalign returned memory below the memory pool start address"
                );

                assert!(
                    ptr as usize + size <= end,
                    "memalign allocated memory exceeds the memory pool end address"
                );
                assert_eq!(
                    ptr as usize % alignment,
                    0,
                    "memalign memory should be aligned to the specified boundary"
                );
                unsafe { libc::free(ptr) };
            }
        }
    }

    #[test]
    fn test_memory_limit() {
        // Arrange
        let huge_size = isize::MAX as usize;
        let alignment = 64;
        let mut posix_ptr: *mut c_void = std::ptr::null_mut();
        let normal_ptr = unsafe { libc::malloc(1024) };

        // Act & Assert
        assert!(
            unsafe { libc::malloc(huge_size) }.is_null(),
            "malloc should return NULL for huge size"
        );

        assert!(
            unsafe { libc::calloc(huge_size, 1) }.is_null(),
            "calloc should return NULL for huge size"
        );

        assert!(
            unsafe { libc::aligned_alloc(alignment, huge_size) }.is_null(),
            "aligned_alloc should return NULL for huge size"
        );

        assert!(
            unsafe { libc::memalign(alignment, huge_size) }.is_null(),
            "memalign should return NULL for huge size"
        );

        // Act
        let result = unsafe { libc::posix_memalign(&mut posix_ptr, alignment, huge_size) };

        // Assert
        assert_eq!(
            result,
            libc::ENOMEM,
            "posix_memalign should return ENOMEM for huge size"
        );
        assert!(
            posix_ptr.is_null(),
            "posix_memalign should not set pointer on failure"
        );

        // Act
        let realloc_ptr = unsafe { libc::realloc(normal_ptr, huge_size) };

        // Assert
        assert!(
            realloc_ptr.is_null(),
            "realloc should return NULL for huge size"
        );
        if realloc_ptr.is_null() {
            unsafe { libc::free(normal_ptr) };
        } else {
            unsafe { libc::free(realloc_ptr) };
        }
    }

    #[test]
    fn test_posix_memalign_should_fail() {
        let mut ptr: *mut c_void = ptr::null_mut();

        assert_eq!(
            unsafe { libc::posix_memalign(&mut ptr, 0, 8) },
            libc::EINVAL,
            "posix_memalign should return EINVAL if the alignment is not a power of two"
        );

        assert_eq!(
            unsafe {libc::posix_memalign(&mut ptr, size_of::<*mut c_void>() / 2, 8)},
            libc::EINVAL,
            "posix_memalign should return EINVAL if the alignment is not a multiple of `sizeof(void *)`"
        );
    }

    #[test]
    fn test_aligned_alloc_should_fail() {
        assert_eq!(
            unsafe { libc::aligned_alloc(0, 8) },
            ptr::null_mut(),
            "aligned_alloc should return NULL if the alignment is not a power of two"
        );

        assert_eq!(
            unsafe { libc::aligned_alloc(2, 7) },
            ptr::null_mut(),
            "aligned_alloc should return NULL if the size is not a multiple of the alignment"
        );
    }

    #[test]
    fn test_memalign_should_fail() {
        assert_eq!(
            unsafe { libc::memalign(0, 8) },
            ptr::null_mut(),
            "memalign should return NULL if the alignment is not a power of two"
        );
    }
}
