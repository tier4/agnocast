use std::{
    alloc::Layout,
    ffi::{CStr, CString},
    mem::MaybeUninit,
    os::raw::{c_char, c_int, c_void},
    ptr::NonNull,
    sync::{
        atomic::{AtomicBool, AtomicUsize, Ordering},
        OnceLock,
    },
};

mod tlsf;

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

#[cfg(not(test))]
fn init_agnocast_memory_pool() -> &'static mut [MaybeUninit<u8>] {
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

    pool
}

#[cfg(not(test))]
fn should_use_original_func() -> bool {
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

    false
}

unsafe trait AgnocastHeapHookApi {
    fn init(&self, pool: &'static mut [MaybeUninit<u8>]);

    unsafe fn alloc(&self, layout: Layout) -> *mut u8;

    unsafe fn dealloc(&self, ptr: NonNull<u8>);

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        let size = layout.size();
        let ptr = self.alloc(layout);
        if !ptr.is_null() {
            ptr.write_bytes(0, size);
        }
        ptr
    }

    unsafe fn realloc(&self, ptr: NonNull<u8>, new_layout: Layout) -> *mut u8;
}

// See: https://doc.rust-lang.org/src/std/sys/alloc/mod.rs.html
const MIN_ALIGN: usize = 16;

#[macro_export]
macro_rules! global_agnocast_heaphook_allocator {
    ($allocator:expr) => {
        /// # Safety
        ///
        #[no_mangle]
        pub unsafe extern "C" fn __libc_start_main(
            main: unsafe extern "C" fn(
                std::os::raw::c_int,
                *const *const u8,
            ) -> std::os::raw::c_int,
            argc: std::os::raw::c_int,
            argv: *const *const u8,
            init: unsafe extern "C" fn(),
            fini: unsafe extern "C" fn(),
            rtld_fini: unsafe extern "C" fn(),
            stack_end: *const std::os::raw::c_void,
        ) -> std::os::raw::c_int {
            let pool = crate::init_agnocast_memory_pool();
            $allocator.init(pool);

            (*crate::ORIGINAL_LIBC_START_MAIN.get_or_init(crate::init_original_libc_start_main))(
                main, argc, argv, init, fini, rtld_fini, stack_end,
            )
        }

        #[no_mangle]
        pub extern "C" fn malloc(size: usize) -> *mut std::os::raw::c_void {
            if crate::should_use_original_func() {
                return unsafe {
                    (*crate::ORIGINAL_MALLOC.get_or_init(crate::init_original_malloc))(size)
                };
            }

            // The default global allocator assumes `malloc` returns 16-byte aligned address (on x64 platforms).
            // See: https://doc.rust-lang.org/beta/src/std/sys/alloc/unix.rs.html#13-15
            let layout = Layout::from_size_align(size, crate::MIN_ALIGN).unwrap();
            unsafe { $allocator.alloc(layout) as _ }
        }

        /// # Safety
        ///
        #[no_mangle]
        pub unsafe extern "C" fn free(ptr: *mut std::os::raw::c_void) {
            let non_null_ptr: std::ptr::NonNull<u8> = match std::ptr::NonNull::new(ptr as *mut u8) {
                Some(ptr) => ptr,
                None => return,
            };

            let ptr_addr: usize = non_null_ptr.as_ptr() as usize;
            let allocated_by_original: bool = ptr_addr
                < crate::MEMPOOL_START.load(std::sync::atomic::Ordering::Relaxed)
                || ptr_addr > crate::MEMPOOL_END.load(std::sync::atomic::Ordering::Relaxed);

            if crate::IS_FORKED_CHILD.load(std::sync::atomic::Ordering::Relaxed) {
                // In the child processes, ignore the free operation to the shared memory
                if !allocated_by_original {
                    return;
                }

                return (*crate::ORIGINAL_FREE.get_or_init(crate::init_original_free))(ptr);
            }

            if allocated_by_original {
                (*crate::ORIGINAL_FREE.get_or_init(crate::init_original_free))(ptr);
            } else {
                $allocator.dealloc(non_null_ptr);
            }
        }

        #[no_mangle]
        pub extern "C" fn calloc(num: usize, size: usize) -> *mut std::os::raw::c_void {
            if crate::should_use_original_func() {
                return unsafe {
                    (*crate::ORIGINAL_CALLOC.get_or_init(crate::init_original_calloc))(num, size)
                };
            }

            // TODO: fix alignment?
            let layout = Layout::from_size_align(num * size, 1).unwrap();
            unsafe { $allocator.alloc_zeroed(layout) as _ }
        }

        /// # Safety
        ///
        #[no_mangle]
        pub unsafe extern "C" fn realloc(
            ptr: *mut std::os::raw::c_void,
            new_size: usize,
        ) -> *mut std::os::raw::c_void {
            let (ptr_addr, allocated_by_original) =
                if let Some(non_null_ptr) = std::ptr::NonNull::new(ptr as *mut u8) {
                    let addr = non_null_ptr.as_ptr() as usize;
                    let is_original = addr
                        < crate::MEMPOOL_START.load(std::sync::atomic::Ordering::Relaxed)
                        || addr > crate::MEMPOOL_END.load(std::sync::atomic::Ordering::Relaxed);
                    (Some(non_null_ptr), is_original)
                } else {
                    (None, false)
                };

            if crate::should_use_original_func() {
                // In the child processes, ignore the free operation to the shared memory
                let realloc_ret: *mut std::os::raw::c_void = if !allocated_by_original {
                    (*crate::ORIGINAL_MALLOC.get_or_init(crate::init_original_malloc))(new_size)
                } else {
                    (*crate::ORIGINAL_REALLOC.get_or_init(crate::init_original_realloc))(
                        ptr, new_size,
                    )
                };

                return realloc_ret;
            }

            // The default global allocator assumes `malloc` returns 16-byte aligned address (on x64 platforms).
            // See: https://doc.rust-lang.org/beta/src/std/sys/alloc/unix.rs.html#13-15
            let new_layout = Layout::from_size_align(new_size, crate::MIN_ALIGN).unwrap();

            match ptr_addr {
                Some(addr) => {
                    if allocated_by_original {
                        (*crate::ORIGINAL_REALLOC.get_or_init(crate::init_original_realloc))(
                            ptr, new_size,
                        )
                    } else {
                        $allocator.realloc(addr, new_layout) as _
                    }
                }
                None => $allocator.alloc(new_layout) as _,
            }
        }

        #[no_mangle]
        pub extern "C" fn posix_memalign(memptr: &mut *mut std::os::raw::c_void, alignment: usize, size: usize) -> i32 {
            if crate::should_use_original_func() {
                return unsafe {
                    (*crate::ORIGINAL_POSIX_MEMALIGN.get_or_init(crate::init_original_posix_memalign))(
                        memptr, alignment, size,
                    )
                };
            }
            let layout = Layout::from_size_align(size, alignment).unwrap();
            *memptr = unsafe { $allocator.alloc(layout) as _ };
            0
        }

        #[no_mangle]
        pub extern "C" fn aligned_alloc(alignment: usize, size: usize) -> *mut std::os::raw::c_void {
            if crate::should_use_original_func() {
                return unsafe {
                    (*crate::ORIGINAL_ALIGNED_ALLOC.get_or_init(crate::init_original_aligned_alloc))(alignment, size)
                };
            }
            let layout = Layout::from_size_align(size, alignment).unwrap();
            unsafe { $allocator.alloc(layout) as _ }
        }

        #[no_mangle]
        pub extern "C" fn memalign(alignment: usize, size: usize) -> *mut std::os::raw::c_void {
            if crate::should_use_original_func() {
                return unsafe {
                    (*crate::ORIGINAL_MEMALIGN.get_or_init(crate::init_original_memalign))(alignment, size)
                };
            }
            let layout = Layout::from_size_align(size, alignment).unwrap();
            unsafe { $allocator.alloc(layout) as _ }
        }

        #[no_mangle]
        pub extern "C" fn valloc(_size: usize) -> *mut std::os::raw::c_void {
            panic!("[ERROR] [Agnocast] valloc is not supported");
        }

        #[no_mangle]
        pub extern "C" fn pvalloc(_size: usize) -> *mut std::os::raw::c_void {
            panic!("[ERROR] [Agnocast] pvalloc is not supported");
        }
    };
}

#[cfg(test)]
pub fn init_agnocast_memory_pool() -> &'static mut [MaybeUninit<u8>] {
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

    pool
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
    fn test_aligned_alloc() {
        // Arrange
        let start = MEMPOOL_START.load(Ordering::SeqCst);
        let end = MEMPOOL_END.load(Ordering::SeqCst);
        let alignments = [8, 16, 32, 64, 128, 256, 512, 1024, 2048];
        let sizes = [10, 32, 100, 512, 1000, 4096];

        for &alignment in &alignments {
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
}
