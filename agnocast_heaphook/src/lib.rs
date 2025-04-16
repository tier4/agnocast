use rlsf::Tlsf;
use std::{
    alloc::Layout,
    ffi::{CStr, CString},
    mem::MaybeUninit,
    os::raw::{c_char, c_int, c_void},
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
const ALIGNMENT: usize = 64; // must be larger than POINTER_SIZE

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

fn tlsf_allocate(size: usize) -> *mut c_void {
    let layout: Layout = Layout::from_size_align(size, ALIGNMENT).unwrap_or_else(|error| {
        panic!(
            "[ERROR] [Agnocast] {}: size={}, alignment={}",
            error, size, ALIGNMENT
        );
    });

    let mut tlsf = TLSF.get().unwrap().lock().unwrap();

    let ptr: std::ptr::NonNull<u8> = tlsf.allocate(layout).unwrap_or_else(|| {
        panic!("[ERROR] [Agnocast] memory allocation failed: use larger AGNOCAST_MEMPOOL_SIZE");
    });

    ptr.as_ptr() as *mut c_void
}

fn tlsf_reallocate(ptr: std::ptr::NonNull<u8>, size: usize) -> *mut c_void {
    let layout: Layout = Layout::from_size_align(size, ALIGNMENT).unwrap_or_else(|error| {
        panic!(
            "[ERROR] [Agnocast] {}: size={}, alignment={}",
            error, size, ALIGNMENT
        );
    });

    let mut tlsf = TLSF.get().unwrap().lock().unwrap();

    let new_ptr: std::ptr::NonNull<u8> = unsafe {
        tlsf.reallocate(ptr, layout).unwrap_or_else(|| {
            panic!("[ERROR] [Agnocast] memory allocation failed: use larger AGNOCAST_MEMPOOL_SIZE");
        })
    };

    new_ptr.as_ptr() as *mut c_void
}

fn tlsf_deallocate(ptr: std::ptr::NonNull<u8>) {
    let mut tlsf = TLSF.get().unwrap().lock().unwrap();
    unsafe { tlsf.deallocate(ptr, ALIGNMENT) }
}

fn tlsf_allocate_wrapped(alignment: usize, size: usize) -> *mut c_void {
    // return value from internal alloc
    let start_addr: usize = tlsf_allocate(ALIGNMENT + size + alignment) as usize;

    // aligned address returned to user
    let aligned_addr: usize = if alignment == 0 {
        start_addr + ALIGNMENT
    } else {
        start_addr + ALIGNMENT + alignment - ((start_addr + ALIGNMENT) % alignment)
    };

    // store `start_addr`
    let start_addr_ptr: *mut usize = (aligned_addr - POINTER_SIZE) as *mut usize;
    unsafe { *start_addr_ptr = start_addr };

    aligned_addr as *mut c_void
}

fn tlsf_reallocate_wrapped(ptr: usize, size: usize) -> *mut c_void {
    // get the original start address from internal allocator
    let original_start_addr: usize = unsafe { *((ptr - POINTER_SIZE) as *mut usize) };
    let original_start_addr_ptr: std::ptr::NonNull<u8> =
        std::ptr::NonNull::new(original_start_addr as *mut c_void as *mut u8).unwrap();

    // return value from internal alloc
    let start_addr: usize = tlsf_reallocate(original_start_addr_ptr, ALIGNMENT + size) as usize;
    let aligned_addr: usize = start_addr + ALIGNMENT;

    // store `start_addr`
    let start_addr_ptr: *mut usize = (aligned_addr - POINTER_SIZE) as *mut usize;
    unsafe { *start_addr_ptr = start_addr };

    aligned_addr as *mut c_void
}

fn tlsf_deallocate_wrapped(ptr: usize) {
    // get the original start address from internal allocator
    let original_start_addr: usize = unsafe { *((ptr - POINTER_SIZE) as *mut usize) };
    let original_start_addr_ptr: std::ptr::NonNull<u8> =
        std::ptr::NonNull::new(original_start_addr as *mut c_void as *mut u8).unwrap();

    tlsf_deallocate(original_start_addr_ptr);
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

    tlsf_allocate_wrapped(0, size)
}

/// # Safety
///
#[no_mangle]
pub unsafe extern "C" fn free(ptr: *mut c_void) {
    let non_null_ptr: std::ptr::NonNull<u8> = match std::ptr::NonNull::new(ptr as *mut u8) {
        Some(ptr) => ptr,
        None => return,
    };

    let ptr_addr: usize = non_null_ptr.as_ptr() as usize;
    let allocated_by_original: bool = ptr_addr < MEMPOOL_START.load(Ordering::Relaxed)
        || ptr_addr > MEMPOOL_END.load(Ordering::Relaxed);

    if IS_FORKED_CHILD.load(Ordering::Relaxed) {
        // In the child processes, ignore the free operation to the shared memory
        if !allocated_by_original {
            return;
        }

        return (*ORIGINAL_FREE.get_or_init(init_original_free))(ptr);
    }

    if allocated_by_original {
        (*ORIGINAL_FREE.get_or_init(init_original_free))(ptr);
    } else {
        tlsf_deallocate_wrapped(ptr_addr);
    }
}

#[no_mangle]
pub extern "C" fn calloc(num: usize, size: usize) -> *mut c_void {
    if should_use_original_func() {
        return unsafe { (*ORIGINAL_CALLOC.get_or_init(init_original_calloc))(num, size) };
    }

    let ret: *mut c_void = tlsf_allocate_wrapped(0, num * size);
    unsafe {
        std::ptr::write_bytes(ret, 0, num * size);
    }
    ret
}

/// # Safety
///
#[no_mangle]
pub unsafe extern "C" fn realloc(ptr: *mut c_void, new_size: usize) -> *mut c_void {
    let (ptr_addr, allocated_by_original) =
        if let Some(non_null_ptr) = std::ptr::NonNull::new(ptr as *mut u8) {
            let addr = non_null_ptr.as_ptr() as usize;
            let is_original = addr < MEMPOOL_START.load(Ordering::Relaxed)
                || addr > MEMPOOL_END.load(Ordering::Relaxed);
            (Some(addr), is_original)
        } else {
            (None, false)
        };

    if should_use_original_func() {
        // In the child processes, ignore the free operation to the shared memory
        let realloc_ret: *mut c_void = if !allocated_by_original {
            (*ORIGINAL_MALLOC.get_or_init(init_original_malloc))(new_size)
        } else {
            (*ORIGINAL_REALLOC.get_or_init(init_original_realloc))(ptr, new_size)
        };

        return realloc_ret;
    }

    match ptr_addr {
        Some(addr) => {
            if allocated_by_original {
                (*ORIGINAL_REALLOC.get_or_init(init_original_realloc))(ptr, new_size)
            } else {
                tlsf_reallocate_wrapped(addr, new_size)
            }
        }
        None => tlsf_allocate_wrapped(0, new_size),
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

    *memptr = tlsf_allocate_wrapped(alignment, size);
    0
}

#[no_mangle]
pub extern "C" fn aligned_alloc(alignment: usize, size: usize) -> *mut c_void {
    if should_use_original_func() {
        return unsafe {
            (*ORIGINAL_ALIGNED_ALLOC.get_or_init(init_original_aligned_alloc))(alignment, size)
        };
    }

    tlsf_allocate_wrapped(alignment, size)
}

#[no_mangle]
pub extern "C" fn memalign(alignment: usize, size: usize) -> *mut c_void {
    if should_use_original_func() {
        return unsafe {
            (*ORIGINAL_MEMALIGN.get_or_init(init_original_memalign))(alignment, size)
        };
    }

    tlsf_allocate_wrapped(alignment, size)
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
    let mempool_ptr: *mut c_void = 0x8B000000000 as *mut c_void;
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
        let ptr = malloc(malloc_size);

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

        unsafe { free(ptr) };
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
        let ptr = calloc(elements, element_size);

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

        unsafe { free(ptr) };
    }
}
