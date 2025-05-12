use rlsf::Tlsf;
use std::{
    alloc::Layout,
    mem::MaybeUninit,
    os::raw::c_void,
    sync::{atomic::Ordering, Mutex, OnceLock},
};

use crate::{MEMPOOL_END, MEMPOOL_START};

// FIXME: Add assert
const POINTER_SIZE: usize = std::mem::size_of::<&usize>();
const ALIGNMENT: usize = 64; // must be larger than POINTER_SIZE

const FLLEN: usize = 28; // The maximum block size is (32 << 28) - 1 = 8_589_934_591 (nearly 8GiB)
const SLLEN: usize = 64; // The worst-case internal fragmentation is ((32 << 28) / 64 - 2) = 134_217_726 (nearly 128MiB)
type FLBitmap = u32; // FLBitmap should contain at least FLLEN bits
type SLBitmap = u64; // SLBitmap should contain at least SLLEN bits
type TlsfType = Tlsf<'static, FLBitmap, SLBitmap, FLLEN, SLLEN>;
static TLSF: OnceLock<Mutex<TlsfType>> = OnceLock::new();

#[cfg(test)]
pub fn init_tlsf() {
    use std::ffi::CStr;

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

#[cfg(not(test))]
pub fn init_tlsf() {
    use crate::post_fork_handler_in_child;
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

pub fn tlsf_allocate_wrapped(alignment: usize, size: usize) -> *mut c_void {
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

pub fn tlsf_reallocate_wrapped(ptr: usize, size: usize) -> *mut c_void {
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

pub fn tlsf_deallocate_wrapped(ptr: usize) {
    // get the original start address from internal allocator
    let original_start_addr: usize = unsafe { *((ptr - POINTER_SIZE) as *mut usize) };
    let original_start_addr_ptr: std::ptr::NonNull<u8> =
        std::ptr::NonNull::new(original_start_addr as *mut c_void as *mut u8).unwrap();

    tlsf_deallocate(original_start_addr_ptr);
}
