use rlsf::Tlsf;
use std::{
    alloc::Layout,
    mem::MaybeUninit,
    os::raw::c_void,
    sync::{Mutex, OnceLock},
};

// FIXME: Add assert
const POINTER_SIZE: usize = std::mem::size_of::<&usize>();
const ALIGNMENT: usize = 64; // must be larger than POINTER_SIZE

const FLLEN: usize = 28; // The maximum block size is (32 << 28) - 1 = 8_589_934_591 (nearly 8GiB)
const SLLEN: usize = 64; // The worst-case internal fragmentation is ((32 << 28) / 64 - 2) = 134_217_726 (nearly 128MiB)
type FLBitmap = u32; // FLBitmap should contain at least FLLEN bits
type SLBitmap = u64; // SLBitmap should contain at least SLLEN bits
type TlsfType = Tlsf<'static, FLBitmap, SLBitmap, FLLEN, SLLEN>;
static TLSF: OnceLock<Mutex<TlsfType>> = OnceLock::new();

pub fn init_tlsf(pool: &'static mut [MaybeUninit<u8>]) {
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
