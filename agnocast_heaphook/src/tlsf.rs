use rlsf::Tlsf;
use std::{
    alloc::Layout,
    mem::MaybeUninit,
    ptr::NonNull,
    sync::{Mutex, OnceLock},
};

use crate::{global_agnocast_heaphook_allocator, AgnocastHeapHookApi};

const POINTER_SIZE: usize = std::mem::size_of::<&usize>();
const FLLEN: usize = 28; // The maximum block size is (32 << 28) - 1 = 8_589_934_591 (nearly 8GiB)
const SLLEN: usize = 64; // The worst-case internal fragmentation is ((32 << 28) / 64 - 2) = 134_217_726 (nearly 128MiB)
type FLBitmap = u32; // FLBitmap should contain at least FLLEN bits
type SLBitmap = u64; // SLBitmap should contain at least SLLEN bits
type TlsfType = Tlsf<'static, FLBitmap, SLBitmap, FLLEN, SLLEN>;

pub static TLSF: TLSFAllocator = TLSFAllocator::new();
global_agnocast_heaphook_allocator!(TLSF);

pub struct TLSFAllocator {
    inner: OnceLock<Mutex<TlsfType>>,
}

unsafe impl AgnocastHeapHookApi for TLSFAllocator {
    fn init(&self, pool: &'static mut [MaybeUninit<u8>]) {
        let mut tlsf: TlsfType = Tlsf::new();
        tlsf.insert_free_block(pool);

        if self.inner.set(Mutex::new(tlsf)).is_err() {
            panic!("[ERROR] [Agnocast] TLSF is already initialized.");
        }
    }

    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let size = layout.size();
        let align = layout.align();
        let layout = Layout::from_size_align(POINTER_SIZE + size + align, 1).unwrap();

        let mut tlsf = TLSF.inner.get().unwrap().lock().unwrap();
        let ptr = tlsf
            .allocate(layout)
            .unwrap_or_else(|| {
                panic!(
                    "[ERROR] [Agnocast] memory allocation failed: use larger AGNOCAST_MEMPOOL_SIZE"
                );
            })
            .as_ptr();

        // It is our responsibility to satisfy alignment constraints. While we could deglegate
        // this responsibility to the TLSF allocator by using `Layout::align`, the Tlsf::{reallocate, deallocate}
        // functons require the same alignment specified at allocation time. Therefore, in this case, we would
        // need to remember the alignement.
        let aligned_ptr = ((ptr as usize + POINTER_SIZE + align - 1) & !(align - 1)) as *mut u8;
        debug_assert!(aligned_ptr as usize % align == 0);

        // store original pointer
        *aligned_ptr.byte_sub(POINTER_SIZE).cast() = ptr as usize;

        aligned_ptr
    }

    unsafe fn dealloc(&self, ptr: NonNull<u8>) {
        let original_ptr =
            NonNull::new(unsafe { *ptr.as_ptr().byte_sub(POINTER_SIZE).cast() }).unwrap();
        let mut tlsf = TLSF.inner.get().unwrap().lock().unwrap();
        unsafe { tlsf.deallocate(original_ptr, 1) }
    }

    unsafe fn realloc(&self, ptr: NonNull<u8>, new_layout: Layout) -> *mut u8 {
        let original_ptr =
            NonNull::new(unsafe { *ptr.as_ptr().byte_sub(POINTER_SIZE).cast() }).unwrap();

        let size = new_layout.size();
        let align = new_layout.align();
        let new_layout = Layout::from_size_align(POINTER_SIZE + size + align, 1).unwrap();

        let mut tlsf = TLSF.inner.get().unwrap().lock().unwrap();
        let ptr = unsafe {
            tlsf.reallocate(original_ptr, new_layout)
                .unwrap_or_else(|| {
                    panic!(
                    "[ERROR] [Agnocast] memory allocation failed: use larger AGNOCAST_MEMPOOL_SIZE"
                );
                })
        }
        .as_ptr();

        // It is our responsibility to satisfy alignment constraints. While we could deglegate
        // this responsibility to the TLSF allocator by using `Layout::align`, the Tlsf::{reallocate, deallocate}
        // functons require the same alignment specified at allocation time. Therefore, in this case, we would
        // need to remember the alignement.
        let aligned_ptr = ((ptr as usize + POINTER_SIZE + align - 1) & !(align - 1)) as *mut u8;
        debug_assert!(aligned_ptr as usize % align == 0);

        // store original pointer
        *aligned_ptr.byte_sub(POINTER_SIZE).cast() = ptr as usize;

        aligned_ptr
    }
}

impl TLSFAllocator {
    const fn new() -> Self {
        Self {
            inner: OnceLock::new(),
        }
    }
}
