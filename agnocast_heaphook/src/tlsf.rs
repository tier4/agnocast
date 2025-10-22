use rlsf::Tlsf;
use std::{alloc::Layout, mem::MaybeUninit, ptr::NonNull, sync::Mutex};

use crate::{AgnocastSharedMemory, SharedMemoryAllocator};

const FLLEN: usize = 28; // The maximum block size is (32 << 28) - 1 = 8_589_934_591 (nearly 8GiB)
const SLLEN: usize = 64; // The worst-case internal fragmentation is ((32 << 28) / 64 - 2) = 134_217_726 (nearly 128MiB)
type FLBitmap = u32; // FLBitmap should contain at least FLLEN bits
type SLBitmap = u64; // SLBitmap should contain at least SLLEN bits
type TlsfType = Tlsf<'static, FLBitmap, SLBitmap, FLLEN, SLLEN>;

const POINTER_SIZE: usize = std::mem::size_of::<&usize>();
const POINTER_ALIGN: usize = std::mem::align_of::<&usize>();
const LAYOUT_ALIGN: usize = 1; // Minimun value that is a power of 2.

pub struct TLSFAllocator {
    inner: Mutex<TlsfType>,
}

unsafe impl SharedMemoryAllocator for TLSFAllocator {
    fn new(shm: &'static AgnocastSharedMemory) -> Self {
        let pool = unsafe {
            std::slice::from_raw_parts_mut(shm.as_ptr() as *mut MaybeUninit<u8>, shm.len())
        };
        let mut tlsf: TlsfType = Tlsf::new();
        tlsf.insert_free_block(pool);
        Self {
            inner: Mutex::new(tlsf),
        }
    }

    fn allocate(&self, layout: Layout) -> Option<NonNull<u8>> {
        // `alignment` must be at least `POINTER_ALIGN` to ensure that `aligned_ptr` is properly aligned to store a pointer.
        let alignment = layout.align().max(POINTER_ALIGN);
        let size = layout.size();
        let layout = Layout::from_size_align(POINTER_SIZE + size + alignment, LAYOUT_ALIGN).ok()?;

        // the original pointer returned by the internal allocator
        let mut tlsf = self.inner.lock().unwrap();
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

    fn reallocate(&self, ptr: NonNull<u8>, new_layout: Layout) -> Option<NonNull<u8>> {
        // `alignment` must be at least `POINTER_ALIGN` to ensure that `aligned_ptr` is properly aligned to store a pointer.
        let alignment = new_layout.align().max(POINTER_ALIGN);
        let size = new_layout.size();
        let new_layout =
            Layout::from_size_align(POINTER_SIZE + size + alignment, LAYOUT_ALIGN).ok()?;

        // get the original pointer
        // SAFETY: `ptr` must have been allocated by `tlsf_allocate_wrapped`.
        let old_original_ptr = unsafe { *ptr.as_ptr().byte_sub(POINTER_SIZE).cast() };

        // the original pointer returned by the internal allocator
        let mut tlsf = self.inner.lock().unwrap();
        let new_original_ptr = unsafe { tlsf.reallocate(old_original_ptr, new_layout) }?;
        let new_original_addr = new_original_ptr.as_ptr() as usize;

        // the aligned pointer returned to the user
        //
        // It is our responsibility to satisfy alignment constraints.
        // We avoid using `Layout::align` because doing so requires us to remember the alignment.
        // This is because `Tlsf::{reallocate, deallocate}` functions require the same alignment.
        // See: https://docs.rs/rlsf/latest/rlsf/struct.Tlsf.html
        let new_aligned_addr =
            (new_original_addr + POINTER_SIZE + alignment - 1) & !(alignment - 1);

        // SAFETY: `new_aligned_addr` must be non-zero.
        debug_assert!(new_aligned_addr % alignment == 0 && new_aligned_addr != 0);
        let new_aligned_ptr = unsafe { NonNull::new_unchecked(new_aligned_addr as *mut u8) };

        // store the original pointer
        unsafe { *new_aligned_ptr.as_ptr().byte_sub(POINTER_SIZE).cast() = new_original_ptr };

        Some(new_aligned_ptr)
    }

    fn deallocate(&self, ptr: NonNull<u8>) {
        // get the original pointer
        // SAFETY: `ptr` must have been allocated by `tlsf_{allocate, reallocate}_wrapped`.
        let original_ptr = unsafe { *ptr.as_ptr().byte_sub(POINTER_SIZE).cast() };

        let mut tlsf = self.inner.lock().unwrap();
        unsafe { tlsf.deallocate(original_ptr, LAYOUT_ALIGN) }
    }
}
