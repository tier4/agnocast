use rlsf::Tlsf;
use std::{
    alloc::Layout,
    cell::Cell,
    collections::HashMap,
    ffi::CStr,
    mem::MaybeUninit,
    os::raw::c_void,
    sync::{LazyLock, Mutex},
};

const ALIGNMENT: usize = 64;

type MallocType = unsafe extern "C" fn(usize) -> *mut c_void;
static ORIGINAL_MALLOC: LazyLock<MallocType> = LazyLock::new(|| {
    let symbol: &CStr = CStr::from_bytes_with_nul(b"malloc\0").unwrap();
    unsafe {
        let malloc_ptr: *mut c_void = libc::dlsym(libc::RTLD_NEXT, symbol.as_ptr());
        std::mem::transmute::<*mut c_void, MallocType>(malloc_ptr)
    }
});

type FreeType = unsafe extern "C" fn(*mut c_void) -> ();
static ORIGINAL_FREE: LazyLock<FreeType> = LazyLock::new(|| {
    let symbol: &CStr = CStr::from_bytes_with_nul(b"free\0").unwrap();
    unsafe {
        let free_ptr: *mut c_void = libc::dlsym(libc::RTLD_NEXT, symbol.as_ptr());
        std::mem::transmute::<*mut c_void, FreeType>(free_ptr)
    }
});

type CallocType = unsafe extern "C" fn(usize, usize) -> *mut c_void;
static ORIGINAL_CALLOC: LazyLock<CallocType> = LazyLock::new(|| {
    let symbol: &CStr = CStr::from_bytes_with_nul(b"calloc\0").unwrap();
    unsafe {
        let calloc_ptr: *mut c_void = libc::dlsym(libc::RTLD_NEXT, symbol.as_ptr());
        std::mem::transmute::<*mut c_void, CallocType>(calloc_ptr)
    }
});

type ReallocType = unsafe extern "C" fn(*mut c_void, usize) -> *mut c_void;
static ORIGINAL_REALLOC: LazyLock<ReallocType> = LazyLock::new(|| {
    let symbol: &CStr = CStr::from_bytes_with_nul(b"realloc\0").unwrap();
    unsafe {
        let realloc_ptr: *mut c_void = libc::dlsym(libc::RTLD_NEXT, symbol.as_ptr());
        std::mem::transmute::<*mut c_void, ReallocType>(realloc_ptr)
    }
});

type PosixMemalignType = unsafe extern "C" fn(*mut *mut c_void, usize, usize) -> i32;
static ORIGINAL_POSIX_MEMALIGN: LazyLock<PosixMemalignType> = LazyLock::new(|| {
    let symbol: &CStr = CStr::from_bytes_with_nul(b"posix_memalign\0").unwrap();
    unsafe {
        let posix_memalign_ptr: *mut c_void = libc::dlsym(libc::RTLD_NEXT, symbol.as_ptr());
        std::mem::transmute(posix_memalign_ptr)
    }
});

type AlignedAllocType = unsafe extern "C" fn(usize, usize) -> *mut c_void;
static ORIGINAL_ALIGNED_ALLOC: LazyLock<AlignedAllocType> = LazyLock::new(|| {
    let symbol: &CStr = CStr::from_bytes_with_nul(b"aligned_alloc\0").unwrap();
    unsafe {
        let aligned_alloc_ptr: *mut c_void = libc::dlsym(libc::RTLD_NEXT, symbol.as_ptr());
        std::mem::transmute(aligned_alloc_ptr)
    }
});

type MemalignType = unsafe extern "C" fn(usize, usize) -> *mut c_void;
static ORIGINAL_MEMALIGN: LazyLock<MemalignType> = LazyLock::new(|| {
    let symbol: &CStr = CStr::from_bytes_with_nul(b"memalign\0").unwrap();
    unsafe {
        let memalign_ptr: *mut c_void = libc::dlsym(libc::RTLD_NEXT, symbol.as_ptr());
        std::mem::transmute(memalign_ptr)
    }
});

const FLLEN: usize = 28; // The maximum block size is (32 << 28) - 1 = 8_589_934_591 (nearly 8GiB)
const SLLEN: usize = 64; // The worst-case internal fragmentation is ((32 << 28) / 64 - 2) = 134_217_726 (nearly 128MiB)
type FLBitmap = u32; // FLBitmap should contain at least FLLEN bits
type SLBitmap = u64; // SLBitmap should contain at least SLLEN bits
type TlsfType = Tlsf<'static, FLBitmap, SLBitmap, FLLEN, SLLEN>;
static TLSF: LazyLock<Mutex<TlsfType>> = LazyLock::new(|| {
    // TODO: These mmap related procedures will be moved to agnocast

    let mempool_size_env: String = std::env::var("MEMPOOL_SIZE").unwrap_or_else(|error| {
        panic!("{}: MEMPOOL_SIZE", error);
    });

    let mempool_size: usize = mempool_size_env.parse::<usize>().unwrap_or_else(|error| {
        panic!("{}: MEMPOOL_SIZE", error);
    });

    let page_size: usize = unsafe { libc::sysconf(libc::_SC_PAGESIZE) as usize };
    let aligned_size: usize = (mempool_size + page_size - 1) & !(page_size - 1);

    let addr: *mut c_void = 0x40000000000 as *mut c_void;

    let ptr = unsafe {
        libc::mmap(
            addr,
            aligned_size,
            libc::PROT_READ | libc::PROT_WRITE,
            libc::MAP_PRIVATE | libc::MAP_ANONYMOUS | libc::MAP_FIXED_NOREPLACE,
            -1,
            0,
        )
    };

    if ptr == libc::MAP_FAILED {
        panic!("mmap failed");
    }

    let pool: &mut [MaybeUninit<u8>] =
        unsafe { std::slice::from_raw_parts_mut(ptr as *mut MaybeUninit<u8>, mempool_size) };

    let mut tlsf: TlsfType = Tlsf::new();
    tlsf.insert_free_block(pool);

    Mutex::new(tlsf)
});

static ALIGNED_TO_ORIGINAL: LazyLock<Mutex<HashMap<usize, usize>>> =
    LazyLock::new(|| Mutex::new(HashMap::new()));

fn tlsf_allocate(size: usize) -> *mut c_void {
    let layout: Layout = Layout::from_size_align(size, ALIGNMENT).unwrap_or_else(|error| {
        panic!("{}: size={}, alignment={}", error, size, ALIGNMENT);
    });

    let mut tlsf = TLSF.lock().unwrap();

    let ptr: std::ptr::NonNull<u8> = tlsf.allocate(layout).unwrap_or_else(|| {
        panic!("memory allocation failed: consider using larger MEMPOOL_SIZE");
    });

    ptr.as_ptr() as *mut c_void
}

fn tlsf_reallocate(ptr: std::ptr::NonNull<u8>, size: usize) -> *mut c_void {
    let layout: Layout = Layout::from_size_align(size, ALIGNMENT).unwrap_or_else(|error| {
        panic!("{}: size={}, alignment={}", error, size, ALIGNMENT);
    });

    let mut tlsf = TLSF.lock().unwrap();

    let new_ptr: std::ptr::NonNull<u8> = unsafe {
        tlsf.reallocate(ptr, layout).unwrap_or_else(|| {
            panic!("memory allocation failed: consider using larger MEMPOOL_SIZE");
        })
    };

    new_ptr.as_ptr() as *mut c_void
}

fn tlsf_deallocate(ptr: std::ptr::NonNull<u8>) {
    let mut tlsf = TLSF.lock().unwrap();
    unsafe { tlsf.deallocate(ptr, ALIGNMENT) }
}

fn aligned_alloc_wrapped(alignment: usize, size: usize) -> *mut c_void {
    let addr: usize = tlsf_allocate(size + alignment) as usize;
    let aligned_addr: usize = addr + alignment - (addr % alignment);

    let mut aligned_to_original = ALIGNED_TO_ORIGINAL.lock().unwrap();
    aligned_to_original.insert(aligned_addr, addr);

    aligned_addr as *mut c_void
}

thread_local! {
    static HOOKED : Cell<bool> = const { Cell::new(false) }
}

#[no_mangle]
pub extern "C" fn malloc(size: usize) -> *mut c_void {
    HOOKED.with(|hooked: &Cell<bool>| {
        if hooked.get() {
            unsafe { ORIGINAL_MALLOC(size) }
        } else {
            hooked.set(true);
            let ret: *mut c_void = tlsf_allocate(size);
            hooked.set(false);
            ret
        }
    })
}

#[no_mangle]
pub extern "C" fn free(ptr: *mut c_void) {
    let non_null_ptr: std::ptr::NonNull<u8> = match std::ptr::NonNull::new(ptr as *mut u8) {
        Some(ptr) => ptr,
        None => return,
    };

    HOOKED.with(|hooked: &Cell<bool>| {
        // TODO: address range should use the one the kernel module assigns
        let ptr_addr: usize = non_null_ptr.as_ptr() as usize;
        if hooked.get() || !(0x40000000000..=0x50000000000).contains(&ptr_addr) {
            unsafe { ORIGINAL_FREE(ptr) }
        } else {
            hooked.set(true);

            let mut aligned_to_original = ALIGNED_TO_ORIGINAL.lock().unwrap();

            if let Some(original_addr) = aligned_to_original.get(&ptr_addr) {
                let original_ptr: std::ptr::NonNull<u8> =
                    std::ptr::NonNull::new(*original_addr as *mut c_void as *mut u8).unwrap();
                aligned_to_original.remove(&ptr_addr);
                tlsf_deallocate(original_ptr);
            } else {
                tlsf_deallocate(non_null_ptr);
            }

            hooked.set(false);
        }
    });
}

#[no_mangle]
pub extern "C" fn calloc(num: usize, size: usize) -> *mut c_void {
    HOOKED.with(|hooked: &Cell<bool>| {
        if hooked.get() {
            unsafe { ORIGINAL_CALLOC(num, size) }
        } else {
            hooked.set(true);
            let ret: *mut c_void = tlsf_allocate(num * size);
            unsafe {
                std::ptr::write_bytes(ret, 0, num * size);
            };
            hooked.set(false);
            ret
        }
    })
}

#[no_mangle]
pub extern "C" fn realloc(ptr: *mut c_void, new_size: usize) -> *mut c_void {
    HOOKED.with(|hooked: &Cell<bool>| {
        if hooked.get() {
            unsafe { ORIGINAL_REALLOC(ptr, new_size) }
        } else {
            hooked.set(true);

            let realloc_ret: *mut c_void =
                if let Some(non_null_ptr) = std::ptr::NonNull::new(ptr as *mut u8) {
                    // TODO: address range should use the one the kernel module assigns
                    let ptr_addr: usize = non_null_ptr.as_ptr() as usize;
                    if !(0x40000000000..=0x50000000000).contains(&ptr_addr) {
                        unsafe { ORIGINAL_REALLOC(ptr, new_size) }
                    } else {
                        let mut aligned_to_original = ALIGNED_TO_ORIGINAL.lock().unwrap();
                        if let Some(original_addr) = aligned_to_original.get(&ptr_addr) {
                            let original_ptr: std::ptr::NonNull<u8> =
                                std::ptr::NonNull::new(*original_addr as *mut c_void as *mut u8)
                                    .unwrap();
                            aligned_to_original.remove(&ptr_addr);
                            tlsf_reallocate(original_ptr, new_size)
                        } else {
                            tlsf_reallocate(non_null_ptr, new_size)
                        }
                    }
                } else {
                    tlsf_allocate(new_size)
                };

            hooked.set(false);
            realloc_ret
        }
    })
}

#[no_mangle]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn posix_memalign(memptr: *mut *mut c_void, alignment: usize, size: usize) -> i32 {
    HOOKED.with(|hooked: &Cell<bool>| {
        if hooked.get() {
            unsafe { ORIGINAL_POSIX_MEMALIGN(memptr, alignment, size) }
        } else {
            hooked.set(true);
            unsafe { *memptr = aligned_alloc_wrapped(alignment, size) };
            hooked.set(false);
            0
        }
    })
}

#[no_mangle]
pub extern "C" fn aligned_alloc(alignment: usize, size: usize) -> *mut c_void {
    HOOKED.with(|hooked: &Cell<bool>| {
        if hooked.get() {
            unsafe { ORIGINAL_ALIGNED_ALLOC(alignment, size) }
        } else {
            hooked.set(true);
            let ret = aligned_alloc_wrapped(alignment, size);
            hooked.set(false);
            ret
        }
    })
}

#[no_mangle]
pub extern "C" fn memalign(alignment: usize, size: usize) -> *mut c_void {
    HOOKED.with(|hooked: &Cell<bool>| {
        if hooked.get() {
            unsafe { ORIGINAL_MEMALIGN(alignment, size) }
        } else {
            hooked.set(true);
            let ret = aligned_alloc_wrapped(alignment, size);
            hooked.set(false);
            ret
        }
    })
}

#[no_mangle]
pub extern "C" fn valloc(_size: usize) -> *mut c_void {
    eprintln!("NOTE: valloc is not supported");
    std::ptr::null_mut()
}

#[no_mangle]
pub extern "C" fn pvalloc(_size: usize) -> *mut c_void {
    eprintln!("NOTE: pvalloc is not supported");
    std::ptr::null_mut()
}
