use rlsf::Tlsf;
use std::{
    alloc::Layout,
    cell::Cell,
    ffi::{c_char, CStr},
    mem::MaybeUninit,
    os::raw::c_void,
    sync::{
        atomic::{AtomicUsize, Ordering},
        LazyLock, Mutex,
    },
};

type InitializeAgnocastType = unsafe extern "C" fn(usize) -> *mut c_void;

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

type PosixMemalignType = unsafe extern "C" fn(&mut *mut c_void, usize, usize) -> i32;
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

static MEMPOOL_START: AtomicUsize = AtomicUsize::new(0);
static MEMPOOL_END: AtomicUsize = AtomicUsize::new(0);

const FLLEN: usize = 28; // The maximum block size is (32 << 28) - 1 = 8_589_934_591 (nearly 8GiB)
const SLLEN: usize = 64; // The worst-case internal fragmentation is ((32 << 28) / 64 - 2) = 134_217_726 (nearly 128MiB)
type FLBitmap = u32; // FLBitmap should contain at least FLLEN bits
type SLBitmap = u64; // SLBitmap should contain at least SLLEN bits
type TlsfType = Tlsf<'static, FLBitmap, SLBitmap, FLLEN, SLLEN>;
static TLSF: LazyLock<Mutex<TlsfType>> = LazyLock::new(|| {
    let mempool_size_env: String = std::env::var("MEMPOOL_SIZE").unwrap_or_else(|error| {
        panic!("[ERROR] [Agnocast] {}: MEMPOOL_SIZE", error);
    });

    let mempool_size: usize = mempool_size_env.parse::<usize>().unwrap_or_else(|error| {
        panic!("[ERROR] [Agnocast] {}: MEMPOOL_SIZE", error);
    });

    let page_size: usize = unsafe { libc::sysconf(libc::_SC_PAGESIZE) as usize };
    let aligned_size: usize = (mempool_size + page_size - 1) & !(page_size - 1);

    let agnocast_lib: *mut c_void = unsafe {
        libc::dlopen(
            b"libagnocast.so\0".as_ptr() as *const c_char,
            libc::RTLD_NOW,
        )
    };
    if agnocast_lib.is_null() {
        panic!("[ERROR] [Agnocast] Failed to load libagnocast.so");
    }

    let symbol: &CStr = CStr::from_bytes_with_nul(b"initialize_agnocast\0").unwrap();
    let initialize_agnocast_ptr: *mut c_void =
        unsafe { libc::dlsym(agnocast_lib, symbol.as_ptr()) };
    if initialize_agnocast_ptr.is_null() {
        panic!("[ERROR] [Agnocast] Failed to find initialize_agnocast() function");
    }

    let initialize_agnocast: InitializeAgnocastType =
        unsafe { std::mem::transmute(initialize_agnocast_ptr) };

    let mempool_ptr: *mut c_void = unsafe { initialize_agnocast(aligned_size) };

    unsafe { libc::dlclose(agnocast_lib) };

    let pool: &mut [MaybeUninit<u8>] = unsafe {
        std::slice::from_raw_parts_mut(mempool_ptr as *mut MaybeUninit<u8>, mempool_size)
    };

    MEMPOOL_START.store(mempool_ptr as usize, Ordering::Relaxed);
    MEMPOOL_END.store(mempool_ptr as usize + mempool_size, Ordering::Relaxed);

    let mut tlsf: TlsfType = Tlsf::new();
    tlsf.insert_free_block(pool);

    Mutex::new(tlsf)
});

fn tlsf_allocate(size: usize) -> *mut c_void {
    let layout: Layout = Layout::from_size_align(size, ALIGNMENT).unwrap_or_else(|error| {
        panic!(
            "[ERROR] [Agnocast] {}: size={}, alignment={}",
            error, size, ALIGNMENT
        );
    });

    let mut tlsf = TLSF.lock().unwrap();

    let ptr: std::ptr::NonNull<u8> = tlsf.allocate(layout).unwrap_or_else(|| {
        panic!("[ERROR] [Agnocast] memory allocation failed: use larger MEMPOOL_SIZE");
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

    let mut tlsf = TLSF.lock().unwrap();

    let new_ptr: std::ptr::NonNull<u8> = unsafe {
        tlsf.reallocate(ptr, layout).unwrap_or_else(|| {
            panic!("[ERROR] [Agnocast] memory allocation failed: use larger MEMPOOL_SIZE");
        })
    };

    new_ptr.as_ptr() as *mut c_void
}

fn tlsf_deallocate(ptr: std::ptr::NonNull<u8>) {
    let mut tlsf = TLSF.lock().unwrap();
    unsafe { tlsf.deallocate(ptr, ALIGNMENT) }
}

fn tlsf_allocate_wrapped(alignment: usize, size: usize) -> *mut c_void {
    // size of void pointer
    static POINTER_SIZE: usize = std::mem::size_of::<&usize>();

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
    // size of void pointer
    static POINTER_SIZE: usize = std::mem::size_of::<&usize>();

    // get the original start address from internal allocator
    let original_start_addr: usize = unsafe { *((ptr - POINTER_SIZE) as *mut usize) };
    let original_start_addr_ptr: std::ptr::NonNull<u8> =
        std::ptr::NonNull::new(original_start_addr as *mut c_void as *mut u8).unwrap();

    // return value from internal alloc
    let start_addr: usize = tlsf_reallocate(original_start_addr_ptr, ALIGNMENT + size) as usize;
    let start_addr_ptr: *mut usize = (start_addr + ALIGNMENT - POINTER_SIZE) as *mut usize;

    // store `start_addr`
    unsafe { *start_addr_ptr = start_addr };

    (start_addr + ALIGNMENT) as *mut c_void
}

fn tlsf_deallocate_wrapped(ptr: usize) {
    // size of void pointer
    static POINTER_SIZE: usize = std::mem::size_of::<&usize>();

    // get the original start address from internal allocator
    let start_addr: usize = unsafe { *((ptr - POINTER_SIZE) as *mut usize) };
    let start_addr_ptr: std::ptr::NonNull<u8> =
        std::ptr::NonNull::new(start_addr as *mut c_void as *mut u8).unwrap();

    tlsf_deallocate(start_addr_ptr);
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
            let ret: *mut c_void = tlsf_allocate_wrapped(0, size);
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
        let ptr_addr: usize = non_null_ptr.as_ptr() as usize;
        let allocated_by_original: bool = ptr_addr < MEMPOOL_START.load(Ordering::Relaxed)
            || ptr_addr > MEMPOOL_END.load(Ordering::Relaxed);

        if hooked.get() || allocated_by_original {
            unsafe { ORIGINAL_FREE(ptr) }
        } else {
            hooked.set(true);
            tlsf_deallocate_wrapped(ptr_addr);
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
            let ret: *mut c_void = tlsf_allocate_wrapped(0, num * size);
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

            let realloc_ret: *mut c_void = if let Some(non_null_ptr) =
                std::ptr::NonNull::new(ptr as *mut u8)
            {
                let ptr_addr: usize = non_null_ptr.as_ptr() as usize;
                let allocated_by_original: bool = ptr_addr < MEMPOOL_START.load(Ordering::Relaxed)
                    || ptr_addr > MEMPOOL_END.load(Ordering::Relaxed);

                if allocated_by_original {
                    unsafe { ORIGINAL_REALLOC(ptr, new_size) }
                } else {
                    tlsf_reallocate_wrapped(ptr_addr, new_size)
                }
            } else {
                tlsf_allocate_wrapped(0, new_size)
            };

            hooked.set(false);
            realloc_ret
        }
    })
}

#[no_mangle]
pub extern "C" fn posix_memalign(memptr: &mut *mut c_void, alignment: usize, size: usize) -> i32 {
    HOOKED.with(|hooked: &Cell<bool>| {
        if hooked.get() {
            unsafe { ORIGINAL_POSIX_MEMALIGN(memptr, alignment, size) }
        } else {
            hooked.set(true);
            *memptr = tlsf_allocate_wrapped(alignment, size);
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
            let ret = tlsf_allocate_wrapped(alignment, size);
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
            let ret = tlsf_allocate_wrapped(alignment, size);
            hooked.set(false);
            ret
        }
    })
}

#[no_mangle]
pub extern "C" fn valloc(_size: usize) -> *mut c_void {
    panic!("[ERROR] [Agnocast] valloc is not supported");
}

#[no_mangle]
pub extern "C" fn pvalloc(_size: usize) -> *mut c_void {
    panic!("[ERROR] [Agnocast] pvalloc is not supported");
}
