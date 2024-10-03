use once_cell::sync::Lazy;
use rlsf::Tlsf;
use std::{
    alloc::Layout, cell::RefCell, ffi::CStr, mem::MaybeUninit, os::raw::c_void, sync::Mutex,
};

const ALIGNMENT: usize = 64;

type MallocType = unsafe extern "C" fn(usize) -> *mut c_void;
static ORIGINAL_MALLOC: Lazy<MallocType> = Lazy::new(|| {
    let symbol: &CStr = CStr::from_bytes_with_nul(b"malloc\0").unwrap();
    unsafe {
        let malloc_ptr: *mut c_void = libc::dlsym(libc::RTLD_NEXT, symbol.as_ptr());
        std::mem::transmute(malloc_ptr)
    }
});

type FreeType = unsafe extern "C" fn(*mut c_void) -> ();
static ORIGINAL_FREE: Lazy<FreeType> = Lazy::new(|| {
    let symbol: &CStr = CStr::from_bytes_with_nul(b"free\0").unwrap();
    unsafe {
        let free_ptr: *mut c_void = libc::dlsym(libc::RTLD_NEXT, symbol.as_ptr());
        std::mem::transmute(free_ptr)
    }
});

type CallocType = unsafe extern "C" fn(usize, usize) -> *mut c_void;
static ORIGINAL_CALLOC: Lazy<CallocType> = Lazy::new(|| {
    let symbol: &CStr = CStr::from_bytes_with_nul(b"calloc\0").unwrap();
    unsafe {
        let calloc_ptr: *mut c_void = libc::dlsym(libc::RTLD_NEXT, symbol.as_ptr());
        std::mem::transmute(calloc_ptr)
    }
});

type ReallocType = unsafe extern "C" fn(*mut c_void, usize) -> *mut c_void;
static ORIGINAL_REALLOC: Lazy<ReallocType> = Lazy::new(|| {
    let symbol: &CStr = CStr::from_bytes_with_nul(b"realloc\0").unwrap();
    unsafe {
        let realloc_ptr: *mut c_void = libc::dlsym(libc::RTLD_NEXT, symbol.as_ptr());
        std::mem::transmute(realloc_ptr)
    }
});

type TlsfType = Tlsf<'static, u32, u32, 32, 32>;
static TLSF: Lazy<Mutex<TlsfType>> = Lazy::new(|| {
    // TODO: These mmap related procedures will be moved to agnocast

    let mempool_size_env: String = match std::env::var("MEMPOOL_SIZE") {
        Ok(value) => value,
        Err(error) => {
            println!("MEMPOOL_SIZE is not set in environment variable: {}", error);
            std::process::exit(1);
        }
    };

    const PAGE_SIZE: usize = 4096;
    let mempool_size: usize = mempool_size_env.parse::<usize>().unwrap();
    let aligned_size: usize = (mempool_size + PAGE_SIZE - 1) & !(PAGE_SIZE - 1);

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
        println!("mmap failed");
        std::process::exit(1);
    }

    let pool: &mut [MaybeUninit<u8>] =
        unsafe { std::slice::from_raw_parts_mut(ptr as *mut MaybeUninit<u8>, mempool_size) };

    let mut tlsf: TlsfType = Tlsf::new();
    tlsf.insert_free_block(pool);

    Mutex::new(tlsf)
});

fn tlsf_allocate(size: usize) -> *mut c_void {
    let layout: Layout = Layout::from_size_align(size, ALIGNMENT).unwrap();
    let ptr: std::ptr::NonNull<u8> = TLSF.lock().unwrap().allocate(layout).unwrap();
    ptr.as_ptr() as *mut c_void
}

fn tlsf_reallocate(ptr: *mut c_void, size: usize) -> *mut c_void {
    let layout: Layout = Layout::from_size_align(size, ALIGNMENT).unwrap();
    let new_ptr: std::ptr::NonNull<u8> = unsafe {
        let non_null_ptr: std::ptr::NonNull<u8> = std::ptr::NonNull::new_unchecked(ptr as *mut u8);
        TLSF.lock()
            .unwrap()
            .reallocate(non_null_ptr, layout)
            .unwrap()
    };
    new_ptr.as_ptr() as *mut c_void
}

fn tlsf_deallocate(ptr: *mut c_void) {
    unsafe {
        let non_null_ptr: std::ptr::NonNull<u8> = std::ptr::NonNull::new_unchecked(ptr as *mut u8);
        TLSF.lock().unwrap().deallocate(non_null_ptr, ALIGNMENT);
    }
}

thread_local! {
    static HOOKED : RefCell<bool> = const { RefCell::new(false) }
}

#[no_mangle]
pub extern "C" fn malloc(size: usize) -> *mut c_void {
    HOOKED.with(|hooked: &RefCell<bool>| {
        if *hooked.borrow() {
            unsafe { ORIGINAL_MALLOC(size) }
        } else {
            hooked.replace(true);
            let ret: *mut c_void = tlsf_allocate(size);
            hooked.replace(false);
            ret
        }
    })
}

#[no_mangle]
pub extern "C" fn free(ptr: *mut c_void) {
    if ptr.is_null() {
        return;
    };

    let ptr_addr: usize =
        unsafe { std::ptr::NonNull::new_unchecked(ptr as *mut u8).as_ptr() as usize };

    HOOKED.with(|hooked: &RefCell<bool>| {
        // TODO: address range should use the one the kernel module assigns
        if *hooked.borrow() || !(0x40000000000..=0x50000000000).contains(&ptr_addr) {
            unsafe {
                ORIGINAL_FREE(ptr);
            }
        } else {
            hooked.replace(true);
            tlsf_deallocate(ptr);
            hooked.replace(false);
        }
    });
}

#[no_mangle]
pub extern "C" fn calloc(num: usize, size: usize) -> *mut c_void {
    HOOKED.with(|hooked: &RefCell<bool>| {
        if *hooked.borrow() {
            unsafe { ORIGINAL_CALLOC(num, size) }
        } else {
            hooked.replace(true);
            let ret: *mut c_void = tlsf_allocate(num * size);
            unsafe {
                std::ptr::write_bytes(ret, 0, num * size);
            };
            hooked.replace(false);
            ret
        }
    })
}

#[no_mangle]
pub extern "C" fn realloc(ptr: *mut c_void, new_size: usize) -> *mut c_void {
    HOOKED.with(|hooked: &RefCell<bool>| {
        if *hooked.borrow() {
            unsafe { ORIGINAL_REALLOC(ptr, new_size) }
        } else {
            hooked.replace(true);

            let realloc_ret: *mut c_void = if ptr.is_null() {
                tlsf_allocate(new_size)
            } else {
                let ptr_addr: usize =
                    unsafe { std::ptr::NonNull::new_unchecked(ptr as *mut u8).as_ptr() as usize };
                // TODO: address range should use the one the kernel module assigns
                if !(0x40000000000..=0x50000000000).contains(&ptr_addr) {
                    unsafe { ORIGINAL_REALLOC(ptr, new_size) }
                } else {
                    tlsf_reallocate(ptr, new_size)
                }
            };

            hooked.replace(false);
            realloc_ret
        }
    })
}

#[no_mangle]
pub extern "C" fn posix_memalign(
    _memptr: *mut *mut c_void,
    _alignment: usize,
    _size: usize,
) -> i32 {
    println!("NOTE: posix_memalign is not supported");
    0
}

#[no_mangle]
pub extern "C" fn aligned_alloc(_alignment: usize, _size: usize) -> *mut c_void {
    println!("TODO: aligned_alloc is not supported");
    std::ptr::null_mut()
}

#[no_mangle]
pub extern "C" fn memalign(_alignment: usize, _size: usize) -> *mut c_void {
    println!("TODO: memalign is not supported");
    std::ptr::null_mut()
}

#[no_mangle]
pub extern "C" fn valloc(_size: usize) -> *mut c_void {
    println!("NOTE: valloc is not supported");
    std::ptr::null_mut()
}

#[no_mangle]
pub extern "C" fn pvalloc(_size: usize) -> *mut c_void {
    println!("NOTE: pvalloc is not supported");
    std::ptr::null_mut()
}
