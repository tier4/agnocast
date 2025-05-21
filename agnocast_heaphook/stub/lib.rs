use std::os::raw::{c_void, c_char};

#[no_mangle]
pub extern "C" fn initialize_agnocast(size: usize, version: *const c_char, length: usize) -> *mut c_void{
    std::ptr::null_mut()
}

#[no_mangle]
pub extern "C" fn agnocast_get_borrowed_publisher_num() -> u32 {
    0
}

#[no_mangle]
pub extern "C" fn get_gl() -> u32 {
    0
}

#[no_mangle]
pub extern "C" fn get_gl_addr() -> u64 {
    0
}
