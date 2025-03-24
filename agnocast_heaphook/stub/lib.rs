use std::os::raw::c_void;

#[no_mangle]
pub extern fn initialize_agnocast(size: usize, version: *const c_char, length: usize) -> *mut c_void{
    std::ptr::null_mut()
}
