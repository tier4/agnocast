use std::os::raw::c_void;

#[no_mangle]
pub extern fn initialize_agnocast(size: usize) -> *mut c_void{
    std::ptr::null_mut()
}

#[no_mangle]
pub extern "C" fn agnocast_get_borrowed_publisher_num() -> u32 {	
    0	
}	
