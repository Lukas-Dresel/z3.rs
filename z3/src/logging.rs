use std::ffi::CString;

use z3_sys::*;

pub fn open_log(log_file_path: &str) {
    let s = CString::new(log_file_path.as_bytes()).unwrap();
    unsafe {
        Z3_open_log(s.as_ptr() as *const i8)
    };
}

pub fn append_log(to_append: &str) {
    let s = CString::new(to_append.as_bytes()).unwrap();
    unsafe {
        Z3_append_log(s.as_ptr() as *const i8)
    }
}

pub fn close_log() {
    unsafe {
        Z3_close_log()
    };
}

pub fn toggle_warning_messages(enabled: bool) {
    unsafe {
        Z3_toggle_warning_messages(enabled)
    }
}