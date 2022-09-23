use std::{ptr::null, ffi::{CStr, CString}};

use z3_sys::*;
use Config;
use Context;
use ContextHandle;

use crate::{AstVector, ast::Dynamic};

#[derive(Debug)]
pub struct ParseError {
    code : ErrorCode,
    msg: String,
}

impl Context {
    pub fn new(cfg: &Config) -> Context {
        Context {
            z3_ctx: unsafe {
                let p = Z3_mk_context_rc(cfg.z3_cfg);
                debug!("new context {:p}", p);
                Z3_set_error_handler(p, None);
                p
            },
        }
    }

    pub unsafe fn get_z3_ctx(&self) -> Z3_context {
        self.z3_ctx
    }

    /// Interrupt a solver performing a satisfiability test, a tactic processing a goal, or simplify functions.
    pub fn interrupt(&self) {
        self.handle().interrupt()
    }

    /// Obtain a handle that can be used to interrupt computation from another thread.
    ///
    /// # See also:
    ///
    /// - [`ContextHandle`]
    /// - [`ContextHandle::interrupt()`]
    pub fn handle(&self) -> ContextHandle {
        ContextHandle { ctx: self }
    }

    pub fn set_ast_print_mode(&self, mode: AstPrintMode) {
        unsafe {
            Z3_set_ast_print_mode(self.z3_ctx, mode)
        };
    }

    pub fn last_error(&self) -> (ErrorCode, String) {
        unsafe {
            let error_code = Z3_get_error_code(self.z3_ctx);
            let error_msg_ptr = Z3_get_error_msg(self.z3_ctx, error_code);
            assert!(!error_msg_ptr.is_null());
            let error_msg = String::from(CStr::from_ptr(error_msg_ptr).to_str().unwrap());
            (error_code, error_msg)
        }
    }

    pub fn parse_file(&self, filename: &str) -> Result<Vec<Dynamic>, ParseError> {
        unsafe {
            let filename = CString::new(filename).expect("your filename cannot contain null bytes");
            let result = Z3_parse_smtlib2_file(
                        self.z3_ctx,
                        filename.as_ptr() as *const i8,
                        0,
                        null(),
                        null(),
                        0,
                        null(),
                        null(),
                    );
            let error_code = Z3_get_error_code(self.z3_ctx);
            if error_code != ErrorCode::OK {
                let error_msg_ptr = Z3_get_error_msg(self.z3_ctx, error_code);
                assert!(!error_msg_ptr.is_null());
                let error_msg = String::from(CStr::from_ptr(error_msg_ptr).to_str().unwrap());
                return Err(ParseError { code : error_code, msg: error_msg })
            }

            match AstVector::wrap(self, result) {
                Some(ast_vec) => {
                    // println!("ast_vec: {:?}", ast_vec);
                    Ok(ast_vec.as_vec().unwrap())
                },
                None => Ok(vec![])
            }
        }
    }
    pub fn parse_string(&self, smtlib2_string: &str) -> Result<Vec<Dynamic>, ParseError> {
        unsafe {
            let result = Z3_parse_smtlib2_string(
                self.z3_ctx,
                smtlib2_string.as_ptr() as *const i8,
                0,
                null(),
                null(),
                0,
                null(),
                null(),
            );
            let error_code = Z3_get_error_code(self.z3_ctx);
            if error_code != ErrorCode::OK {
                let error_msg_ptr = Z3_get_error_msg(self.z3_ctx, error_code);
                assert!(!error_msg_ptr.is_null());
                let error_msg = String::from(unsafe { CStr::from_ptr(error_msg_ptr) }.to_str().unwrap());
                return Err(ParseError { code : error_code, msg: error_msg })
            }
            match AstVector::wrap(self, result) {
                Some(ast_vec) => {
                    println!("ast_vec: {:?}", ast_vec);
                    Ok(ast_vec.as_vec().unwrap())
                },
                None => Ok(vec![])
            }
        }
    }
}

impl<'ctx> ContextHandle<'ctx> {
    /// Interrupt a solver performing a satisfiability test, a tactic processing a goal, or simplify functions.
    pub fn interrupt(&self) {
        unsafe {
            Z3_interrupt(self.ctx.z3_ctx);
        }
    }
}

unsafe impl<'ctx> Sync for ContextHandle<'ctx> {}
unsafe impl<'ctx> Send for ContextHandle<'ctx> {}

impl Drop for Context {
    fn drop(&mut self) {
        unsafe { Z3_del_context(self.z3_ctx) };
    }
}
