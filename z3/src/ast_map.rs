
use std::ffi::{CStr};
use std::fmt;
use z3_sys::*;
use Context;
use crate::AstMap;


#[cfg(feature = "arbitrary-size-numeral")]
use num::{
    bigint::{BigInt, BigUint, Sign},
    rational::BigRational,
};

impl<'ctx> AstMap<'ctx> {

    pub fn wrap(ctx: &'ctx Context, z3_ast_map: Z3_ast_map) -> Self {
        unsafe {
            Z3_ast_map_inc_ref(ctx.z3_ctx, z3_ast_map);
        }
        Self { ctx, z3_ast_map }
    }
    /// Create a new Ast vector.
    pub fn new(ctx: &'ctx Context) -> AstMap {
        unsafe {
            AstMap::wrap(ctx, Z3_mk_ast_map(ctx.z3_ctx))
        }
    }

}

impl<'ctx> fmt::Display for AstMap<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let p = unsafe { Z3_ast_map_to_string(self.ctx.z3_ctx, self.z3_ast_map) };
        if p.is_null() {
            return Result::Err(fmt::Error);
        }
        match unsafe { CStr::from_ptr(p) }.to_str() {
            Ok(s) => write!(f, "{}", s),
            Err(_) => Result::Err(fmt::Error),
        }
    }
}

impl<'ctx> fmt::Debug for AstMap<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        <Self as fmt::Display>::fmt(self, f)
    }
}

impl<'ctx> Drop for AstMap<'ctx> {
    fn drop(&mut self) {
        unsafe { Z3_ast_map_dec_ref(self.ctx.z3_ctx, self.z3_ast_map) };
    }
}