use ast::Ast;
use std::convert::{TryInto, TryFrom};
use std::ffi::{CStr};
use std::fmt;
use z3_sys::*;
use Context;
use crate::ast::Dynamic;
use crate::AstVector;


#[cfg(feature = "arbitrary-size-numeral")]
use num::{
    bigint::{BigInt, BigUint, Sign},
    rational::BigRational,
};

impl<'ctx> AstVector<'ctx> {
    pub unsafe fn wrap(ctx: &'ctx Context, z3_ast_vec: Z3_ast_vector) -> Option<AstVector> {
        if z3_ast_vec.is_null() {
            return None;
        }
        Z3_ast_vector_inc_ref(ctx.z3_ctx, z3_ast_vec);
        Some(AstVector {
            ctx,
            z3_ast_vector: z3_ast_vec
        })
    }

    pub fn retrieve<T>(ctx: &'ctx Context, object: T, getter: &dyn Fn(Z3_context, T) -> Z3_ast_vector) -> Option<AstVector<'ctx>> {
        let ast_vec = getter(ctx.z3_ctx, object);
        unsafe {
            AstVector::wrap(
                ctx,
                ast_vec
            ).map(|x| x.into())
        }
    }
    pub fn as_vec<T: Ast<'ctx> + TryFrom<Dynamic<'ctx>>>(&self) -> Result<Vec<T>, T::Error>
    {
        let ctx = self.ctx;
        let len = unsafe { Z3_ast_vector_size(ctx.z3_ctx, self.z3_ast_vector) };

        (0..len)
            .map(|idx| unsafe {
                    Dynamic::wrap(
                    ctx,
                    unsafe { Z3_ast_vector_get(ctx.z3_ctx, self.z3_ast_vector, idx) }
                ).try_into()
            })
            .collect()
    }
    /// Create a new Ast vector.
    pub fn new(ctx: &'ctx Context) -> Option<AstVector> {
        unsafe {
            AstVector::wrap(
                ctx,
                Z3_mk_ast_vector(ctx.z3_ctx)
            )
        }
    }

}

impl<'ctx> fmt::Display for AstVector<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        unsafe {
            let p = Z3_ast_vector_to_string(self.ctx.z3_ctx, self.z3_ast_vector);
            if p.is_null() {
                return Result::Err(fmt::Error);
            }
            match CStr::from_ptr(p).to_str() {
                Ok(s) => write!(f, "{}", s),
                Err(_) => Result::Err(fmt::Error),
            }
        }
    }
}

impl<'ctx> fmt::Debug for AstVector<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        <Self as fmt::Display>::fmt(self, f)
    }
}

impl<'ctx> Drop for AstVector<'ctx> {
    fn drop(&mut self) {
        unsafe { Z3_ast_vector_dec_ref(self.ctx.z3_ctx, self.z3_ast_vector) };
    }
}

impl<'ctx> From<AstVector<'ctx>> for Vec<Dynamic<'ctx>>
{
    fn from(vec: AstVector<'ctx>) -> Vec<Dynamic<'ctx>> {
        vec.as_vec().expect("A conversion to Dynamic should never fail!")
    }
}