use ast::{Ast,Dynamic};
use std::{ffi::CStr, convert::TryInto};
use std::fmt;
use z3_sys::*;
use Context;
use Model;
use Optimize;
use Solver;

use crate::{FuncDecl, Sort};

impl<'ctx> Model<'ctx> {
    unsafe fn wrap(ctx: &'ctx Context, z3_mdl: Z3_model) -> Model<'ctx> {
        Z3_model_inc_ref(ctx.z3_ctx, z3_mdl);
        Model { ctx, z3_mdl }
    }

    pub fn of_solver(slv: &Solver<'ctx>) -> Option<Model<'ctx>> {
        unsafe {
            let m = Z3_solver_get_model(slv.ctx.z3_ctx, slv.z3_slv);
            if m.is_null() {
                None
            } else {
                Some(Self::wrap(slv.ctx, m))
            }
        }
    }

    pub fn of_optimize(opt: &Optimize<'ctx>) -> Option<Model<'ctx>> {
        unsafe {
            let m = Z3_optimize_get_model(opt.ctx.z3_ctx, opt.z3_opt);
            if m.is_null() {
                None
            } else {
                Some(Self::wrap(opt.ctx, m))
            }
        }
    }

    pub fn get_context(&self) -> &'ctx Context {
        self.ctx
    }

    /// Translate model to context `dest`
    pub fn translate<'dest_ctx>(&self, dest: &'dest_ctx Context) -> Model<'dest_ctx> {
        unsafe {
            Model::wrap(
                dest,
                Z3_model_translate(self.ctx.z3_ctx, self.z3_mdl, dest.z3_ctx),
            )
        }
    }

    pub fn eval<T>(&self, ast: &T, model_completion: bool) -> Option<T>
    where
        T: Ast<'ctx>,
    {
        let mut tmp: Z3_ast = ast.get_z3_ast();
        let res = {
            unsafe {
                Z3_model_eval(
                    self.ctx.z3_ctx,
                    self.z3_mdl,
                    ast.get_z3_ast(),
                    model_completion,
                    &mut tmp,
                )
            }
        };
        if res {
            Some(unsafe { T::wrap(self.ctx, tmp) })
        } else {
            None
        }
    }

    /// Return the interpretation (i.e., assignment) of constant `a` in the current model.
    ///
    /// Return `None`, if the model does not assign an interpretation for `a`.
    /// That should be interpreted as: the value of `a` does not matter.
    ///
    /// # Preconditions:
    ///
    /// - `a.arity() == 0`
    pub fn get_const_interpretation(&self, a: &FuncDecl) -> Option<Dynamic<'ctx>>
    {
        assert!(a.arity() == 0);
        unsafe {
            let res = Z3_model_get_const_interp (
                self.ctx.z3_ctx,
                self.z3_mdl,
                a.z3_func_decl
            );
            if !res.is_null() {
                Some(Dynamic::wrap(self.ctx, res))
            } else {
                None
            }
        }
    }

    pub fn num_consts(&self) -> usize {
        unsafe
        {
            Z3_model_get_num_consts(self.ctx.z3_ctx, self.z3_mdl)
                .try_into().unwrap() // panic on out of bounds
        }
    }

    pub fn num_functions(&self) -> usize {
        unsafe {
            Z3_model_get_num_funcs(self.ctx.z3_ctx, self.z3_mdl)
                .try_into().unwrap() // panic on out of bounds
        }
    }

    pub fn num_sorts(&self) -> usize {
        unsafe
        {
            Z3_model_get_num_sorts(self.ctx.z3_ctx, self.z3_mdl)
                .try_into().unwrap() // panic on out of bounds
        }
    }

    pub fn constant(&self, idx: usize) -> FuncDecl<'ctx> {
        let idx: u32 = idx.try_into().unwrap();  // panic on out of bounds
        unsafe {
            FuncDecl::wrap(self.ctx, Z3_model_get_const_decl(self.ctx.z3_ctx, self.z3_mdl, idx))
        }
    }

    pub fn constants(&self) -> Vec<FuncDecl<'ctx>> {
        (0..self.num_consts())
            .map(|idx| self.constant(idx))
            .collect()
    }

    pub fn function_decl(&self, idx: usize) -> FuncDecl<'ctx> {
        unsafe {
            FuncDecl::wrap(
                self.ctx,
                Z3_model_get_func_decl(self.ctx.z3_ctx, self.z3_mdl, idx.try_into().unwrap()),
            )
        }
    }

    pub fn function_decls(&self) -> Vec<FuncDecl<'ctx>> {
        (0..self.num_functions())
            .map(|idx| self.function_decl(idx))
            .collect()
    }

    pub fn sort_at(&self, idx: usize) -> Sort {
        let idx = idx.try_into().unwrap();
        unsafe {
            Sort::wrap(
                self.ctx,
                Z3_model_get_sort(self.ctx.z3_ctx, self.z3_mdl, idx)
            )
        }
    }

    pub fn sorts(&self) -> Vec<Sort> {
        (0..self.num_sorts())
            .map(|idx| self.sort_at(idx))
            .collect()
    }
}

impl<'ctx> fmt::Display for Model<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let p = unsafe { Z3_model_to_string(self.ctx.z3_ctx, self.z3_mdl) };
        if p.is_null() {
            return Result::Err(fmt::Error);
        }
        match unsafe { CStr::from_ptr(p) }.to_str() {
            Ok(s) => write!(f, "{}", s),
            Err(_) => Result::Err(fmt::Error),
        }
    }
}

impl<'ctx> fmt::Debug for Model<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        <Self as fmt::Display>::fmt(self, f)
    }
}

impl<'ctx> Drop for Model<'ctx> {
    fn drop(&mut self) {
        unsafe { Z3_model_dec_ref(self.ctx.z3_ctx, self.z3_mdl) };
    }
}

#[test]
fn test_unsat() {
    use crate::{ast, Config, SatResult};
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);
    solver.assert(&ast::Bool::from_bool(&ctx, false));
    assert_eq!(solver.check(), SatResult::Unsat);
    assert!(solver.get_model().is_none());
}
