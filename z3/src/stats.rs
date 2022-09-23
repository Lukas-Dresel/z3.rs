use std::ffi::CStr;
use std::fmt;
use z3_sys::*;
use Stats;
use Optimize;
use Solver;
use Z3_MUTEX;


impl<'ctx> Stats<'ctx> {
    pub fn of_solver(slv: &Solver<'ctx>) -> Option<Stats<'ctx>> {
        Some(Stats {
            ctx: slv.ctx,
            z3_stats: unsafe {
                let guard = Z3_MUTEX.lock().unwrap();
                let z3_stats = Z3_solver_get_statistics(slv.ctx.z3_ctx, slv.z3_slv);
                if z3_stats.is_null() {
                    return None;
                }
                Z3_stats_inc_ref(slv.ctx.z3_ctx, z3_stats);
                z3_stats
            },
        })
    }

    pub fn of_optimize(opt: &Optimize<'ctx>) -> Option<Stats<'ctx>> {
        Some(Stats {
            ctx: opt.ctx,
            z3_stats: unsafe {
                let guard = Z3_MUTEX.lock().unwrap();
                let z3_stats = Z3_optimize_get_statistics(opt.ctx.z3_ctx, opt.z3_opt);
                if z3_stats.is_null() {
                    return None;
                }
                Z3_stats_inc_ref(opt.ctx.z3_ctx, z3_stats);
                z3_stats
            },
        })
    }
}

impl<'ctx> fmt::Display for Stats<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let p = unsafe { Z3_stats_to_string(self.ctx.z3_ctx, self.z3_stats) };
        if p.is_null() {
            return Result::Err(fmt::Error);
        }
        match unsafe { CStr::from_ptr(p) }.to_str() {
            Ok(s) => write!(f, "{}", s),
            Err(_) => Result::Err(fmt::Error),
        }
    }
}

impl<'ctx> fmt::Debug for Stats<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        <Self as fmt::Display>::fmt(self, f)
    }
}

impl<'ctx> Drop for Stats<'ctx> {
    fn drop(&mut self) {
        let guard = Z3_MUTEX.lock().unwrap();
        unsafe { Z3_stats_dec_ref(self.ctx.z3_ctx, self.z3_stats) };
    }
}

#[test]
fn test_stats() {
    use crate::{ast, Config, SatResult};
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);
    solver.assert(&ast::Bool::from_bool(&ctx, false));
    assert_eq!(solver.check(), SatResult::Unsat);
    assert!(solver.get_statistics().is_some());
    debug!("{:?}", solver.get_statistics());
}
