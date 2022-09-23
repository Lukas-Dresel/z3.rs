use ast;
use ast::{Ast, Dynamic};
use std::convert::TryInto;
use std::hash::{Hash,Hasher};
use std::ffi::CStr;
use std::fmt;
use z3_sys::*;
use {Context, FuncDecl, Sort, Symbol};

#[derive(Debug, Clone, PartialEq)]
pub enum DeclParam<'ctx> {
    AST(ast::Dynamic<'ctx>),
    Double(f64),
    Int(i32),
    Sort(Sort<'ctx>),
    Symbol(Symbol),
    Rational(String),
}
impl<'ctx> FuncDecl<'ctx> {
    pub(crate) unsafe fn wrap(ctx: &'ctx Context, z3_func_decl: Z3_func_decl) -> Self {
        Z3_inc_ref(ctx.z3_ctx, Z3_func_decl_to_ast(ctx.z3_ctx, z3_func_decl));
        Self { ctx, z3_func_decl }
    }

    pub fn new<S: Into<Symbol>>(
        ctx: &'ctx Context,
        name: S,
        domain: &[&Sort<'ctx>],
        range: &Sort<'ctx>,
    ) -> Self {
        assert!(domain.iter().all(|s| s.ctx.z3_ctx == ctx.z3_ctx));
        assert_eq!(ctx.z3_ctx, range.ctx.z3_ctx);

        let domain: Vec<_> = domain.iter().map(|s| s.z3_sort).collect();

        unsafe {
            Self::wrap(
                ctx,
                Z3_mk_func_decl(
                    ctx.z3_ctx,
                    name.into().as_z3_symbol(ctx),
                    domain.len().try_into().unwrap(),
                    domain.as_ptr(),
                    range.z3_sort,
                ),
            )
        }
    }

    pub fn as_dynamic(&self) -> Dynamic<'ctx> {
        unsafe {
            Dynamic::wrap(self.ctx, Z3_func_decl_to_ast(self.ctx.z3_ctx, self.z3_func_decl))
        }
    }

    /// Return the number of arguments of a function declaration.
    ///
    /// If the function declaration is a constant, then the arity is `0`.
    ///
    /// ```
    /// # use z3::{Config, Context, FuncDecl, Solver, Sort, Symbol};
    /// # let cfg = Config::new();
    /// # let ctx = Context::new(&cfg);
    /// let f = FuncDecl::new(
    ///     &ctx,
    ///     "f",
    ///     &[&Sort::int(&ctx), &Sort::real(&ctx)],
    ///     &Sort::int(&ctx));
    /// assert_eq!(f.arity(), 2);
    /// ```
    pub fn arity(&self) -> usize {
        unsafe { Z3_get_arity(self.ctx.z3_ctx, self.z3_func_decl) as usize }
    }

    pub fn domain_size(&self) -> usize {
        unsafe { Z3_get_domain_size(self.ctx.z3_ctx, self.z3_func_decl) as usize }
    }

    pub fn domain_at(&self, idx: usize) -> Sort {
        unsafe {
            Sort::wrap(self.ctx, Z3_get_domain(self.ctx.z3_ctx, self.z3_func_decl, idx as u32))
        }
    }

    pub fn domain(&self) -> Vec<Sort> {
        (0..self.domain_size())
            .map(|idx| self.domain_at(idx))
            .collect()
    }
    /// Return the range of the given declaration.
    ///
    /// If it is a constant (i.e., has zero arguments), then this
    /// function returns the sort of the constant.
    pub fn range(&self) -> Sort {
        unsafe {
            Sort::wrap(self.ctx, Z3_get_range(self.ctx.z3_ctx, self.z3_func_decl))
        }
    }
    pub fn parameter_kind(&self, idx: usize) -> ParameterKind {
        unsafe { Z3_get_decl_parameter_kind(self.ctx.z3_ctx, self.z3_func_decl, idx as u32) }
    }
    pub fn num_params(&self) -> usize {
        unsafe { Z3_get_decl_num_parameters(self.ctx.z3_ctx, self.z3_func_decl) as usize }
    }
    pub fn parameter(&self, idx: usize) -> DeclParam {
        let kind = self.parameter_kind(idx);
        let c = self.ctx.z3_ctx;
        let d = self.z3_func_decl;
        let i = idx as u32;
        match kind {
            ParameterKind::AST => DeclParam::AST(
                unsafe {
                    ast::Dynamic::wrap(
                        self.ctx,
                        Z3_get_decl_ast_parameter(c, d, i)
                    )
                }
            ),
            ParameterKind::Double => DeclParam::Double(
                unsafe { Z3_get_decl_double_parameter(c, d, i) }
            ),
            ParameterKind::Int => DeclParam::Int(
                unsafe { Z3_get_decl_int_parameter(c, d, i) }
            ),
            ParameterKind::Sort => {
                DeclParam::Sort(unsafe { Sort::wrap(self.ctx, Z3_get_decl_sort_parameter(c, d, i)) })
            },
            ParameterKind::Symbol => DeclParam::Symbol(unsafe {
                let sym = Z3_get_decl_symbol_parameter(c, d, i);
                let kind = Z3_get_symbol_kind(c, sym);
                match kind {
                    SymbolKind::Int => Symbol::Int(Z3_get_symbol_int(c, sym) as u32),
                    SymbolKind::String => Symbol::String({
                        let p = Z3_get_symbol_string(c, sym);
                        assert!(!p.is_null());
                        String::from(CStr::from_ptr(p).to_str().unwrap())
                    })
                }
            }),
            ParameterKind::Rational => DeclParam::Rational(unsafe {
                let p = Z3_get_decl_rational_parameter(c, d, i);
                assert!(!p.is_null());
                String::from(CStr::from_ptr(p).to_str().unwrap())
            }),
            _ => {
                println!("{:?}", kind);
                todo!()
            }
        }
    }
    pub fn params(&self) -> Vec<DeclParam> {
        (0..self.num_params())
            .map(|idx| self.parameter(idx))
            .collect()
    }
    /// Create a constant (if `args` has length 0) or function application (otherwise).
    ///
    /// Note that `args` should have the types corresponding to the `domain` of the `FuncDecl`.
    pub fn apply(&self, args: &[&dyn ast::Ast<'ctx>]) -> ast::Dynamic<'ctx> {
        assert!(args.iter().all(|s| s.get_ctx().z3_ctx == self.ctx.z3_ctx));

        let args: Vec<_> = args.iter().map(|a| a.get_z3_ast()).collect();

        unsafe {
            ast::Dynamic::wrap(self.ctx, {
                Z3_mk_app(
                    self.ctx.z3_ctx,
                    self.z3_func_decl,
                    args.len().try_into().unwrap(),
                    args.as_ptr(),
                )
            })
        }
    }

    /// Return the `DeclKind` of this `FuncDecl`.
    pub fn kind(&self) -> DeclKind {
        unsafe { Z3_get_decl_kind(self.ctx.z3_ctx, self.z3_func_decl) }
    }

    /// Return the name of this `FuncDecl`.
    ///
    /// Strings will return the `Symbol`.  Ints will have a `"k!"` prepended to
    /// the `Symbol`.
    pub fn name(&self) -> String {
        unsafe {
            let z3_ctx = self.ctx.z3_ctx;
            let symbol = Z3_get_decl_name(z3_ctx, self.z3_func_decl);
            match Z3_get_symbol_kind(z3_ctx, symbol) {
                SymbolKind::String => CStr::from_ptr(Z3_get_symbol_string(z3_ctx, symbol))
                    .to_string_lossy()
                    .into_owned(),
                SymbolKind::Int => format!("k!{}", Z3_get_symbol_int(z3_ctx, symbol)),
            }
        }
    }
}
impl<'ctx> PartialEq for FuncDecl<'ctx> {
    fn eq(&self, other: &Self) -> bool {
        assert_eq!(self.ctx, other.ctx);
        self.as_dynamic().z3_ast == other.as_dynamic().z3_ast
    }
}
impl<'ctx> Eq for FuncDecl<'ctx> { }

impl<'ctx> Hash for FuncDecl<'ctx> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_dynamic().hash(state)
    }
}

impl<'ctx> fmt::Display for FuncDecl<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let p = unsafe { Z3_func_decl_to_string(self.ctx.z3_ctx, self.z3_func_decl) };
        if p.is_null() {
            return Result::Err(fmt::Error);
        }
        match unsafe { CStr::from_ptr(p) }.to_str() {
            Ok(s) => write!(f, "{}", s),
            Err(_) => Result::Err(fmt::Error),
        }
    }
}

impl<'ctx> fmt::Debug for FuncDecl<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        <Self as fmt::Display>::fmt(self, f)
    }
}

impl<'ctx> Clone for FuncDecl<'ctx> {
    fn clone(&self) -> Self {
        unsafe {
            FuncDecl::wrap(self.ctx, self.z3_func_decl)
        }
    }
}

impl<'ctx> Drop for FuncDecl<'ctx> {
    fn drop(&mut self) {
        unsafe {
            Z3_dec_ref(
                self.ctx.z3_ctx,
                Z3_func_decl_to_ast(self.ctx.z3_ctx, self.z3_func_decl),
            );
        }
    }
}
