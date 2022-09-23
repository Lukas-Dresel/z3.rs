use std::collections::HashSet;

use crate::AstKind;
use crate::ast::{Ast, Dynamic};

#[allow(non_snake_case)]
pub trait AstVisitor<'ctx> {
    fn visit_Numeral(&mut self, ast: &Dynamic<'ctx>) {}
    fn visit_App(&mut self, ast: &Dynamic<'ctx>) {}
    fn visit_FuncDecl(&mut self, ast: &Dynamic<'ctx>) {}
    fn visit_Quantifier(&mut self, ast: &Dynamic<'ctx>) {}
    fn visit_Sort(&mut self, ast: &Dynamic<'ctx>) {}
    fn visit_Unknown(&mut self, ast: &Dynamic<'ctx>) {}
    fn visit_Var(&mut self, ast: &Dynamic<'ctx>) {}
}

pub trait AstTraversal<'ctx, V: AstVisitor<'ctx>> {
    fn accept_depth_first(&self, visitor: &mut V, postorder: bool, visited: HashSet<u32>) -> HashSet<u32>;
}



impl<'ctx, V: 'ctx + AstVisitor<'ctx>> AstTraversal<'ctx, V> for Dynamic<'ctx> {
    fn accept_depth_first(&self, visitor: &mut V, postorder: bool, visited: HashSet<u32>) -> HashSet<u32> {
        let ast_id = self.get_ast_id();
        if visited.contains(&ast_id) {
            return visited;
        }

        let mut visited = visited;
        visited.insert(ast_id);

        if postorder {
            for c in self.children() {
                visited = c.accept_depth_first(visitor, postorder, visited);
            }
        }
        match self.kind() {
            AstKind::App => visitor.visit_App(self),
            AstKind::FuncDecl => visitor.visit_FuncDecl(self),
            AstKind::Numeral => visitor.visit_Numeral(self),
            AstKind::Quantifier => visitor.visit_Quantifier(self),
            AstKind::Sort => visitor.visit_Sort(self),
            AstKind::Unknown => visitor.visit_Unknown(self),
            AstKind::Var => visitor.visit_Var(self),
        }
        if !postorder {
            for c in self.children() {
                visited = c.accept_depth_first(visitor, postorder, visited);
            }
        }
        visited
    }
}

impl<'ctx, V: 'ctx + AstVisitor<'ctx>> AstTraversal<'ctx, V> for dyn Ast<'ctx> {
    fn accept_depth_first(&self, visitor: &mut V, postorder: bool, visited: HashSet<u32>) -> HashSet<u32> {
        unsafe {
            Dynamic::wrap(self.get_ctx(), self.get_z3_ast())
        }.accept_depth_first(visitor, postorder, visited)
    }
}