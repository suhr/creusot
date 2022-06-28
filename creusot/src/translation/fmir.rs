use super::specification::typing::{Literal, Term};
use crate::{
    ctx::{item_name, CloneMap, TranslationCtx},
    translation::{
        binop_to_binop,
        function::{place::translate_rplace_inner, terminator::get_func_name},
        unop_to_unop,
    },
    util::item_qname,
};
use creusot_rustc::{
    hir::{def::DefKind, def_id::DefId},
    middle::ty::{subst::SubstsRef, AdtDef},
    smir::mir::{BasicBlock, BinOp, Body, Place, UnOp},
    span::{Span, Symbol, DUMMY_SP},
    target::abi::VariantIdx,
};
use indexmap::IndexMap;
use std::collections::HashMap;

pub enum Statement<'tcx> {
    Assignment(Place<'tcx>, Expr<'tcx>),
    Borrow(Place<'tcx>, Expr<'tcx>),
    Resolve(Place<'tcx>),
    Assertion(Term<'tcx>),
    Ghost(Term<'tcx>),
    Invariant(Symbol, Term<'tcx>),
}

pub enum Expr<'tcx> {
    Place(Place<'tcx>),
    BinOp(BinOp, Box<Expr<'tcx>>, Box<Expr<'tcx>>),
    UnaryOp(UnOp, Box<Expr<'tcx>>),
    Constructor(DefId, SubstsRef<'tcx>, Vec<Expr<'tcx>>),
    Call(DefId, SubstsRef<'tcx>, Vec<Expr<'tcx>>),
    Constant(Literal),
    Tuple(Vec<Expr<'tcx>>),
    Span(Span, Box<Expr<'tcx>>),
    // Migration escape hatch
    Exp(why3::exp::Exp),
}

impl<'tcx> Expr<'tcx> {
    pub fn to_why(
        self,
        ctx: &mut TranslationCtx<'_, 'tcx>,
        names: &mut CloneMap<'tcx>,
        body: Option<&Body<'tcx>>,
    ) -> why3::exp::Exp {
        use why3::exp::Exp;
        match self {
            Expr::Place(pl) => translate_rplace_inner(
                ctx,
                names,
                body.unwrap(),
                &HashMap::new(),
                pl.local,
                pl.projection,
            ),
            Expr::BinOp(BinOp::BitAnd, l, r) => Exp::BinaryOp(
                why3::exp::BinOp::LazyAnd,
                box l.to_why(ctx, names, body),
                box r.to_why(ctx, names, body),
            ),
            Expr::BinOp(op, l, r) => Exp::BinaryOp(
                binop_to_binop(op),
                box l.to_why(ctx, names, body),
                box r.to_why(ctx, names, body),
            ),
            Expr::UnaryOp(op, arg) => {
                Exp::UnaryOp(unop_to_unop(op), box arg.to_why(ctx, names, body))
            }
            Expr::Constructor(id, subst, args) => {
                let args = args.into_iter().map(|a| a.to_why(ctx, names, body)).collect();

                match ctx.def_kind(id) {
                    DefKind::Closure => {
                        let mut cons_name = item_name(ctx.tcx, id);
                        cons_name.capitalize();
                        let ctor = names.insert(id, subst).qname_ident(cons_name);
                        Exp::Constructor { ctor, args }
                    }
                    _ => {
                        let ctor = item_qname(ctx.tcx, id);
                        Exp::Constructor { ctor, args }
                    }
                }
            }
            Expr::Call(id, subst, args) => {
                let args: Vec<_> = args.into_iter().map(|a| a.to_why(ctx, names, body)).collect();
                let fname = get_func_name(ctx, names, id, subst, DUMMY_SP);
                Exp::Call(box Exp::impure_qvar(fname), args)
            }
            Expr::Constant(_) => todo!(),
            Expr::Tuple(f) => {
                Exp::Tuple(f.into_iter().map(|f| f.to_why(ctx, names, body)).collect())
            }
            Expr::Exp(e) => e,
            Expr::Span(sp, e) => {
                let e = e.to_why(ctx, names, body);
                ctx.attach_span(sp, e)
            }
        }
    }
}

pub enum Terminator<'tcx> {
    Goto(BasicBlock),
    Switch(Place<'tcx>, Vec<(Pattern<'tcx>, BasicBlock)>),
}

pub enum Pattern<'tcx> {
    Constructor { adt: AdtDef<'tcx>, variant: VariantIdx, fields: Vec<Pattern<'tcx>> },
    Tuple(Vec<Pattern<'tcx>>),
    Wildcard,
    Binder(Symbol),
    Boolean(bool),
}

pub struct Block<'tcx> {
    stmts: Vec<Statement<'tcx>>,
    terminator: Option<Terminator<'tcx>>,
}

impl<'tcx> Block<'tcx> {
    pub fn to_why(self) -> why3::mlcfg::Block {
        todo!()
    }
}

pub struct Builder<'tcx> {
    blocks: IndexMap<BasicBlock, Block<'tcx>>,
    current: Block<'tcx>,
    block_id: BasicBlock,
}

impl<'tcx> Builder<'tcx> {
    pub fn new() -> Self {
        Builder {
            blocks: Default::default(),
            block_id: BasicBlock::MAX,
            current: Block { stmts: Vec::new(), terminator: None },
        }
    }
}
