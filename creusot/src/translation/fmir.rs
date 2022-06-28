use super::specification::typing::Term;
use creusot_rustc::{
    hir::def_id::DefId,
    middle::ty::{subst::SubstsRef, AdtDef},
    smir::mir::{BasicBlock, BinOp, Place},
    span::Symbol,
    target::abi::VariantIdx,
};
use indexmap::IndexMap;

pub enum Statement<'tcx> {
    Assignment(Place<'tcx>, Expr<'tcx>),
    Resolve(Place<'tcx>),
    Assertion(Term<'tcx>),
    Ghost(Term<'tcx>),
    Invariant(Symbol, Term<'tcx>),
}

pub enum Expr<'tcx> {
    Place(Place<'tcx>),
    BinOp(BinOp, Box<Expr<'tcx>>, Box<Expr<'tcx>>),
    Constructor(DefId, SubstsRef<'tcx>, Vec<Expr<'tcx>>),
    BorrowMut(Place<'tcx>),
    Call(DefId, SubstsRef<'tcx>, Vec<Expr<'tcx>>),
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
