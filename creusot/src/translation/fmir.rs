use super::{function::place, specification::lower_pure, traits};
use crate::{
    ctx::{item_name, CloneMap, TranslationCtx},
    specification::typing::{Literal, Term},
    translation::{
        binop_to_binop,
        function::{place::translate_rplace_inner, terminator::get_func_name},
        unop_to_unop,
    },
    util::item_qname,
};
use creusot_rustc::{
    hir::{def::DefKind, def_id::DefId},
    middle::ty::{subst::SubstsRef, AdtDef, GenericArg, ParamEnv, Ty, TypeFoldable},
    smir::mir::{BasicBlock, BinOp, Body, Place, UnOp},
    span::{Span, Symbol, DUMMY_SP},
    target::abi::VariantIdx,
};
use indexmap::IndexMap;
use why3::{exp::Pattern, mlcfg, mlcfg::BlockId};

pub enum Statement<'tcx> {
    Assignment(Place<'tcx>, Expr<'tcx>),
    Borrow(Place<'tcx>, Expr<'tcx>),
    Resolve(Place<'tcx>),
    Assertion(Term<'tcx>),
    Ghost(Place<'tcx>, Term<'tcx>),
    Invariant(Symbol, Term<'tcx>),
}

pub enum Expr<'tcx> {
    Place(Place<'tcx>),
    BinOp(BinOp, Box<Expr<'tcx>>, Box<Expr<'tcx>>),
    UnaryOp(UnOp, Box<Expr<'tcx>>),
    Constructor(DefId, SubstsRef<'tcx>, Vec<Expr<'tcx>>),
    Call(DefId, SubstsRef<'tcx>, Vec<Expr<'tcx>>),
    Constant(Literal),
    // Cast(Expr<'tcx>, Ty<'tcx>),
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
            Expr::Place(pl) => {
                translate_rplace_inner(ctx, names, body.unwrap(), pl.local, pl.projection)
            }
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
            } // Expr::Cast(_, _) => todo!(),
        }
    }
}

pub enum Terminator<'tcx> {
    Goto(BasicBlock),
    Switch(Expr<'tcx>, Branches<'tcx>),
    Return,
    Abort,
}

pub enum Branches<'tcx> {
    Int(Vec<(i128, BasicBlock)>, BasicBlock),
    Uint(Vec<(u128, BasicBlock)>, BasicBlock),
    Constructor(AdtDef<'tcx>, Vec<(VariantIdx, BasicBlock)>, BasicBlock),
    Bool(BasicBlock, BasicBlock),
}

impl<'tcx> Terminator<'tcx> {
    pub fn to_why(
        self,
        ctx: &mut TranslationCtx<'_, 'tcx>,
        names: &mut CloneMap<'tcx>,
        body: Option<&Body<'tcx>>,
    ) -> why3::mlcfg::Terminator {
        use why3::{exp::Exp, mlcfg::Terminator::*};
        match self {
            Terminator::Goto(bb) => Goto(BlockId(bb.into())),
            Terminator::Switch(switch, branches) => {
                let discr = switch.to_why(ctx, names, body);
                match branches {
                    Branches::Int(brs, def) => {
                        brs.into_iter().rfold(Goto(BlockId(def.into())), |acc, (val, bb)| {
                            Switch(
                                Exp::BinaryOp(
                                    why3::exp::BinOp::Eq,
                                    box discr.clone(),
                                    box Exp::Const(why3::exp::Constant::Int(val, None)),
                                ),
                                vec![
                                    (Pattern::mk_true(), Goto(BlockId(bb.into()))),
                                    (Pattern::mk_false(), acc),
                                ],
                            )
                        })
                    }
                    Branches::Uint(brs, def) => {
                        brs.into_iter().rfold(Goto(BlockId(def.into())), |acc, (val, bb)| {
                            Switch(
                                Exp::BinaryOp(
                                    why3::exp::BinOp::Eq,
                                    box discr.clone(),
                                    box Exp::Const(why3::exp::Constant::Uint(val, None)),
                                ),
                                vec![
                                    (Pattern::mk_true(), Goto(BlockId(bb.into()))),
                                    (Pattern::mk_false(), acc),
                                ],
                            )
                        })
                    }
                    Branches::Constructor(adt, vars, def) => {
                        use crate::util::constructor_qname;
                        let count = adt.variants().len();
                        let brs = vars
                            .into_iter()
                            .map(|(var, bb)| {
                                let variant = &adt.variant(var);
                                let wilds =
                                    variant.fields.iter().map(|_| Pattern::Wildcard).collect();
                                let cons_name = constructor_qname(ctx.tcx, variant);
                                (Pattern::ConsP(cons_name, wilds), Goto(BlockId(bb.into())))
                            })
                            .chain(std::iter::once((Pattern::Wildcard, Goto(BlockId(def.into())))))
                            .take(count);

                        Switch(discr, brs.collect())
                    }
                    Branches::Bool(f, t) => Switch(
                        discr,
                        vec![
                            (Pattern::mk_false(), Goto(BlockId(f.into()))),
                            (Pattern::mk_true(), Goto(BlockId(t.into()))),
                        ],
                    ),
                }
            }
            Terminator::Return => Return,
            Terminator::Abort => Absurd,
        }
    }
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
impl<'tcx> Statement<'tcx> {
    pub(crate) fn to_why(
        self,
        ctx: &mut TranslationCtx<'_, 'tcx>,
        names: &mut CloneMap<'tcx>,
        body: &Body<'tcx>,
        param_env: ParamEnv<'tcx>,
    ) -> Option<mlcfg::Statement> {
        match self {
            Statement::Assignment(_, _) => todo!(),
            Statement::Borrow(_, _) => todo!(),
            Statement::Resolve(pl) => {
                match resolve_predicate_of(ctx, names, param_env, pl.ty(body, ctx.tcx).ty) {
                    Some(rp) => Some(mlcfg::Statement::Assume(rp.app_to(Expr::Place(pl).to_why(
                        ctx,
                        names,
                        Some(body),
                    )))),
                    None => None,
                }
            }
            Statement::Assertion(a) => {
                Some(mlcfg::Statement::Assert(lower_pure(ctx, names, param_env, a)))
            }
            Statement::Ghost(lhs, rhs) => {
                let ghost = why3::exp::Exp::Ghost(box lower_pure(ctx, names, param_env, rhs));

                Some(place::create_assign_inner(ctx, names, body, &lhs, ghost))
            }
            Statement::Invariant(nm, inv) => Some(mlcfg::Statement::Invariant(
                nm.to_string().into(),
                lower_pure(ctx, names, param_env, inv),
            )),
        }
    }
}

fn resolve_predicate_of<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    param_env: ParamEnv<'tcx>,
    ty: Ty<'tcx>,
) -> Option<why3::exp::Exp> {
    if !super::function::resolve_trait_loaded(ctx.tcx) {
        ctx.warn(
            DUMMY_SP,
            "load the `creusot_contract` crate to enable resolution of mutable borrows.",
        );
        return None;
    }

    let trait_id = ctx.get_diagnostic_item(Symbol::intern("creusot_resolve")).unwrap();
    let trait_meth_id = ctx.get_diagnostic_item(Symbol::intern("creusot_resolve_method")).unwrap();
    let subst = ctx.mk_substs([GenericArg::from(ty)].iter());

    let resolve_impl = traits::resolve_opt(ctx.tcx, param_env, trait_meth_id, subst);

    match resolve_impl {
        Some(method) => {
            if !ty.still_further_specializable()
                && ctx.is_diagnostic_item(Symbol::intern("creusot_resolve_default"), method.0)
                && !method.1.type_at(0).is_closure()
            {
                return None;
            }
            ctx.translate(method.0);

            Some(why3::exp::Exp::impure_qvar(
                names.insert(method.0, method.1).qname(ctx.tcx, method.0),
            ))
        }
        None => {
            ctx.translate(trait_id);

            Some(why3::exp::Exp::impure_qvar(
                names.insert(trait_meth_id, subst).qname(ctx.tcx, trait_meth_id),
            ))
        }
    }
}
