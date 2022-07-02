use creusot_rustc::{
    borrowck::borrow_set::TwoPhaseActivation,
    middle::ty::{IntTy, TyKind, UintTy},
    smir::mir::{
        BinOp, BorrowKind::*, CastKind, Location, Operand::*, Place, Rvalue, SourceInfo, Statement,
        StatementKind,
    },
};

use why3::{exp::Exp, QName};

use super::BodyTranslator;
use crate::{
    translation::fmir::{self, Expr},
    util::{self, is_ghost_closure, item_name},
};

impl<'tcx> BodyTranslator<'_, '_, 'tcx> {
    pub fn translate_statement(&mut self, statement: &'_ Statement<'tcx>, loc: Location) {
        use StatementKind::*;
        match statement.kind {
            Assign(box (ref pl, ref rv)) => {
                self.translate_assign(statement.source_info, pl, rv, loc)
            }
            SetDiscriminant { .. } => {
                // TODO: implement support for set discriminant
                self.ctx
                    .crash_and_error(statement.source_info.span, "SetDiscriminant is not supported")
            }
            // Erase Storage markers and Nops
            StorageDead(_) | StorageLive(_) | Nop => {}
            // Not real instructions
            FakeRead(_) | AscribeUserType(_, _) | Retag(_, _) | Coverage(_) => {}
            CopyNonOverlapping(_) => self.ctx.crash_and_error(
                statement.source_info.span,
                "copy non overlapping is not supported",
            ),
            Deinit(_) => unreachable!("Deinit unsupported")
            // No assembly!
            // LlvmInlineAsm(_) => self
            //     .ctx
            //     .crash_and_error(statement.source_info.span, "inline assembly is not supported"),
        }
    }

    fn translate_assign(
        &mut self,
        si: SourceInfo,
        place: &'_ Place<'tcx>,
        rvalue: &'_ Rvalue<'tcx>,
        loc: Location,
    ) {
        let rval: Expr<'tcx> = match rvalue {
            Rvalue::Use(rval) => match rval {
                Move(pl) | Copy(pl) => {
                    // TODO: should this be done for *any* form of assignment?
                    // let ty = place.ty(self.body, self.tcx).ty;
                    self.emit_statementf(fmir::Statement::Resolve(*place));
                    // self.resolve_ty(ty).emit(*place, self);
                    Expr::Exp(self.translate_rplace(pl))
                }
                Constant(box c) => {
                    if let Some(c) = c.literal.const_for_ty() {
                        if is_ghost_closure(self.tcx, c.ty()).is_some() {
                            return;
                        }
                    };
                    crate::constant::from_mir_constant(self.param_env(), self.ctx, self.names, c)
                }
            },
            Rvalue::Ref(_, ss, pl) => match ss {
                Shared | Shallow | Unique => {
                    if self.erased_locals.contains(pl.local) {
                        return;
                    }

                    let dom = self.body.dominators();
                    let two_phase = self
                        .borrows
                        .local_map
                        .get(&pl.local)
                        .iter()
                        .flat_map(|is| is.iter())
                        .filter(|i| {
                            let res_loc = self.borrows[**i].reserve_location;
                            if res_loc.block == loc.block {
                                res_loc.statement_index <= loc.statement_index
                            } else {
                                dom.is_dominated_by(loc.block, res_loc.block)
                            }
                        })
                        .filter(|i| {
                            if let TwoPhaseActivation::ActivatedAt(act_loc) =
                                self.borrows[**i].activation_location
                            {
                                if act_loc.block == loc.block {
                                    loc.statement_index < act_loc.statement_index
                                } else {
                                    dom.is_dominated_by(act_loc.block, loc.block)
                                }
                            } else {
                                false
                            }
                        })
                        .nth(0);
                    if let Some(two_phase) = two_phase {
                        let place = self.borrows[*two_phase].assigned_place.clone();
                        Expr::Exp(Exp::Current(box self.translate_rplace(&place)))
                    } else {
                        Expr::Place(*pl)
                    }
                }
                Mut { .. } => {
                    if self.erased_locals.contains(pl.local) {
                        return;
                    }

                    self.emit_borrow(place, pl);
                    return;
                }
            },
            Rvalue::Discriminant(_) => return,
            Rvalue::BinaryOp(BinOp::BitAnd, box (l, r)) if !l.ty(self.body, self.tcx).is_bool() => {
                self.ctx.crash_and_error(si.span, "bitwise operations are currently unsupported")
            }
            //     self.translate_operand(l).to_why(self.ctx, self.names, Some(self.body)).and(self.translate_operand(r).to_why(self.ctx, self.names, Some(self.body)))
            // }
            // Rvalue::BinaryOp(BinOp::Eq, box (l, r)) if l.ty(self.body, self.tcx).is_bool() => {
            //     self.names.import_prelude_module(PreludeModule::Prelude);
            //     Call(
            //         box Exp::impure_qvar(QName::from_string("Prelude.eqb").unwrap()),
            //         vec![self.translate_operand(l).to_why(self.ctx, self.names, Some(self.body)), self.translate_operand(r).to_why(self.ctx, self.names, Some(self.body))],
            //     )
            // }
            Rvalue::BinaryOp(op, box (l, r)) | Rvalue::CheckedBinaryOp(op, box (l, r)) => {
                let exp =
                    Expr::BinOp(*op, box self.translate_operand(l), box self.translate_operand(r));
                Expr::Span(si.span, box exp)
            }
            Rvalue::UnaryOp(op, v) => Expr::UnaryOp(*op, box self.translate_operand(v)),
            Rvalue::Aggregate(box kind, ops) => {
                use creusot_rustc::smir::mir::AggregateKind::*;
                let fields = ops.iter().map(|op| self.translate_operand(op)).collect();

                match kind {
                    Tuple => Expr::Tuple(fields),
                    Adt(adt, varix, subst, _, _) => {
                        let adt = self.tcx.adt_def(*adt).variant(*varix).def_id;

                        Expr::Constructor(adt, subst, fields)
                    }
                    Closure(def_id, subst) => {
                        if util::is_invariant(self.tcx, *def_id) {
                            return;
                        } else if util::is_assertion(self.tcx, *def_id) {
                            let assertion = self
                                .assertions
                                .remove(def_id)
                                .expect("Could not find body of assertion");
                            self.emit_statementf(fmir::Statement::Assertion(assertion));
                            return;
                        } else if util::is_ghost(self.tcx, *def_id) {
                            return;
                        } else if util::is_spec(self.tcx, *def_id) {
                            return;
                        } else {
                            let mut cons_name = item_name(self.tcx, *def_id);
                            cons_name.capitalize();
                            Expr::Constructor(*def_id, subst, fields)
                        }
                    }
                    _ => self.ctx.crash_and_error(
                        si.span,
                        &format!("the rvalue {:?} is not currently supported", kind),
                    ),
                }
            }
            Rvalue::Len(pl) => {
                let int_conversion = uint_from_int(&UintTy::Usize);
                let len_call = Exp::impure_qvar(QName::from_string("Seq.length").unwrap())
                    .app_to(self.translate_rplace(pl));
                Expr::Exp(int_conversion.app_to(len_call))
            }
            Rvalue::Cast(CastKind::Misc, op, ty) => {
                let op_ty = op.ty(self.body, self.tcx);
                if !op_ty.is_integral() {
                    self.ctx
                        .crash_and_error(si.span, "Non integral casts are currently unsupported")
                } else {
                    let op_to_int = match op_ty.kind() {
                        TyKind::Int(ity) => int_to_int(ity),
                        TyKind::Uint(uty) => uint_to_int(uty),
                        _ => unreachable!(),
                    };
                    match ty.kind() {
                        TyKind::Int(ity) => Expr::Exp(int_from_int(ity).app_to(op_to_int.app_to(
                            self.translate_operand(op).to_why(
                                self.ctx,
                                self.names,
                                Some(self.body),
                            ),
                        ))),
                        TyKind::Uint(uty) => Expr::Exp(uint_from_int(uty).app_to(
                            op_to_int.app_to(self.translate_operand(op).to_why(
                                self.ctx,
                                self.names,
                                Some(self.body),
                            )),
                        )),
                        _ => unreachable!(),
                    }
                }
            }
            Rvalue::Cast(
                CastKind::Pointer(_)
                | CastKind::PointerExposeAddress
                | CastKind::PointerFromExposedAddress,
                _,
                _,
            ) => self.ctx.crash_and_error(si.span, "Pointer casts are currently unsupported"),
            Rvalue::ShallowInitBox(_, _)
            | Rvalue::NullaryOp(_, _)
            | Rvalue::Repeat(_, _)
            | Rvalue::ThreadLocalRef(_)
            | Rvalue::AddressOf(_, _) => self.ctx.crash_and_error(
                si.span,
                &format!("MIR code used an unsupported Rvalue {:?}", rvalue),
            ),
        };

        self.emit_assignment(place, rval);
    }
}

fn int_from_int(ity: &IntTy) -> Exp {
    match ity {
        IntTy::Isize => Exp::impure_qvar(QName::from_string("Int64.of_int").unwrap()),
        IntTy::I8 => unimplemented!(),
        IntTy::I16 => unimplemented!(),
        IntTy::I32 => Exp::impure_qvar(QName::from_string("Int32.of_int").unwrap()),
        IntTy::I64 => Exp::impure_qvar(QName::from_string("Int64.of_int").unwrap()),
        IntTy::I128 => unimplemented!(),
    }
}

pub fn uint_from_int(uty: &UintTy) -> Exp {
    match uty {
        UintTy::Usize => Exp::impure_qvar(QName::from_string("UInt64.of_int").unwrap()),
        UintTy::U8 => unimplemented!(),
        UintTy::U16 => unimplemented!(),
        UintTy::U32 => Exp::impure_qvar(QName::from_string("UInt32.of_int").unwrap()),
        UintTy::U64 => Exp::impure_qvar(QName::from_string("UInt64.of_int").unwrap()),
        UintTy::U128 => unimplemented!(),
    }
}

fn int_to_int(ity: &IntTy) -> Exp {
    match ity {
        IntTy::Isize => Exp::impure_qvar(QName::from_string("Int64.to_int").unwrap()),
        IntTy::I8 => unimplemented!(),
        IntTy::I16 => unimplemented!(),
        IntTy::I32 => Exp::impure_qvar(QName::from_string("Int32.to_int").unwrap()),
        IntTy::I64 => Exp::impure_qvar(QName::from_string("Int64.to_int").unwrap()),
        IntTy::I128 => unimplemented!(),
    }
}

pub fn uint_to_int(uty: &UintTy) -> Exp {
    match uty {
        UintTy::Usize => Exp::impure_qvar(QName::from_string("UInt64.to_int").unwrap()),
        UintTy::U8 => unimplemented!(),
        UintTy::U16 => unimplemented!(),
        UintTy::U32 => Exp::impure_qvar(QName::from_string("UInt32.to_int").unwrap()),
        UintTy::U64 => Exp::impure_qvar(QName::from_string("UInt64.to_int").unwrap()),
        UintTy::U128 => unimplemented!(),
    }
}
