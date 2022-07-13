pub use crate::clone_map::*;
use crate::{metadata::Metadata, util};
use creusot_rustc::hir::def_id::DefId;
use indexmap::IndexMap;
pub use util::{item_name, module_name, ItemType};
use why3::declaration::{Decl, Module, TyDecl};

pub enum TranslatedItem<'tcx> {
    Logic {
        interface: Module,
        modl: Module,
        proof_modl: Option<Module>,
        dependencies: CloneSummary<'tcx>,
        has_axioms: bool,
    },
    Program {
        interface: Module,
        modl: Module,
        dependencies: CloneSummary<'tcx>,
        has_axioms: bool,
    },
    Trait {
        laws: Vec<DefId>,
        dependencies: CloneSummary<'tcx>, // always empty
    },
    Impl {
        laws: Vec<DefId>, // Instantiations of trait laws
        modl: Module,     // Refinement of traits,
        dependencies: CloneSummary<'tcx>,
    },
    AssocTy {
        modl: Module,
        dependencies: CloneSummary<'tcx>,
    },
    Extern {
        interface: Module,
        body: Module,
        // TODO: Get rid of this result.
        dependencies: Result<CloneSummary<'tcx>, DefId>,
    },
    Constant {
        modl: Module,
        dependencies: CloneSummary<'tcx>,
    },
}

pub struct TypeDeclaration {
    pub ty_decl: TyDecl,
    pub accessors: IndexMap<DefId, IndexMap<DefId, Decl>>,
}

impl TypeDeclaration {
    pub fn accessors(&self) -> impl Iterator<Item = &Decl> {
        self.accessors.values().flat_map(|v| v.values())
    }
}

impl<'a, 'tcx> TranslatedItem<'tcx> {
    pub fn dependencies(&'a self, metadata: &'a Metadata<'tcx>) -> &'a CloneSummary<'tcx> {
        use TranslatedItem::*;
        match self {
            Extern { dependencies, .. } => match dependencies {
                Ok(deps) => deps,
                Err(id) => metadata.dependencies(*id).unwrap(),
            },
            _ => self.local_dependencies(),
        }
    }

    // Get the dependencies of a locally defined function
    // Panics if `self` is not local
    pub fn local_dependencies(&self) -> &CloneSummary<'tcx> {
        use TranslatedItem::*;

        match self {
            Logic { dependencies, .. } => dependencies,
            Program { dependencies, .. } => dependencies,
            Trait { dependencies, .. } => dependencies,
            Impl { dependencies, .. } => dependencies,
            AssocTy { dependencies, .. } => dependencies,
            Constant { dependencies, .. } => dependencies,
            Extern { .. } => unreachable!("local_dependencies: called on a non-local item"),
        }
    }

    pub fn has_axioms(&self) -> bool {
        match self {
            TranslatedItem::Logic { has_axioms, .. } => *has_axioms,
            TranslatedItem::Program { has_axioms, .. } => *has_axioms,
            _ => false,
        }
    }

    pub fn laws(&self) -> Option<&[DefId]> {
        match self {
            TranslatedItem::Trait { laws, .. } => Some(&laws[..]),
            TranslatedItem::Impl { laws, .. } => Some(&laws[..]),
            _ => None,
        }
    }

    pub fn modules(&'a self) -> Box<dyn Iterator<Item = &Module> + 'a> {
        use std::iter;
        use TranslatedItem::*;
        match self {
            Logic { interface, modl, proof_modl, .. } => {
                box iter::once(interface).chain(iter::once(modl)).chain(proof_modl.iter())
            }
            Program { interface, modl, .. } => box iter::once(interface).chain(iter::once(modl)),
            Trait { .. } => box iter::empty(),
            Impl { modl, .. } => box iter::once(modl),
            AssocTy { modl, .. } => box iter::once(modl),
            Constant { modl, .. } => box iter::once(modl),
            Extern { interface, body, .. } => box iter::once(interface).chain(iter::once(body)),
        }
    }

    pub fn interface(&'a self) -> Box<dyn Iterator<Item = &Module> + 'a> {
        match &self {
            TranslatedItem::Logic { interface, modl, .. } => {
                box std::iter::once(interface).chain(std::iter::once(modl))
            }
            TranslatedItem::Program { interface, .. } => box std::iter::once(interface),
            TranslatedItem::Trait { .. } => box std::iter::empty(),
            TranslatedItem::Impl { modl, .. } => box std::iter::once(modl),
            TranslatedItem::AssocTy { modl, .. } => box std::iter::once(modl),
            TranslatedItem::Extern { interface, .. } => box std::iter::once(interface),
            TranslatedItem::Constant { modl, .. } => box std::iter::once(modl),
        }
    }
}
