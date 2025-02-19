#![feature(rustc_private, register_tool)]
#![feature(box_syntax, box_patterns, control_flow_enum, drain_filter)]
#![feature(let_else, let_chains, never_type, try_blocks)]

#[macro_use]
extern crate log;
extern crate rustc_middle;
extern crate rustc_serialize;
extern crate rustc_smir;
extern crate rustc_type_ir;

mod analysis;
pub mod arg_value;
pub mod callbacks;
mod cleanup_spec_closures;
pub mod clone_map;
pub(crate) mod creusot_items;
pub mod ctx;

mod extended_location;
mod gather_spec_closures;
pub mod options;
mod resolve;
// #[allow(dead_code)]
mod rustc_extensions;
mod translation;
pub mod util;
use translation::*;
mod error;
pub mod metadata;
mod translated_item;
mod validate;
