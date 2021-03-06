// Copyright 2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use deriving::{path_local, path_std};
use deriving::generic::*;
use deriving::generic::ty::*;

use syntax::ast::{BinOpKind, Expr, MetaItem};
use syntax::ext::base::{Annotatable, ExtCtxt};
use syntax::ext::build::AstBuilder;
use syntax::ptr::P;
use syntax::symbol::Symbol;
use syntax_pos::Span;

pub fn expand_deriving_partial_eq(cx: &mut ExtCtxt,
                                  span: Span,
                                  mitem: &MetaItem,
                                  item: &Annotatable,
                                  push: &mut dyn FnMut(Annotatable)) {
    // structures are equal if all fields are equal, and non equal, if
    // any fields are not equal or if the enum variants are different
    fn cs_op(cx: &mut ExtCtxt,
             span: Span,
             substr: &Substructure,
             op: BinOpKind,
             combiner: BinOpKind,
             base: bool)
             -> P<Expr>
    {
        let op = |cx: &mut ExtCtxt, span: Span, self_f: P<Expr>, other_fs: &[P<Expr>]| {
            let other_f = match (other_fs.len(), other_fs.get(0)) {
                (1, Some(o_f)) => o_f,
                _ => cx.span_bug(span, "not exactly 2 arguments in `derive(PartialEq)`"),
            };

            cx.expr_binary(span, op, self_f, other_f.clone())
        };

        cs_fold1(true, // use foldl
            |cx, span, subexpr, self_f, other_fs| {
                let eq = op(cx, span, self_f, other_fs);
                cx.expr_binary(span, combiner, subexpr, eq)
            },
            |cx, args| {
                match args {
                    Some((span, self_f, other_fs)) => {
                        // Special-case the base case to generate cleaner code.
                        op(cx, span, self_f, other_fs)
                    }
                    None => cx.expr_bool(span, base),
                }
            },
            Box::new(|cx, span, _, _| cx.expr_bool(span, !base)),
            cx,
            span,
            substr)
    }

    fn cs_eq(cx: &mut ExtCtxt, span: Span, substr: &Substructure) -> P<Expr> {
        cs_op(cx, span, substr, BinOpKind::Eq, BinOpKind::And, true)
    }
    fn cs_ne(cx: &mut ExtCtxt, span: Span, substr: &Substructure) -> P<Expr> {
        cs_op(cx, span, substr, BinOpKind::Ne, BinOpKind::Or, false)
    }

    macro_rules! md {
        ($name:expr, $f:ident) => { {
            let inline = cx.meta_word(span, Symbol::intern("inline"));
            let attrs = vec![cx.attribute(span, inline)];
            MethodDef {
                name: $name,
                generics: LifetimeBounds::empty(),
                explicit_self: borrowed_explicit_self(),
                args: vec![(borrowed_self(), "other")],
                ret_ty: Literal(path_local!(bool)),
                attributes: attrs,
                is_unsafe: false,
                unify_fieldless_variants: true,
                combine_substructure: combine_substructure(Box::new(|a, b, c| {
                    $f(a, b, c)
                }))
            }
        } }
    }

    // avoid defining `ne` if we can
    // c-like enums, enums without any fields and structs without fields
    // can safely define only `eq`.
    let mut methods = vec![md!("eq", cs_eq)];
    if !is_type_without_fields(item) {
        methods.push(md!("ne", cs_ne));
    }

    let trait_def = TraitDef {
        span,
        attributes: Vec::new(),
        path: path_std!(cx, cmp::PartialEq),
        additional_bounds: Vec::new(),
        generics: LifetimeBounds::empty(),
        is_unsafe: false,
        supports_unions: false,
        methods,
        associated_types: Vec::new(),
    };
    trait_def.expand(cx, mitem, item, push)
}
