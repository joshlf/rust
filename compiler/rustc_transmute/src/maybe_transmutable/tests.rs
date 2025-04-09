use itertools::Itertools;

use super::query_context::test::{Def, UltraMinimal};
use crate::{Answer, Assume, Reason, layout};

type Tree = layout::Tree<Def, !>;
type Dfa = layout::Dfa<!>;

trait Representation {
    fn is_transmutable(src: Self, dst: Self, assume: Assume) -> Answer<!>;
}

impl Representation for Tree {
    fn is_transmutable(src: Self, dst: Self, assume: Assume) -> Answer<!> {
        crate::maybe_transmutable::MaybeTransmutableQuery::new(src, dst, assume, UltraMinimal)
            .answer()
    }
}

impl Representation for Dfa {
    fn is_transmutable(src: Self, dst: Self, assume: Assume) -> Answer<!> {
        crate::maybe_transmutable::MaybeTransmutableQuery::new(src, dst, assume, UltraMinimal)
            .answer()
    }
}

fn is_transmutable<R: Representation + Clone>(
    src: &R,
    dst: &R,
    assume: Assume,
) -> crate::Answer<!> {
    let src = src.clone();
    let dst = dst.clone();
    // The only dimension of the transmutability analysis we want to test
    // here is the safety analysis. To ensure this, we disable all other
    // toggleable aspects of the transmutability analysis.
    R::is_transmutable(src, dst, assume)
}

mod safety {
    use super::*;
    use crate::Answer;

    const DST_HAS_SAFETY_INVARIANTS: Answer<!> =
        Answer::No(crate::Reason::DstMayHaveSafetyInvariants);

    #[test]
    fn src_safe_dst_safe() {
        let src = Tree::Def(Def::NoSafetyInvariants).then(Tree::u8());
        let dst = Tree::Def(Def::NoSafetyInvariants).then(Tree::u8());
        assert_eq!(is_transmutable(&src, &dst, Assume::default()), Answer::Yes);
        assert_eq!(
            is_transmutable(&src, &dst, Assume { safety: true, ..Assume::default() }),
            Answer::Yes
        );
    }

    #[test]
    fn src_safe_dst_unsafe() {
        let src = Tree::Def(Def::NoSafetyInvariants).then(Tree::u8());
        let dst = Tree::Def(Def::HasSafetyInvariants).then(Tree::u8());
        assert_eq!(is_transmutable(&src, &dst, Assume::default()), DST_HAS_SAFETY_INVARIANTS);
        assert_eq!(
            is_transmutable(&src, &dst, Assume { safety: true, ..Assume::default() }),
            Answer::Yes
        );
    }

    #[test]
    fn src_unsafe_dst_safe() {
        let src = Tree::Def(Def::HasSafetyInvariants).then(Tree::u8());
        let dst = Tree::Def(Def::NoSafetyInvariants).then(Tree::u8());
        assert_eq!(is_transmutable(&src, &dst, Assume::default()), Answer::Yes);
        assert_eq!(
            is_transmutable(&src, &dst, Assume { safety: true, ..Assume::default() }),
            Answer::Yes
        );
    }

    #[test]
    fn src_unsafe_dst_unsafe() {
        let src = Tree::Def(Def::HasSafetyInvariants).then(Tree::u8());
        let dst = Tree::Def(Def::HasSafetyInvariants).then(Tree::u8());
        assert_eq!(is_transmutable(&src, &dst, Assume::default()), DST_HAS_SAFETY_INVARIANTS);
        assert_eq!(
            is_transmutable(&src, &dst, Assume { safety: true, ..Assume::default() }),
            Answer::Yes
        );
    }
}

mod bool {
    use super::*;

    #[test]
    fn should_permit_identity_transmutation_tree() {
        let src = Tree::bool();
        assert_eq!(is_transmutable(&src, &src, Assume::default()), Answer::Yes);
        assert_eq!(
            is_transmutable(&src, &src, Assume { validity: true, ..Assume::default() }),
            Answer::Yes
        );
    }

    #[test]
    fn should_permit_identity_transmutation_dfa() {
        let src = Dfa::bool();
        assert_eq!(is_transmutable(&src, &src, Assume::default()), Answer::Yes);
        assert_eq!(
            is_transmutable(&src, &src, Assume { validity: true, ..Assume::default() }),
            Answer::Yes
        );
    }

    #[test]
    fn transmute_u8() {
        let bool = &Tree::bool();
        let u8 = &Tree::u8();
        for (src, dst, assume_validity, answer) in [
            (bool, u8, false, Answer::Yes),
            (bool, u8, true, Answer::Yes),
            (u8, bool, false, Answer::No(Reason::DstIsBitIncompatible)),
            (u8, bool, true, Answer::Yes),
        ] {
            assert_eq!(
                is_transmutable(
                    src,
                    dst,
                    Assume { validity: assume_validity, ..Assume::default() }
                ),
                answer
            );
        }
    }

    #[test]
    fn should_permit_validity_expansion_and_reject_contraction() {
        let b0 = layout::Tree::<Def, !>::from_bits(0);
        let b1 = layout::Tree::<Def, !>::from_bits(1);
        let b2 = layout::Tree::<Def, !>::from_bits(2);

        let alts = [b0, b1, b2];

        let into_layout = |alts: Vec<_>| {
            alts.into_iter().fold(layout::Tree::<Def, !>::uninhabited(), layout::Tree::<Def, !>::or)
        };

        let into_set = |alts: Vec<_>| {
            #[cfg(feature = "rustc")]
            let mut set = crate::Set::default();
            #[cfg(not(feature = "rustc"))]
            let mut set = std::collections::HashSet::new();
            set.extend(alts);
            set
        };

        for src_alts in alts.clone().into_iter().powerset() {
            let src_layout = into_layout(src_alts.clone());
            let src_set = into_set(src_alts.clone());

            for dst_alts in alts.clone().into_iter().powerset().filter(|alts| !alts.is_empty()) {
                let dst_layout = into_layout(dst_alts.clone());
                let dst_set = into_set(dst_alts.clone());

                if src_set.is_subset(&dst_set) {
                    assert_eq!(
                        Answer::Yes,
                        is_transmutable(&src_layout, &dst_layout, Assume::default()),
                        "{:?} SHOULD be transmutable into {:?}",
                        src_layout,
                        dst_layout
                    );
                } else if !src_set.is_disjoint(&dst_set) {
                    assert_eq!(
                        Answer::Yes,
                        is_transmutable(
                            &src_layout,
                            &dst_layout,
                            Assume { validity: true, ..Assume::default() }
                        ),
                        "{:?} SHOULD be transmutable (assuming validity) into {:?}",
                        src_layout,
                        dst_layout
                    );
                } else {
                    assert_eq!(
                        Answer::No(Reason::DstIsBitIncompatible),
                        is_transmutable(&src_layout, &dst_layout, Assume::default()),
                        "{:?} should NOT be transmutable into {:?}",
                        src_layout,
                        dst_layout
                    );
                }
            }
        }
    }
}

mod alt {
    use super::*;
    use crate::Answer;

    #[test]
    fn should_permit_identity_transmutation() {
        type Tree = layout::Tree<Def, !>;

        let x = Tree::Seq(vec![Tree::from_bits(0), Tree::from_bits(0)]);
        let y = Tree::Seq(vec![Tree::bool(), Tree::from_bits(1)]);
        let layout = Tree::Alt(vec![x, y]);

        for v in [false, true] {
            let answer =
                is_transmutable(&layout, &layout, Assume { validity: v, ..Assume::default() });
            assert_eq!(answer, Answer::Yes, "assume validity:{v}");
        }
    }
}

mod char {
    use super::*;
    use crate::{
        Answer, Reason,
        layout::{automaton::State, dfa, tree::Endian},
    };

    #[test]
    fn should_permit_identity_transmutation() {
        for order in [Endian::Little, Endian::Big] {
            let char = layout::Tree::<Def, !>::char(order);
            for v in [false, true] {
                let answer =
                    is_transmutable(&char, &char, Assume { validity: v, ..Assume::default() });
                assert_eq!(answer, Answer::Yes, "endian:{order:?}, assume validity:{v}");
            }
        }
    }

    #[test]
    fn should_permit_valid_transmutation() {
        for order in [Endian::Little] {
            use Answer::*;
            let char_layout = layout::Tree::<Def, !>::char(order);
            let char_layout = char_layout.prune(&|_def| false);
            let char_layout = layout::Nfa::from_tree(char_layout).unwrap();
            let char_layout_nfa_graphviz = char_layout.0.serialize_to_graphviz_dot();
            let char_layout = layout::Dfa::from_nfa(State::new, char_layout);

            // `char`s can be in the following ranges:
            // - [0, 0xD7FF]
            // - [0xE000, 10FFFF]
            //
            // This loop synthesizes a singleton-validity type for the extremes
            // of each range, and for one past the end of the extremes of each
            // range.
            let no = No(Reason::DstIsBitIncompatible);
            for (src, answer) in [
                (0u32, Yes),
                (0xD7FF, Yes),
                (0xD800, no.clone()),
                (0xDFFF, no.clone()),
                (0xE000, Yes),
                (0x10FFFF, Yes),
                (0x110000, no.clone()),
                (0xFFFF0000, no.clone()),
                (0xFFFFFFFF, no),
            ] {
                let src = layout::tree::Tree::<Def, !>::from_big_endian(
                    order,
                    src.to_be_bytes().map(|b| b..=b),
                );
                let src = src.prune(&|_def| false);
                let src = layout::Nfa::from_tree(src).unwrap();
                let src = layout::Dfa::from_nfa(State::new, src);
                let a = crate::maybe_transmutable::MaybeTransmutableQuery::new(
                    src.clone(),
                    char_layout.clone(),
                    crate::Assume::default(),
                    UltraMinimal,
                )
                .answer();
                assert_eq!(
                    a,
                    answer,
                    "endian:{order:?},\nsrc:{},\ndst_nfa:{}\ndst:{}",
                    src.0.serialize_to_graphviz_dot(),
                    char_layout_nfa_graphviz,
                    char_layout.0.serialize_to_graphviz_dot()
                );
            }
        }
    }
}

mod nonzero {
    use std::num::NonZeroUsize;

    use super::*;
    use crate::{Answer, Reason};

    const NONZERO_BYTE_WIDTHS: [NonZeroUsize; 5] = [
        NonZeroUsize::new(1).unwrap(),
        NonZeroUsize::new(2).unwrap(),
        NonZeroUsize::new(4).unwrap(),
        NonZeroUsize::new(8).unwrap(),
        NonZeroUsize::new(16).unwrap(),
    ];

    #[test]
    fn should_permit_identity_transmutation() {
        for width in NONZERO_BYTE_WIDTHS {
            if width.get() != 4 {
                continue;
            }

            let layout = layout::Tree::<Def, !>::nonzero(width);
            let answer = crate::maybe_transmutable::MaybeTransmutableQuery::new(
                layout.clone(),
                layout,
                crate::Assume::default(),
                UltraMinimal,
            )
            .answer();
            assert_eq!(answer, Answer::Yes);
        }
    }

    #[test]
    fn should_permit_valid_transmutation() {
        for width in NONZERO_BYTE_WIDTHS {
            use Answer::*;

            let num = layout::Tree::<Def, !>::number(width);
            let nz = layout::Tree::<Def, !>::nonzero(width);

            for (src, dst, answer) in
                [(num.clone(), nz.clone(), No(Reason::DstIsBitIncompatible)), (nz, num, Yes)]
            {
                let a = crate::maybe_transmutable::MaybeTransmutableQuery::new(
                    src.clone(),
                    dst.clone(),
                    crate::Assume::default(),
                    UltraMinimal,
                )
                .answer();
                assert_eq!(a, answer, "width:{width},\nsrc:{src:?},\ndst:{dst:?}");
            }
        }
    }
}

mod size {
    use std::num::NonZeroUsize;

    use super::*;

    #[test]
    fn should_reject_size_extension() {
        const SIZES: [usize; 5] = [1, 2, 4, 8, 16];
        for src_size in SIZES {
            for dst_size in SIZES {
                let src = Tree::number(src_size.try_into().unwrap());
                let dst = Tree::number(dst_size.try_into().unwrap());
                let answer = is_transmutable(&src, &dst, Assume::default());
                assert_eq!(
                    answer,
                    if src_size < dst_size { Answer::No(Reason::DstIsTooBig) } else { Answer::Yes }
                );
            }
        }
    }
}
