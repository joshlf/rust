use std::fmt::{self, Debug};
use std::hash::Hash;
use std::sync::atomic::{AtomicU32, Ordering};

pub(crate) mod tree;
pub(crate) use tree::Tree;

pub(crate) mod nfa;
pub(crate) use nfa::Nfa;

pub(crate) mod dfa;
pub(crate) use dfa::Dfa;

#[derive(Debug)]
pub(crate) struct Uninhabited;

#[derive(Hash, Eq, PartialEq, Clone, Copy)]
pub(crate) struct U256(
    // Stored in little-endian order
    [u128; 2],
);

impl U256 {
    fn trailing_zeros(&self) -> u32 {
        let t = self.0[0].trailing_zeros();
        if t == 128 { t + self.0[1].trailing_zeros() } else { t }
    }

    fn trailing_ones(&self) -> u32 {
        let t = self.0[0].trailing_ones();
        if t == 128 { t + self.0[1].trailing_ones() } else { t }
    }

    fn unbounded_shr(&self, rhs: u32) -> U256 {
        if rhs < 128 {
            let lower = self.0[0].unbounded_shr(rhs);
            let mid = self.0[1].unbounded_shl(128 - rhs);
            let upper = self.0[1].unbounded_shr(rhs);
            U256([lower | mid, upper])
        } else {
            let lower = self.0[1].unbounded_shr(rhs - 128);
            U256([lower, 0])
        }
    }

    pub(crate) fn and(&self, other: &U256) -> U256 {
        U256([self.0[0] & other.0[0], self.0[1] & other.0[1]])
    }

    pub(crate) fn or(&self, other: &U256) -> U256 {
        U256([self.0[0] | other.0[0], self.0[1] | other.0[1]])
    }

    fn not(&self) -> U256 {
        U256([!self.0[0], !self.0[1]])
    }
}

#[derive(Hash, Eq, PartialEq, Clone, Copy)]
pub(crate) struct Byte {
    // `None` means uninit
    values: Option<U256>,
}

impl Byte {
    fn from_iters<const N: usize, I: Iterator<Item = u8>>(vals: [I; N]) -> Byte {
        let mut values = [0u128, 0];
        for b in vals.into_iter().flatten() {
            values[usize::from(b / 128)] |= 1u128 << (b % 128);
        }

        Byte { values: Some(U256(values)) }
    }

    pub(crate) fn uninit() -> Byte {
        Byte { values: None }
    }

    pub(crate) fn from_mask(mask: U256) -> Byte {
        Byte { values: Some(mask) }
    }

    pub(crate) fn mask(&self) -> Option<U256> {
        self.values
    }

    /// Are any of the values in `self` transmutable into `other`?
    pub(crate) fn transmutable_into(&self, other: &Byte) -> bool {
        match (self.values, other.values) {
            (None, None) => true,
            (None, Some(_)) => false,
            (Some(_), None) => true,
            (Some(s), Some(o)) => [s.0[0] & o.0[0], s.0[1] & o.0[1]] != [0, 0],
        }
    }

    pub(crate) fn into_disjoint(&self, other: &Byte) -> (Option<Byte>, Option<Byte>, Option<Byte>) {
        match (self.values, other.values) {
            (None, None) => (None, Some(*self), None),
            (None, Some(_)) | (Some(_), None) => (Some(*self), None, Some(*other)),
            (Some(s), Some(o)) => {
                let intersection = s.and(&o);
                let mask = intersection.not();
                let s = s.and(&mask);
                let o = o.and(&mask);

                let b = |values: U256| {
                    if values.0 == [0, 0] { None } else { Some(Byte { values: Some(values) }) }
                };

                (b(s), b(intersection), b(o))
            }
        }
    }
}

impl fmt::Debug for Byte {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut range_start = 0;

        match self.values {
            None => write!(f, "{{ uninit }}"),
            Some(mut v) => {
                write!(f, "{{")?;
                while v.0 != [0, 0] {
                    let run_len = v.trailing_zeros();
                    range_start += run_len;
                    v = v.unbounded_shr(run_len);

                    // NOTE: The loop condition ensures that we only execute if
                    // there's some (non-zero-sized) range of 1 bits. Thus,
                    // `run_len > 0`.
                    let run_len = v.trailing_ones();
                    let range_end = range_start + run_len;
                    if run_len == 1 {
                        write!(f, " {:?}", range_start)
                    } else {
                        write!(f, " {:?}", range_start..=(range_end - 1))
                    }?;

                    v = v.unbounded_shr(run_len);
                }
                write!(f, " }}")
            }
        }
    }
}

pub(crate) trait Def: Debug + Hash + Eq + PartialEq + Copy + Clone {
    fn has_safety_invariants(&self) -> bool;
}
pub trait Ref: Debug + Hash + Eq + PartialEq + Copy + Clone {
    fn min_align(&self) -> usize;

    fn size(&self) -> usize;

    fn is_mutable(&self) -> bool;
}

impl Def for ! {
    fn has_safety_invariants(&self) -> bool {
        unreachable!()
    }
}

impl Ref for ! {
    fn min_align(&self) -> usize {
        unreachable!()
    }
    fn size(&self) -> usize {
        unreachable!()
    }
    fn is_mutable(&self) -> bool {
        unreachable!()
    }
}

#[derive(Hash, Eq, PartialEq, PartialOrd, Ord, Copy, Clone)]
struct GlobalCounter(u32);

impl GlobalCounter {
    fn new() -> Self {
        static COUNTER: AtomicU32 = AtomicU32::new(0);
        Self(COUNTER.fetch_add(1, Ordering::SeqCst))
    }
}

#[cfg(feature = "rustc")]
pub mod rustc {
    use std::fmt::{self, Write};

    use rustc_abi::Layout;
    use rustc_middle::mir::Mutability;
    use rustc_middle::ty::layout::{HasTyCtxt, LayoutCx, LayoutError};
    use rustc_middle::ty::{self, Ty};

    /// A reference in the layout.
    #[derive(Debug, Hash, Eq, PartialEq, Clone, Copy)]
    pub struct Ref<'tcx> {
        pub lifetime: ty::Region<'tcx>,
        pub ty: Ty<'tcx>,
        pub mutability: Mutability,
        pub align: usize,
        pub size: usize,
    }

    impl<'tcx> super::Ref for Ref<'tcx> {
        fn min_align(&self) -> usize {
            self.align
        }

        fn size(&self) -> usize {
            self.size
        }

        fn is_mutable(&self) -> bool {
            match self.mutability {
                Mutability::Mut => true,
                Mutability::Not => false,
            }
        }
    }
    impl<'tcx> Ref<'tcx> {}

    impl<'tcx> fmt::Display for Ref<'tcx> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_char('&')?;
            if self.mutability == Mutability::Mut {
                f.write_str("mut ")?;
            }
            self.ty.fmt(f)
        }
    }

    /// A visibility node in the layout.
    #[derive(Debug, Hash, Eq, PartialEq, Clone, Copy)]
    pub enum Def<'tcx> {
        Adt(ty::AdtDef<'tcx>),
        Variant(&'tcx ty::VariantDef),
        Field(&'tcx ty::FieldDef),
        Primitive,
    }

    impl<'tcx> super::Def for Def<'tcx> {
        fn has_safety_invariants(&self) -> bool {
            // Rust presently has no notion of 'unsafe fields', so for now we
            // make the conservative assumption that everything besides
            // primitive types carry safety invariants.
            self != &Self::Primitive
        }
    }

    pub(crate) fn layout_of<'tcx>(
        cx: LayoutCx<'tcx>,
        ty: Ty<'tcx>,
    ) -> Result<Layout<'tcx>, &'tcx LayoutError<'tcx>> {
        use rustc_middle::ty::layout::LayoutOf;
        let ty = cx.tcx().erase_regions(ty);
        cx.layout_of(ty).map(|tl| tl.layout)
    }
}
