use std::fmt;

use itertools::Itertools;
use tracing::instrument;

use super::{Byte, GlobalCounter, Nfa, Ref, nfa};
use crate::Map;

#[derive(PartialEq, Clone, Debug)]
pub(crate) struct Dfa<R>
where
    R: Ref,
{
    pub(crate) transitions: Map<State, Transitions<R>>,
    pub(crate) start: State,
    pub(crate) accepting: State,
}

#[derive(PartialEq, Clone, Debug)]
pub(crate) struct Transitions<R>
where
    R: Ref,
{
    byte_transitions: Map<Byte, State>,
    ref_transitions: Map<R, State>,
}

impl<R> Default for Transitions<R>
where
    R: Ref,
{
    fn default() -> Self {
        Self { byte_transitions: Map::default(), ref_transitions: Map::default() }
    }
}

impl<R> Transitions<R>
where
    R: Ref,
{
    #[cfg(test)]
    fn insert(&mut self, transition: Transition<R>, state: State) {
        match transition {
            Transition::Byte(b) => {
                self.byte_transitions.insert(b, state);
            }
            Transition::Ref(r) => {
                self.ref_transitions.insert(r, state);
            }
        }
    }
}

/// The states in a `Nfa` represent byte offsets.
#[derive(Hash, Eq, PartialEq, PartialOrd, Ord, Copy, Clone)]
pub(crate) struct State(GlobalCounter);

#[cfg(test)]
#[derive(Hash, Eq, PartialEq, Clone, Copy)]
pub(crate) enum Transition<R>
where
    R: Ref,
{
    Byte(Byte),
    Ref(R),
}

impl fmt::Debug for State {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "S_{}", self.0.0)
    }
}

#[cfg(test)]
impl<R> fmt::Debug for Transition<R>
where
    R: Ref,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self {
            Self::Byte(b) => b.fmt(f),
            Self::Ref(r) => r.fmt(f),
        }
    }
}

impl<R> Dfa<R>
where
    R: Ref,
{
    #[cfg(test)]
    pub(crate) fn bool() -> Self {
        let mut transitions: Map<State, Transitions<R>> = Map::default();
        let start = State::new();
        let accepting = State::new();

        transitions
            .entry(start)
            .or_default()
            .insert(Transition::Byte(Byte::from_iters([0x00..=0x01])), accepting);

        Self { transitions, start, accepting }
    }

    #[instrument(level = "debug")]
    pub(crate) fn from_nfa(nfa: Nfa<R>) -> Self {
        let mut old = nfa;
        println!("from_nfa: original: {}", old.serialize_to_graphviz_dot());
        loop {
            let (new, is_dfa) = partial_determinize(&old);
            println!("from_nfa: {}", new.serialize_to_graphviz_dot());
            if is_dfa {
                return dfa_from_nfa_unchecked(new);
            }
            println!("Failed to fully determinize; retrying...");
            old = new;
        }

        fn partial_determinize<R: Ref>(old: &Nfa<R>) -> (Nfa<R>, bool) {
            let mut new = Nfa {
                transitions: Map::default(),
                start: nfa::State::new(),
                // NOTE: This will be overwritten later. We just need to
                // initialize with *some* value.
                accepting: old.accepting,
            };

            // let mut dfa_transitions: Map<State, Transitions<R>> = Map::default();
            let mut old_to_new: Map<nfa::State, nfa::State> = Map::default();
            // let mut nfa_to_dfa: Map<nfa::State, State> = Map::default();
            // let dfa_start = State::new();
            old_to_new.insert(old.start, new.start);

            let mut queue = vec![(old.start, new.start)];

            while let Some((old_state, new_state)) = queue.pop() {
                if old_state == old.accepting {
                    continue;
                }

                let (byte_transitions, ref_transitions): (Vec<_>, Vec<_>) =
                    old.transitions[&old_state].iter().partition_map(|(edge, dst)| match edge {
                        nfa::Transition::Byte(b) => itertools::Either::Left((b, dst)),
                        nfa::Transition::Ref(_) => itertools::Either::Right((*edge, dst.clone())),
                    });

                struct Foo {
                    lhs: Byte,
                    dst: crate::Set<nfa::State>,
                    overlaps: Vec<Byte>,
                }
                let mut foos = Vec::new();
                let len = byte_transitions.len();
                for i in 0..len {
                    let i_edge = *byte_transitions[i].0;
                    let i_dst = byte_transitions[i].1.clone();
                    let mut foo = Foo { lhs: i_edge, dst: i_dst, overlaps: Vec::new() };
                    for j in 0..len {
                        if i == j {
                            continue;
                        }

                        let j_edge = *byte_transitions[j].0;
                        match i_edge.into_disjoint(&j_edge) {
                            // `i_edge` and `j_edge` don't overlap.
                            (_, None, _) => {}
                            // `i_edge == j_edge`; this is handled by the
                            // determinization step below.
                            (None, _, None) => {}
                            (_, Some(_), _) => {
                                foo.overlaps.push(j_edge);
                            }
                        }
                    }
                    foos.push(foo);
                }

                let mut byte_transitions = Vec::new();
                for Foo { lhs, dst, overlaps } in foos {
                    // INVARIANT: All values in `lhs` are disjoint from one another.
                    let mut lhs = vec![lhs];
                    for o in overlaps {
                        let mut new_lhs = Vec::new();
                        for l in lhs {
                            // INVARIANT: Since `l` was in `lhs`, it is disjoint
                            // from all other values in `lhs` by invariant. `a` and
                            // `b` are disjoint by post-condition on
                            // `into_disjoint`. Thus, `a` and `b` are disjoint and
                            // also disjoint from all other values in `lhs`.
                            let (a, b, _) = l.into_disjoint(&o);
                            if let Some(a) = a {
                                new_lhs.push(a);
                            }
                            if let Some(b) = b {
                                new_lhs.push(b);
                            }
                        }
                        lhs = new_lhs;
                    }

                    byte_transitions.extend(lhs.into_iter().map(|lhs| (lhs, dst.clone())));
                }

                let new_transitions =
                    new.transitions.entry(new_state).or_insert_with(Default::default);
                for (old_transition, old_next_states) in byte_transitions
                    .into_iter()
                    .map(|(b, state)| (nfa::Transition::Byte(b), state))
                    .chain(ref_transitions.into_iter())
                {
                    let mapped_state =
                        old_next_states.iter().find_map(|x| old_to_new.get(x).copied());

                    let new_next_state =
                        new_transitions.entry(old_transition).or_insert_with(|| {
                            [mapped_state.unwrap_or_else(nfa::State::new)].into_iter().collect()
                        });

                    for old_next_state in old_next_states {
                        old_to_new.entry(old_next_state).or_insert_with(|| {
                            let mut iter = new_next_state.iter();
                            let state = *iter.next().unwrap();
                            debug_assert!(iter.next().is_none());
                            queue.push((old_next_state, state));
                            state
                        });
                    }
                }
            }

            new.accepting = old_to_new[&old.accepting];
            let is_dfa = old.transitions.len() == new.transitions.len();
            (new, is_dfa)
        }

        fn dfa_from_nfa_unchecked<R: Ref>(nfa: Nfa<R>) -> Dfa<R> {
            Dfa {
                transitions: nfa
                    .transitions
                    .into_iter()
                    .map(|(state, transitions)| {
                        let (byte_transitions, ref_transitions) =
                            transitions.into_iter().partition_map(|(transition, states)| {
                                let state = states.into_iter().exactly_one().unwrap();
                                let state = State::from(state);
                                match transition {
                                    nfa::Transition::Byte(b) => itertools::Either::Left((b, state)),
                                    nfa::Transition::Ref(r) => itertools::Either::Right((r, state)),
                                }
                            });

                        (state.into(), Transitions { byte_transitions, ref_transitions })
                    })
                    .collect(),
                start: nfa.start.into(),
                accepting: nfa.accepting.into(),
            }
        }
    }

    pub(crate) fn bytes_from(&self, start: State) -> Option<&Map<Byte, State>> {
        Some(&self.transitions.get(&start)?.byte_transitions)
    }

    pub(crate) fn states_from(
        &self,
        state: State,
        src_validity: Byte,
    ) -> impl Iterator<Item = (Byte, State)> {
        self.transitions
            .get(&state)
            .map(move |t| {
                t.byte_transitions.iter().filter_map(move |(dst_validity, dst_state)| {
                    src_validity
                        .transmutable_into(&dst_validity)
                        .then_some((*dst_validity, *dst_state))
                })
            })
            .into_iter()
            .flatten()
    }

    pub(crate) fn refs_from(&self, start: State) -> Option<&Map<R, State>> {
        Some(&self.transitions.get(&start)?.ref_transitions)
    }

    pub(crate) fn serialize_to_graphviz_dot(&self) -> String {
        use std::fmt::Write as _;

        let mut st = String::new();
        let s = &mut st;
        writeln!(s, "digraph {{").unwrap();
        writeln!(s, "{:?};", self.start).unwrap();

        for (src, transitions) in self.transitions.iter() {
            for (byte, dst) in transitions.byte_transitions.iter() {
                writeln!(s, "{src:?} -> {dst:?} [label=\"{byte:?}\"]").unwrap();
            }

            for (rf, dst) in transitions.ref_transitions.iter() {
                writeln!(s, "{src:?} -> {dst:?} [label=\"{rf:?}\"]").unwrap();
            }
        }

        writeln!(s, "}}").unwrap();

        st
    }
}

impl State {
    pub(crate) fn new() -> Self {
        Self(GlobalCounter::new())
    }
}

impl From<nfa::State> for State {
    fn from(s: nfa::State) -> State {
        State(s.0)
    }
}

#[cfg(test)]
impl<R> From<nfa::Transition<R>> for Transition<R>
where
    R: Ref,
{
    fn from(nfa_transition: nfa::Transition<R>) -> Self {
        match nfa_transition {
            nfa::Transition::Byte(byte) => Transition::Byte(byte),
            nfa::Transition::Ref(r) => Transition::Ref(r),
        }
    }
}
