use std::fmt;
use std::sync::atomic::{AtomicU32, Ordering};

use tracing::instrument;

use super::{Byte, Nfa, Ref, nfa};
use crate::{Map, Set};

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
    fn insert_from_nfa(&mut self, transition: nfa::Transition<R>, state: State) {
        match transition {
            nfa::Transition::Byte(b) => {
                self.byte_transitions.insert(b, state);
            }
            nfa::Transition::Ref(r) => {
                self.ref_transitions.insert(r, state);
            }
        }
    }
}

/// The states in a `Nfa` represent byte offsets.
#[derive(Hash, Eq, PartialEq, PartialOrd, Ord, Copy, Clone)]
pub(crate) struct State(u32);

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
        write!(f, "S_{}", self.0)
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

        transitions.entry(start).or_default().byte_transitions.insert(Byte::Init(0x00), accepting);

        transitions.entry(start).or_default().byte_transitions.insert(Byte::Init(0x01), accepting);

        Self { transitions, start, accepting }
    }

    pub(crate) fn from_nfa(mut new_state: impl FnMut() -> State, nfa: Nfa<R>) -> Self {
        let dfa_start = new_state();
        let mut dfa = Dfa {
            transitions: Map::default(),
            start: dfa_start,
            accepting: if nfa.start == nfa.accepting { dfa_start } else { new_state() },
        };

        let mut nfa_to_dfa: Map<nfa::State, State> = Map::default();
        nfa_to_dfa.insert(nfa.start, dfa_start);

        let mut queue: Vec<(Set<_>, _)> = vec![([nfa.start].into_iter().collect(), dfa_start)];

        while let Some((nfa_states, dfa_state)) = queue.pop() {
            if nfa_states.contains(&nfa.accepting) {
                continue;
            }

            let dfa_transitions =
                dfa.transitions.entry(dfa_state).or_insert_with(Transitions::default);

            let nfa_edges: Map<_, Set<_>> = nfa_states
                .iter()
                .flat_map(|state| nfa.transitions.get(state))
                .flatten()
                .flat_map(|(symbol, dsts)| dsts.iter().map(move |dst| (symbol, dst)))
                .fold(Map::default(), |mut map, (symbol, dst)| {
                    map.entry(symbol).or_default().insert(*dst);
                    map
                });
            for (nfa_symbol, nfa_dsts) in nfa_edges {
                let dfa_dst = if nfa_dsts.contains(&nfa.accepting) {
                    dfa.accepting
                } else if nfa_dsts.len() == 1 {
                    use itertools::Itertools as _;
                    let nfa_dst = *nfa_dsts.iter().exactly_one().unwrap();
                    *nfa_to_dfa.entry(nfa_dst).or_insert_with(&mut new_state)
                } else {
                    new_state()
                };

                dfa_transitions.insert_from_nfa(*nfa_symbol, dfa_dst);
                queue.push((nfa_dsts, dfa_dst));
            }
        }

        dfa
    }

    pub(crate) fn bytes_from(&self, start: State) -> Option<&Map<Byte, State>> {
        Some(&self.transitions.get(&start)?.byte_transitions)
    }

    pub(crate) fn byte_from(&self, start: State, byte: Byte) -> Option<State> {
        self.transitions.get(&start)?.byte_transitions.get(&byte).copied()
    }

    pub(crate) fn refs_from(&self, start: State) -> Option<&Map<R, State>> {
        Some(&self.transitions.get(&start)?.ref_transitions)
    }

    #[cfg(test)]
    fn serialize_to_graphviz_dot(&self) -> String {
        use std::fmt::Write as _;

        let mut st = String::new();
        let s = &mut st;
        writeln!(s, "digraph {{").unwrap();
        writeln!(s, "{:?} [shape = doublecircle]", self.start).unwrap();
        writeln!(s, "{:?} [shape = doublecircle]", self.accepting).unwrap();

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
        static COUNTER: AtomicU32 = AtomicU32::new(0);
        Self(COUNTER.fetch_add(1, Ordering::SeqCst))
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

#[cfg(test)]
mod tests {
    use super::*;

    type Tree = crate::layout::Tree<!, !>;
    type Nfa = crate::layout::Nfa<!>;
    type Dfa = super::Dfa<!>;

    #[test]
    fn test_determinization() {
        // Construct the following NFA with start state A and accepting state E:
        //
        //     +-- A --+
        //   0 | / 1   | 1
        //     B       C
        //   2 |       | 3
        //     +-- D --+
        //       4 |
        //         E
        //
        // Note that A->B has two edges: one labeled 0, and one labeled 1.
        let tree = Tree::from_bits(0)
            .or(Tree::from_bits(1))
            .then(Tree::from_bits(2))
            .or(Tree::from_bits(1).then(Tree::from_bits(3)))
            .then(Tree::from_bits(4));
        let nfa = Nfa::from_tree(tree).unwrap();

        let mut ctr = 0;
        let new_state = || {
            ctr += 1;
            super::State(ctr)
        };

        let nfa_graphviz = nfa.serialize_to_graphviz_dot();
        let dfa = Dfa::from_nfa(new_state, nfa);
        let dfa_graphviz = dfa.serialize_to_graphviz_dot();

        assert_eq!(
            dfa,
            Dfa {
                start: State(1),
                accepting: State(2),
                transitions: [
                    (1, transitions([(0, 3), (1, 4)])),
                    (3, transitions([(2, 5)])),
                    (4, transitions([(2, 5), (3, 5)])),
                    (5, transitions([(4, 2)])),
                ]
                .into_iter()
                .map(|(state, transitions)| (State(state), transitions))
                .collect(),
            },
            "NFA: {nfa_graphviz}\nDFA: {dfa_graphviz}"
        );

        fn transitions<const N: usize, R: Ref>(pairs: [(u8, u32); N]) -> Transitions<R> {
            Transitions {
                byte_transitions: pairs
                    .into_iter()
                    .map(|(byte, state)| (Byte::Init(byte), State(state)))
                    .collect(),
                ref_transitions: Map::default(),
            }
        }
    }
}
