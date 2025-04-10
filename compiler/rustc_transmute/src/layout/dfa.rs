use itertools::Itertools;
use tracing::instrument;

use super::{
    Byte, Nfa, Ref,
    automaton::{Automaton, State, Transition},
};
use crate::{Map, Set};

#[derive(PartialEq, Clone, Debug)]
pub(crate) struct Dfa<R: Ref>(
    // INVARIANT: `Automaton` is a DFA, which means that, for any `state`, each
    // transition in `self.0.transitions[state]` contains exactly one
    // destination state.
    pub(crate) Automaton<R>,
);

impl<R> Dfa<R>
where
    R: Ref,
{
    #[cfg(test)]
    pub(crate) fn bool() -> Self {
        let mut transitions: Map<State, Map<Transition<R>, Set<State>>> = Map::default();
        let start = State::new();
        let accept = State::new();

        transitions.entry(start).or_default().insert(
            Transition::Byte(Byte::from_iters([0x0..=0x01])),
            [accept].into_iter().collect(),
        );

        Dfa(Automaton { transitions, start, accept })
    }

    #[instrument(level = "debug", skip(new_state))]
    pub(crate) fn from_nfa(mut new_state: impl FnMut() -> State, nfa: Nfa<R>) -> Self {
        // It might already be the case that `nfa` is a DFA. If that's the case,
        // we can avoid reconstructing the DFA.
        let is_dfa = nfa
            .0
            .transitions
            .iter()
            .flat_map(|(_, transitions)| transitions.iter())
            .all(|(_, dsts)| dsts.len() <= 1);
        if is_dfa {
            return Dfa(nfa.0);
        }

        // This function implements "determinization", the process of converting
        // an NFA to a DFA. The execution state of an NFA permits being in
        // multiple NFA states during the same execution step. This is not
        // permitted in the execution of a DFA, and so the process of
        // determinization requires us to synthesize a single DFA state for
        // every *set* of NFA states that are reachable during the same
        // execution step.
        //
        // Note that the algorithm implemented here takes advantage of the fact
        // that we only need to support acyclic NFAs, and so it can be somewhat
        // simpler than the general-purpose determinization algorithm.

        let dfa_start = new_state();
        let mut dfa = Dfa(Automaton {
            transitions: Map::default(),
            start: dfa_start,
            accept: if nfa.0.start == nfa.0.accept { dfa_start } else { new_state() },
        });

        // A queue of states to process. Each (nfa_states, dfa_state) pair has
        // the property that the set of paths reachable from `nfa_states` is
        // identical to the set of paths reachable from `dfa_state`.
        let mut queue: Vec<(Set<_>, _)> = vec![([nfa.0.start].into_iter().collect(), dfa_start)];

        // A map from NFA state to equivalent DFA state. This is actually a map
        // from *sets* of NFA states to their equivalent DFA state, but, for
        // simplicity, we only use it to map the subset of cases where the NFA
        // set is a singleton.
        let mut nfa_to_dfa: Map<State, State> = Map::default();
        nfa_to_dfa.insert(nfa.0.start, dfa_start);

        while let Some((nfa_states, dfa_state)) = queue.pop() {
            if nfa_states.contains(&nfa.0.accept) {
                continue;
            }

            let dfa_transitions = dfa.0.transitions.entry(dfa_state).or_insert_with(Map::default);

            // Recall that `nfa_states` is a set of NFA states which can be
            // occupied during a single step of NFA execution. `nfa_edges` is
            // the set of edges out of *any* of these states, grouped by symbol.
            let nfa_edges = {
                let nfa_edges = nfa_states
                    .iter()
                    .flat_map(|state| nfa.0.transitions.get(state))
                    .flatten()
                    .flat_map(|(symbol, dsts)| dsts.iter().map(move |dst| (symbol, dst)));

                let mut byte_transitions: [Set<State>; 256] = [(); 256].map(|_| Set::default());
                let mut uninit_transitions = Set::default();
                let mut ref_transitions: Map<R, Set<State>> = Map::default();
                for (&symbol, &dst) in nfa_edges {
                    match symbol {
                        Transition::Byte(b) => {
                            for b in b.iter() {
                                if let Some(b) = b {
                                    byte_transitions[usize::from(b)].insert(dst);
                                } else {
                                    uninit_transitions.insert(dst);
                                }
                            }
                        }
                        Transition::Ref(r) => {
                            ref_transitions.entry(r).or_default().insert(dst);
                        }
                    }
                }

                // `Set<nfa::State>: !Hash`, so we use `Vec` as the key type
                // instead. In order to ensure key equality, each `Vec` must be
                // sorted.
                let mut states_to_edge: Map<Vec<State>, Byte> = Map::default();
                if !uninit_transitions.is_empty() {
                    states_to_edge.insert(
                        {
                            let mut states: Vec<_> = uninit_transitions.into_iter().collect();
                            states.sort();
                            states
                        },
                        Byte::uninit(),
                    );
                }

                for (b, states) in byte_transitions.into_iter().enumerate() {
                    if states.is_empty() {
                        continue;
                    }

                    let b = u8::try_from(b).unwrap();
                    let byte = states_to_edge
                        .entry({
                            let mut states: Vec<_> = states.into_iter().collect();
                            states.sort();
                            states
                        })
                        .or_insert(Byte::from_iters([b..=b]));
                    byte.insert(b);
                }

                states_to_edge
                    .into_iter()
                    .map(|(states, edge)| {
                        let states: Set<_> = states.into_iter().collect();
                        (Transition::Byte(edge), states)
                    })
                    .chain(
                        ref_transitions.into_iter().map(|(r, states)| (Transition::Ref(r), states)),
                    )
            };

            for (nfa_symbol, nfa_dsts) in nfa_edges {
                // Recall that `nfa_states` and `dfa_state` are semantically
                // equivalent in the sense that the set of paths reachable from
                // either is identical. From `nfa_states`, we can follow
                // `nfa_symbol` and reach any of `nfa_dsts`. Thus, we need to
                // add an edge from `dfa_state` following `nfa_symbol` which
                // brings us to a new DFA state which is equivalent to
                // `nfa_dsts`.

                let dfa_dst = if nfa_dsts.contains(&nfa.0.accept) {
                    // If any of `nfa_dsts` is the accept state, then if the
                    // NFA is in any of `nfa_states` and consumes `nfa_symbol`,
                    // the NFA accepts. Thus, if the DFA is in `dfa_state` and
                    // consumes `nfa_symbol`, it should accept.
                    dfa.0.accept
                } else if nfa_dsts.len() == 1 {
                    // If `nfa_dsts` contains a single NFA state, then we can
                    // attempt to re-use an existing DFA state which is known to
                    // be equivalent to this single NFA state. Otherwise, we can
                    // allocate a new DFA state and record this equivalence
                    // relation.

                    use itertools::Itertools as _;
                    let nfa_dst = *nfa_dsts.iter().exactly_one().unwrap();
                    *nfa_to_dfa.entry(nfa_dst).or_insert_with(&mut new_state)
                } else {
                    new_state()
                };

                dfa_transitions.insert(nfa_symbol, [dfa_dst].into_iter().collect());
                queue.push((nfa_dsts, dfa_dst));
            }
        }

        dfa
    }

    pub(crate) fn states_from(
        &self,
        state: State,
        src_validity: Byte,
    ) -> impl Iterator<Item = (Byte, State)> {
        self.0
            .transitions
            .get(&state)
            .map(move |t| {
                t.iter().filter_map(move |(dst_validity, dst_state)| {
                    if let Transition::Byte(dst_validity) = dst_validity {
                        let dst_state = dst_state.iter().exactly_one().unwrap();
                        src_validity
                            .transmutable_into(&dst_validity)
                            .then_some((*dst_validity, *dst_state))
                    } else {
                        None
                    }
                })
            })
            .into_iter()
            .flatten()
    }

    pub(crate) fn iter_bytes_from(&self, start: State) -> impl Iterator<Item = (Byte, State)> {
        self.0.transitions.get(&start).into_iter().flat_map(|transitions| {
            transitions.iter().filter_map(|(t, s)| {
                let s = s.iter().copied().exactly_one().unwrap();
                if let Transition::Byte(b) = t { Some((*b, s)) } else { None }
            })
        })
    }

    pub(crate) fn iter_refs_from(&self, start: State) -> impl Iterator<Item = (R, State)> {
        self.0.transitions.get(&start).into_iter().flat_map(|transitions| {
            transitions.iter().filter_map(|(t, s)| {
                let s = s.iter().copied().exactly_one().unwrap();
                if let Transition::Ref(r) = t { Some((*r, s)) } else { None }
            })
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type Nfa = crate::layout::Nfa<!>;
    type Dfa = super::Dfa<!>;

    #[test]
    fn test_determinization() {
        // Construct the following NFA with start state A and accept state E:
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
        let [a, b, c, d, e] = [0, 1, 2, 3, 4];
        let nfa = Nfa::from_edges(
            a,
            e,
            &[(a, 0, b), (a, 1, b), (a, 1, c), (b, 2, d), (c, 3, d), (d, 4, e)],
        );

        let mut ctr = 0;
        let new_state = || {
            ctr += 1;
            super::State(ctr)
        };

        let nfa_graphviz = nfa.0.serialize_to_graphviz_dot();
        let dfa = Dfa::from_nfa(new_state, nfa);
        let dfa_graphviz = dfa.0.serialize_to_graphviz_dot();

        assert_eq!(
            dfa,
            Dfa(Automaton {
                start: State(1),
                accept: State(2),
                transitions: [
                    (1, transitions([((0, 0), 3), ((1, 1), 4)])),
                    (3, transitions([((2, 2), 5)])),
                    (4, transitions([((2, 3), 5)])),
                    (5, transitions([((4, 4), 2)])),
                ]
                .into_iter()
                .map(|(state, transitions)| (State(state), transitions))
                .collect(),
            }),
            "NFA: {nfa_graphviz}\nDFA: {dfa_graphviz}"
        );

        fn transitions<const N: usize, R: Ref>(
            pairs: [((u8, u8), u32); N],
        ) -> Map<Transition<R>, Set<State>> {
            pairs
                .into_iter()
                .map(|((lo, hi), state)| {
                    (
                        Transition::Byte(Byte::from_iters([lo..=hi])),
                        [State(state)].into_iter().collect(),
                    )
                })
                .collect()
        }
    }
}
