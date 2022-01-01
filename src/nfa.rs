use slab::Slab;
use std::collections::HashSet;

/*
 * Convert infix regexp re to postfix notation.
 * Insert . as explicit concatenation operator.
 */
fn re2post(re: &str) -> Result<String, usize> {
    let mut natom = 0;
    let mut nalt = 0;
    let mut paren: Vec<(usize /*nalt */, usize /*natom */)> = vec![];
    let mut postfix = String::new();
    for (index, ch) in re.chars().enumerate() {
        match ch {
            '(' => {
                if natom > 1 {
                    natom -= 1;
                    postfix.push('.');
                }
                paren.push((nalt, natom));
                nalt = 0;
                natom = 0;
            }
            '|' => {
                if natom == 0 {
                    return Err(index);
                }
                for _ in 1..natom {
                    postfix.push('.');
                }
                natom = 0;
                nalt += 1;
            }
            ')' => {
                if natom == 0 {
                    return Err(index);
                }
                for _ in 1..natom {
                    postfix.push('.');
                }
                while nalt > 0 {
                    postfix.push('|');
                    nalt -= 1;
                }
                let tmp = paren.pop().ok_or(index)?;
                nalt = tmp.0;
                natom = tmp.1;
                natom += 1;
            }
            '*' | '+' | '?' => {
                if natom == 0 {
                    return Err(index);
                }
                postfix.push(ch);
            }
            _ => {
                if natom > 1 {
                    postfix.push('.');
                    natom -= 1;
                }
                postfix.push(ch);
                natom += 1;
            }
        }
    }
    for _ in 1..natom {
        postfix.push('.');
    }
    while nalt > 0 {
        postfix.push('|');
        nalt -= 1;
    }
    Ok(postfix)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CharS {
    Char(char),
    Split,
    Match,
    Null,
}
impl From<char> for CharS {
    fn from(ch: char) -> Self {
        CharS::Char(ch)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum StateIndex {
    Index(usize),
    DualIndex2out(usize), // use dual_index simluate double pointer. modify DualIndex2out(2) equal modify state.out which state = slab[2];
    DualIndex2out1(usize), // modify DualIndex2out1(2) equal modify state.out1 which state = slab[2];
}

impl From<usize> for StateIndex {
    fn from(index: usize) -> Self {
        Self::Index(index)
    }
}
impl StateIndex {
    fn value(&self) -> usize {
        match self {
            StateIndex::Index(index) => *index,
            StateIndex::DualIndex2out(dual_index) => *dual_index,
            StateIndex::DualIndex2out1(dual_index) => *dual_index,
        }
    }
    fn point2out(self) -> StateIndex {
        StateIndex::DualIndex2out(self.value())
    }
    fn point2out1(self) -> StateIndex {
        StateIndex::DualIndex2out1(self.value())
    }
}
const NULL_INDEX: StateIndex = StateIndex::Index(0);
const NULL_STATE: State = State {
    c: CharS::Null,
    out: NULL_INDEX,
    out1: NULL_INDEX,
};
const MATCH_INDEX: StateIndex = StateIndex::Index(1);
const MATCH_STATE: State = State {
    c: CharS::Match,
    out: NULL_INDEX,
    out1: NULL_INDEX,
};

/*
 * Represents an NFA state plus zero or one or two arrows exiting.
 * if c == CharS::Match, no arrows out; matching state.
 * If c == CharS::Split, unlabeled arrows to out and out1 (if != NULL_INDEX).
 * If c == CharS::Char, labeled arrow with character c to out.
 */
#[derive(Debug, Clone, Copy)]
struct State {
    c: CharS,
    out: StateIndex,
    out1: StateIndex,
}
impl Default for State {
    fn default() -> Self {
        Self {
            c: CharS::Null,
            out: NULL_INDEX,
            out1: NULL_INDEX,
        }
    }
}
fn state(states: &mut Slab<State>, c: CharS, out: StateIndex, out1: StateIndex) -> StateIndex {
    let s = State { c, out, out1 };
    let state_index = states.insert(s).into();
    debug_assert_ne!(state_index, NULL_INDEX);
    debug_assert_ne!(state_index, MATCH_INDEX);
    return state_index;
}

/*
 * A partially built NFA without the matching state filled in.
 * Frag.start points at the start state.
 * Frag.out is a list of places that need to be set to the
 * next state for this fragment.
 */
struct Frag {
    start: StateIndex,
    out: Vec<StateIndex>, //dual index only exist here.
}
impl Default for Frag {
    fn default() -> Self {
        Self {
            start: NULL_INDEX,
            out: vec![],
        }
    }
}
impl Frag {
    /* Patch the list of states at out to point to state_index. */
    fn patch(&mut self, state_index: StateIndex, states: &mut Slab<State>) {
        for index in &self.out {
            match index {
                StateIndex::Index(index) => {
                    let state = states.get_mut(*index).unwrap();
                    state.out = state_index;
                }
                StateIndex::DualIndex2out(doul_index) => {
                    let state = states.get_mut(*doul_index).unwrap();
                    state.out = state_index;
                }
                StateIndex::DualIndex2out1(doul_index) => {
                    let state = states.get_mut(*doul_index).unwrap();
                    state.out1 = state_index;
                }
            }
        }
    }
    /* Join the two lists self.out and other.out */
    fn append(&mut self, mut other: Frag) {
        self.out.append(&mut other.out);
    }
}

/* Create singleton list containing just outp. */
fn list1(outp: StateIndex) -> Vec<StateIndex> {
    vec![outp]
}
// Transmitt postfix to nfa, return first state's index and slab wihch is all state allocated.
fn postfix2nfa(postfix: &str) -> (StateIndex, Slab<State>) {
    let mut states = Slab::with_capacity(postfix.len());
    let null_index: StateIndex = states.insert(NULL_STATE).into(); /* simulate null pointer, segfault!!! */
    let match_index: StateIndex = states.insert(MATCH_STATE).into(); /* matching state */
    debug_assert_eq!(null_index, NULL_INDEX);
    debug_assert_eq!(match_index, MATCH_INDEX);
    let mut frags: Vec<Frag> = vec![];
    for ch in postfix.chars() {
        match ch {
            '.' => {
                let e2 = frags.pop().unwrap();
                let mut e1 = frags.pop().unwrap();
                e1.patch(e2.start, &mut states);
                frags.push(Frag {
                    start: e1.start,
                    out: e2.out,
                });
            }
            '|' => {
                let e2 = frags.pop().unwrap();
                let mut e1 = frags.pop().unwrap();
                let state_index = state(&mut states, CharS::Split, e1.start, e2.start);
                e1.append(e2);
                frags.push(Frag {
                    start: state_index,
                    out: e1.out,
                });
            }
            '*' => {
                let mut e = frags.pop().unwrap();
                let s = state(&mut states, CharS::Split, e.start, NULL_INDEX);
                e.patch(s, &mut states);
                frags.push(Frag {
                    start: s,
                    out: list1(s.point2out1()),
                });
            }
            '?' => {
                let mut e = frags.pop().unwrap();
                let s = state(&mut states, CharS::Split, e.start, NULL_INDEX);
                e.out.push(s.point2out1());
                frags.push(Frag {
                    start: s,
                    out: e.out,
                });
            }
            '+' => {
                let mut e = frags.pop().unwrap();
                let s = state(&mut states, CharS::Split, e.start, NULL_INDEX);
                e.patch(s, &mut states);
                frags.push(Frag {
                    start: e.start,
                    out: list1(s.point2out1()),
                });
            }
            _ => {
                let state_index = state(&mut states, ch.into(), NULL_INDEX, NULL_INDEX);
                let frag = Frag {
                    start: state_index,
                    out: list1(state_index.point2out()),
                };
                frags.push(frag);
            }
        }
    }

    let mut e = frags.pop().unwrap_or_default();
    e.patch(MATCH_INDEX, &mut states);
    (e.start, states)
}

/* Check whether state list contains a match. */
fn is_match(set: &HashSet<StateIndex>, states: &mut Slab<State>) -> bool {
    for index in set.iter() {
        if let Some(state) = states.get(index.value()) {
            if state.c == CharS::Match {
                return true;
            }
        } else {
            panic!("segment fault(");
        }
    }
    return false;
}
/* Add state_index to set, following unlabeled arrows. */
fn add_state(set: &mut HashSet<StateIndex>, state_index: StateIndex, slab: &mut Slab<State>) {
    if let Some(&state) = slab.get(state_index.value()) {
        match state.c {
            CharS::Char(_) | CharS::Match | CharS::Null => {
                set.insert(state_index);
            }
            /* follow unlabeled arrows */
            CharS::Split => {
                add_state(set, state.out, slab);
                add_state(set, state.out1, slab);
            }
        }
    } else {
        panic!("segment fault(");
    }
}

/*
 * Step the NFA from the states in cset
 * past the character c,
 * to create next NFA state set nset.
 */
fn step(
    ch: char,
    cset: &mut HashSet<StateIndex>,
    nset: &mut HashSet<StateIndex>,
    states: &mut Slab<State>,
) {
    nset.clear();
    for index in cset.iter() {
        if let Some(state) = states.get(index.value()) {
            //debug_assert!(state.c != CharS::Null);
            if state.c == ch.into() {
                add_state(nset, state.out, states);
            }
        } else {
            panic!("segment fault(");
        }
    }
}

/* Run NFA to determine whether it matches string. */
fn match_expr(string: &str, start: StateIndex, states: &mut Slab<State>) -> bool {
    let mut cset: HashSet<StateIndex> = HashSet::new();
    let mut nset: HashSet<StateIndex> = HashSet::new();
    add_state(&mut cset, start, states);
    for ch in string.chars() {
        step(ch, &mut cset, &mut nset, states);
        std::mem::swap(&mut cset, &mut nset);
    }
    is_match(&cset, states)
}
mod test {
    use super::*;
    macro_rules! regex_assert {
        ($re:expr, $string:expr) => {
            let postfix = re2post($re).unwrap();
            let (start, mut states) = postfix2nfa(&postfix);
            assert!(match_expr(&$string, start, &mut states));
        };
    }
    #[test]
    fn test() {
        let re = "a?b?c*d+(e|f)";
        let postfix = re2post(re).unwrap();
        println!("postfix: {}", postfix);
        let (start, mut states) = postfix2nfa(&postfix);
        println!("{:?}", start);
        for (i, s) in &states {
            println!("{:?}==>{:?}", i, s);
        }
        dbg!(match_expr("abccdf", start, &mut states));
    }
    #[test]
    fn test_regex() {
        regex_assert!("abcdefg", "abcdefg");
        regex_assert!("(a*|b)cd?", "aaaaacd");
        regex_assert!("a?b?c*d+(e|f)", "abccdf");
        regex_assert!(
            "a?a?a?a?a?a?a?a?a?a?a?a*a*a*a*a*a*a*a*a*a*a*",
            "aaaaaaaaaaa"
        );
        
    }
}
