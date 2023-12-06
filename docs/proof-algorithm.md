# A high-level overview of our proof procedure

```rust
struct Eq {
  lhs: Term,
  rhs: Term,
}

struct Prop {
  eq: Eq,
  /// Preconditions on the prop
  conds: Vec<Eq>,
  /// The variables the prop is parameterized over
  params: Vec<Var>,
}

struct ProofState {
  /// Our search is conducted in a manner where we need to prove 
  /// _all_ of the goals in this list to prove the original prop.
  goals: Vec<Goal>,
  candidate_lemmas: Vec<Prop>,
}

struct Goal {
  prop: Prop,
  egraph: EGraph,
}

enum ProofResult {
  Invalid,
  Valid,
}

fn prove(prop: Prop) -> ProofResult {
  let mut state = ProofState {
    goals:            [prop.to_goal()],
    candidate_lemmas: [],
  };
  
  // If the cvec analysis deems the prop false, don't bother trying
  // to prove it.
  if cvecs_invalid(prop) {
    return Invalid;
  }
  
  while !state.is_empty() {
    // Take the first unproven goal
    let g = state.goals.pop();
    
    // The rewrites we apply to the e-graph are:
    //   * Reductions from function definitions
    //     - Applied unconditionally
    //   * Proven lemmas
    //     - Applied unconditionally
    //   * The goal's inductive hypothesis
    //     - Conditioned on our termination check
    g.saturate_egraph();
    
    if g.is_proven() {
      continue;
    }
    
    // Look for lemmas from pairs of subterms in the egraph
    state.candidate_lemmas.extend(g.find_lemmas());
    
    // It is too inefficient with our current implementation
    // to always try and prove lemmas, so we use heuristics
    sometimes {
      // This procedure returns true if it proves a lemma that
      // allows it to discharge the goal.
      if try_prove_lemmas(g, candidate_lemmas) {
        continue;
      }
    }
    
    // Find the first variable in g that is blocking a reduction
    // (this is done breadth-first so as to avoid infinitely case
    // splitting a single variable's descendents)
    let blocking_var = g.find_blocking_var();
    
    match blocking_var {
      None => {
        return Invalid;
      }
      Some(v) => {
        // Case split that blocking variable, generating new goals
        state.goals.extend(g.case_split(v));
      }
    }
  }

  return Valid;
}

impl Goal {
  /// Uses the cvecs (concrete vectors) in the egraph's analysis to
  /// hypothesize lemmas between two eclasses.
  ///
  /// Also generalizes the hypothesized lemmas.
  fn find_lemmas(&self) -> Vec<Prop> {
    let mut lemmas = vec!();
    for class1 in self.egraph.classes() {
      for class2 in self.egraph.classes() {
        // Do these classes have the same cvec?
        if cvecs_match(self.egraph, class1, class2) {
           let ls = all_lemmas_from(self.egraph, class1, class2);
           let generalized_ls = ls.map(generalize);
           lemmas.extend(ls);
           lemmas.extend(generalized_ls);
        }
      }
    }
    return lemmas;
  }
}

/// Iterates over the lemmas, trying to prove each of them.
/// If a proven lemma lets us finish proving the goal, then
/// stop trying to prove lemmas and return true.
/// If none help (or are provable), return false.
fn try_prove_lemmas(g: Goal, lemmas: Vec<Prop>) -> bool {
  // Lemmas can be ordered in terms of how general they are.
  //
  // We try to iterate over the most general lemmas first,
  // only attempting to prove a lemma that is less general if
  // we cannot prove the more general lemma.
  //
  // Right now, our notion of generalization is completely
  // _syntactic_, i.e. a lemma L1 only generalizes a lemma L2
  // if there is some substitution S on L1's variables such
  // that S(L1) = L2.
  for lemma in topological_order(lemmas) {
    // We sometimes check if the lemma will help us prove g
    // before we try to prove it.
    //
    // It might be useful to prove a lemma that
    // does not immediately let us prove g (perhaps we 
    // need two lemmas total), so we don't always perform
    // this optimization.
    sometimes {
      if !g.can_prove_assuming_lemma(lemma) {
        continue;
      }
    }
    
    // We record the lemma for future use if it is valid.
    prove(lemma);
    
    // Try to use the lemma (if it was proven).
    g.saturate_egraph();

    if g.is_proven() {
      return true;
    }
  } 
  // No lemma (that we could prove) helped
  return false;
}

```
