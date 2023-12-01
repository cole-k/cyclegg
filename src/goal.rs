use colored::Colorize;
use egg::*;
use itertools::Itertools;
use log::warn;
use std::collections::HashSet;
use std::collections::{HashMap, VecDeque};
use std::fmt::Display;
use std::iter::zip;
use std::time::{Duration, Instant};
use symbolic_expressions::{parser, Sexp};

use crate::analysis::{CycleggAnalysis, CanonicalFormAnalysis, CanonicalForm, cvecs_equal};
use crate::ast::*;
use crate::config::*;
use crate::egraph::*;
use crate::utils::*;

// We will use SymbolLang for now
pub type Eg = EGraph<SymbolLang, CycleggAnalysis>;
pub type Rw = Rewrite<SymbolLang, CycleggAnalysis>;
pub type CvecRw = Rewrite<SymbolLang, ()>;

/// A special scrutinee name used to signal that case split bound has been exceeded
pub const LEMMA_PREFIX: &str = "lemma";
pub const CC_LEMMA_PREFIX: &str = "cc-lemma";
pub const IH_EQUALITY_PREFIX: &str = "ih-equality-"; // TODO: remove

/// Condition that checks whether it is sound to apply a lemma
#[derive(Clone)]
pub struct Soundness {
  /// A substitution from lemma's free variables
  /// to the original e-classes these variables came from
  pub free_vars: IdSubst,
  /// All premises that must hold for this lemma to apply,
  /// expressed in terms of the free variables
  pub premises: Vec<ETermEquation>,
}

impl Soundness {
  /// Substitution as a string, for debugging purposes
  fn _pretty_subst(subst: &[(Symbol, Expr, Expr)]) -> String {
    let strings: Vec<String> = subst
      .iter()
      .map(|(x, orig, new)| {
        format!(
          "{} = {} -> {}",
          &x.to_string(),
          &orig.to_string(),
          &new.to_string()
        )
      })
      .collect();
    strings.join(", ")
  }

  /// Are the canonical forms of the e-classes in new_subst strictly smaller than those in orig_subst?
  /// For now implements a sound but incomplete measure,
  /// where all forms need to be no larger, and at least one has to be strictly smaller.
  fn smaller_tuple(&self, triples: &Vec<(Symbol, Expr, Expr)>, _blocking_vars: &HashSet<Symbol>) -> bool {
    let mut has_strictly_smaller = false;
    for (_, orig, new) in triples {
      match is_subterm(new, orig) {
        StructuralComparison::LT => {
          has_strictly_smaller = true;
        }
        StructuralComparison::Incomparable => {
          return false;
        }
        _ => (),
      }
    }
    has_strictly_smaller
  }

  /// Apply subst to self.premise (if any)
  /// and check whether the resulting terms are equal in the egraph
  fn check_premise(premise: &ETermEquation, triples: &[(Symbol, Expr, Expr)], egraph: &Eg) -> bool {
    // let info = SmallerVar::pretty_subst(triples);
    // println!("checking premise {} = {} for {}", premise.lhs.sexp, premise.rhs.sexp, info);

    // TODO: it's annoying having to convert everything to s-expressions and back
    // but substituting over RecExprs is too much of a pain
    // Convert triples to a substitution over s-expressions
    let subst: SSubst = triples
      .iter()
      .map(|(var, _, new_expr)| {
        (
          var.to_string(),
          // FIXME: we give an empty expression if the var is not blocking.
          // Right now, we just substitute the var for itself, but we should instead
          // find the correct expression to give.
          if new_expr.as_ref().len() == 0 {
            Sexp::String(var.to_string())
          } else {
            symbolic_expressions::parser::parse_str(&new_expr.to_string()).unwrap()
          },
        )
      })
      .collect();

    // Perform the substitution
    let lhs: Expr = resolve_sexp(&premise.lhs.sexp, &subst)
      .to_string()
      .parse()
      .unwrap();
    let rhs: Expr = resolve_sexp(&premise.rhs.sexp, &subst)
      .to_string()
      .parse()
      .unwrap();

    // Lookup the sides of the new premise in the egraph;
    // they must be there, since we added them during grounding
    if let Some(lhs_id) = egraph.lookup_expr(&lhs) {
      if let Some(rhs_id) = egraph.lookup_expr(&rhs) {
        // println!("{} == {}", lhs_id, rhs_id);
        return lhs_id == rhs_id;
      }
    }
    // This cannot happen in uncyclic mode, because we have grounded all the premises,
    // but it can happen in cyclic mode
    // panic!("premise {:?} = {:?} not found in egraph", lhs, rhs);
    false
  }

  /// Check all of the premises of this condition
  fn check_premises(&self, triples: &[(Symbol, Expr, Expr)], egraph: &Eg) -> bool {
    self
      .premises
      .iter()
      .all(|premise| Soundness::check_premise(premise, triples, egraph))
  }
}

impl SearchCondition<SymbolLang, CycleggAnalysis> for Soundness {
  // FIXME: needs to be updated to accurately handle dealing with cases where
  // we can skip the soundness check on some variables because they are not blocking
  /// Returns true if the substitution is into a smaller tuple of variables
  fn check(&self, egraph: &Eg, _eclass: Id, subst: &Subst) -> bool {
    // Create an iterator over triples: (variable, old canonical form, new canonical form)
    let triples = self
      .free_vars
      .iter()
      .map(|(x, orig_id)| {
        let v = to_wildcard(x);
        // Subst must have all lemma variables defined
        // because we did the filtering when creating SmallerVars
        let new_id = subst.get(v).unwrap();
        // Exit early with something guaranteed to be LE if this var is not blocking
        if CONFIG.better_termination && !egraph.analysis.blocking_vars.contains(x) {
          // FIXME: we need to give the actual value here
          return Some((*x, vec!().into(), vec!().into()))
        }
        // match &egraph[*orig_id].data.canonical_form_data {
        //   CanonicalForm::Var(var) if !egraph.analysis.blocking_vars.contains(&var.op) => {
        //     assert_eq!(&var.op, x, "Canonical form analysis is bad");
        //     // println!("skipping checking {} because it's not blocking", var);
        //     return Some((*x, vec!().into(), vec!().into()))
        //   }
        //   _ => {}
        // };
        // If the actual argument of the lemma is not canonical, give up
        let new_canonical = CanonicalFormAnalysis::extract_canonical(egraph, *new_id)?;
        // Same for the original argument:
        // it might not be canonical if it's inconsistent, in which case there's no point applying any lemmas
        let orig_canonical = CanonicalFormAnalysis::extract_canonical(egraph, *orig_id)?;
        Some((*x, orig_canonical, new_canonical))
      })
      .collect::<Option<Vec<(Symbol, Expr, Expr)>>>();

    match triples {
      None => false, // All actual arguments must be canonical in order to be comparable to the formals
      Some(triples) => {
        // Check that the actuals are smaller than the formals
        // and that the actual premise holds
        let terminates = self.smaller_tuple(&triples, &egraph.analysis.blocking_vars);
        // Let's not check the premises if the termination check doesn't hold:
        terminates && self.check_premises(&triples, egraph)
        // println!("trying IH with subst {}; checks: {} {}", SmallerVar::pretty_subst(&triples), terminates, sound);
      }
    }
  }
}

/// A term inside the egraph;
/// we store multiple representations because they are useful for different purposes.
#[derive(Debug, Clone)]
pub struct ETerm {
  /// Term as a symbolic expression
  pub sexp: Sexp,
  /// E-class id of the term in the egraph
  id: Id,
  /// Terms as egg's RecExpr
  pub expr: Expr,
}

impl ETerm {
  /// Create a new term from a symbolic expression
  /// and add it to the egraph
  fn new(sexp: &Sexp, egraph: &mut Eg) -> ETerm {
    let expr = sexp.to_string().parse().unwrap();
    egraph.add_expr(&expr);
    let id = egraph.lookup_expr(&expr).unwrap();
    Self {
      sexp: sexp.clone(),
      id,
      expr,
    }
  }

  fn new_from_expr(expr: &Expr, egraph: &mut Eg) -> ETerm {
    let sexp = parser::parse_str(&expr.to_string()).unwrap();
    egraph.add_expr(expr);
    let id = egraph.lookup_expr(expr).unwrap();
    Self {
      sexp,
      id,
      expr: expr.clone(),
    }
  }

  fn from_expr(expr: Expr, egraph: &Eg) -> Self {
    let id = egraph.lookup_expr(&expr).unwrap();
    let sexp = parser::parse_str(&expr.to_string()).unwrap();
    Self { sexp, id, expr }
  }

  /// Update variables in my expressions with their canonical forms
  fn update_variables(&self, subst: &IdSubst, egraph: &Eg) -> Self {
    let ssubst: SSubst = subst
      .iter()
      .map(|(x, id)| {
        let expr = CanonicalFormAnalysis::extract_canonical(egraph, *id).unwrap();
        (
          x.to_string(),
          symbolic_expressions::parser::parse_str(&expr.to_string()).unwrap(),
        )
      })
      .collect();
    let new_sexp = resolve_sexp(&self.sexp, &ssubst);
    let new_expr = new_sexp.to_string().parse().unwrap();
    Self {
      sexp: new_sexp,
      id: egraph.lookup_expr(&new_expr).unwrap(),
      expr: new_expr,
    }
  }
}

impl Display for ETerm {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{}", self.sexp)
  }
}

/// As opposed to the Equation in ast.rs, an ETermEquation additionally records
/// an e-class id for the LHS and RHS.
#[derive(Debug, Clone)]
pub struct ETermEquation {
  pub lhs: ETerm,
  pub rhs: ETerm,
}

impl Display for ETermEquation {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{} === {}", self.lhs.sexp, self.rhs.sexp)
  }
}

fn find_generalizations_prop(prop: &Prop, global_context: &Context, fresh_name: String) -> Vec<Prop> {
  let lhs_nontrivial_subexprs = nontrivial_sexp_subexpressions_containing_vars(&prop.eq.lhs);
  let rhs_nontrivial_subexprs = nontrivial_sexp_subexpressions_containing_vars(&prop.eq.rhs);
  let mut output = vec!();
  // println!("Trying to generalize {} = {}", raw_eq.eq.lhs, raw_eq.eq.rhs);
  for (rhs_subexpr_str, subexpr) in &rhs_nontrivial_subexprs {
    // should be the same subexpr so we don't need to bind it
    if let Some(_) = lhs_nontrivial_subexprs.get(rhs_subexpr_str) {
      let op = match subexpr {
        Sexp::Empty => unreachable!(),
        // This shouldn't happen unless we generalize a constant
        Sexp::String(s) => s,
        Sexp::List(list) => list.first().unwrap().string().unwrap(),
      };
      let op_ty = &global_context[&Symbol::new(op)];
      // Again, we assume that the expression here is fully applied, i.e. it is not a $
      let (_, ty) = op_ty.args_ret();
      let var_symb = Symbol::new(&fresh_name);
      let generalized_var = Sexp::String(fresh_name.clone());
      let new_lhs = substitute_sexp(&prop.eq.lhs, subexpr, &generalized_var);
      let new_rhs = substitute_sexp(&prop.eq.rhs, subexpr, &generalized_var);
      let lhs_vars = sexp_leaves(&new_lhs);
      let rhs_vars = sexp_leaves(&new_lhs);
      let mut new_params = prop.params.clone();
      // Only keep the vars that remain after substituting.
      new_params.retain(|(var, _ty)| lhs_vars.contains(&var.to_string()) || rhs_vars.contains(&var.to_string()));
      new_params.push((var_symb, ty));
      // println!("Genearlization candidate: {} = {}", new_lhs, new_rhs);
      output.push(Prop::new(Equation::new(new_lhs, new_rhs), new_params));
    }
  }
  output
}


impl ETermEquation {
  /// Add both sides of a raw equation to the egraph,
  /// producing an equation;
  /// if assume is true, also union the the two sides
  fn new(eq: &Equation, egraph: &mut Eg, assume: bool) -> Self {
    let lhs = ETerm::new(&eq.lhs, egraph);
    let rhs = ETerm::new(&eq.rhs, egraph);
    if assume {
      // Assume the premise
      egraph.union_trusted(lhs.id, rhs.id, format!("premise {}={}", lhs.sexp, rhs.sexp));
      egraph.rebuild();
    }
    Self { lhs, rhs }
  }

  /// Update variables in my expressions with their canonical forms
  fn update_variables(&self, subst: &IdSubst, egraph: &Eg) -> Self {
    Self {
      lhs: self.lhs.update_variables(subst, egraph),
      rhs: self.rhs.update_variables(subst, egraph),
    }
  }

}

/// When we make a new lemma and rewrites out of it, this tracks the the
/// rewrites we made as well as the information about the lemma.
pub struct LemmaRewrite {
  pub lhs_to_rhs: Option<(String, Rw)>,
  pub rhs_to_lhs: Option<(String, Rw)>,
  pub lemma_name: String,
  pub lemma_prop: Prop,
}

impl LemmaRewrite {
  pub fn new(lhs_to_rhs: Option<(String, Rw)>, rhs_to_lhs: Option<(String, Rw)>, lemma_name: String, lemma_prop: Prop) -> Self { Self { lhs_to_rhs, rhs_to_lhs, lemma_name, lemma_prop } }

  pub fn names_and_rewrites(&self) -> Vec<(String, Rw)> {
    self.lhs_to_rhs.iter().chain(self.rhs_to_lhs.iter()).cloned().collect()
  }

  pub fn rewrites(&self) -> Vec<Rw> {
    self.names_and_rewrites().into_iter().map(|(_, rw)| rw).collect()
  }

  pub fn add_to_rewrites(&self, rewrites: &mut HashMap<String, Rw>) {
    self.lhs_to_rhs.as_ref().map(|(name, rw)| {
      rewrites.entry(name.clone()).or_insert(rw.clone());
    });
    self.rhs_to_lhs.as_ref().map(|(name, rw)| {
      rewrites.entry(name.clone()).or_insert(rw.clone());
    });
  }


}

#[derive(Debug, Clone)]
enum ScrutineeType {
  Guard,
  Var,
}

#[derive(Debug, Clone)]
struct Scrutinee {
  pub name: Symbol,
  pub depth: usize,
  pub scrutinee_type: ScrutineeType,
}

impl Scrutinee {
  /// Creates a new var scrutinee
  pub fn new_var(name: Symbol, depth: usize) -> Self {
    Self {
      name,
      depth,
      scrutinee_type: ScrutineeType::Var
    }
  }
  /// Creates a new guard scrutinee (a scrutinee that will split a conditional
  /// expression).
  ///
  /// This will have depth 0 since it will always be fresh.
  pub fn new_guard(name: Symbol) -> Self {
    Self {
      name,
      depth: 0,
      scrutinee_type: ScrutineeType::Guard
    }
  }
}

/// These are all values that will not be modified throughout the course of
/// proving the goal which we will thread through new goals we create from it.
///
/// Contains things such as the global context or environment.
///
/// This is copyable because it only refers to shared references.
///
// TODO: Can we wrap most of this state in a lazy_static! block at initialization?
// - reductions and cvec_reductions might need to be cloned
//   * Or we could make the full set of reductions and cvec_reductions lazy_static!
//     and pass around a small set that corresponds to the keys which we can obtain
//     the rewrites from the global map. Cloning that shouldn't be too bad.
// - defns doesn't need to be threaded through in the first place.
// - searchers could be copied since it's for debugging
// - The rest should be safe to keep in a truly global block.
#[derive(Copy, Clone)]
pub struct GlobalSearchState<'a> {
  /// Environment
  pub env: &'a Env,
  /// Global context (i.e. constructors and top-level bindings)
  pub context: &'a Context,
  /// Rewrites are split into reductions (invertible rules) and lemmas
  /// (non-invertible rules). Lemmas may (and often will) change between goals,
  /// but reductions will always be the same.
  pub reductions: &'a Vec<Rw>,
  /// HACK: an identical copy to the reductions used for the cvec egraph.
  /// This is because of type system stuff.
  pub cvec_reductions: &'a Vec<CvecRw>,
  /// Definitions in a form amenable to proof emission
  pub defns: &'a Defns,
  /// Searchers for whether the LHS and RHS of some rewrite appears in our
  /// e-graph.
  pub searchers: &'a Vec<ConditionalSearcher<Pattern<SymbolLang>, Pattern<SymbolLang>>>,
}

impl<'a> GlobalSearchState<'a> {
    pub fn new(env: &'a Env, context: &'a Context, reductions: &'a Vec<Rw>, cvec_reductions: &'a Vec<CvecRw>, defns: &'a Defns, searchers: &'a Vec<ConditionalSearcher<Pattern<SymbolLang>, Pattern<SymbolLang>>>) -> Self { Self { env, context, reductions, cvec_reductions, defns, searchers } }
}

/// Proof goal
pub struct Goal<'a> {
  /// Goal name
  pub name: String,
  /// Equivalences we already proved
  pub egraph: Eg,
  /// Rewrites are split into reductions (invertible rules) and lemmas (non-invertible rules)
  /// Rewrites are split into reductions (invertible rules) and lemmas
  /// (non-invertible rules). Reductions - being unchanging - live in
  /// global_search_state.
  lemmas: HashMap<String, Rw>,
  /// Mapping from all universally-quantified variables of the goal to their types
  /// (note this includes both current and old variables, which have been case-split away)
  pub local_context: Context,
  /// Mapping from all universally-quantified variables of the goal to the e-classes they are stored in
  /// (note this includes both current and old variables, which have been case-split away)
  pub var_classes: IdSubst,
  /// The top-level parameters to the goal
  pub params: Vec<Symbol>,
  /// Variables we can case-split
  /// (i.e. the subset of local_context that have datatype types)
  scrutinees: VecDeque<Scrutinee>,
  /// Variables that we have already case split
  pub case_split_vars: HashSet<Symbol>,
  /// Instantiations of the induction hypothesis that are in the egraph
  grounding_instantiations: Vec<IdSubst>,
  /// The equation we are trying to prove
  pub eq: ETermEquation,
  /// If this is a conditional prop, the premises
  pub premises: Vec<ETermEquation>,
  /// If the goal is discharged, how it was discharged and an explanation of the
  /// proof
  pub explanation: Option<(ProofType, Explanation<SymbolLang>)>,
  /// Stores the expression each guard variable maps to
  guard_exprs: HashMap<String, Expr>,
  /// The global search state.
  pub global_search_state: GlobalSearchState<'a>,
}

impl<'a> Goal<'a> {
  /// Create top-level goal
  pub fn top(
    name: &str,
    prop: &Prop,
    premise: &Option<Equation>,
    global_search_state: GlobalSearchState<'a>,
  ) -> Self {
    let mut egraph: Eg = EGraph::default().with_explanations_enabled();
    let eq = ETermEquation::new(&prop.eq, &mut egraph, false);
    let premise = premise
      .as_ref()
      .map(|eq| ETermEquation::new(eq, &mut egraph, true));
    let var_classes = lookup_vars(&egraph, prop.params.iter().map(|(x, _)| x));

    let mut res = Self {
      name: name.to_string(),
      // The only instantiation we have so far is where the parameters map to themselves
      var_classes: var_classes.clone(),
      grounding_instantiations: vec![var_classes.clone()],
      egraph,
      explanation: None,
      lemmas: HashMap::new(),
      local_context: Context::new(),
      params: prop.params.iter().map(|(x, _)| *x).collect(),
      case_split_vars: HashSet::new(),
      guard_exprs: HashMap::new(),
      scrutinees: VecDeque::new(),
      eq,
      // Convert to a singleton list if the Option is Some, else the empty list
      premises: premise.into_iter().collect(),
      global_search_state,
    };
    // FIXME: this could really also be a reference. Probably not necessary
    // for efficiency reason but yeah.
    res.egraph.analysis.cvec_analysis.reductions = global_search_state.cvec_reductions.clone();
    for (name, ty) in &prop.params {
      res.add_scrutinee(*name, &ty, 0);
      res.local_context.insert(*name, ty.clone());
    }
    res.build_cvecs();
    res
  }

  /// Construct cvecs for the goal's parameters. We need type information in order
  /// to construct these, so they cannot be created automatically.
  fn build_cvecs(&mut self) {
    // Update the timestamp so that we ensure the new cvecs are applied.
    self.egraph.analysis.cvec_analysis.current_timestamp += 1;
    for name in self.params.iter() {
      let ty = &self.local_context[name];
      if !ty.is_arrow() {
        let var_id = self.var_classes[name];
        let var_cvec = self.egraph.analysis.cvec_analysis.make_cvec_for_type(&ty, self.global_search_state.env, &self.global_search_state.context);
        let mut analysis = self.egraph[var_id].data.clone();
        analysis.timestamp = self.egraph.analysis.cvec_analysis.current_timestamp;
        analysis.cvec_data = var_cvec;
        self.egraph.set_analysis_data(var_id, analysis);
        // println!("var {} has id {}", name, var_id);
      }
    }
    self.egraph.rebuild();
  }

  pub fn cvecs_valid(&mut self) -> bool {
    self.egraph.analysis.cvec_analysis.saturate();
    let lhs_cvec = &self.egraph[self.eq.lhs.id].data.cvec_data;
    let rhs_cvec = &self.egraph[self.eq.rhs.id].data.cvec_data;
    let res = cvecs_equal(&self.egraph.analysis.cvec_analysis, lhs_cvec, rhs_cvec);
    res == Some(true)
  }

  // FIXME: Can we figure out if it's possible to implement clone in a reasonable way?
  // Maybe we shouldn't even have this function.
  pub fn duplicate(&self) -> Self {
    Goal {
      name: self.name.clone(),
      egraph: self.egraph.clone(),
      // TODO: Verify if this is true
      lemmas: HashMap::new(), // the lemmas will be re-generated immediately anyway
      local_context: self.local_context.clone(),
      var_classes: self.var_classes.clone(),
      params: self.params.clone(),
      case_split_vars: self.case_split_vars.clone(),
      scrutinees: self.scrutinees.clone(),
      grounding_instantiations: self.grounding_instantiations.clone(),
      eq: self.eq.clone(),
      premises: self.premises.clone(),
      // If we reach this point, I think we won't have an explanation
      explanation: None,
      guard_exprs: self.guard_exprs.clone(),
      global_search_state: self.global_search_state,
    }
  }

  /// Saturate the goal by applying all available rewrites
  pub fn saturate(&mut self, top_lemmas: &HashMap<String, Rw>) {
    let rewrites = self.global_search_state.reductions.iter().chain(self.lemmas.values()).chain(top_lemmas.values());
    let lhs_id = self.eq.lhs.id;
    let rhs_id = self.eq.rhs.id;
    let runner = Runner::default()
      .with_explanations_enabled()
      .with_egraph(self.egraph.to_owned())
      .with_hook(move |runner| {
        // Stop iteration if we have proven lhs == rhs
        if runner.egraph.find(lhs_id) == runner.egraph.find(rhs_id) {
          Err("Goal proven".to_string())
        } else {
          Ok(())
        }
      })
      .run(rewrites);
    self.egraph = runner.egraph;
  }

  /// Look to see if we have proven the goal somehow. Note that this does not
  /// perform the actual proof search, it simply checks if the proof exists.
  pub fn find_proof(&mut self) -> Option<(ProofType, Explanation<SymbolLang>)> {
    find_proof(&self.eq, &mut self.egraph)
  }

  /// Check whether an expression is reducible using this goal's reductions
  /// NOTE: This is largely not necessary when we have destructive rewrites
  /// enabled (the default). This is why it is by default disabled.
  pub fn is_reducible(&self, expr: &Expr) -> bool {
    let mut local_graph: Eg = Default::default();
    local_graph.add_expr(expr);
    local_graph.rebuild();
    for reduction in self.global_search_state.reductions {
      if !reduction.search(&local_graph).is_empty() {
        return true;
      }
    }
    false
  }

  /// Creates rewrites from all of the expressions in lhs_id to all of the
  /// expressions in rhs_id.
  ///
  /// Returns a hashmap of the rewrites as well as a vector of LemmaRewrites
  /// describing each rewrite.
  ///
  /// The rewrites will have a termination (soundness) check if
  /// add_termination_check is true, otherwise they will not.
  ///
  /// The rewrites will each be named lemma_n.
  fn make_lemma_rewrites_from_all_exprs(&self, lhs_id: Id, rhs_id: Id, premises: Vec<ETermEquation>, state: &mut ProofState, add_termination_check: bool) -> (HashMap<String, Rw>, Vec<LemmaRewrite>) {
    let exprs = get_all_expressions(&self.egraph, vec![lhs_id, rhs_id]);
    let is_var = |v| self.local_context.contains_key(v);
    let mut rewrites = self.lemmas.clone();
    let mut lemma_rws = vec!();
    for lhs_expr in exprs.get(&lhs_id).unwrap() {
      let lhs: Pattern<SymbolLang> = to_pattern(lhs_expr, is_var);
      if (CONFIG.irreducible_only && self.is_reducible(lhs_expr)) || has_guard_wildcards(&lhs) {
        continue;
      }
      for rhs_expr in exprs.get(&rhs_id).unwrap() {
        if state.timeout() {
          return (rewrites, lemma_rws);
        }
        let lemma_name = state.fresh_lemma_name();

        if let Some(lemma_rw) = self.make_lemma_rewrite(lhs_expr, rhs_expr, &premises, add_termination_check, lemma_name) {
          // Add the rewrites (if lemma_rw is some at least one is guaranteed to exist).
          lemma_rw.add_to_rewrites(&mut rewrites);
          lemma_rws.push(lemma_rw);
        }

      }
    }
    (rewrites, lemma_rws)
  }

  fn make_lemma_rewrite(&self, lhs_expr: &Expr, rhs_expr: &Expr, premises: &Vec<ETermEquation>, add_termination_check: bool, lemma_name: String)
                        -> Option<LemmaRewrite> {
    let is_var = |v| self.local_context.contains_key(v);

    // NOTE: (CK) Before we would not recreate the lhs from lhs_expr every time we made a lemma rewrite since we did nested for loops
    // for lhs_expr {
    //   let lhs = ...
    //   for rhs_expr {
    //   ...
    //
    // which meant we just needed to clone it.
    //
    // I don't think this is a huge hit to efficiency though. If we cared, we
    // could instead loop over all lhs and rhs exprs first and precompute their
    // patterns + figure out which ones we don't need to consider.
    let lhs: Pattern<SymbolLang> = to_pattern(lhs_expr, is_var);
    if (CONFIG.irreducible_only && self.is_reducible(lhs_expr)) || has_guard_wildcards(&lhs) {
      return None;
    }

    let rhs: Pattern<SymbolLang> = to_pattern(rhs_expr, is_var);
    if (CONFIG.irreducible_only && self.is_reducible(rhs_expr)) || has_guard_wildcards(&rhs) {
      return None;
    }

    let lhs_vars = var_set(&lhs);
    let rhs_vars = var_set(&rhs);
    let lemma_vars = lhs_vars.union(&rhs_vars).cloned().collect();

    // If any of my premises contain variables that are not present in lhs or rhs,
    // skip because we don't know how to check such a premise
    if !premises.iter().all(|eq| {
      let premise_lhs_vars = var_set(&to_pattern(&eq.lhs.expr, is_var));
      let premise_rhs_vars = var_set(&to_pattern(&eq.rhs.expr, is_var));
      let premise_vars: HashSet<Var> =
        premise_lhs_vars.union(&premise_rhs_vars).cloned().collect();
      premise_vars.is_subset(&lemma_vars)
    }) {
      return None;
    }

    // Pick out those variables that occur in the lemma
    let lemma_var_classes: IdSubst = self
      .var_classes
      .iter()
      .filter(|(x, _)| lemma_vars.contains(&to_wildcard(x)))
      .map(|(x, id)| (*x, *id))
      .collect();
    let params: Vec<(Symbol, Type)> = lemma_var_classes.keys().map(|var|{
      (*var, self.local_context.get(var).unwrap().clone())
    }).collect();

    let condition = Soundness {
      free_vars: lemma_var_classes,
      premises: premises.clone(),
    };
    let rewrite_eq = Equation::from_exprs(lhs_expr, rhs_expr);
    let mut lemma_rw = LemmaRewrite {
      lhs_to_rhs: None,
      rhs_to_lhs: None,
      lemma_name: lemma_name.clone(),
      lemma_prop: Prop {
        eq: rewrite_eq,
        params: params.clone(),
      }
    };
    if rhs_vars.is_subset(&lhs_vars) {
      // if rhs has no extra wildcards, create a lemma lhs => rhs
      let lhs_to_rhs = Goal::make_rewrite(lhs.clone(), rhs.clone(), condition.clone(), lemma_name.clone(), add_termination_check);
      lemma_rw.lhs_to_rhs = Some(lhs_to_rhs);

      if CONFIG.single_rhs {
        return Some(lemma_rw);
      };
    }
    if lhs_vars.is_subset(&rhs_vars) {
      // if lhs has no extra wildcards, create a lemma rhs => lhs;
      // NOTE: (CK) This below comment is no longer true when our termination check is more complicated.
      // in non-cyclic mode, a single direction of IH is always sufficient
      // (because grounding adds all instantiations we could possibly care about).
      let rhs_to_lhs = Goal::make_rewrite(rhs.clone(), lhs.clone(), condition.clone(), lemma_name.clone(), add_termination_check);
      lemma_rw.rhs_to_lhs = Some(rhs_to_lhs);
    }
    let has_lemma_rw = lemma_rw.lhs_to_rhs.is_some() || lemma_rw.rhs_to_lhs.is_some();
    if !has_lemma_rw {
      warn!("cannot create a lemma from {} and {}", lhs, rhs);
      None
    } else {
      Some(lemma_rw)
    }
  }

  /// Before creating a lemma with premises, we need to update the variables
  /// in the premises with their canonical forms in terms of the current goal
  /// variables
  fn update_premises(&self) -> Vec<ETermEquation> {
    self
      .premises
      .iter()
      .map(|eq| eq.update_variables(&self.var_classes, &self.egraph))
      .collect()
  }

  /// Create a rewrite `lhs => rhs` which will serve as the lemma ("induction hypothesis") for a cycle in the proof;
  /// here lhs and rhs are patterns, created by replacing all scrutinees with wildcards;
  /// soundness requires that the pattern only apply to variable tuples smaller than the current scrutinee tuple.
  fn add_lemma_rewrites(&self, state: &mut ProofState) -> HashMap<String, Rw> {
    // Special case: the first time we add lemmas (i.e. when there are no
    // previous lemmas), we will make lemma rewrites out of the lhs and rhs only
    // and we will use the special IH name.
    if self.lemmas.is_empty() {
      let premises = self.update_premises();
      let mut rewrites = self.lemmas.clone();
      // In the non-cyclic case, only use the original LHS and RHS
      // and only if no other lemmas have been added yet
      let lemma_rw = self.make_lemma_rewrite(&self.eq.lhs.expr, &self.eq.rhs.expr, &premises, true, state.ih_lemma_name.clone()).unwrap();
      lemma_rw.add_to_rewrites(&mut rewrites);
      return rewrites;
    }
    // Otherwise, we only create lemmas when we are operating in the cyclic mode
    if CONFIG.is_cyclic() {
      self.make_cyclic_lemma_rewrites(state, true).0
    } else {
      self.lemmas.clone()
    }

  }

  /// Creates cyclic lemmas from the current goal.
  fn make_cyclic_lemma_rewrites(&self, state: &mut ProofState, add_termination_check: bool) -> (HashMap<String, Rw>, Vec<LemmaRewrite>) {
    let lhs_id = self.egraph.find(self.eq.lhs.id);
    let rhs_id = self.egraph.find(self.eq.rhs.id);

    let premises = self.update_premises();
    self.make_lemma_rewrites_from_all_exprs(lhs_id, rhs_id, premises, state, add_termination_check)
  }

  /// Add a rewrite `lhs => rhs` to `rewrites` if not already present
  fn make_rewrite(lhs: Pat, rhs: Pat, cond: Soundness, lemma_name: String, add_termination_check: bool) -> (String, Rw) {
    // TODO: I think we should put just the lemma name and rewrite direction now
    // that we can record information about the lemmas elsewhere.
    let name = format!("{}-{}={}", lemma_name, lhs, rhs);
    warn!("creating{}lemma: {} => {}", if add_termination_check {" "} else {" unconditional "}, lhs, rhs);
    let rw =
      if add_termination_check {
        Rewrite::new(
          name.clone(),
          ConditionalSearcher {
            condition: cond,
            searcher: lhs,
          },
          rhs,
        )
        .unwrap()
      } else {
        Rewrite::new(
          name.clone(),
          lhs,
          rhs,
        )
        .unwrap()
      };
    (name, rw)
  }

  /// Add var as a scrutinee if its type `ty` is a datatype
  fn add_scrutinee(&mut self, var: Symbol, ty: &Type, depth: usize) {
    if let Ok((dt, _)) = ty.datatype() {
      if self.global_search_state.env.contains_key(&Symbol::from(dt)) {
        self.scrutinees.push_back(Scrutinee::new_var(var, depth));
      }
    }
  }

  /// If the egraph contains ITEs whose condition is "irreducible"
  /// (i.e. not equivalent to a constant or a scrutinee variable),
  /// add a fresh scrutinee to its eclass, so that we can match on it.
  fn split_ite(&mut self) {
    let guard_var = "?g".parse().unwrap();
    // Pattern "(ite ?g ?x ?y)"
    let searcher: Pattern<SymbolLang> = format!("({} {} ?x ?y)", *ITE, guard_var).parse().unwrap();
    let matches = searcher.search(&self.egraph);
    // Collects class IDs of all stuck guards;
    // it's a map because the same guard can match more than once, but we only want to add a new scrutinee once
    let mut stuck_guards = HashMap::new();
    for m in matches {
      for subst in m.substs {
        let guard_id = *subst.get(guard_var).unwrap();
        if let CanonicalForm::Stuck(_) = self.egraph[guard_id].data.canonical_form_data {
          stuck_guards.insert(guard_id, subst);
        }
      }
    }
    // Iterate over all stuck guard eclasses and add a new scrutinee to each
    for (guard_id, subst) in stuck_guards {
      let fresh_var = Symbol::from(format!("{}{}", GUARD_PREFIX, guard_id));
      // This is here only for logging purposes
      let expr = Extractor::new(&self.egraph, AstSize).find_best(guard_id).1;
      let add_scrutinee_message =
        format!("adding scrutinee {} to split condition {}", fresh_var, expr);
      warn!("{}", add_scrutinee_message);
      self
        .local_context
        .insert(fresh_var, BOOL_TYPE.parse().unwrap());
      // We are adding the new scrutinee to the front of the deque,
      // because we want to split conditions first, since they don't introduce new variables
      self.scrutinees.push_front(Scrutinee::new_guard(fresh_var));
      let new_node = SymbolLang::leaf(fresh_var);
      let new_pattern_ast = vec![ENodeOrVar::ENode(new_node.clone())].into();
      let guard_var_pattern_ast = vec![ENodeOrVar::Var(guard_var)].into();
      self.guard_exprs.insert(fresh_var.to_string(), expr);
      self.egraph.union_instantiations(
        &guard_var_pattern_ast,
        &new_pattern_ast,
        &subst,
        add_scrutinee_message,
      );
    }
    self.egraph.rebuild();
  }

  /// Consume this goal and add its case splits to the proof state
  fn case_split(self, scrutinee: Scrutinee, state: &mut ProofState<'a>) {
    let new_lemmas = self.add_lemma_rewrites(state);

    let var_str = scrutinee.name.to_string();
    warn!("case-split on {}", scrutinee.name);
    let var_node = SymbolLang::leaf(scrutinee.name);
    let var_pattern_ast: RecExpr<ENodeOrVar<SymbolLang>> = vec![ENodeOrVar::ENode(var_node.clone())].into();
    // Get the type of the variable, and then remove the variable
    let ty = match self.local_context.get(&scrutinee.name) {
      Some(ty) => ty,
      None => panic!("{} not in local context", scrutinee.name),
    };
    // Convert to datatype name
    let dt = Symbol::from(ty.datatype().unwrap().0);
    // Get the constructors of the datatype
    let (_, cons) = self.global_search_state.env.get(&dt).unwrap();
    // We will add this to state.proof to describe the case split.
    let mut instantiated_cons_and_goals: Vec<(String, String)> = vec![];

    // (we process constructors in reverse order so that base case ends up at the top of the stack)
    for &con in cons.iter().rev() {
      let mut new_goal = self.duplicate();
      new_goal.case_split_vars.insert(scrutinee.name);
      new_goal.name = format!("{}:", self.name);
      new_goal.lemmas = new_lemmas.clone();

      // Get the types of constructor arguments
      let con_ty = self.global_search_state.context.get(&con).unwrap();
      let con_args = Goal::instantiate_constructor(con_ty, ty);
      // For each argument: create a fresh variable and add it to the context and to scrutinees
      let mut fresh_vars = vec![];

      new_goal.egraph.analysis.cvec_analysis.current_timestamp += 1;

      for (i, arg_type) in con_args.iter().enumerate() {
        let fresh_var_name = format!("{}_{}{}", scrutinee.name, self.egraph.total_size(), i);
        let fresh_var = Symbol::from(fresh_var_name.clone());
        fresh_vars.push(fresh_var);
        // Add new variable to context
        new_goal.local_context.insert(fresh_var, arg_type.clone());
        new_goal.add_scrutinee(fresh_var, arg_type, scrutinee.depth + 1);
        let id = new_goal.egraph.add(SymbolLang::leaf(fresh_var));
        new_goal.var_classes.insert(fresh_var, id);
        // We can only generate a cvec for non-arrow types.
        if !arg_type.is_arrow() {
          // new_goal.egraph.analysis.cvec_analysis.timestamp += 1;
          let fresh_var_cvec = new_goal.egraph.analysis.cvec_analysis.make_cvec_for_type(arg_type, self.global_search_state.env, &self.global_search_state.context);
          let mut analysis = new_goal.egraph[id].data.clone();
          analysis.timestamp = new_goal.egraph.analysis.cvec_analysis.current_timestamp;
          analysis.cvec_data = fresh_var_cvec;
          new_goal.egraph.set_analysis_data(id, analysis);
        }

        if CONFIG.add_grounding && ty == arg_type {
          // This is a recursive constructor parameter:
          // add new grounding instantiations replacing var with fresh_var
          new_goal.add_grounding(scrutinee.name, fresh_var);
        }
      }

      // Create an application of the constructor to the fresh vars
      let fresh_var_strings_iter = fresh_vars.iter().map(|x| x.to_string());
      let con_app_string = format!(
        "({} {})",
        con,
        fresh_var_strings_iter
          .clone()
          .collect::<Vec<String>>()
          .join(" ")
      );
      let con_app: Expr = con_app_string.parse().unwrap();

      new_goal.name = format!("{}{}={}", new_goal.name, scrutinee.name, con_app);

      instantiated_cons_and_goals.push((con_app_string, new_goal.name.clone()));
      // new_goal.egraph.analysis.cvec_analysis.timestamp += 1;

      // let var_id = new_goal.egraph.lookup(var_node.clone()).unwrap();
      // println!("egraph pre union: {:?}", new_goal.egraph.dump());
      // Add con_app to the new goal's egraph and union it with var
      new_goal.egraph.add_expr(&con_app);
      // Not sure if it's proper to use new_goal.name here
      new_goal.egraph.union_instantiations(
        &var_pattern_ast,
        &rec_expr_to_pattern_ast(con_app.clone()),
        &Subst::default(),
        format!("case-split:{}", new_goal.name),
      );
      // Remove old variable from the egraph and context
      remove_node(&mut new_goal.egraph, &var_node);
      // println!("id: {}", con_app_id);
      // for node in new_goal.egraph[con_app_id].nodes.iter() {
      //   println!("node: {:?}", node);
      // }
      // println!("egraph: {:?}", new_goal.egraph.dump());
      // if count == 3 {
      //   panic!();
      // }

      // new_goal.egraph.analysis.cvec_analysis.timestamp += 1;
      new_goal.egraph.rebuild();

      // // After we instantiate the variable, its class's new cvec is just the instantiated value.
      // let cvec_con_app_id = new_goal.egraph.analysis.cvec_analysis.cvec_egraph.borrow_mut().add_expr(&con_app);
      // let mut analysis = new_goal.egraph[con_app_id].data.clone();
      // analysis.cvec_data = Cvec::Stuck(cvec_con_app_id);
      // new_goal.egraph.set_analysis_data(con_app_id, analysis);

      // new_goal.egraph.rebuild();
      // let cvec_var_id = new_goal.egraph.analysis.cvec_analysis.cvec_egraph.borrow().lookup(var_node.clone()).unwrap();
      // new_goal.egraph.analysis.cvec_analysis.cvec_egraph.borrow_mut().union_trusted(cvec_var_id, cvec_con_app_id, "case split");
      // new_goal.egraph.analysis.cvec_analysis.cvec_egraph.borrow_mut().rebuild();
      // remove_node(&mut new_goal.egraph.analysis.cvec_analysis.cvec_egraph.borrow_mut(), &var_node);

      // In cyclic mode: add the guard to premises,
      if CONFIG.is_cyclic() && var_str.starts_with(GUARD_PREFIX) && self.guard_exprs.contains_key(&var_str) {
        let lhs = ETerm::from_expr(self.guard_exprs[&var_str].clone(), &new_goal.egraph);
        let rhs = ETerm::from_expr(con_app, &new_goal.egraph);
        let eq = ETermEquation { lhs, rhs };
        new_goal.premises.push(eq);
      }

      // Add the subgoal to the proof state
      state.goals.push_back(new_goal);
    }
    // We split on var into the various instantiated constructors and subgoals.
    //
    // If the var is an ITE split, we will add the condition that was split on
    // to our proof term. This is necessary because for ITE splits we introduce
    // a new variable that we bind an expression to.
    match scrutinee.scrutinee_type {
      ScrutineeType::Guard => {
        // There should only be two cases.
        assert_eq!(instantiated_cons_and_goals.len(), 2);
        state.proof_info.proof.insert(
          self.name,
          ProofTerm::ITESplit(
            var_str.clone(),
            self.guard_exprs[&var_str].to_string(),
            instantiated_cons_and_goals,
          ),
        );
      }
      ScrutineeType::Var => {
        state.proof_info.proof.insert(
          self.name,
          ProofTerm::CaseSplit(var_str, instantiated_cons_and_goals),
        );
      }
    };
  }

  fn find_blocking(&self, state: &ProofState) -> (HashSet<Symbol>, HashSet<Id>) {
    let mut blocking_vars: HashSet<_> = HashSet::default();
    let mut blocking_exprs: HashSet<Id> = HashSet::default();

    let mut lhs_descendents = HashSet::default();
    self.compute_descendents(self.eq.lhs.id, &mut lhs_descendents);

    let mut rhs_descendents = HashSet::default();
    self.compute_descendents(self.eq.rhs.id, &mut rhs_descendents);

    for reduction in self.global_search_state.reductions {
      let x = reduction.searcher.get_pattern_ast().unwrap();
      let sexp = symbolic_expressions::parser::parse_str(&x.to_string()).unwrap();

      // Hack to dedup the new patterns (sexps) we generated
      let mut new_sexps: Vec<Sexp> = self
        .analyze_sexp_for_blocking_vars(&sexp)
        .into_iter()
        .map(|x| x.to_string())
        .collect::<HashSet<_>>()
        .into_iter()
        .map(|x| symbolic_expressions::parser::parse_str(x.as_str()).unwrap())
        .collect();

      // the patterns we generated contained only ? instead of ?var, so we go and add fresh variable names everywhere
      for ns in new_sexps.iter_mut() {
        *ns = self.gen_fresh_vars(ns.clone(), 1);
      }

      // use these patterns to search over the egraph
      for new_sexp in new_sexps {
        if state.timeout() {
          return (blocking_vars, blocking_exprs);
        }
        let mod_searcher: Pattern<SymbolLang> = new_sexp.to_string().parse().unwrap();

        // for each new pattern, find the pattern variables in blocking positions so that we can use them to look up the substs later
        let bvs: Vec<Var> = mod_searcher
          .vars()
          .iter()
          .filter(|&x| x.to_string().contains("block_"))
          .cloned()
          .collect();

        let matches = mod_searcher.search(&self.egraph);

        // let extractor = Extractor::new(&self.egraph, AstSize);

        // look at the e-class analysis for each matched e-class, if any of them has a variable, use it
        for m in matches {
          for subst in m.substs {
            for v in &bvs[0..] {
              if let Some(&ecid) = subst.get(*v) {
                match &self.egraph[ecid].data.canonical_form_data {
                  CanonicalForm::Var(n) => {
                    blocking_vars.insert(n.op);
                  }
                  CanonicalForm::Stuck(_) | CanonicalForm::Const(_) => {
                    if lhs_descendents.contains(&ecid) && rhs_descendents.contains(&ecid) {
                      blocking_exprs.insert(ecid);
                      // let expr = extractor.find_best(ecid).1;
                      // blocking_exprs.insert(expr.to_string());
                    }
                  }
                  _ => (),
                }
              }
            }
          }
        }

      }
    }
    // println!("Searching for blocking exprs...");
    // for blocking_expr in blocking_exprs {
    //   println!("Blocking expr: {}", blocking_expr);
    // }
    (blocking_vars, blocking_exprs)
  }

  fn compute_descendents(&self, class: Id, descendents: &mut HashSet<Id>) {
    if descendents.contains(&class) {
      return;
    }
    descendents.insert(class);
    for node in self.egraph[class].nodes.iter() {
      for child in node.children() {
        self.compute_descendents(*child, descendents);
      }
    }
  }

  /// Gets the next variable to case split on using the blocking var analysis
  fn next_scrutinee(&mut self, mut blocking_vars: HashSet<Symbol>) -> Option<Scrutinee> {
    let blocking = self
      .scrutinees
      .iter()
      .find_position(|s| blocking_vars.contains(&s.name));

    // Add the vars we already have case split on, since those were previously
    // blocking. This is important for our soundness check, since we skip
    // checking any variables which are not blocking.
    blocking_vars.extend(&self.case_split_vars);
    // Record into the e-graph analysis so that we can
    // use this infromation in the soundness check
    self.egraph.analysis.blocking_vars = blocking_vars;

    if blocking.is_none() {
      return None;
    }

    let var_idx = blocking.unwrap().0;
    self.scrutinees.remove(var_idx)
  }

  fn sexp_is_constructor(&self, sexp: &Sexp) -> bool {
    match sexp {
      Sexp::String(s) => is_constructor(s),
      Sexp::List(v) => is_constructor(&v[0].string().unwrap()),
      _ => false,
    }
  }

  fn gen_fresh_vars(&self, sexp: Sexp, mut idx: i32) -> Sexp {
    let qm = "?".to_string();
    match sexp {
      Sexp::String(s) if s == qm => Sexp::String(format!("?block_{}", idx)),
      Sexp::List(v) => Sexp::List(
        v.iter()
          .map(|x| {
            idx = idx + 1;
            self.gen_fresh_vars(x.clone(), idx + 1)
          })
          .collect(),
      ),
      _ => sexp,
    }
  }

  /// Looks at an sexp representing a rewrite (or part of a rewrite) to determine where blocking vars might be
  /// e.g. if we have a rule that looks like `foo Z (Cons Z ?xs)` => ...)
  /// then we want to generate patterns like
  ///   1. `foo ?fresh1 (Cons Z ?xs)`
  ///   2. `foo ?fresh1 ?fresh2`
  ///   3. `foo ?fresh1 (Cons ?fresh2 ?xs)`
  ///   4. `foo Z ?fresh2`
  ///   5. `foo Z (Cons ?fresh1 ?xs)`
  fn analyze_sexp_for_blocking_vars(&self, sexp: &Sexp) -> Vec<Sexp> {
    let mut new_exps: Vec<Sexp> = vec![];
    new_exps.push(sexp.clone());

    // If this sexp is a constructor application, replace it by ?
    if self.sexp_is_constructor(sexp) {
      // for now, just indicate by "?" each position where we could have a blocking var, and later go and replace them with fresh vars
      let fresh_var_indicator = "?";
      new_exps.push(Sexp::String(fresh_var_indicator.to_string()));
    }

    // also recursively analyse its children to find other potential blocking arguments
    match sexp {
      Sexp::List(v) => {
        let head = &v[0];
        let mut all_replacements: Vec<Vec<Sexp>> = vec![];
        for (_, sub_arg) in v[1..].iter().enumerate() {
          all_replacements.push(self.analyze_sexp_for_blocking_vars(sub_arg));
        }
        // get all possible subsets of the replacements (i.e. every subset of constructor applications replaced by fresh pattern vars)
        let all_combinations = cartesian_product(&all_replacements);
        for mut combination in all_combinations {
          combination.insert(0, head.clone());
          new_exps.push(Sexp::List(combination));
        }
      }
      _ => {}
    };

    return new_exps;
  }

  /// Save e-graph to file
  fn save_egraph(&self) {
    let filename = CONFIG.output_directory.join(format!("{}.png", self.name));
    let verbosity = format!("-q{}", CONFIG.log_level as usize);
    let dot = self.egraph.dot();
    dot
      .run_dot([
        "-Tpng",
        verbosity.as_str(),
        "-o",
        &filename.to_string_lossy(),
      ])
      .unwrap();
  }

  /// Given a polymorphic constructor type and a concrete instantiation of a datatype,
  /// return the concrete types of constructor arguments.
  fn instantiate_constructor(con_ty: &Type, actual: &Type) -> Vec<Type> {
    let (args, ret) = con_ty.args_ret();
    let instantiations = find_instantiations(&ret.repr, &actual.repr, is_var).unwrap();
    let ret = args
      .iter()
      .map(|arg| Type::new(resolve_sexp(&arg.repr, &instantiations)))
      .collect();
    ret
  }

  /// Add new grounding instantiations
  /// that replace parent with child in previous instantiations
  fn add_grounding(&mut self, parent: Symbol, child: Symbol) {
    // First gather all the terms we want to instantiate:
    // take both sides of the equation and all the premises
    let mut sides = vec![&self.eq.lhs, &self.eq.rhs];
    for premise in self.premises.iter() {
      sides.push(&premise.lhs);
      sides.push(&premise.rhs);
    }

    // Now create new instantiations from existing ones
    let mut new_instantiations = vec![];
    for inst in self.grounding_instantiations.iter() {
      let replaced_canonicals: Vec<(Symbol, ETerm, bool)> = self
        .params
        .iter()
        .map(|x| {
          // Which class was this param instantiated to?
          let id = inst.get(x).unwrap();
          // Parameters must be canonical (at least in a clean state)
          let canonical = CanonicalFormAnalysis::extract_canonical(&self.egraph, *id).unwrap();
          // Try replacing the case-split variable with its child
          let (new_expr, replaced) = replace_var(&canonical, parent, child);
          let eterm = if replaced {
            ETerm::new_from_expr(&new_expr, &mut self.egraph)
          } else {
            ETerm::from_expr(new_expr, &self.egraph)
          };
          (*x, eterm, replaced)
        })
        .collect();
      // If any of the canonical forms had a replacement, add a new instantiation:
      if replaced_canonicals.iter().any(|(_, _, b)| *b) {
        let new_instantiation = replaced_canonicals
          .iter()
          .map(|(x, e, _)| (x.to_string(), e.sexp.clone()))
          .collect();
        // For each new instantiation, instantiate all the sides and add them to the egraph
        for term in sides.iter() {
          let new_term = resolve_sexp(&term.sexp, &new_instantiation);
          ETerm::new(&new_term, &mut self.egraph);
        }
        // Add the new instantiation to the list of grounding instantiations
        let new_subst = replaced_canonicals
          .iter()
          .map(|(x, e, _)| (*x, e.id))
          .collect();
        new_instantiations.push(new_subst);
      }
    }

    // Add the new instantiations to the list of grounding instantiations
    self.grounding_instantiations.extend(new_instantiations);
  }

  fn search_for_cc_lemmas(&mut self, state: &mut ProofState) -> Vec<Prop> {
    let mut lemmas = vec!();
    self.egraph.analysis.cvec_analysis.saturate();
    let resolved_lhs_id = self.egraph.find(self.eq.lhs.id);
    let resolved_rhs_id = self.egraph.find(self.eq.rhs.id);
    let class_ids: Vec<Id> = self.egraph.classes().map(|c| c.id).collect();
    for class_1_id in &class_ids {
      for class_2_id in &class_ids {
        if state.timeout() {
          return lemmas;
        }
        // Resolve the ids because as we union things, we might make more
        // equalities.
        let class_1_id = self.egraph.find(*class_1_id);
        let class_2_id = self.egraph.find(*class_2_id);
        // Don't try to union two of the same e-class.
        //
        // Also, only try pairs (id1, id2) where id1 < id2.
        // Since unioning doesn't care about order, we can avoid
        // trying classes redundantly.
        if class_1_id >= class_2_id {
          continue;
        }

        // NOTE: We no longer skip here because we need to generalize sometimes
        // Don't try unioning the LHS and RHS, we've seen those already.
        // if class_1_id == resolved_lhs_id && class_2_id == resolved_rhs_id
        //   || class_1_id == resolved_rhs_id && class_2_id == resolved_lhs_id {
        //     continue
        // }

        if let Some(true) = cvecs_equal(&self.egraph.analysis.cvec_analysis, &self.egraph[class_1_id].data.cvec_data, &self.egraph[class_2_id].data.cvec_data) {
          let class_1_canonical = &self.egraph[class_1_id].data.canonical_form_data;
          let class_2_canonical = &self.egraph[class_2_id].data.canonical_form_data;
          match (class_1_canonical, class_2_canonical) {
            (CanonicalForm::Const(c1_node), CanonicalForm::Const(c2_node)) => {
              let num_differing_children: usize = zip(c1_node.children(), c2_node.children()).map(|(child_1, child_2)|{
                if child_1 != child_2 {
                  0
                } else {
                  1
                }
              }).sum();
              // There is a simpler CC lemma to prove.
              if num_differing_children <= 1 {
                continue;
              }
            }
            _ => {}
          }
          let (_rewrites, rewrite_infos) = self.make_lemma_rewrites_from_all_exprs(class_1_id, class_2_id, vec!(), state, false);
          let new_rewrite_eqs: Vec<Prop> = rewrite_infos.into_iter().map(|rw_info| rw_info.lemma_prop).collect();
          // let new_egraph = self.egraph.clone();
          // let rewrites = self.reductions.iter().chain(new_rewrites.values());
          // let mut runner = Runner::default()
          //   .with_explanations_enabled()
          //   .with_egraph(new_egraph)
          //   .run(rewrites);
          // let (explanation, valid) = Goal::get_explanation_and_validity(&self.eq, &mut runner.egraph);
          // if explanation.is_none() {
          //   continue;
          // }
          // if valid && explanation.is_none() {
          //   println!("Skipping useful CC lemma {} = {} because no explanation came from its use", e1, e2);
          // }
          if new_rewrite_eqs.is_empty() {
            continue;
          }

          if CONFIG.cc_lemmas_generalization {
            let fresh_name = format!("fresh_{}", self.egraph.total_size());
            let generalized_eqs = new_rewrite_eqs.iter().flat_map(|new_rewrite_eq| find_generalizations_prop(&new_rewrite_eq, self.global_search_state.context, fresh_name.clone()));

            lemmas.extend(generalized_eqs);
          }

          // Optimization: skip adding any lemmas that would be subsumed by a cyclic lemma
          if !(class_1_id == resolved_lhs_id && class_2_id == resolved_rhs_id
            || class_1_id == resolved_rhs_id && class_2_id == resolved_lhs_id) {
            lemmas.extend(new_rewrite_eqs);
          }
        }
      }
    }
    lemmas
  }

  fn compute_parents(&self, class: Id, parents_map: &mut HashMap<Id, HashSet<(Id, usize)>>, seen: &mut HashSet<Id>) {
    if seen.contains(&class) {
      return;
    }
    seen.insert(class);
    for (i, node) in self.egraph[class].nodes.iter().enumerate() {
      for child in node.children() {
        parents_map.entry(*child)
                   .and_modify(|e| {e.insert((class, i));})
                   .or_insert(vec!((class, i)).into_iter().collect());
        self.compute_parents(*child, parents_map, seen);
      }
    }
  }

  fn _print_lhs_rhs(&self) {
    let lhs_id = self.egraph.find(self.eq.lhs.id);
    let rhs_id = self.egraph.find(self.eq.rhs.id);

    let exprs = get_all_expressions(&self.egraph, vec![lhs_id, rhs_id]);

    println!("LHS Exprs:");
    for lhs_expr in exprs.get(&lhs_id).unwrap() {
      if CONFIG.irreducible_only && self.is_reducible(lhs_expr) {
        continue;
      }
      println!("{}", lhs_expr);
    }

    println!("RHS Exprs:");
    for rhs_expr in exprs.get(&rhs_id).unwrap() {
      if CONFIG.irreducible_only && self.is_reducible(rhs_expr) {
        continue;
      }
      println!("{}", rhs_expr);
    }

  }

  fn all_parents(&self, start_class: Id, child_to_parent: &HashMap<Id, HashSet<(Id, usize)>>, parent_to_child_index: &mut HashMap<Id, usize>, seen: &mut HashSet<Id>) {
    if seen.contains(&start_class) {
      return;
    }
    seen.insert(start_class);

    child_to_parent.get(&start_class).map(|parents|{
      parents.iter().for_each(|(parent_class, parent_node_index)|{
        parent_to_child_index.insert(*parent_class, *parent_node_index);
        self.all_parents(*parent_class, child_to_parent, parent_to_child_index, seen);
      });
    });
  }

  fn extract_generalized_expr_helper(&self, gen_class: Id, gen_fresh_sym: Symbol, extract_class: Id, parent_to_child_index: &HashMap<Id, usize>, cache: &mut HashMap<Id, Option<Expr>>) -> Expr {
    match cache.get(&extract_class) {
      Some(Some(expr)) => {
        return expr.clone();
      }
      Some(None) => {
        let extractor = Extractor::new(&self.egraph, AstSize);
        let expr = extractor.find_best(extract_class).1;
        cache.insert(extract_class, Some(expr.clone()));
        return expr;
      }
      _ => {}
    }
    if gen_class == extract_class {
      return vec!(SymbolLang::leaf(gen_fresh_sym)).into();
    }

    parent_to_child_index.get(&extract_class).map(|node_index|{
      let node = &self.egraph[extract_class].nodes[*node_index];
      cache.insert(extract_class, None);
      let expr = node.join_recexprs(|child_class| self.extract_generalized_expr_helper(gen_class, gen_fresh_sym, child_class, parent_to_child_index, cache));
      cache.insert(extract_class, Some(expr.clone()));
      expr
    }).unwrap_or_else(||{
      let extractor = Extractor::new(&self.egraph, AstSize);
      let expr = extractor.find_best(extract_class).1;
      cache.insert(extract_class, Some(expr.clone()));
      expr
    })
  }

  fn extract_generalized_expr(&self, gen_class: Id, gen_fresh_sym: Symbol, extract_class: Id) -> Expr {
    // println!("extracting generalized expr ({}) for {}", gen_class, extract_class);
    let mut parent_map = HashMap::default();
    let mut parents = HashSet::default();
    self.compute_parents(extract_class, &mut parent_map, &mut parents);
    // println!("parent map: {:?}", parent_map);
    let mut parent_to_child_index = HashMap::default();
    self.all_parents(gen_class, &parent_map, &mut parent_to_child_index, &mut HashSet::default());
    // println!("parent to child index: {:?}", parent_to_child_index);
    let mut cache = HashMap::default();
    cache.insert(gen_class, Some(vec!(SymbolLang::leaf(gen_fresh_sym)).into()));
    // FIXME: skip extraction if gen_class can't reach both the LHS and RHS. I
    // think it's fine to keep it as is for now because the generalized lemma
    // will just be the LHS = RHS and it will probably be rejected by our lemma
    // set since we seed it with LHS = RHS.
    self.extract_generalized_expr_helper(gen_class, gen_fresh_sym, extract_class, &parent_to_child_index, &mut cache)
  }

  fn make_generalized_goal(&self, class: Id) -> Option<(Prop, Goal)> {
    // Get an op (function/constructor/var) that is a representative of this class.
    let class_op = self.egraph[class].data.canonical_form_data.get_enode().op;
    // NOTE We're assuming that we don't have to deal with higher-order
    // functions for generalizations, because we never will inspect a function's
    // value when pattern matching. However, a more correct analysis would take
    // into consideration how many arguments there are in the enode and from
    // those construct the appropriate (possibly higher-order) type.
    let (_, class_ty) = self.global_search_state.context.get(&class_op).or_else(||self.local_context.get(&class_op)).unwrap().args_ret();
    // println!("generalizing {} with type {}", class_op, class_ty);
    let fresh_var = format!("fresh_{}", self.egraph.total_size());
    let fresh_symb = Symbol::from(&fresh_var);
    let lhs_id = self.egraph.find(self.eq.lhs.id);
    let rhs_id = self.egraph.find(self.eq.rhs.id)
;
    // println!("starting generalization {} {} {}", lhs_id, rhs_id, class);
    let lhs_expr = self.extract_generalized_expr(class, fresh_symb, lhs_id);
    let rhs_expr = self.extract_generalized_expr(class, fresh_symb, rhs_id);
    // println!("generalizing {} === {}", lhs_expr, rhs_expr);
    let params: Vec<(Symbol, Type)> = get_vars(&lhs_expr).union(&get_vars(&rhs_expr)).into_iter().flat_map(|var| {
      let var_ty_opt = if var == &fresh_symb {
        Some(class_ty.clone())
      } else if self.local_context.contains_key(var) {
        Some(self.local_context.get(var).unwrap().clone())
      } else {
        warn!("Leaf of term that isn't a known variable: {}", var);
        None
      };
      var_ty_opt.map(|var_ty| {
        (*var, var_ty)
      })
    }).collect();
    let eq = Equation::from_exprs(&lhs_expr, &rhs_expr);
    let prop = Prop::new(eq.clone(), params.clone());
    let mut new_goal = Goal::top(&format!("{}_gen", self.name),
                             &prop,
                             &None,
                             self.global_search_state,
    );
    // // Add the node as a scrutinee and note its type.
    // new_goal.local_context.insert(fresh_symb, class_ty.clone());
    // new_goal.scrutinees.push_front(fresh_symb);
    // // Add the new variable and clear the other nodes in the eclass so that we
    // // don't do anything unsound.
    // new_goal.egraph[class].nodes = vec!(SymbolLang::leaf(fresh_symb));
    // // Create the cvec for the new var
    // let var_cvec = new_goal.egraph.analysis.cvec_analysis.make_cvec_for_type(&class_ty, new_goal.env, &new_goal.global_context);
    // let mut analysis = new_goal.egraph[class].data.clone();
    // // println!("var_cvec: {:?}", var_cvec);
    // analysis.cvec_data = var_cvec;
    // new_goal.egraph.set_analysis_data(class, analysis);
    // new_goal.egraph.rebuild();
    // new_goal.saturate_cvecs();
    // let new_goal_lhs_cvec = &new_goal.egraph[new_goal.eq.lhs.id].data.cvec_data;
    // let new_goal_rhs_cvec = &new_goal.egraph[new_goal.eq.rhs.id].data.cvec_data;
    // // println!("lhs_cvecs: {:?}, rhs_cvecs: {:?}", new_goal_lhs_cvec, new_goal_rhs_cvec);
    // let orig_extractor = Extractor::new(&self.egraph, AstSize);
    // let extractor = Extractor::new(&new_goal.egraph, AstSize);
    // let gen_exp = orig_extractor.find_best(class).1;
    // let lhs_exp = extractor.find_best(new_goal.eq.lhs.id).1;
    // let rhs_exp = extractor.find_best(new_goal.eq.rhs.id).1;
    if new_goal.cvecs_valid() {
      // println!("generalizing {} === {}", lhs_expr, rhs_expr);
      Some((Prop::new(eq, params), new_goal))
    } else {

      // println!("cvecs disagree for {} === {}", lhs_expr, rhs_expr);
      None
    }
  }

  fn find_generalized_goals(&self, blocking_exprs: &HashSet<Id>) -> Vec<Prop> {
    blocking_exprs.iter().flat_map(|blocking_expr| {
      self.make_generalized_goal(*blocking_expr).map(|(generalized_prop, _new_goal)|{
        generalized_prop
      })
    }).collect()
  }
}

impl<'a> Display for Goal<'a> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    if !self.premises.is_empty() {
      let premises_string = self
        .premises
        .iter()
        .map(|premise| format!("{}", premise))
        .collect::<Vec<String>>()
        .join(", ");
      write!(f, "{} ==> ", premises_string)?;
    }
    write!(f, "{}", self.eq)
  }
}

#[derive(Clone, Debug)]
pub enum ProofTerm {
  /// - Arg0: Name of the variable we split on
  /// - Arg1: List of cases we split on
  ///   * Arg0: Sexp we split to
  ///   * Arg1: Name of goal from this split
  ///
  /// Example:
  /// ```
  /// CaseSplit("x", [("(Z)", "goal_1"), ("(S x')","goal_2")])
  /// ```
  /// corresponds to the proof
  /// ```
  /// case x of
  ///   Z    -> goal_1
  ///   S x' -> goal_2
  /// ```
  CaseSplit(String, Vec<(String, String)>),
  /// The same thing as a case split, except instead of splitting on one of the
  /// symbolic variables, we split on an expression.
  ///
  /// - Arg0: A fresh variable introduced that is equal to the expression
  /// - Arg1: The expression we split on
  /// - Arg2: List of cases we split on (same as above).
  ///         There will always be two cases, corresponding to `True` and `False`.
  ///
  /// Example:
  /// ```
  /// ITESplit("g0", "(lt x y)", [("True", "goal_1"), ("False", "goal_2")])
  /// ```
  /// corresponds to the proof
  /// ```
  /// let g0 = lt x y in
  ///   case g0 of
  ///     True  -> goal_1
  ///     False -> goal_2
  /// ```
  ITESplit(String, String, Vec<(String, String)>),
}

pub enum ProofType {
  /// Constructive equality shown: LHS = RHS
  Refl,
  /// Contradiction shown (e.g. True = False)
  Contradiction,
}

impl std::fmt::Display for ProofType {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    match *self {
      ProofType::Refl => write!(f, "Refl"),
      ProofType::Contradiction => write!(f, "Contradiction"),
    }
  }
}

#[derive(Default, Clone)]
pub struct LemmasState {
  pub proven_lemmas: MinElements<Prop>,
  pub invalid_lemmas: MaxElements<Prop>,
  pub possible_lemmas: ChainSet<Prop>,
  pub lemma_rewrites: HashMap<String, Rw>,
  pub cyclic_lemmas: ChainSet<Prop>,
  pub cyclic_lemma_rewrites: HashMap<String, Rw>,
  pub last_lemma_proven: Option<String>,
  /// What was the last lemma we had proven at the time of our last attempt to
  /// prove this lemma?
  pub last_lemma_proven_at_last_attempt: HashMap<String, Option<String>>,
}

impl LemmasState {
  pub fn add_possible_lemmas<I: IntoIterator<Item = Prop>>(&mut self, iter: I) {
    // Ignore the lemma if we already have a lemma that subsumes it
    self.possible_lemmas.extend(iter.into_iter().filter(|lemma| {
      let is_proven = self.proven_lemmas.contains_leq(&lemma);
      let is_cyclic = self.cyclic_lemmas.contains_leq(&lemma);
      let is_invalid = self.invalid_lemmas.contains_geq(&lemma);
      let is_too_big = CONFIG.max_lemma_size > 0
        && sexp_size(&lemma.eq.lhs) + sexp_size(&lemma.eq.rhs) > CONFIG.max_lemma_size;
      // if is_proven {
      //   println!("skipping lemma {}={}", lemma.eq.lhs, lemma.eq.rhs);
      // } else {
      //   println!("adding lemma {}={}", lemma.eq.lhs, lemma.eq.rhs);
      // }
      !is_proven && !is_invalid && !is_too_big && !is_cyclic
    }));
  }
}

pub struct ProofInfo {
  pub solved_goal_explanation_and_context: HashMap<String, (ProofType, Explanation<SymbolLang>, Context)>,
  pub proof: HashMap<String, ProofTerm>,
}

/// A proof state is a list of subgoals,
/// all of which have to be discharged
pub struct ProofState<'a> {
  pub goals: VecDeque<Goal<'a>>,
  pub proof_info: ProofInfo,
  pub start_time: Instant,
  pub proof_depth: usize,
  pub lemmas_state: LemmasState,
  pub case_split_depth: usize,
  pub lemma_proofs: Vec<(String, Prop, ProofInfo)>,
  pub ih_lemma_name: String,
  pub lemma_number: usize,
  // pub cc_lemmas: HashMap<String, Rw>,
}

impl<'a> ProofState<'a> {
  // Has timeout been reached?
  pub fn timeout(&self) -> bool {
    CONFIG.timeout.is_some()
      && self.start_time.elapsed() > Duration::new(CONFIG.timeout.unwrap(), 0)
  }

  pub fn fresh_lemma_name(&mut self) -> String {
    let name = format!("lemma_{}", self.lemma_number);
    self.lemma_number += 1;
    name
  }

  /// Try to prove all of the lemmas we've collected so far.
  pub fn try_prove_lemmas(&mut self, goal: &mut Goal) -> Option<(ProofType, Explanation<SymbolLang>)> {
    if self.proof_depth == CONFIG.proof_depth {
      return None;
    }
    // println!("Try prove lemmas for goal {}", goal.name);
    // self.lemmas_state.possible_lemmas.chains.iter().for_each(|chain| chain.chain.iter().for_each(|lem| println!("lemma: {} = {}", lem.eq.lhs, lem.eq.rhs)));

    // Need to copy so we can mutably borrow self later
    let lemma_chains = self.lemmas_state.possible_lemmas.chains.clone();
    for chain in lemma_chains.iter() {
      for (i, lemma_prop) in chain.chain.iter().enumerate() {
        if self.timeout() {
          return None;
        }
        // Is the lemma already proven or subsumed by a cyclic lemma?
        if self.lemmas_state.proven_lemmas.contains_leq(&lemma_prop) || self.lemmas_state.cyclic_lemmas.contains_leq(&lemma_prop) {
          continue;
        }
        // Is the lemma invalid?
        // if self.lemmas_state.invalid_lemmas.contains_geq(&lemma_prop) {
        //   continue;
        // }
        let goal_name = format!("lemma-{}={}", lemma_prop.eq.lhs, lemma_prop.eq.rhs);
        let mut new_goal = Goal::top(&goal_name,
                                 &lemma_prop,
                                 &None,
                                 goal.global_search_state,
        );
        let try1 = new_goal.cvecs_valid();
        let mut new_goal_2 = Goal::top(&goal_name,
                                 &lemma_prop,
                                 &None,
                                 goal.global_search_state,
        );
        let try2 = new_goal_2.cvecs_valid();
        if try1 && !try2 {
          // println!("Second try helped");
          // println!("Invalidated lemma {} = {}", lemma_prop.eq.lhs, lemma_prop.eq.rhs);
        }
        if !try1 || !try2 {
          warn!("Invalidated lemma {} = {}", lemma_prop.eq.lhs, lemma_prop.eq.rhs);
          self.lemmas_state.invalid_lemmas.insert(lemma_prop.clone());
          continue;
        } else {
          println!("Possible lemma to prove: {} = {}", lemma_prop.eq.lhs, lemma_prop.eq.rhs);
          // println!("proven lemmas so far: {}", self.lemmas_state.proven_lemmas.elems.iter().map(|e| format!("{} = {}", e.eq.lhs, e.eq.rhs)).join(","));
          // print_cvec(&new_goal.egraph.analysis.cvec_analysis, new_goal_lhs_cvec)
        }

        // FIXME: Use a proper name scheme for indexing lemmas instead of using
        // their serialized lhs = rhs (we can use the lemma numbering for this).
        // We should also normalize lemmas so that they have the same names
        // regardless of the names of their variables. Maybe this means
        // converting to a locally nameless form.
        //
        // NOTE: This doesn't actually skip that many lemmas because we don't
        // carry old lemmas around with us. Maybe we should and see if this is
        // useful or maybe we should
        let lemma_prop_name = format!("{} = {}", lemma_prop.eq.lhs, lemma_prop.eq.rhs);
        // NOTE: Having None in the hashmap is meaningfully different from
        // having no entry in the hashmap. We always try and prove if there is
        // no entry.
        if let Some(last_lemma_proven_at_last_attempt) = self.lemmas_state.last_lemma_proven_at_last_attempt.get(&lemma_prop_name) {
          if last_lemma_proven_at_last_attempt == &self.lemmas_state.last_lemma_proven {
            println!("Skipping lemma because nothing has changed");
            continue;
          } else {
            println!("New lemma proven since last attempt");
          }
        }
        self.lemmas_state.last_lemma_proven_at_last_attempt.insert(lemma_prop_name, self.lemmas_state.last_lemma_proven.clone());

        let new_lemma_name = self.fresh_lemma_name();
        let lemma_rw_opt = new_goal.make_lemma_rewrite(&new_goal.eq.lhs.expr, &new_goal.eq.rhs.expr, &new_goal.premises, false, new_lemma_name.clone());
        // If we can't make a rewrite out of this lemma, it's not useful to us, so we'll just keep going.
        let lemma_rw = match lemma_rw_opt {
          None => continue,
          Some(lemma_rw) => lemma_rw,
        };
        // NOTE CK: This used to be necessary for speed, but with some patches to efficiency, we
        // no longer need it. Perhaps if we allowed a greater proof depth we would need it.
        // // HACK: Optimization to proving lemmas
        // // We will always try to prove the most general lemma we've theorized so far, but thereafter
        // // we require that the lemma be actually useful to us if we are going to try and prove it.
        // //
        // // This eliminates us spending time trying to prove a junk lemma like
        // // (mult (S n) Z) = (plus (mult (S n) Z) Z)
        // // when we already failed to prove the more general lemma
        // // (mult n Z) = (plus (mult n Z) Z)
        // //
        // // Really we should have more sophisticated lemma filtering - the junk
        // // lemma in this case is really no easier to prove than the first lemma
        // // (since we will try to prove it eventually when we case split the first),
        // // so we shouldn't consider it in the first place.
        // //
        // // Hence why I consider this optimization a hack, even though it
        // // probably avoids some lemmas which are junky in a more complicated
        // // way. I imagine it might rarely pass on interesting and useful lemmas.
        // // This is because sometimes you need more than one lemma to prove a goal.
        if i > 0 {
          let goal_egraph_copy = goal.egraph.clone();
          let new_lemma_rws = lemma_rw.rewrites();
          let rewrites = goal.global_search_state.reductions.iter().chain(goal.lemmas.values()).chain(new_lemma_rws.iter()).chain(self.lemmas_state.lemma_rewrites.values());
          let runner = Runner::default()
            // .with_explanations_enabled()
            .with_egraph(goal_egraph_copy)
            .run(rewrites);
          if runner.egraph.find(goal.eq.lhs.id) != runner.egraph.find(goal.eq.rhs.id) {
            break;
          }
        }
        println!("Trying to prove lemma: forall {}. {} = {}", lemma_prop.params.iter().map(|(v, t)| format!("{}: {}", v, t)).join(" "), lemma_prop.eq.lhs, lemma_prop.eq.rhs);

        let new_lemma_eq = &lemma_rw.lemma_prop;
        // Give the new goal the new lemma's name so that we can match its proof.
        // Actually this isn't necessary for anything other than prettying the output,
        // but having the name be ugly is better for debugging.
        new_goal.name = new_lemma_name.clone();
        let mut new_lemmas_state = self.lemmas_state.clone();
        // Zero out the possible lemmas and cyclic lemmas, we only want
        // to carry forward what we've proven already.
        new_lemmas_state.possible_lemmas = ChainSet::new();
        new_lemmas_state.cyclic_lemmas = ChainSet::new();
        new_lemmas_state.cyclic_lemma_rewrites = HashMap::new();
        let (outcome, ps) = prove(new_goal, self.proof_depth + 1, new_lemmas_state, new_lemma_name.clone(), self.lemma_number);
        // Update the lemma number so we don't have a lemma name clash.
        self.lemma_number = ps.lemma_number;
        // Steal the lemmas we got from the recursive proving, as well as any
        // other info we learned from the lemmas state.
        self.lemmas_state.proven_lemmas.extend(ps.lemmas_state.proven_lemmas.elems);
        self.lemmas_state.invalid_lemmas.extend(ps.lemmas_state.invalid_lemmas.elems);
        self.lemmas_state.lemma_rewrites.extend(ps.lemmas_state.lemma_rewrites);
        self.lemmas_state.last_lemma_proven = ps.lemmas_state.last_lemma_proven;
        self.lemmas_state.last_lemma_proven_at_last_attempt.extend(ps.lemmas_state.last_lemma_proven_at_last_attempt);
        self.lemma_proofs.extend(ps.lemma_proofs);
        if outcome == Outcome::Valid {
          println!("proved {} = {}", lemma_prop.eq.lhs, lemma_prop.eq.rhs);
          // TODO: This comes for free in the proven lemmas we get, so we
          // probably don't need to insert it.
          self.lemmas_state.proven_lemmas.insert(lemma_prop.clone());
          self.lemmas_state.lemma_rewrites.extend(lemma_rw.names_and_rewrites());
          // Add any cyclic lemmas we proved too
          self.lemmas_state.proven_lemmas.extend(ps.lemmas_state.cyclic_lemmas.chains.into_iter().flat_map(|chain| chain.chain.into_iter()));
          self.lemmas_state.lemma_rewrites.extend(ps.lemmas_state.cyclic_lemma_rewrites);
          // Add its proof
          self.lemma_proofs.push((new_lemma_name.clone(), new_lemma_eq.clone(), ps.proof_info));
          // This is now the last lemma we've proven
          self.lemmas_state.last_lemma_proven = Some(new_lemma_name);
          goal.saturate(&self.lemmas_state.lemma_rewrites);
          let proof = goal.find_proof();
          if proof.is_some() {
            return proof;
          }
          break;
        }
        // TODO: We want to record that all of the previous lemmas including
        // this are invalid, but for now we won't record anything.
        if outcome == Outcome::Invalid {
          self.lemmas_state.invalid_lemmas.insert(lemma_prop.clone());
        } else {
          // NOTE: We will try to prove a lemma twice
          // self.lemmas_state.proven_lemmas.insert(lemma_prop.clone());
        }
      }
    }
    None
  }

  pub fn add_cyclic_lemmas(&mut self, goal: &Goal) {
    // FIXME: add premises properly
    if !goal.premises.is_empty() {
      return;
    }
    let (rws, lemma_rws) = goal.make_cyclic_lemma_rewrites(self, false);
    self.lemmas_state.cyclic_lemmas.extend(lemma_rws.into_iter().map(|lemma_rw| lemma_rw.lemma_prop));
    self.lemmas_state.cyclic_lemma_rewrites.extend(rws);
  }

  pub fn update_depth(&mut self, depth: usize) -> bool {
    if depth > self.case_split_depth {
      self.case_split_depth = depth;
      true
    } else {
      false
    }
  }

  pub fn process_goal_explanation(&mut self, proof_type: ProofType, mut explanation: Explanation<SymbolLang>, goal: Goal) {
    // This goal has been discharged, proceed to the next goal
    if CONFIG.verbose {
      println!("{} {} by {}", "Proved case".bright_blue(), goal.name, proof_type);
      println!("{}", explanation.get_flat_string());
    }
    self
      .proof_info
      .solved_goal_explanation_and_context
      .insert(goal.name, (proof_type, explanation, goal.local_context));
  }
}

/// Pretty-printed proof state
pub fn pretty_state(state: &ProofState) -> String {
  format!(
    "[{}]",
    state
      .goals
      .iter()
      .map(|g| g.name.clone())
      .collect::<Vec<String>>()
      .join(", ")
  )
}

/// Outcome of a proof attempt
#[derive(Debug, PartialEq, PartialOrd, Eq, Ord)]
pub enum Outcome {
  Valid,
  Invalid,
  Unknown,
  Timeout,
}

impl std::fmt::Display for Outcome {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    match *self {
      Outcome::Valid => write!(f, "{}", "VALID".green()),
      Outcome::Invalid => write!(f, "{}", "INVALID".red()),
      Outcome::Unknown => write!(f, "{}", "UNKNOWN".yellow()),
      Outcome::Timeout => write!(f, "{}", "TIMEOUT".yellow()),
    }
  }
}

pub fn explain_goal_failure(goal: &Goal) {
  println!("{} {}", "Could not prove".red(), goal.name);

  println!("{}", "LHS Nodes".cyan());
  print_expressions_in_eclass(&goal.egraph, goal.eq.lhs.id);

  println!("{}", "RHS Nodes".cyan());
  print_expressions_in_eclass(&goal.egraph, goal.eq.rhs.id);
}

fn find_proof(eq: &ETermEquation, egraph: &mut Eg) -> Option<(ProofType, Explanation<SymbolLang>)> {
  if egraph.find(eq.lhs.id) == egraph.find(eq.rhs.id) {
    // We have shown that LHS == RHS
    Some((ProofType::Refl,
        egraph
        .explain_equivalence(&eq.lhs.expr, &eq.rhs.expr)
    ))
  } else {
    // Check if this case in unreachable (i.e. if there are any inconsistent
    // e-classes in the e-graph)

    // TODO: Right now we only look for contradictions using the canonical
    // form analysis. We currently don't generate contradictions from the
    // cvec analysis, but we should be able to. However, even if we find
    // a cvec contradiction, it isn't as easy to use in our proof.
    //
    // If we find a contradiction from the cvecs, we need to first find which
    // enodes the cvecs came from, then we need to explain why those nodes are
    // equal, then we need to provide the concrete values that cause them to
    // be unequal. This will probably require us to update the Cvec analysis
    // to track enodes, which is a little unfortunate.
    let inconsistent_exprs = egraph.classes().find_map(|eclass| {
      if let CanonicalForm::Inconsistent(n1, n2) = &eclass.data.canonical_form_data {
        // println!("Proof by contradiction {} != {}", n1, n2);

        // FIXME: these nodes might have been removed, we'll need to be
        // careful about how we generate this proof. Perhaps we can generate
        // the proof when we discover the contradiction, since we hopefully
        // will not have finished removing the e-node at this point.

        // This is here only for the purpose of proof generation:
        let extractor = Extractor::new(&egraph, AstSize);
        let expr1 = extract_with_node(n1, &extractor);
        let expr2 = extract_with_node(n2, &extractor);
        if CONFIG.verbose {
          println!("{}: {} = {}", "UNREACHABLE".bright_red(), expr1, expr2);
        }
        Some((expr1, expr2))
      } else {
        None
      }
    });
    inconsistent_exprs.map(|(expr1, expr2)| {
      let explanation = egraph.explain_equivalence(&expr1, &expr2);
      (ProofType::Contradiction, explanation)
    })
  }

}


/// Top-level interface to the theorem prover.
pub fn prove(mut goal: Goal, depth: usize, mut lemmas_state: LemmasState, ih_name: String, lemma_number: usize) -> (Outcome, ProofState) {
  // let goal_name = goal.name.clone();
  let goal_eq = Equation::new(goal.eq.lhs.sexp.clone(), goal.eq.rhs.sexp.clone());
  let goal_prop = Prop::new(goal_eq, goal.params.iter().cloned().map(|param| (param, goal.local_context.get(&param).unwrap().clone())).collect());
  // We won't attempt to prove the goal again (it isn't actually proven).
  lemmas_state.proven_lemmas.insert(goal_prop);
  let mut state = ProofState {
    goals: vec![goal].into(),
    proof_info: ProofInfo {
      solved_goal_explanation_and_context: HashMap::default(),
      proof: HashMap::default(),
    },
    start_time: Instant::now(),
    proof_depth: depth,
    lemmas_state,
    case_split_depth: 0,
    lemma_proofs: vec!(),
    // FIXME: should use an option
    ih_lemma_name: ih_name,
    lemma_number,
  };
  // FIXME: put in config
  if state.proof_depth > CONFIG.proof_depth {
    return (Outcome::Unknown, state);
  }
  while !state.goals.is_empty() {
    // println!("Taking next step for goal {}", goal_name);
    // println!("proven lemmas: {}", state.lemmas_state.proven_lemmas.elems.iter().map(|e| format!("{} = {}", e.eq.lhs, e.eq.rhs)).join(","));
    if state.timeout() {
      return (Outcome::Timeout, state);
    }

    // TODO: This should be info! but I don't know how to suppress all the info output from egg
    warn!("PROOF STATE: {}", pretty_state(&state));
    // Pop the first subgoal
    goal = state.goals.pop_front().unwrap();
    // Saturate the goal
    goal.saturate(&state.lemmas_state.lemma_rewrites);
    if CONFIG.save_graphs {
      goal.save_egraph();
    }
    if let Some((proof_type, explanation)) = goal.find_proof() {
      // println!("Proven goal {} has e-graph size {}, lhs/rhs size {}", goal.name, goal.egraph.total_number_of_nodes(), goal.egraph[goal.eq.lhs.id].nodes.len());
      state.process_goal_explanation(proof_type, explanation, goal);
      continue;

    }
    if CONFIG.verbose {
      explain_goal_failure(&goal);
    }
    warn!("goal scrutinees before split: {:?}", goal.scrutinees);
    goal.split_ite();
    warn!("goal scrutinees after split: {:?}", goal.scrutinees);
    if goal.scrutinees.is_empty() {
      // This goal has no more variables to case-split on,
      // so this goal, and hence the whole conjecture, is invalid
      if CONFIG.verbose {
        for remaining_goal in &state.goals {
          println!("{} {}", "Remaining case".yellow(), remaining_goal.name);
        }
      }
      return (Outcome::Invalid, state);
    }
    let (blocking_vars, blocking_exprs) =
      if !CONFIG.blocking_vars_analysis {
        warn!("Blocking var analysis is disabled");
        (goal.scrutinees.iter().map(|s| s.name).collect(), HashSet::default())
      } else {
        let (blocking_vars, blocking_exprs) = goal.find_blocking(&state);
        if CONFIG.verbose {
          println!("blocking vars: {:?}", blocking_vars);
        }
        (blocking_vars, blocking_exprs)
      };

    if CONFIG.generalization {
      // TODO: now that we generalize in the cc lemma search, do we need this?
      state.lemmas_state.add_possible_lemmas(goal.find_generalized_goals(&blocking_exprs));
    }
    if CONFIG.cc_lemmas {
      let possible_lemmas = goal.search_for_cc_lemmas(&mut state);
      state.lemmas_state.add_possible_lemmas(possible_lemmas);
    }
    // This ends up being really slow so we'll just take the lemma duplication for now
    // It's unclear that it lets us prove that much more anyway.
    // state.add_cyclic_lemmas(&goal);

    goal.global_search_state.searchers.iter().for_each(|searcher: &ConditionalSearcher<Pattern<SymbolLang>, Pattern<SymbolLang>>| {
      let results = searcher.search(&goal.egraph);
      let extractor = Extractor::new(&goal.egraph, AstSize);
      if results.len() > 0 {
        println!("Found search result for {} =?> {}", searcher.searcher, searcher.condition);
        for result in results {
          println!("Result eclass: {}", result.eclass);
          result.substs.iter().for_each(|subst|{
            for var in searcher.searcher.vars().iter() {
              let exp = extractor.find_best(subst[*var]).1;
              println!("Var {} = {}", var, exp);
            }
          });
          let result_cvec = &goal.egraph[result.eclass].data.cvec_data;
          for eclass in goal.egraph.classes() {
            if eclass.id == result.eclass {
              continue;
            }
            if let Some(true) = cvecs_equal(&goal.egraph.analysis.cvec_analysis, result_cvec, &goal.egraph[eclass.id].data.cvec_data) {
              let exp = extractor.find_best(eclass.id).1;
              println!("Matching eclass via cvec analysis: {} (id {})", exp, eclass.id);
            }
          }
        }
      };
    });

    if let Some(scrutinee) = goal.next_scrutinee(blocking_vars) {
      // let d = depth.max(depth_at_front);
      if scrutinee.depth > state.case_split_depth {
        // println!("depth {} is greater than current depth, increasing.", depth);
        state.case_split_depth = depth;
        if let Some((proof_type, explanation)) = state.try_prove_lemmas(&mut goal) {
          state.process_goal_explanation(proof_type, explanation, goal);
          continue;
        }
      }
      if state.case_split_depth >= CONFIG.max_split_depth {
        // println!("Bailing because depth is too high");
        // This goal could be further split, but we have reached the maximum depth,
        // we cannot prove or disprove the conjecture
        // state.goals.push_back(goal);
        // continue;
        return (Outcome::Unknown, state);
      }
      if CONFIG.verbose {
        println!(
          "{}: {}",
          "Case splitting and continuing".purple(),
          scrutinee.name.to_string().purple()
        );
      }
      goal.case_split(scrutinee, &mut state);
    } else {
      if CONFIG.verbose {
        println!("{}", "Cannot case split: no blocking variables found".red());
        for remaining_goal in &state.goals {
          println!("{} {}", "Remaining case".yellow(), remaining_goal.name);
        }
      }
      if goal.scrutinees.iter().any(|s| s.depth >= CONFIG.max_split_depth) {
        if let Some((proof_type, explanation)) = state.try_prove_lemmas(&mut goal) {
          state.process_goal_explanation(proof_type, explanation, goal);
          continue;
        }

        // state.goals.push_back(goal);
        // continue;
        return (Outcome::Unknown, state);
      } else {
        return (Outcome::Invalid, state);
      }
    }
  }
  // All goals have been discharged, so the conjecture is valid:
  (Outcome::Valid, state)
}
