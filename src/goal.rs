use colored::Colorize;
use egg::*;
use itertools::Itertools;
use log::warn;
use std::collections::BTreeSet;
use std::collections::{BTreeMap, VecDeque};
use std::fmt::Display;
use std::iter::zip;
use std::str::FromStr;
use std::time::{Duration, Instant};
use symbolic_expressions::{parser, Sexp};

use crate::analysis::{CycleggAnalysis, CanonicalFormAnalysis, CanonicalForm, cvecs_equal, print_cvec};
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
  fn smaller_tuple(&self, triples: &Vec<(Symbol, Expr, Expr)>, _blocking_vars: &BTreeSet<Symbol>) -> bool {
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
      // FIXME: hacky way to find variables
      let lhs_vars = sexp_leaves(&new_lhs);
      let rhs_vars = sexp_leaves(&new_rhs);
      let mut new_params = prop.params.clone();
      // Only keep the vars that remain after substituting.
      new_params.retain(|(var, _ty)| lhs_vars.contains(&var.to_string()) || rhs_vars.contains(&var.to_string()));
      new_params.push((var_symb, ty));
      // println!("Generalization candidate: {} = {}", new_lhs, new_rhs);
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
  pub lemma_number: usize,
  pub lemma_prop: Prop,
}

impl LemmaRewrite {
  pub fn new(lhs_to_rhs: Option<(String, Rw)>, rhs_to_lhs: Option<(String, Rw)>, lemma_number: usize, lemma_prop: Prop) -> Self { Self { lhs_to_rhs, rhs_to_lhs, lemma_number, lemma_prop } }

  pub fn lemma_name(&self) -> String {
    format!("lemma_{}", self.lemma_number)
  }

  pub fn names_and_rewrites(&self) -> Vec<(String, Rw)> {
    self.lhs_to_rhs.iter().chain(self.rhs_to_lhs.iter()).cloned().collect()
  }

  pub fn rewrites(&self) -> Vec<Rw> {
    self.names_and_rewrites().into_iter().map(|(_, rw)| rw).collect()
  }

  pub fn add_to_rewrites(&self, rewrites: &mut BTreeMap<String, Rw>) {
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
// TODO: This can probably be moved into the ProofState.
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
#[derive(Clone)]
pub struct Goal<'a> {
  /// Goal name
  pub name: String,
  /// Equivalences we already proved
  pub egraph: Eg,
  /// Rewrites are split into reductions (invertible rules) and lemmas (non-invertible rules)
  /// Rewrites are split into reductions (invertible rules) and lemmas
  /// (non-invertible rules). Reductions - being unchanging - live in
  /// global_search_state.
  lemmas: BTreeMap<String, Rw>,
  /// Mapping from all universally-quantified variables of the goal to their types
  /// (note this includes both current and old variables, which have been case-split away)
  pub local_context: Context,
  /// Mapping from all universally-quantified variables of the goal to the e-classes they are stored in
  /// (note this includes both current and old variables, which have been case-split away)
  pub var_classes: IdSubst,
  /// The top-level parameters to the goal
  pub top_level_params: Vec<Symbol>,
  /// Variables we can case-split
  /// (i.e. the subset of local_context that have datatype types)
  scrutinees: VecDeque<Scrutinee>,
  /// Variables that we have already case split
  pub case_split_vars: BTreeSet<Symbol>,
  /// Instantiations of the induction hypothesis that are in the egraph
  grounding_instantiations: Vec<IdSubst>,
  /// The equation we are trying to prove
  pub eq: ETermEquation,
  /// If this is a conditional prop, the premises
  pub premises: Vec<ETermEquation>,
  /// Stores the expression each guard variable maps to
  guard_exprs: BTreeMap<String, Expr>,
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
      lemmas: BTreeMap::new(),
      local_context: Context::new(),
      top_level_params: prop.params.iter().map(|(x, _)| *x).collect(),
      case_split_vars: BTreeSet::new(),
      guard_exprs: BTreeMap::new(),
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
  // FIXME: This currently does not work for any goal other than the top-level goal.
  fn build_cvecs(&mut self) {
    // Update the timestamp so that we ensure the new cvecs are applied.
    self.egraph.analysis.cvec_analysis.current_timestamp += 1;
    // Annoyingly, we need to collect these values before we iterate over them
    // to avoid mutably borrowing self. I think it's worth it so that we can
    // factor out the add_cvec_for_class function which is used elsewhere.
    let var_tys: Vec<(Id, Type)> = self.top_level_params.iter().map(|param|{
      let ty = self.local_context[param].clone();
      let var_id = self.var_classes[param];
      (var_id, ty)
    }).collect();
    for (var_id, ty) in var_tys {
      self.add_cvec_for_class(var_id, &ty);
    }
    self.egraph.analysis.cvec_analysis.saturate();
    self.egraph.rebuild();
  }

  /// Constructs a cvec for the class at id with type ty.
  ///
  /// It's important to update the current timestamp before calling this function.
  ///
  /// Returns whether it made a cvec (we don't make cvecs for arrow types
  /// because we don't know how to make arbitrary functions).
  fn add_cvec_for_class(&mut self, id: Id, ty: &Type) -> bool {
    if ty.is_arrow() {
      return false;
    }
    let cvec = self.egraph.analysis.cvec_analysis.make_cvec_for_type(&ty, self.global_search_state.env, &self.global_search_state.context);
    let mut analysis = self.egraph[id].data.clone();
    analysis.timestamp = self.egraph.analysis.cvec_analysis.current_timestamp;
    analysis.cvec_data = cvec;
    self.egraph.set_analysis_data(id, analysis);
    true
  }

  pub fn cvecs_valid(&mut self) -> Option<bool> {
    self.egraph.analysis.cvec_analysis.saturate();
    let lhs_cvec = &self.egraph[self.eq.lhs.id].data.cvec_data;
    let rhs_cvec = &self.egraph[self.eq.rhs.id].data.cvec_data;
    // print_cvec(&self.egraph.analysis.cvec_analysis, lhs_cvec);
    // print_cvec(&self.egraph.analysis.cvec_analysis, rhs_cvec);
    cvecs_equal(&self.egraph.analysis.cvec_analysis, lhs_cvec, rhs_cvec)
  }

  /// Saturate the goal by applying all available rewrites
  pub fn saturate(&mut self, top_lemmas: &BTreeMap<String, Rw>) {
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
  pub fn find_proof(&mut self) -> Option<ProofLeaf> {
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
  fn make_lemma_rewrites_from_all_exprs(&self, lhs_id: Id, rhs_id: Id, premises: Vec<ETermEquation>, timer: &Timer, lemmas_state: &mut LemmasState, add_termination_check: bool) -> (BTreeMap<String, Rw>, Vec<LemmaRewrite>) {
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
        if timer.timeout() {
          return (rewrites, lemma_rws);
        }
        let lemma_number = lemmas_state.fresh_lemma();

        if let Some(lemma_rw) = self.make_lemma_rewrite(lhs_expr, rhs_expr, &premises, add_termination_check, lemma_number) {
          // Add the rewrites (if lemma_rw is some at least one is guaranteed to exist).
          lemma_rw.add_to_rewrites(&mut rewrites);
          lemma_rws.push(lemma_rw);
        }

      }
    }
    (rewrites, lemma_rws)
  }

  fn make_lemma_rewrite(&self, lhs_expr: &Expr, rhs_expr: &Expr, premises: &Vec<ETermEquation>, add_termination_check: bool, lemma_number: usize)
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
    // println!("trying to make lemma rewrite forall {:?}. {} = {}", lemma_vars, lhs, rhs);

    // If any of my premises contain variables that are not present in lhs or rhs,
    // skip because we don't know how to check such a premise
    if !premises.iter().all(|eq| {
      let premise_lhs_vars = var_set(&to_pattern(&eq.lhs.expr, is_var));
      let premise_rhs_vars = var_set(&to_pattern(&eq.rhs.expr, is_var));
      let premise_vars: BTreeSet<Var> =
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
      lemma_number,
      lemma_prop: Prop {
        eq: rewrite_eq,
        params: params.clone(),
      }
    };
    let lemma_name = lemma_rw.lemma_name();
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
  fn add_lemma_rewrites(&self, timer: &Timer, lemmas_state: &mut LemmasState, ih_lemma_number: usize) -> BTreeMap<String, Rw> {
    // Special case: the first time we add lemmas (i.e. when there are no
    // previous lemmas), we will make lemma rewrites out of the lhs and rhs only
    // and we will use the special IH name.
    if self.lemmas.is_empty() {
      let premises = self.update_premises();
      let mut rewrites = self.lemmas.clone();
      // In the non-cyclic case, only use the original LHS and RHS
      // and only if no other lemmas have been added yet
      let lemma_rw = self.make_lemma_rewrite(&self.eq.lhs.expr, &self.eq.rhs.expr, &premises, true, ih_lemma_number).unwrap();
      lemma_rw.add_to_rewrites(&mut rewrites);
      return rewrites;
    }
    // Otherwise, we only create lemmas when we are operating in the cyclic mode
    if CONFIG.is_cyclic() {
      self.make_cyclic_lemma_rewrites(timer, lemmas_state, true).0
    } else {
      self.lemmas.clone()
    }

  }

  /// Creates cyclic lemmas from the current goal.
  fn make_cyclic_lemma_rewrites(&self, timer: &Timer, lemmas_state: &mut LemmasState, add_termination_check: bool) -> (BTreeMap<String, Rw>, Vec<LemmaRewrite>) {
    let lhs_id = self.egraph.find(self.eq.lhs.id);
    let rhs_id = self.egraph.find(self.eq.rhs.id);

    let premises = self.update_premises();
    self.make_lemma_rewrites_from_all_exprs(lhs_id, rhs_id, premises, timer, lemmas_state, add_termination_check)
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
    let mut stuck_guards = BTreeMap::new();
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
  fn case_split(self, scrutinee: Scrutinee, timer: &Timer, lemmas_state: &mut LemmasState, ih_lemma_number: usize) -> (ProofTerm, Vec<Goal<'a>>) {
    let new_lemmas = self.add_lemma_rewrites(timer, lemmas_state, ih_lemma_number);

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
    // These are the new goals generated from the case split
    let mut goals = vec![];

    // Create a new goal for each constructor we can case split to and add it to
    // the proof state.
    //
    // (We process constructors in reverse order so that base case ends up at
    // the top of the stack - this is due to how we typically define the orders
    // for our datatypes in our definitions files. It's not a very principled
    // iteration order)
    for &con in cons.iter().rev() {
      let mut new_goal = self.clone();
      new_goal.case_split_vars.insert(scrutinee.name);
      new_goal.lemmas = new_lemmas.clone();

      // Get the arguments of the constructor.
      let con_args = self.instantiate_constructor(&con, ty);
      // For each argument: we will create a fresh variable that we can use as a
      // scrutinee.
      let mut fresh_vars = vec![];

      // We will update the timestamp of the cvec analysis so that we enforce
      // the update when we generate a cvec.
      new_goal.egraph.analysis.cvec_analysis.current_timestamp += 1;

      for (i, arg_type) in con_args.iter().enumerate() {
        let fresh_var_name = format!("{}_{}{}", scrutinee.name, self.egraph.total_size(), i);
        let fresh_var = Symbol::from(fresh_var_name.clone());
        fresh_vars.push(fresh_var);
        // Add new variable to context
        new_goal.local_context.insert(fresh_var, arg_type.clone());
        // The depth of a scrutinee tracks how many ancestors are between it and
        // a top-level parameter, so we add 1 when we case split.
        new_goal.add_scrutinee(fresh_var, arg_type, scrutinee.depth + 1);
        let id = new_goal.egraph.add(SymbolLang::leaf(fresh_var));
        // The class corresponding to this var is its class in the e-graph.
        new_goal.var_classes.insert(fresh_var, id);
        // Generate a cvec for the fresh_var.
        new_goal.add_cvec_for_class(id, arg_type);

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

      new_goal.name = format!("{}_{}={}", new_goal.name, scrutinee.name, con_app);
      // This is tracked for proof emission.
      instantiated_cons_and_goals.push((con_app_string, new_goal.name.clone()));

      // Add con_app to the new goal's egraph and union it with var
      new_goal.egraph.add_expr(&con_app);
      new_goal.egraph.union_instantiations(
        &var_pattern_ast,
        &rec_expr_to_pattern_ast(con_app.clone()),
        &Subst::default(),
        format!("case-split:{}", new_goal.name),
      );
      // Remove old variable from the egraph and context
      remove_node(&mut new_goal.egraph, &var_node);

      new_goal.egraph.rebuild();

      // In cyclic mode: add the guard to premises,
      if CONFIG.is_cyclic() && var_str.starts_with(GUARD_PREFIX) && self.guard_exprs.contains_key(&var_str) {
        let lhs = ETerm::from_expr(self.guard_exprs[&var_str].clone(), &new_goal.egraph);
        let rhs = ETerm::from_expr(con_app, &new_goal.egraph);
        let eq = ETermEquation { lhs, rhs };
        new_goal.premises.push(eq);
      }

      // Add the subgoal to the proof state
      goals.push(new_goal);
    }
    // We split on var into the various instantiated constructors and subgoals.
    //
    // If the var is an ITE split, we will add the condition that was split on
    // to our proof term. This is necessary because for ITE splits we introduce
    // a new variable that we bind an expression to.
    let proof_term = match scrutinee.scrutinee_type {
      ScrutineeType::Guard => {
        // There should only be two cases.
        assert_eq!(instantiated_cons_and_goals.len(), 2);
        ProofTerm::ITESplit(
          var_str.clone(),
          self.guard_exprs[&var_str].to_string(),
          instantiated_cons_and_goals,
        )
      }
      ScrutineeType::Var => {
        ProofTerm::CaseSplit(var_str, instantiated_cons_and_goals)
      }
    };
    (proof_term, goals)
  }

  fn find_blocking(&self, timer: &Timer) -> (BTreeSet<Symbol>, BTreeSet<Id>) {
    let mut blocking_vars: BTreeSet<_> = BTreeSet::default();
    let mut blocking_exprs: BTreeSet<Id> = BTreeSet::default();

    let mut lhs_descendents = BTreeSet::default();
    self.compute_descendents(self.eq.lhs.id, &mut lhs_descendents);

    let mut rhs_descendents = BTreeSet::default();
    self.compute_descendents(self.eq.rhs.id, &mut rhs_descendents);

    for reduction in self.global_search_state.reductions {
      let x = reduction.searcher.get_pattern_ast().unwrap();
      let sexp = symbolic_expressions::parser::parse_str(&x.to_string()).unwrap();

      // Hack to dedup the new patterns (sexps) we generated
      let mut new_sexps: Vec<Sexp> = Goal::analyze_sexp_for_blocking_vars(&sexp)
        .into_iter()
        .map(|x| x.to_string())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .map(|x| symbolic_expressions::parser::parse_str(x.as_str()).unwrap())
        .collect();

      // the patterns we generated contained only ? instead of ?var, so we go and add fresh variable names everywhere
      for ns in new_sexps.iter_mut() {
        *ns = Goal::gen_fresh_vars(ns.clone(), 1);
      }

      // use these patterns to search over the egraph
      for new_sexp in new_sexps {
        if timer.timeout() {
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

  fn compute_descendents(&self, class: Id, descendents: &mut BTreeSet<Id>) {
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
  fn next_scrutinee(&mut self, mut blocking_vars: BTreeSet<Symbol>) -> Option<Scrutinee> {
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

  // FIXME: factor this out somehow
  // (it relies on the magic string "?" so I'm not sure how to)
  fn gen_fresh_vars(sexp: Sexp, mut idx: i32) -> Sexp {
    match sexp {
      Sexp::String(s) if s == "?" => Sexp::String(format!("?block_{}", idx)),
      Sexp::List(v) => Sexp::List(
        v.iter()
          .map(|x| {
            idx = idx + 1;
            Goal::gen_fresh_vars(x.clone(), idx + 1)
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
  // FIXME: factor this out somehow
  fn analyze_sexp_for_blocking_vars(sexp: &Sexp) -> Vec<Sexp> {
    let mut new_exps: Vec<Sexp> = vec![];
    new_exps.push(sexp.clone());

    // If this sexp is a constructor application, replace it by ?
    if sexp_is_constructor(sexp) {
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
          all_replacements.push(Goal::analyze_sexp_for_blocking_vars(sub_arg));
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

  /// Given a polymorphic constructor and a concrete instantiation of a
  /// datatype, return the concrete types of the constructor's arguments.
  fn instantiate_constructor(&self, con: &Symbol, actual: &Type) -> Vec<Type> {
    let con_ty = self.global_search_state.context.get(con).unwrap();
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
        .top_level_params
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

  /// Search for cc (concrete correspondence) lemmas.
  ///
  /// These are lemmas we propose from subterms in the e-graph that our concrete
  /// analysis deems equal on some set of random terms.
  fn search_for_cc_lemmas(&mut self, timer: &Timer, lemmas_state: &mut LemmasState) -> Vec<Prop> {
    let mut lemmas = vec!();
    self.egraph.analysis.cvec_analysis.saturate();
    let resolved_lhs_id = self.egraph.find(self.eq.lhs.id);
    let resolved_rhs_id = self.egraph.find(self.eq.rhs.id);
    let class_ids: Vec<Id> = self.egraph.classes().map(|c| c.id).collect();
    for class_1_id in &class_ids {
      for class_2_id in &class_ids {
        if timer.timeout() {
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
              //
              // Consider for example the case when the canonical forms are
              //   c1: (S (plus x x))
              //   c2: (S (double x))
              // In this case, the number of differing children is only 1.
              // The differing children are
              //   (plus x x) and (double x)
              // However, we can be sure that if the cvec analysis deemed c1 and
              // c2 equal, then it will deem these two differing children equal.
              //
              // Thus we won't waste our time trying to prove c1 == c2 when
              // we could instead prove (plus x x) == (double x), which implies
              // by congruence that c1 == c2.
              if num_differing_children <= 1 {
                continue;
              }
            }
            _ => {}
          }
          let (_rewrites, rewrite_infos) = self.make_lemma_rewrites_from_all_exprs(class_1_id, class_2_id, vec!(), timer, lemmas_state, false);
          let new_rewrite_eqs: Vec<Prop> = rewrite_infos.into_iter().map(|rw_info| rw_info.lemma_prop).collect();
          // We used to check the egraph to see if the lemma helped us, but now
          // we just throw it into our list. We do that check in try_prove_lemmas.
          if new_rewrite_eqs.is_empty() {
            continue;
          }

          if CONFIG.cc_lemmas_generalization {
            let fresh_name = format!("fresh_{}", self.egraph.total_size());
            for new_rewrite_eq in new_rewrite_eqs.iter() {
              if timer.timeout() {
                return lemmas;
              }
              lemmas.extend(find_generalizations_prop(&new_rewrite_eq, self.global_search_state.context, fresh_name.clone()));
            }
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

  /// Used for debugging.
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

  /// Poorly-named helper function for extract_generalized_expr. See that
  /// function for how it works.
  fn compute_parents(&self, class: Id, parents_map: &mut BTreeMap<Id, BTreeSet<(Id, usize)>>, seen: &mut BTreeSet<Id>) {
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

  /// Poorly-named helper function for extract_generalized_expr. See that
  /// function for how it works.
  fn all_parents(&self, start_class: Id, child_to_parent: &BTreeMap<Id, BTreeSet<(Id, usize)>>, parent_to_child_index: &mut BTreeMap<Id, usize>, seen: &mut BTreeSet<Id>) {
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

  fn extract_generalized_expr_helper(&self, gen_class: Id, gen_fresh_sym: Symbol, extract_class: Id, parent_to_child_index: &BTreeMap<Id, usize>, cache: &mut BTreeMap<Id, Option<Expr>>) -> Expr {
    // We handle cycles by using a cache. The cache contains an Option.
    match cache.get(&extract_class) {
      // If the Option is Some, that means we have successfully computed a value
      // and can reuse it.
      Some(Some(expr)) => {
        return expr.clone();
      }
      // If the Option is None, that means we have followed a cycle to this
      // class. If we contined trying to extract normally, we would infinitely
      // loop. So instead, we give up and ask it to do a regular extraction
      // using AstSize.
      Some(None) => {
        let extractor = Extractor::new(&self.egraph, AstSize);
        let expr = extractor.find_best(extract_class).1;
        cache.insert(extract_class, Some(expr.clone()));
        return expr;
      }
      _ => {}
    }

    // If this class can lead us to gen_class, it will be in
    // the parent_to_child_index map.
    parent_to_child_index.get(&extract_class).map(|node_index|{
      // Get the node we need to follow.
      let node = &self.egraph[extract_class].nodes[*node_index];
      // Record that we have seen this class once so that we don't infinitely loop.
      cache.insert(extract_class, None);
      // Extract an expression for it.
      let expr = node.join_recexprs(|child_class| self.extract_generalized_expr_helper(gen_class, gen_fresh_sym, child_class, parent_to_child_index, cache));
      cache.insert(extract_class, Some(expr.clone()));
      expr
    // If this class can't lead us to gen_class, we don't care
    // about it and we can just extract whatever.
    }).unwrap_or_else(||{
      let extractor = Extractor::new(&self.egraph, AstSize);
      let expr = extractor.find_best(extract_class).1;
      cache.insert(extract_class, Some(expr.clone()));
      expr
    })
  }

  /// Extracts an expr from extract_class where all occurrences of gen_class are
  /// replaced by gen_fresh_sym. gen_class is assumed to be contained in the
  /// egraph rooted at extract_class.
  // NOTE (CK): This probably can be more effectively accomplished by using a
  // custom extractor that prioritizes the class we want to generalize - but we
  // would then need to figure out what parts of the returned expression
  // correspond to that class so we can generalize them.
  fn extract_generalized_expr(&self, gen_class: Id, gen_fresh_sym: Symbol, extract_class: Id) -> Expr {
    // println!("extracting generalized expr ({}) for {}", gen_class, extract_class);
    let mut parent_map = BTreeMap::default();
    let mut parents = BTreeSet::default();
    // Compute a map from each eclass to its parent enodes in the egraph rooted
    // at extract_class.
    self.compute_parents(extract_class, &mut parent_map, &mut parents);
    // println!("parent map: {:?}", parent_map);
    let mut parent_to_child_index = BTreeMap::default();

    // Computes a map from parent eclass to the index of the enode that will
    // lead the parent to gen_class. If there are multiple indices, one (I
    // believe the largest) is chosen arbitrarily.
    self.all_parents(gen_class, &parent_map, &mut parent_to_child_index, &mut BTreeSet::default());
    // println!("parent to child index: {:?}", parent_to_child_index);
    let mut cache = BTreeMap::default();
    cache.insert(gen_class, Some(vec!(SymbolLang::leaf(gen_fresh_sym)).into()));
    // FIXME: skip extraction if gen_class isn't contained in either the LHS and
    // RHS. I think it's fine to keep it as is for now because the generalized
    // lemma will just be the LHS = RHS and it will probably be rejected by our
    // lemma set since we seed it with LHS = RHS.
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
    let rhs_id = self.egraph.find(self.eq.rhs.id);

    let is_var = |v: &str| self.local_context.contains_key(&Symbol::from_str(v).unwrap());

    // println!("starting generalization {} {} {}", lhs_id, rhs_id, class);
    let lhs_expr = self.extract_generalized_expr(class, fresh_symb, lhs_id);
    let rhs_expr = self.extract_generalized_expr(class, fresh_symb, rhs_id);
    // println!("generalizing {} === {}", lhs_expr, rhs_expr);
    let params: Vec<(Symbol, Type)> = get_vars(&lhs_expr, is_var).union(&get_vars(&rhs_expr, is_var)).into_iter().flat_map(|var| {
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
    if new_goal.cvecs_valid() == Some(true) {
      // println!("generalizing {} === {}", lhs_expr, rhs_expr);
      Some((Prop::new(eq, params), new_goal))
    } else {

      // println!("cvecs disagree for {} === {}", lhs_expr, rhs_expr);
      None
    }
  }

  /// Return generalizations of the current goal found by generalizing a
  /// blocking_expr.
  fn find_generalized_goals(&self, blocking_exprs: &BTreeSet<Id>) -> Vec<Prop> {
    blocking_exprs.iter().flat_map(|blocking_expr| {
      self.make_generalized_goal(*blocking_expr).map(|(generalized_prop, _new_goal)|{
        generalized_prop
      })
    }).collect()
  }

  /// Debug function to search for a pair of patterns in the e-graph
  fn debug_search_for_patterns_in_egraph(&self) {
    self.global_search_state.searchers.iter().for_each(|searcher: &ConditionalSearcher<Pattern<SymbolLang>, Pattern<SymbolLang>>| {
      let results = searcher.search(&self.egraph);
      let extractor = Extractor::new(&self.egraph, AstSize);
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
          let result_cvec = &self.egraph[result.eclass].data.cvec_data;
          for eclass in self.egraph.classes() {
            if eclass.id == result.eclass {
              continue;
            }
            if let Some(true) = cvecs_equal(&self.egraph.analysis.cvec_analysis, result_cvec, &self.egraph[eclass.id].data.cvec_data) {
              let exp = extractor.find_best(eclass.id).1;
              println!("Matching eclass via cvec analysis: {} (id {})", exp, eclass.id);
            }
          }
        }
      };
    });
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

pub enum ProofLeaf {
  /// Constructive equality shown: LHS = RHS
  Refl(Explanation<SymbolLang>),
  /// Contradiction shown (e.g. True = False)
  Contradiction(Explanation<SymbolLang>),
  /// Unimplemented proof type (will crash on proof emission)
  Todo,
}

impl ProofLeaf {
  fn name(&self) -> String {
    match &self {
      Self::Refl(_) => "Refl".to_string(),
      Self::Contradiction(_) => "Contradiction".to_string(),
      Self::Todo => "TODO".to_string(),
    }
  }
}

impl std::fmt::Display for ProofLeaf {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    match self {
      ProofLeaf::Refl(expl) => write!(f, "{}", expl.get_string()),
      ProofLeaf::Contradiction(expl) => write!(f, "{}", expl.get_string()),
      ProofLeaf::Todo => write!(f, "TODO: proof"),
    }
  }
}

#[derive(Default)]
pub struct LemmasState {
  pub proven_lemmas: MinElements<Prop>,
  pub invalid_lemmas: MaxElements<Prop>,
  pub lemma_rewrites: BTreeMap<String, Rw>,
  // When we make a new state, this gets initialized to 0
  pub lemma_number: usize,
  pub all_lemmas: Vec<(usize, Prop)>,
}

impl LemmasState {
  pub fn is_valid_new_prop(&self, prop: &Prop) -> bool {
    let is_proven = self.proven_lemmas.contains_leq(&prop);
    let is_invalid = self.invalid_lemmas.contains_geq(&prop);
    let is_too_big = CONFIG.max_lemma_size > 0
      && sexp_size(&prop.eq.lhs) + sexp_size(&prop.eq.rhs) > CONFIG.max_lemma_size;
    !is_proven && !is_invalid && !is_too_big
  }

  /// This is slow: a change of data structure might be appropriate here. We
  /// might consider normalizing the props somehow so that we don't have to do a
  /// slow comparison to determine equality.
  pub fn find_or_make_fresh_lemma(&mut self, prop: &Prop) -> usize {
    self.all_lemmas.iter().find_map(|(lemma_number, p)| {
      if p == prop {
        Some(*lemma_number)
      } else {
        None
      }
    })
                          .unwrap_or_else(|| {
                            let lemma_number = self.fresh_lemma();
                            self.all_lemmas.push((lemma_number, prop.clone()));
                            lemma_number
                          })
  }

  pub fn fresh_lemma(&mut self) -> usize {
    let number = self.lemma_number;
    self.lemma_number += 1;
    number
  }

  pub fn lookup_lemma(&self, n: usize) -> Option<&Prop> {
    self.all_lemmas.iter().find_map(|(lemma_number, p)|{
      if n == *lemma_number {
        Some(p)
      } else {
        None
      }
    })
  }

}

#[derive(Default)]
pub struct ProofInfo {
  pub solved_goal_proofs: BTreeMap<String, ProofLeaf>,
  pub proof: BTreeMap<String, ProofTerm>,
}

pub struct Timer {
  pub start_time: Instant,
}

impl Timer {
    fn new(start_time: Instant) -> Self { Self { start_time } }

  /// Has timeout been reached?
  pub fn timeout(&self) -> bool {
    CONFIG
      .timeout
      .map_or(false,
              |timeout| self.start_time.elapsed() > Duration::new(timeout, 0))
  }
}

pub struct ProofState<'a> {
  pub timer: Timer,
  pub lemmas_state: LemmasState,
  pub lemma_proofs: BTreeMap<usize, LemmaProofState<'a>>,
  pub global_search_state: GlobalSearchState<'a>,
}

pub struct LemmaProofState<'a> {
  pub prop: Prop,
  pub goals: VecDeque<Goal<'a>>,
  pub lemma_proof: ProofInfo,
  pub outcome: Option<Outcome>,
  pub proof_depth: usize,
  pub case_split_depth: usize,
  pub ih_lemma_number: usize,
  pub theorized_lemmas: ChainSet<Prop>,
  // FIXME: Should not be an option - if we can't get any rewrites from a lemma
  // we shouldn't try to prove it
  pub rw: Option<LemmaRewrite>,
}

impl<'a> LemmaProofState<'a> {
  pub fn new(lemma_number: usize, prop: Prop, premise: &Option<Equation>, global_search_state: GlobalSearchState<'a>, proof_depth: usize) -> Self {
    let lemma_name = format!("lemma_{}", lemma_number);
    let mut goal = Goal::top(&lemma_name, &prop, premise, global_search_state);
    let lemma_rw_opt = goal.make_lemma_rewrite(&goal.eq.lhs.expr, &goal.eq.rhs.expr, &goal.premises, false, lemma_number);
    let outcome = goal.cvecs_valid().and_then(|is_valid| {
      // println!("{} cvec is valid = {}", lemma_name, is_valid);
      // FIXME: Handle premises in cvecs so that we can reject invalid props
      // with preconditions
      if premise.is_none() && !is_valid {
        Some(Outcome::Invalid)
      } else {
        None
      }
    });
    // println!("{} {:?} ({} == {}) has initial outcome {:?}", lemma_name, prop.params, prop.eq.lhs, prop.eq.rhs, outcome);
    // FIXME: add the option to do more cvec checks like we do in the old try_prove_lemmas
    Self {
      prop,
      goals: [goal].into(),
      lemma_proof: ProofInfo::default(),
      outcome,
      proof_depth,
      case_split_depth: 0,
      ih_lemma_number: lemma_number,
      theorized_lemmas: ChainSet::default(),
      rw: lemma_rw_opt,
    }
  }

  pub fn add_possible_lemmas<I: IntoIterator<Item = Prop>>(&mut self, iter: I, lemmas_state: &LemmasState) {
    self.theorized_lemmas.extend(iter.into_iter().filter(|lemma| {
      let is_valid = lemmas_state.is_valid_new_prop(lemma);
      if is_valid {
        // println!("adding lemma: forall {:?} {} == {}" , lemma.params, lemma.eq.lhs, lemma.eq.rhs);
      }
      is_valid
    }));
  }

  pub fn try_next_goal(&mut self, timer: &Timer, lemmas_state: &mut LemmasState) {
    if self.goals.is_empty() {
      self.outcome = Some(Outcome::Valid);
      return;
    }
    // TODO: This should be info! but I don't know how to suppress all the info output from egg
    warn!("PROOF STATE: {}", pretty_state(&self));
    // Pop the first subgoal
    let mut goal = self.goals.pop_front().unwrap();
    // FIXME: need to run the analysis properly here
    // if goal.cvecs_valid() == Some(false) {
    //   // FIXME: add cvec counterexample to proof
    //   if CONFIG.verbose {
    //     println!("proved goal via cvec counterexample");
    //   }
    //   continue;
    // }
    // Saturate the goal
    goal.saturate(&lemmas_state.lemma_rewrites);
    if CONFIG.save_graphs {
      goal.save_egraph();
    }
    if let Some(proof_leaf) = goal.find_proof() {
      // println!("Proven goal {} has e-graph size {}, lhs/rhs size {}", goal.name, goal.egraph.total_number_of_nodes(), goal.egraph[goal.eq.lhs.id].nodes.len());
      self.process_goal_explanation(proof_leaf, &goal.name);
      return;

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
        for remaining_goal in &self.goals {
          println!("{} {}", "Remaining case".yellow(), remaining_goal.name);
        }
      }
      self.outcome = Some(Outcome::Invalid);
      return;
    }
    let (blocking_vars, blocking_exprs) =
      if !CONFIG.blocking_vars_analysis {
        warn!("Blocking var analysis is disabled");
        (goal.scrutinees.iter().map(|s| s.name).collect(), BTreeSet::default())
      } else {
        let (blocking_vars, blocking_exprs) = goal.find_blocking(&timer);
        if CONFIG.verbose {
          println!("blocking vars: {:?}", blocking_vars);
        }
        (blocking_vars, blocking_exprs)
      };

    // println!("searching for generalized lemmas");
    if CONFIG.generalization {
      // TODO: now that we generalize in the cc lemma search, do we need this?
      self.add_possible_lemmas(goal.find_generalized_goals(&blocking_exprs), lemmas_state);
    }
    // println!("searching for cc lemmas");
    if CONFIG.cc_lemmas {
      let possible_lemmas = goal.search_for_cc_lemmas(&timer, lemmas_state);
      self.add_possible_lemmas(possible_lemmas, lemmas_state);
    }
    // println!("done searching for cc lemmas");
    // This ends up being really slow so we'll just take the lemma duplication for now
    // It's unclear that it lets us prove that much more anyway.
    // state.add_cyclic_lemmas(&goal);

    goal.debug_search_for_patterns_in_egraph();

    if let Some(scrutinee) = goal.next_scrutinee(blocking_vars) {
      // let d = depth.max(depth_at_front);
      if scrutinee.depth > self.case_split_depth {
        // println!("depth {} is greater than current depth, increasing.", depth);
        self.case_split_depth = scrutinee.depth;
      }
      if self.case_split_depth >= CONFIG.max_split_depth {
        // println!("Bailing because depth is too high");
        // This goal could be further split, but we have reached the maximum depth,
        // we cannot prove or disprove the conjecture
        self.outcome = Some(Outcome::Unknown);
        return;
      }
      if CONFIG.verbose {
        println!(
          "{}: {}",
          "Case splitting and continuing".purple(),
          scrutinee.name.to_string().purple()
        );
      }
      let goal_name = goal.name.clone();
      let (proof_term, goals) = goal.case_split(scrutinee, &timer, lemmas_state, self.ih_lemma_number);
      // This goal is now an internal node in the proof tree.
      self.lemma_proof.proof.insert(goal_name, proof_term);
      // Add the new goals to the back of the VecDeque.
      self.goals.extend(goals);
    } else {
      if CONFIG.verbose {
        println!("{}", "Cannot case split: no blocking variables found".red());
        for remaining_goal in &self.goals {
          println!("{} {}", "Remaining case".yellow(), remaining_goal.name);
        }
      }
      // We cannot guarantee that the lemma is invalid if there are still
      // non-blocking variables of a higher case split depth than we will
      // consider.
      //
      // FIXME: Why?
      if goal.scrutinees.iter().any(|s| s.depth >= CONFIG.max_split_depth) {
        self.outcome = Some(Outcome::Unknown);
      } else {
        // FIXME: This used to be Invalid but that seems wrong?
        self.outcome = Some(Outcome::Unknown);
      }
    }
  }

  fn process_goal_explanation(&mut self, proof_leaf: ProofLeaf, goal_name: &str) {
    // This goal has been discharged, proceed to the next goal
    if CONFIG.verbose {
      println!("{} {} by {}", "Proved case".bright_blue(), goal_name, proof_leaf.name());
      println!("{}", proof_leaf);
    }
    self
      .lemma_proof
      .solved_goal_proofs
      .insert(goal_name.to_string(), proof_leaf);
  }

  /// Keep attempting goals until we encounter a goal with a hitherto unseen
  /// case split depth.
  pub fn try_goals_until_next_depth(&mut self, timer: &Timer, lemmas_state: &mut LemmasState) {
    let curr_depth = self.case_split_depth;
    while self.outcome.is_none() && self.case_split_depth == curr_depth && !timer.timeout() {
      self.try_next_goal(timer, lemmas_state);
    }
  }

  /// Iterate over all remaining goals, running them to saturation to see if any
  /// new lemmas solve them. If all of them are solved, the outcome is set to
  /// Some(Outcome::Valid).
  // TODO: Cleanup the code here.
  //
  // I've struggled with the borrow checker due to the definition of
  // `process_goal_explanation`. Realistically this should only require one or
  // two iterations and it shouldn't need all too many clones or additional data
  // structures. But this probably isn't too critical because there shouldn't be
  // too many goals in the list ever.
  pub fn try_finish_goals(&mut self, lemmas_state: &LemmasState) {
    let proofs: Vec<(usize, ProofLeaf)> = self.goals.iter_mut().enumerate().flat_map(|(i, goal)| {
      goal.saturate(&lemmas_state.lemma_rewrites);
      goal.find_proof().map(|proof_leaf| (i, proof_leaf))
    }).collect();
    let indices_to_remove: Vec<usize> = proofs.iter().map(|(i, _)| *i).collect();
    for (i, proof_leaf) in proofs {
      self.process_goal_explanation(proof_leaf, &self.goals[i].name.clone());
    }
    let mut i = 0;
    self.goals.retain(|_| {
      let keep = !indices_to_remove.contains(&i);
      i += 1;
      keep
    });
    if self.goals.is_empty() {
      self.outcome = Some(Outcome::Valid);
    }
  }
}

impl<'a> ProofState<'a> {

  pub fn prove_lemma(&mut self, lemma_number: usize) -> Outcome {
    let mut lemma_proof_state = self.lemma_proofs.remove(&lemma_number).unwrap();

    while lemma_proof_state.outcome.is_none() {
      lemma_proof_state.try_goals_until_next_depth(&self.timer, &mut self.lemmas_state);

      if lemma_proof_state.outcome.is_some() {
        let outcome = lemma_proof_state.outcome.as_ref().unwrap().clone();
        if outcome == Outcome::Valid {
          self.lemmas_state.proven_lemmas.insert(lemma_proof_state.prop.clone());
          lemma_proof_state.rw.as_ref().map(|rw| rw.add_to_rewrites(&mut self.lemmas_state.lemma_rewrites));
        }
        if outcome == Outcome::Invalid {
          self.lemmas_state.invalid_lemmas.insert(lemma_proof_state.prop.clone());
        }
        self.lemma_proofs.insert(lemma_number, lemma_proof_state);
        return outcome.clone();
      }

      let next_goal = lemma_proof_state.goals.front_mut().unwrap();

      self.try_prove_lemmas(&lemma_proof_state.theorized_lemmas, next_goal, lemma_proof_state.proof_depth);
    }

    let outcome = lemma_proof_state.outcome.as_ref().unwrap().clone();
    self.lemma_proofs.insert(lemma_number, lemma_proof_state);
    outcome

  }

  fn try_prove_lemmas(&mut self, lemmas: &ChainSet<Prop>, goal: &mut Goal, proof_depth: usize) {
    let lemma_chains = lemmas.chains.clone();
    for chain in lemma_chains.iter() {
      for (i, lemma_prop) in chain.chain.iter().enumerate() {
        if self.timer.timeout() {
          return;
        }
        let lemma_number = self.lemmas_state.find_or_make_fresh_lemma(lemma_prop);
        let (lemma_outcome, lemma_rws) = {
          let lemma_proof_state = self.lemma_proofs.entry(lemma_number).or_insert_with(|| {
          LemmaProofState::new(lemma_number, lemma_prop.clone(), &None, self.global_search_state, proof_depth + 1)
          });
          (lemma_proof_state.outcome.clone(), lemma_proof_state.rw.as_ref().map(|rw| rw.rewrites()).unwrap_or(vec!()))
        };
        // If we already know the result, don't bother trying to prove it
        if lemma_outcome == Some(Outcome::Invalid) || lemma_outcome == Some(Outcome::Valid) {
          break;
        }
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
          let rewrites = goal.global_search_state.reductions.iter().chain(goal.lemmas.values()).chain(lemma_rws.iter()).chain(self.lemmas_state.lemma_rewrites.values());
          let runner = Runner::default()
            // .with_explanations_enabled()
            .with_egraph(goal_egraph_copy)
            .run(rewrites);
          if runner.egraph.find(goal.eq.lhs.id) != runner.egraph.find(goal.eq.rhs.id) {
            break;
          }
        }
        println!("Trying to prove lemma: forall {}. {} = {}", lemma_prop.params.iter().map(|(v, t)| format!("{}: {}", v, t)).join(" "), lemma_prop.eq.lhs, lemma_prop.eq.rhs);

        self.prove_lemma(lemma_number);
        let lemma_outcome = &self.lemma_proofs.get(&lemma_number).unwrap().outcome;
        if lemma_outcome == &Some(Outcome::Valid) {
          println!("proved {} = {}", lemma_prop.eq.lhs, lemma_prop.eq.rhs);
          goal.saturate(&self.lemmas_state.lemma_rewrites);
          if goal.find_proof().is_some() {
            return;
          }
          break;
        }
      }
    }

  }

  pub fn prove_breadth_first(&mut self, top_level_lemma_number: usize) -> Outcome {
    let mut i = 0;
    loop {
      i += 1;
      // println!("Lemma proving loop iteration {}", i);
      let mut new_lemmas = vec!();
      for (lemma_number, lemma_proof_state) in self.lemma_proofs.iter_mut() {
        if self.timer.timeout() {
          return Outcome::Timeout;
        }
        if lemma_proof_state.outcome.is_some() {
          // If we have an actual outcome on the lemma we care about it, return it
          if *lemma_number == top_level_lemma_number && lemma_proof_state.outcome != Some(Outcome::Unknown) {
            return lemma_proof_state.outcome.as_ref().unwrap().clone();
          // If we ran out of gas trying to prove this lemma, we can still try
          // to finish it
          } else if lemma_proof_state.outcome == Some(Outcome::Unknown) {
            lemma_proof_state.try_finish_goals(&self.lemmas_state);
            // If there was a change, try returning the now solved goal.
            if lemma_proof_state.outcome != Some(Outcome::Unknown) {
              return lemma_proof_state.outcome.as_ref().unwrap().clone();
            }
          }
          continue;
        }
        // println!("Trying to prove {} = {}", lemma_proof_state.prop.eq.lhs, lemma_proof_state.prop.eq.rhs);
        lemma_proof_state.try_goals_until_next_depth(&self.timer, &mut self.lemmas_state);
        if lemma_proof_state.outcome == Some(Outcome::Valid) {
          self.lemmas_state.proven_lemmas.insert(lemma_proof_state.prop.clone());
          lemma_proof_state.rw.as_ref().map(|rw| rw.add_to_rewrites(&mut self.lemmas_state.lemma_rewrites));
        }
        if lemma_proof_state.outcome == Some(Outcome::Invalid) {
          self.lemmas_state.invalid_lemmas.insert(lemma_proof_state.prop.clone());
        }
        for lemma_chain in &lemma_proof_state.theorized_lemmas.chains {
          for lemma in lemma_chain.chain.iter() {
            new_lemmas.push((lemma.clone(), lemma_proof_state.proof_depth + 1));
          }
        }
      }
      for (new_lemma, new_lemma_proof_depth) in new_lemmas {
        if self.timer.timeout() {
          return Outcome::Timeout;
        }
        if new_lemma_proof_depth > CONFIG.proof_depth {
          continue;
        }
        let new_lemma_number = self.lemmas_state.find_or_make_fresh_lemma(&new_lemma);
        self.lemma_proofs.entry(new_lemma_number).or_insert_with(|| {
          LemmaProofState::new(new_lemma_number, new_lemma, &None, self.global_search_state, new_lemma_proof_depth)
        });
      }
    }
  }

  // /// Try to prove all of the lemmas we've collected so far.
  //  pub fn try_prove_lemmas(&mut self, goal: &mut Goal) -> Option<ProofLeaf> {
  //   if self.proof_depth == CONFIG.proof_depth {
  //     return None;
  //   }
  //   // println!("Try prove lemmas for goal {}", goal.name);
  //   // self.lemmas_state.possible_lemmas.chains.iter().for_each(|chain| chain.chain.iter().for_each(|lem| println!("lemma: {} = {}", lem.eq.lhs, lem.eq.rhs)));

  //   // Need to copy so we can mutably borrow self later
  //   let lemma_chains = self.lemmas_state.possible_lemmas.chains.clone();
  //   for chain in lemma_chains.iter() {
  //     for (i, lemma_prop) in chain.chain.iter().enumerate() {
  //       if self.timeout() {
  //         return None;
  //       }
  //       // Is the lemma already proven or subsumed by a cyclic lemma?
  //       if self.lemmas_state.proven_lemmas.contains_leq(&lemma_prop) || self.lemmas_state.cyclic_lemmas.contains_leq(&lemma_prop) {
  //         continue;
  //       }
  //       // Is the lemma invalid?
  //       // if self.lemmas_state.invalid_lemmas.contains_geq(&lemma_prop) {
  //       //   continue;
  //       // }
  //       let goal_name = format!("lemma-{}={}", lemma_prop.eq.lhs, lemma_prop.eq.rhs);
  //       let mut new_goal = Goal::top(&goal_name,
  //                                &lemma_prop,
  //                                &None,
  //                                goal.global_search_state,
  //       );
  //       let try1 = new_goal.cvecs_valid() == Some(true);
  //       let mut new_goal_2 = Goal::top(&goal_name,
  //                                &lemma_prop,
  //                                &None,
  //                                goal.global_search_state,
  //       );
  //       let try2 = new_goal_2.cvecs_valid() == Some(true);
  //       if try1 && !try2 {
  //         // println!("Second try helped");
  //         // println!("Invalidated lemma {} = {}", lemma_prop.eq.lhs, lemma_prop.eq.rhs);
  //       }
  //       if !try1 || !try2 {
  //         warn!("Invalidated lemma {} = {}", lemma_prop.eq.lhs, lemma_prop.eq.rhs);
  //         self.lemmas_state.invalid_lemmas.insert(lemma_prop.clone());
  //         continue;
  //       } else {
  //         println!("Possible lemma to prove: {} = {}", lemma_prop.eq.lhs, lemma_prop.eq.rhs);
  //         // println!("proven lemmas so far: {}", self.lemmas_state.proven_lemmas.elems.iter().map(|e| format!("{} = {}", e.eq.lhs, e.eq.rhs)).join(","));
  //         // print_cvec(&new_goal.egraph.analysis.cvec_analysis, new_goal_lhs_cvec)
  //       }

  //       // FIXME: Use a proper name scheme for indexing lemmas instead of using
  //       // their serialized lhs = rhs (we can use the lemma numbering for this).
  //       // We should also normalize lemmas so that they have the same names
  //       // regardless of the names of their variables. Maybe this means
  //       // converting to a locally nameless form.
  //       //
  //       // NOTE: This doesn't actually skip that many lemmas because we don't
  //       // carry old lemmas around with us. Maybe we should and see if this is
  //       // useful or maybe we should
  //       let lemma_prop_name = format!("{} = {}", lemma_prop.eq.lhs, lemma_prop.eq.rhs);
  //       // NOTE: Having None in the hashmap is meaningfully different from
  //       // having no entry in the hashmap. We always try and prove if there is
  //       // no entry.
  //       if let Some(last_lemma_proven_at_last_attempt) = self.lemmas_state.last_lemma_proven_at_last_attempt.get(&lemma_prop_name) {
  //         if last_lemma_proven_at_last_attempt == &self.lemmas_state.last_lemma_proven {
  //           println!("Skipping lemma because nothing has changed");
  //           continue;
  //         } else {
  //           println!("New lemma proven since last attempt");
  //         }
  //       }
  //       self.lemmas_state.last_lemma_proven_at_last_attempt.insert(lemma_prop_name, self.lemmas_state.last_lemma_proven.clone());

  //       let new_lemma_name = self.fresh_lemma_name();
  //       let lemma_rw_opt = new_goal.make_lemma_rewrite(&new_goal.eq.lhs.expr, &new_goal.eq.rhs.expr, &new_goal.premises, false, new_lemma_name.clone());
  //       // If we can't make a rewrite out of this lemma, it's not useful to us, so we'll just keep going.
  //       let lemma_rw = match lemma_rw_opt {
  //         None => continue,
  //         Some(lemma_rw) => lemma_rw,
  //       };
  //       // NOTE CK: This used to be necessary for speed, but with some patches to efficiency, we
  //       // no longer need it. Perhaps if we allowed a greater proof depth we would need it.
  //       // // HACK: Optimization to proving lemmas
  //       // // We will always try to prove the most general lemma we've theorized so far, but thereafter
  //       // // we require that the lemma be actually useful to us if we are going to try and prove it.
  //       // //
  //       // // This eliminates us spending time trying to prove a junk lemma like
  //       // // (mult (S n) Z) = (plus (mult (S n) Z) Z)
  //       // // when we already failed to prove the more general lemma
  //       // // (mult n Z) = (plus (mult n Z) Z)
  //       // //
  //       // // Really we should have more sophisticated lemma filtering - the junk
  //       // // lemma in this case is really no easier to prove than the first lemma
  //       // // (since we will try to prove it eventually when we case split the first),
  //       // // so we shouldn't consider it in the first place.
  //       // //
  //       // // Hence why I consider this optimization a hack, even though it
  //       // // probably avoids some lemmas which are junky in a more complicated
  //       // // way. I imagine it might rarely pass on interesting and useful lemmas.
  //       // // This is because sometimes you need more than one lemma to prove a goal.
  //       if i > 0 {
  //         let goal_egraph_copy = goal.egraph.clone();
  //         let new_lemma_rws = lemma_rw.rewrites();
  //         let rewrites = goal.global_search_state.reductions.iter().chain(goal.lemmas.values()).chain(new_lemma_rws.iter()).chain(self.lemmas_state.lemma_rewrites.values());
  //         let runner = Runner::default()
  //           // .with_explanations_enabled()
  //           .with_egraph(goal_egraph_copy)
  //           .run(rewrites);
  //         if runner.egraph.find(goal.eq.lhs.id) != runner.egraph.find(goal.eq.rhs.id) {
  //           break;
  //         }
  //       }
  //       println!("Trying to prove lemma: forall {}. {} = {}", lemma_prop.params.iter().map(|(v, t)| format!("{}: {}", v, t)).join(" "), lemma_prop.eq.lhs, lemma_prop.eq.rhs);

  //       let new_lemma_eq = &lemma_rw.lemma_prop;
  //       // Give the new goal the new lemma's name so that we can match its proof.
  //       // Actually this isn't necessary for anything other than prettying the output,
  //       // but having the name be ugly is better for debugging.
  //       new_goal.name = new_lemma_name.clone();
  //       let mut new_lemmas_state = self.lemmas_state.clone();
  //       // Zero out the possible lemmas and cyclic lemmas, we only want
  //       // to carry forward what we've proven already.
  //       new_lemmas_state.possible_lemmas = ChainSet::new();
  //       new_lemmas_state.cyclic_lemmas = ChainSet::new();
  //       new_lemmas_state.cyclic_lemma_rewrites = BTreeMap::new();
  //       let (outcome, ps) = prove(new_goal, self.proof_depth + 1, new_lemmas_state, new_lemma_name.clone(), self.lemma_number);
  //       // Update the lemma number so we don't have a lemma name clash.
  //       self.lemma_number = ps.lemma_number;
  //       // Steal the lemmas we got from the recursive proving, as well as any
  //       // other info we learned from the lemmas state.
  //       self.lemmas_state.proven_lemmas.extend(ps.lemmas_state.proven_lemmas.elems);
  //       self.lemmas_state.invalid_lemmas.extend(ps.lemmas_state.invalid_lemmas.elems);
  //       self.lemmas_state.lemma_rewrites.extend(ps.lemmas_state.lemma_rewrites);
  //       self.lemmas_state.last_lemma_proven = ps.lemmas_state.last_lemma_proven;
  //       self.lemmas_state.last_lemma_proven_at_last_attempt.extend(ps.lemmas_state.last_lemma_proven_at_last_attempt);
  //       self.lemma_proofs.extend(ps.lemma_proofs);
  //       if outcome == Outcome::Valid {
  //         println!("proved {} = {}", lemma_prop.eq.lhs, lemma_prop.eq.rhs);
  //         // TODO: This comes for free in the proven lemmas we get, so we
  //         // probably don't need to insert it.
  //         self.lemmas_state.proven_lemmas.insert(lemma_prop.clone());
  //         self.lemmas_state.lemma_rewrites.extend(lemma_rw.names_and_rewrites());
  //         // Add any cyclic lemmas we proved too
  //         self.lemmas_state.proven_lemmas.extend(ps.lemmas_state.cyclic_lemmas.chains.into_iter().flat_map(|chain| chain.chain.into_iter()));
  //         self.lemmas_state.lemma_rewrites.extend(ps.lemmas_state.cyclic_lemma_rewrites);
  //         // Add its proof
  //         self.lemma_proofs.push((new_lemma_name.clone(), new_lemma_eq.clone(), ps.proof_info));
  //         // This is now the last lemma we've proven
  //         self.lemmas_state.last_lemma_proven = Some(new_lemma_name);
  //         goal.saturate(&self.lemmas_state.lemma_rewrites);
  //         let proof = goal.find_proof();
  //         if proof.is_some() {
  //           return proof;
  //         }
  //         break;
  //       }
  //       // TODO: We want to record that all of the previous lemmas including
  //       // this are invalid, but for now we won't record anything.
  //       if outcome == Outcome::Invalid {
  //         self.lemmas_state.invalid_lemmas.insert(lemma_prop.clone());
  //       } else {
  //         // NOTE: We will try to prove a lemma twice
  //         // self.lemmas_state.proven_lemmas.insert(lemma_prop.clone());
  //       }
  //     }
  //   }
  //   None
  // }

  // pub fn add_cyclic_lemmas(&mut self, goal: &Goal) {
  //   // FIXME: add premises properly
  //   if !goal.premises.is_empty() {
  //     return;
  //   }
  //   let (rws, lemma_rws) = goal.make_cyclic_lemma_rewrites(self, false);
  //   self.lemmas_state.cyclic_lemmas.extend(lemma_rws.into_iter().map(|lemma_rw| lemma_rw.lemma_prop));
  //   self.lemmas_state.cyclic_lemma_rewrites.extend(rws);
  // }

}

/// Pretty-printed proof state
pub fn pretty_state(state: &LemmaProofState) -> String {
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
#[derive(Debug, PartialEq, PartialOrd, Eq, Ord, Clone)]
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

fn find_proof(eq: &ETermEquation, egraph: &mut Eg) -> Option<ProofLeaf> {
  let resolved_lhs_id = egraph.find(eq.lhs.id);
  let resolved_rhs_id = egraph.find(eq.rhs.id);
  // Have we proven LHS == RHS?
  if resolved_lhs_id == resolved_rhs_id {
    return Some(ProofLeaf::Refl(
      egraph
        .explain_equivalence(&eq.lhs.expr, &eq.rhs.expr)
    ));
  }

  match (&egraph[resolved_lhs_id].data.canonical_form_data, &egraph[resolved_rhs_id].data.canonical_form_data) {
    (CanonicalForm::Const(c1), CanonicalForm::Const(c2)) if c1 != c2 => {
      return Some(ProofLeaf::Todo);
    }
    _ => {}
  }

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
      if egraph.lookup(n1.clone()).is_none() || egraph.lookup(n2.clone()).is_none() {
        println!("One of {} or {} was removed from the e-graph! We can't emit a proof", n1, n2);
        None
      } else {
        // This is here only for the purpose of proof generation:
        let extractor = Extractor::new(&egraph, AstSize);
        let expr1 = extract_with_node(n1, &extractor);
        let expr2 = extract_with_node(n2, &extractor);
        if CONFIG.verbose {
          println!("{}: {} = {}", "UNREACHABLE".bright_red(), expr1, expr2);
        }
        Some((expr1, expr2))
      }
    } else {
      None
    }
  });
  inconsistent_exprs.map(|(expr1, expr2)| {
    let explanation = egraph.explain_equivalence(&expr1, &expr2);
    ProofLeaf::Contradiction(explanation)
  })

}

pub fn prove_top<'a>(goal_prop: Prop, goal_premise: Option<Equation>, global_search_state: GlobalSearchState<'a>) -> (Outcome, ProofState) {
  let mut proof_state = ProofState {
    timer: Timer::new(Instant::now()),
    lemmas_state: LemmasState::default(),
    lemma_proofs: BTreeMap::default(),
    global_search_state,
  };

  let top_goal_lemma_number = proof_state.lemmas_state.fresh_lemma();
  let top_goal_lemma_proof = LemmaProofState::new(top_goal_lemma_number, goal_prop, &goal_premise, global_search_state, 0);
  proof_state.lemma_proofs.insert(top_goal_lemma_number, top_goal_lemma_proof);

  // let outcome = proof_state.prove_lemma(top_goal_lemma_number);
  let outcome = proof_state.prove_breadth_first(top_goal_lemma_number);

  (outcome, proof_state)

  // let top_goal_state = proof_state.lemma_proofs.get_mut(&top_goal_lemma_number).unwrap();
  // while top_goal_state.outcome.is_none() {
  //   top_goal_state.try_goals_until_next_depth(&proof_state, &mut proof_state.lemmas_state);

  //   if proof_state.timeout() {
  //     return (Outcome::Timeout, proof_state);
  //   }

  //   // proof_state.try_prove_lemmas(top_goal_state.theorized_lemmas);

  // }

  // return (outcome, proof_state);
}
