use colored::Colorize;
use egg::*;
use itertools::Itertools;
use log::warn;
use std::collections::HashSet;
use std::collections::{hash_map::Entry, HashMap, VecDeque};
use std::fmt::Display;
use std::iter::{zip, empty};
use std::time::{Duration, Instant};
use symbolic_expressions::{parser, Sexp};

use crate::analysis::{CycleggAnalysis, CanonicalFormAnalysis, CanonicalForm, Cvec, cvecs_equal, print_cvec};
use crate::ast::*;
use crate::config::*;
use crate::egraph::*;
use crate::utils::*;

// We will use SymbolLang for now
pub type Eg = EGraph<SymbolLang, CycleggAnalysis>;
pub type Rw = Rewrite<SymbolLang, CycleggAnalysis>;
pub type CvecRw = Rewrite<SymbolLang, ()>;

/// A special scrutinee name used to signal that case split bound has been exceeded
const BOUND_EXCEEDED: &str = "__";
pub const LEMMA_PREFIX: &str = "lemma-";
pub const CC_LEMMA_PREFIX: &str = "cc-lemma-";
pub const IH_EQUALITY_PREFIX: &str = "ih-equality-"; // TODO: remove

/// Condition that checks whether it is sound to apply a lemma
#[derive(Clone)]
pub struct Soundness {
  /// A substitution from lemma's free variables
  /// to the original e-classes these variables came from
  pub free_vars: IdSubst,
  /// All premises that must hold for this lemma to apply,
  /// expressed in terms of the free variables
  pub premises: Vec<Equation>,
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
  fn smaller_tuple(&self, triples: &Vec<(Symbol, Expr, Expr)>, blocking_vars: &HashSet<Symbol>) -> bool {
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
  fn check_premise(premise: &Equation, triples: &[(Symbol, Expr, Expr)], egraph: &Eg) -> bool {
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
        if !egraph.analysis.blocking_vars.contains(x) {
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

/// An equation is a pair of terms
#[derive(Debug, Clone)]
pub struct Equation {
  pub lhs: ETerm,
  pub rhs: ETerm,
}

impl Display for Equation {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{} === {}", self.lhs.sexp, self.rhs.sexp)
  }
}

// TODO: make it work for RawEqWithParams, need to take in global context
fn find_generalizations_raw_eq(raw_eq: &RawEqWithParams, global_context: &Context, fresh_name: String) -> Vec<RawEqWithParams> {
  let lhs_nontrivial_subexprs = nontrivial_sexp_subexpressions_containing_vars(&raw_eq.eq.lhs);
  let rhs_nontrivial_subexprs = nontrivial_sexp_subexpressions_containing_vars(&raw_eq.eq.rhs);
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
      let new_lhs = substitute_sexp(&raw_eq.eq.lhs, subexpr, &generalized_var);
      let new_rhs = substitute_sexp(&raw_eq.eq.rhs, subexpr, &generalized_var);
      let lhs_vars = sexp_leaves(&new_lhs);
      let rhs_vars = sexp_leaves(&new_lhs);
      let mut new_params = raw_eq.params.clone();
      // Only keep the vars that remain after substituting.
      new_params.retain(|(var, _ty)| lhs_vars.contains(&var.to_string()) || rhs_vars.contains(&var.to_string()));
      new_params.push((var_symb, ty));
      // println!("Genearlization candidate: {} = {}", new_lhs, new_rhs);
      output.push(RawEqWithParams::new(RawEquation::new(new_lhs, new_rhs), new_params));
    }
  }
  output
}


impl Equation {
  /// Add both sides of a raw equation to the egraph,
  /// producing an equation;
  /// if assume is true, also union the the two sides
  fn new(eq: &RawEquation, egraph: &mut Eg, assume: bool) -> Self {
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

/// Proof goal
pub struct Goal<'a> {
  /// Goal name
  pub name: String,
  /// Equivalences we already proved
  pub egraph: Eg,
  /// Rewrites are split into reductions (invertible rules) and lemmas (non-invertible rules)
  reductions: &'a Vec<Rw>,
  // HACK: an identical copy to the reductions used for the cvec egraph.
  // This is because of type system stuff.
  cvec_reductions: &'a Vec<CvecRw>,
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
  scrutinees: VecDeque<(Symbol, usize)>,
  /// Variables that we have already case split
  pub case_split_vars: HashSet<Symbol>,
  /// Instantiations of the induction hypothesis that are in the egraph
  grounding_instantiations: Vec<IdSubst>,
  /// The equation we are trying to prove
  pub eq: Equation,
  /// If this is a conditional prop, the premises
  pub premises: Vec<Equation>,
  /// Environment
  pub env: &'a Env,
  /// Global context (i.e. constructors and top-level bindings)
  pub global_context: &'a Context,

  /// If the goal is discharged, an explanation of the proof
  pub explanation: Option<Explanation<SymbolLang>>,
  /// Definitions in a form amenable to proof emission
  pub defns: &'a Defns,
  /// Stores the expression each guard variable maps to
  guard_exprs: HashMap<String, Expr>,
  /// Searchers for whether the LHS and RHS of some rewrite appears in our
  /// e-graph.
  pub searchers: &'a Vec<ConditionalSearcher<Pattern<SymbolLang>, Pattern<SymbolLang>>>,
}

impl<'a> Goal<'a> {
  /// Create top-level goal
  pub fn top(
    name: &str,
    eq: &RawEquation,
    premise: &Option<RawEquation>,
    params: Vec<(Symbol, Type)>,
    env: &'a Env,
    global_context: &'a Context,
    reductions: &'a Vec<Rw>,
    cvec_reductions: &'a Vec<CvecRw>,
    defns: &'a Defns,
    searchers: &'a Vec<ConditionalSearcher<Pattern<SymbolLang>, Pattern<SymbolLang>>>,
  ) -> Self {
    let mut egraph: Eg = EGraph::default().with_explanations_enabled();
    let eq = Equation::new(eq, &mut egraph, false);
    let premise = premise
      .as_ref()
      .map(|eq| Equation::new(eq, &mut egraph, true));
    let var_classes = lookup_vars(&egraph, params.iter().map(|(x, _)| x));

    let mut res = Self {
      name: name.to_string(),
      // The only instantiation we have so far is where the parameters map to themselves
      var_classes: var_classes.clone(),
      grounding_instantiations: vec![var_classes.clone()],
      egraph,
      explanation: None,
      reductions,
      cvec_reductions,
      lemmas: HashMap::new(),
      local_context: Context::new(),
      params: params.iter().map(|(x, _)| *x).collect(),
      case_split_vars: HashSet::new(),
      guard_exprs: HashMap::new(),
      scrutinees: VecDeque::new(),
      eq,
      // Convert to a singleton list if the Option is Some, else the empty list
      premises: premise.into_iter().collect(),
      env,
      global_context,
      defns,
      searchers,
    };
    // FIXME: this could really also be a reference. Probably not necessary
    // for efficiency reason but yeah.
    res.egraph.analysis.cvec_analysis.reductions = cvec_reductions.clone();
    // res.egraph.classes().for_each(|c| println!("class {}: {}, timestamp: {}", c.id, c.data.canonical_form_data.get_enode(), c.data.timestamp));
    for (name, ty) in params {
      res.add_scrutinee(name, &ty, 0);
      res.local_context.insert(name, ty);
    }
    res.build_cvecs();
    // let lhs_cvec = &res.egraph[res.eq.lhs.id].data.cvec_data;
    // let rhs_cvec = &res.egraph[res.eq.rhs.id].data.cvec_data;
    // println!("{}: lhs_cvecs: {:?}, rhs_cvecs: {:?}", res.name, res.egraph[res.eq.lhs.id].data.cvec_data, res.egraph[res.eq.rhs.id].data.cvec_data);
    // println!("eq? {:?}", cvecs_equal(&res.egraph.analysis.cvec_analysis, lhs_cvec, rhs_cvec));
    // res.eq.find_generalizations();
    res
  }

  fn build_cvecs(&mut self) {
    self.egraph.analysis.cvec_analysis.timestamp += 1;
    for name in self.params.iter() {
      let ty = &self.local_context[name];
      if !ty.is_arrow() {
        let var_id = self.var_classes[name];
        let var_cvec = self.egraph.analysis.cvec_analysis.make_cvec_for_type(&ty, self.env, &self.global_context);
        let mut analysis = self.egraph[var_id].data.clone();
        analysis.timestamp = self.egraph.analysis.cvec_analysis.timestamp;
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

  pub fn copy(&self) -> Self {
    Goal {
      name: self.name.clone(),
      egraph: self.egraph.clone(),
      reductions: self.reductions,
      cvec_reductions: self.cvec_reductions,
      lemmas: HashMap::new(), // the lemmas will be re-generated immediately anyway
      local_context: self.local_context.clone(),
      var_classes: self.var_classes.clone(),
      params: self.params.clone(),
      case_split_vars: self.case_split_vars.clone(),
      scrutinees: self.scrutinees.clone(),
      grounding_instantiations: self.grounding_instantiations.clone(),
      eq: self.eq.clone(),
      premises: self.premises.clone(),
      env: self.env,
      global_context: self.global_context,
      // NOTE: We don't really need to clone this.
      defns: self.defns,
      // If we reach this point, I think we won't have an explanation
      explanation: None,
      guard_exprs: self.guard_exprs.clone(),
      searchers: self.searchers,
    }
  }

  /// Saturate the goal by applying all available rewrites
  pub fn saturate(&mut self, top_lemmas: &HashMap<String, Rw>) {
    let rewrites = self.reductions.iter().chain(self.lemmas.values()).chain(top_lemmas.values());
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

  fn get_explanation_and_validity(eq: &Equation, egraph: &mut Eg) -> (Option<Explanation<SymbolLang>>, bool) {
    if egraph.find(eq.lhs.id) == egraph.find(eq.rhs.id) {
      // We have shown that LHS == RHS
      (Some(
          egraph
          .explain_equivalence(&eq.lhs.expr, &eq.rhs.expr),
      ),
      true)
    } else {
      let mut explanation = None;
      // Check if this case in unreachable (i.e. if there are any inconsistent
      // e-classes in the e-graph)
      //
      // FIXME: I've hacked it such that we only get an explanation from the
      // contradiction. If we find a contradiction from the cvecs, we need to
      // first find which enode the cvec came from, then we need to find explain
      // why those nodes are equal, then we need to provide the concrete values
      // that cause them to be unequal. This will probably require us to update
      // the Cvec analysis to track enodes, which is a little unfortunate.
      let res = egraph.classes().find_map(|eclass| {
        if let CanonicalForm::Inconsistent(n1, n2) = &eclass.data.canonical_form_data {
          // This is here only for the purpose of proof generation:
          let extractor = Extractor::new(&egraph, AstSize);
          let expr1 = extract_with_node(n1, &extractor);
          let expr2 = extract_with_node(n2, &extractor);
          if CONFIG.verbose {
            println!("{}: {} = {}", "UNREACHABLE".bright_red(), expr1, expr2);
          }
          Some(((expr1, expr2), true))
        // } else if let Cvec::Contradiction(id1, id2) = &eclass.data.cvec_data {
        //   let cvec_egraph = egraph.analysis.cvec_analysis.cvec_egraph.borrow();
        //   let cvec_extractor = Extractor::new(&cvec_egraph, AstSize);
        //   let (_, expr1) = cvec_extractor.find_best(*id1);
        //   let (_, expr2) = cvec_extractor.find_best(*id2);
        //   if CONFIG.verbose {
        //     println!("{}: {} = {}", "CONTRADICTION".bright_red(), expr1, expr2);
        //   }
        //   Some(((expr1, expr2), false))
        } else {
          None
        }
      });
      let is_valid = res.is_some();
      if let Some(((expr1, expr2), true)) = &res {
        explanation = Some(egraph.explain_equivalence(&expr1, &expr2));
      }
      (explanation, is_valid)
    }

  }

  /// Check if the goal has been discharged,
  /// and if so, create an explanation.
  pub fn check_validity(&mut self) -> bool {
    // for eclass in self.egraph.classes() {
    //   println!("{}: {:?} CANONICAL {}", eclass.id, eclass.nodes, ConstructorFolding::extract_canonical(&self.egraph, eclass.id).unwrap_or(vec![].into()));
    // }

    let (explanation, is_valid) = Goal::get_explanation_and_validity(&self.eq, &mut self.egraph);
    self.explanation = explanation;
    is_valid
  }

  /// Check whether an expression is reducible using this goal's reductions
  pub fn is_reducible(&self, expr: &Expr) -> bool {
    let mut local_graph: Eg = Default::default();
    local_graph.add_expr(expr);
    local_graph.rebuild();
    for reduction in self.reductions {
      if !reduction.search(&local_graph).is_empty() {
        return true;
      }
    }
    false
  }


  fn make_rewrites_from(&self, lhs_id: Id, rhs_id: Id, premises: Vec<Equation>, exprs: HashMap<Id, Vec<Expr>>, state: &ProofState, add_termination_check: bool) -> (HashMap<String, Rw>, Vec<String>, Vec<RawEqWithParams>) {
    let is_var = |v| self.local_context.contains_key(v);
    let mut rewrites = self.lemmas.clone();
    let mut added_rewrite_names = vec!();
    let mut rewrite_eqs = vec!();
    for lhs_expr in exprs.get(&lhs_id).unwrap() {
      let lhs: Pattern<SymbolLang> = to_pattern(lhs_expr, is_var);
      if (CONFIG.irreducible_only && self.is_reducible(lhs_expr)) || has_guard_wildcards(&lhs) {
        continue;
      }
      for rhs_expr in exprs.get(&rhs_id).unwrap() {
        if state.timeout() {
          return (rewrites, added_rewrite_names, rewrite_eqs);
        }

        let rhs: Pattern<SymbolLang> = to_pattern(rhs_expr, is_var);
        if (CONFIG.irreducible_only && self.is_reducible(rhs_expr)) || has_guard_wildcards(&rhs) {
          continue;
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
          continue;
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
        let mut added_lemma = false;
        if rhs_vars.is_subset(&lhs_vars) {
          // if rhs has no extra wildcards, create a lemma lhs => rhs
          if add_termination_check {
            Goal::add_lemma(lhs.clone(), rhs.clone(), condition.clone(), &mut rewrites, &mut added_rewrite_names);
          } else {
            Goal::add_unchecked_lemma(lhs.clone(), rhs.clone(), &mut rewrites, &mut added_rewrite_names);
          }
          let rewrite_eq = RawEquation::from_exprs(lhs_expr, rhs_expr);

          rewrite_eqs.push(RawEqWithParams {
            eq: rewrite_eq,
            params: params.clone(),
          });
          added_lemma = true;
          if CONFIG.single_rhs {
            continue;
          };
        }
        if lhs_vars.is_subset(&rhs_vars) {
          // if lhs has no extra wildcards, create a lemma rhs => lhs;
          // in non-cyclic mode, a single direction of IH is always sufficient
          // (because grounding adds all instantiations we could possibly care about).
          if add_termination_check {
            Goal::add_lemma(rhs.clone(), lhs.clone(), condition.clone(), &mut rewrites, &mut added_rewrite_names);
          } else {
            Goal::add_unchecked_lemma(rhs.clone(), lhs.clone(), &mut rewrites, &mut added_rewrite_names);
          }
          let rewrite_eq = RawEquation::from_exprs(lhs_expr, rhs_expr);
          rewrite_eqs.push(RawEqWithParams {
            eq: rewrite_eq,
            params,
          });
          added_lemma = true;
          if CONFIG.single_rhs {
            continue;
          };
        }
        if !added_lemma {
          warn!("cannot create a lemma from {} and {}", lhs, rhs);
        }
      }
    }
    (rewrites, added_rewrite_names, rewrite_eqs)
  }

  /// Create a rewrite `lhs => rhs` which will serve as the lemma ("induction hypothesis") for a cycle in the proof;
  /// here lhs and rhs are patterns, created by replacing all scrutinees with wildcards;
  /// soundness requires that the pattern only apply to variable tuples smaller than the current scrutinee tuple.
  fn add_lemma_rewrites(&self, state: &ProofState) -> HashMap<String, Rw> {
    let lhs_id = self.egraph.find(self.eq.lhs.id);
    let rhs_id = self.egraph.find(self.eq.rhs.id);

    if CONFIG.is_cyclic() {
      // If we are doing cyclic proofs: make lemmas out of all LHS and RHS variants
      self.make_cyclic_lemmas(state, true).0
    } else {
      // In the non-cyclic case, only use the original LHS and RHS
      // and only if no other lemmas have been added yet
      let mut exprs: HashMap<Id, Vec<Expr>> = vec![(lhs_id, vec![]), (rhs_id, vec![])]
        .into_iter()
        .collect();
      if self.lemmas.is_empty() {
        exprs
          .get_mut(&lhs_id)
          .unwrap()
          .push(self.eq.lhs.expr.clone());
        exprs
          .get_mut(&rhs_id)
          .unwrap()
          .push(self.eq.rhs.expr.clone());
      }

      // Before creating a cyclic lemma with premises,
      // we need to update the variables in the premises
      // with their canonical forms in terms of the current goal variables
      let premises: Vec<Equation> = self
        .premises
        .iter()
        .map(|eq| eq.update_variables(&self.var_classes, &self.egraph))
        .collect();

      let (rewrites, _new_rewrite_names, _) = self.make_rewrites_from(lhs_id, rhs_id, premises, exprs, state, true);
      rewrites
    }

  }

  fn make_cyclic_lemmas(&self, state: &ProofState, add_termination_check: bool) -> (HashMap<String, Rw>, Vec<RawEqWithParams>) {
    let lhs_id = self.egraph.find(self.eq.lhs.id);
    let rhs_id = self.egraph.find(self.eq.rhs.id);

    let exprs = get_all_expressions(&self.egraph, vec![lhs_id, rhs_id]);

    // Before creating a cyclic lemma with premises,
    // we need to update the variables in the premises
    // with their canonical forms in terms of the current goal variables
    let premises: Vec<Equation> = self
      .premises
      .iter()
      .map(|eq| eq.update_variables(&self.var_classes, &self.egraph))
      .collect();


    let (rewrites, _new_rewrite_names, rewrite_eqs) = self.make_rewrites_from(lhs_id, rhs_id, premises, exprs, state, add_termination_check);
    (rewrites, rewrite_eqs)
  }

  /// Add a rewrite `lhs => rhs` to `rewrites` if not already present
  fn add_lemma(lhs: Pat, rhs: Pat, cond: Soundness, rewrites: &mut HashMap<String, Rw>, added_rewrite_names: &mut Vec<String>) {
    let name = format!("{}{}={}", LEMMA_PREFIX, lhs, rhs);
    // Insert the lemma into the rewrites map if it's not already there
    match rewrites.entry(name.clone()) {
      Entry::Occupied(_) => (),
      Entry::Vacant(entry) => {
        warn!("creating lemma: {} => {}", lhs, rhs);
        added_rewrite_names.push(name.clone());
        let rw = Rewrite::new(
          name,
          ConditionalSearcher {
            condition: cond,
            searcher: lhs,
          },
          rhs,
        )
        .unwrap();
        entry.insert(rw);
      }
    }
  }

  fn add_unchecked_lemma(lhs: Pat, rhs: Pat, rewrites: &mut HashMap<String, Rw>, added_rewrite_names: &mut Vec<String>) {
    let name = format!("{}{}={}", CC_LEMMA_PREFIX, lhs, rhs);
    // Insert the lemma into the rewrites map if it's not already there
    match rewrites.entry(name.clone()) {
      Entry::Occupied(_) => (),
      Entry::Vacant(entry) => {
        warn!("making cc lemma: {} => {}", lhs, rhs);
        added_rewrite_names.push(name.clone());
        let rw = Rewrite::new(
          name,
          lhs,
          rhs,
        )
        .unwrap();
        entry.insert(rw);
      }
    }
  }

  /// Add var as a scrutinee if its type `ty` is a datatype;
  /// if depth bound is exceeded, add a sentinel symbol instead
  fn add_scrutinee(&mut self, var: Symbol, ty: &Type, depth: usize) {
    if let Ok((dt, _)) = ty.datatype() {
      if self.env.contains_key(&Symbol::from(dt)) {
        self.scrutinees.push_back((var, depth));
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
      self.scrutinees.push_front((fresh_var, 1));
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
  fn case_split(self, var: Symbol, depth: usize, state: &mut ProofState<'a>) {
    let new_lemmas = self.add_lemma_rewrites(state);

    let var_str = var.to_string();
    warn!("case-split on {}", var);
    let var_node = SymbolLang::leaf(var);
    let var_pattern_ast: RecExpr<ENodeOrVar<SymbolLang>> = vec![ENodeOrVar::ENode(var_node.clone())].into();
    // Get the type of the variable, and then remove the variable
    let ty = match self.local_context.get(&var) {
      Some(ty) => ty,
      None => panic!("{} not in local context", var),
    };
    // Convert to datatype name
    let dt = Symbol::from(ty.datatype().unwrap().0);
    // Get the constructors of the datatype
    let (_, cons) = self.env.get(&dt).unwrap();
    // We will add this to state.proof to describe the case split.
    let mut instantiated_cons_and_goals: Vec<(String, String)> = vec![];

    // (we process constructors in reverse order so that base case ends up at the top of the stack)
    for &con in cons.iter().rev() {
      let mut new_goal = self.copy();
      new_goal.case_split_vars.insert(var);
      new_goal.name = format!("{}:", self.name);
      new_goal.lemmas = new_lemmas.clone();

      // Get the types of constructor arguments
      let con_ty = self.global_context.get(&con).unwrap();
      let con_args = Goal::instantiate_constructor(con_ty, ty);
      // For each argument: create a fresh variable and add it to the context and to scrutinees
      let mut fresh_vars = vec![];

      new_goal.egraph.analysis.cvec_analysis.timestamp += 1;

      for (i, arg_type) in con_args.iter().enumerate() {
        let fresh_var_name = format!("{}_{}{}", var, self.egraph.total_size(), i);
        // let depth = var_depth(&fresh_var_name[..]);
        let fresh_var = Symbol::from(fresh_var_name.clone());
        fresh_vars.push(fresh_var);
        // Add new variable to context
        new_goal.local_context.insert(fresh_var, arg_type.clone());
        new_goal.add_scrutinee(fresh_var, arg_type, depth + 1);
        let id = new_goal.egraph.add(SymbolLang::leaf(fresh_var));
        new_goal.var_classes.insert(fresh_var, id);
        // We can only generate a cvec for non-arrow types.
        if !arg_type.is_arrow() {
          // new_goal.egraph.analysis.cvec_analysis.timestamp += 1;
          let fresh_var_cvec = new_goal.egraph.analysis.cvec_analysis.make_cvec_for_type(arg_type, self.env, &self.global_context);
          let mut analysis = new_goal.egraph[id].data.clone();
          analysis.timestamp = new_goal.egraph.analysis.cvec_analysis.timestamp;
          analysis.cvec_data = fresh_var_cvec;
          new_goal.egraph.set_analysis_data(id, analysis);
        }

        if CONFIG.add_grounding && ty == arg_type {
          // This is a recursive constructor parameter:
          // add new grounding instantiations replacing var with fresh_var
          new_goal.add_grounding(var, fresh_var);
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

      new_goal.name = format!("{}{}={}", new_goal.name, var, con_app);

      instantiated_cons_and_goals.push((con_app_string, new_goal.name.clone()));
      // new_goal.egraph.analysis.cvec_analysis.timestamp += 1;

      // let var_id = new_goal.egraph.lookup(var_node.clone()).unwrap();
      // println!("egraph pre union: {:?}", new_goal.egraph.dump());
      // Add con_app to the new goal's egraph and union it with var
      new_goal.egraph.add_expr(&con_app);
      // Not sure if it's proper to use new_goal.name here
      let (con_app_id, _) = new_goal.egraph.union_instantiations(
        &var_pattern_ast,
        &rec_expr_to_pattern_ast(con_app.clone()),
        &Subst::default(),
        new_goal.name.clone(),
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
        let eq = Equation { lhs, rhs };
        new_goal.premises.push(eq);
      }

      // Add the subgoal to the proof state
      state.goals.push_back(new_goal);
    }
    // We split on var into the various instantiated constructors and subgoals.
    //
    // If the var begins with the guard prefix, it is an ITE split and we will
    // add the condition that was split on to our proof term. This is necessary
    // because for ITE splits we introduce a new variable that we bind an
    // expression to.
    //
    // HACK: We might try to prove a generalization/cc lemma that contains a guard
    // variable, in which case we will skip this part.
    if var_str.starts_with(GUARD_PREFIX) && self.guard_exprs.contains_key(&var_str) {
      // There should only be two cases.
      assert_eq!(instantiated_cons_and_goals.len(), 2);
      state.proof.insert(
        self.name,
        ProofTerm::ITESplit(
          var_str.clone(),
          self.guard_exprs[&var_str].to_string(),
          instantiated_cons_and_goals,
        ),
      );
    // Otherwise, we are doing a case split on a variable.
    } else {
      state.proof.insert(
        self.name,
        ProofTerm::CaseSplit(var_str, instantiated_cons_and_goals),
      );
    }
  }

  fn find_blocking(&self) -> (HashSet<Symbol>, HashSet<Id>) {
    let mut blocking_vars: HashSet<_> = HashSet::default();
    let mut blocking_exprs: HashSet<Id> = HashSet::default();

    let mut lhs_descendents = HashSet::default();
    self.compute_descendents(self.eq.lhs.id, &mut lhs_descendents);

    let mut rhs_descendents = HashSet::default();
    self.compute_descendents(self.eq.rhs.id, &mut rhs_descendents);

    for reduction in self.reductions {
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
        let mod_searcher: Pattern<SymbolLang> = new_sexp.to_string().parse().unwrap();

        // for each new pattern, find the pattern variables in blocking positions so that we can use them to look up the substs later
        let bvs: Vec<Var> = mod_searcher
          .vars()
          .iter()
          .filter(|&x| x.to_string().contains("block_"))
          .cloned()
          .collect();

        let matches = mod_searcher.search(&self.egraph);

        let extractor = Extractor::new(&self.egraph, AstSize);

        // look at the e-class analysis for each matched e-class, if any of them has a variable, use it
        for m in matches {
          for subst in m.substs {
            for v in &bvs[0..] {
              if let Some(&ecid) = subst.get(*v) {
                match &self.egraph[ecid].data.canonical_form_data {
                  CanonicalForm::Var(n) => {
                    blocking_vars.insert(n.op);
                  }
                  CanonicalForm::Stuck(_) => {
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
  fn next_scrutinee(&mut self, mut blocking_vars: HashSet<Symbol>) -> Option<(Symbol, usize)> {
    let blocking = self
      .scrutinees
      .iter()
      .find_position(|(x, _)| blocking_vars.contains(x));

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

  fn saturate_cvecs(&mut self) {
    let cvec_analysis_egraph: EGraph<SymbolLang, ()> = self.egraph.analysis.cvec_analysis.cvec_egraph.borrow().clone();
    let runner = Runner::default()
      .with_egraph(cvec_analysis_egraph)
      .run(self.cvec_reductions);
    self.egraph.analysis.cvec_analysis.cvec_egraph.replace_with(|_| runner.egraph);
  }

  fn search_for_cc_lemmas(&mut self, state: &ProofState) -> Vec<RawEqWithParams> {
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
        // Don't try unioning the LHS and RHS, we've seen those already.
        if class_1_id == resolved_lhs_id && class_2_id == resolved_rhs_id
          || class_1_id == resolved_rhs_id && class_2_id == resolved_lhs_id {
            continue
        }

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
          // let extractor = Extractor::new(&self.egraph, AstSize);
          // let e1 = CanonicalFormAnalysis::extract_canonical(&self.egraph, class_1_id).unwrap_or_else(||{
          //   extractor.find_best(class_1_id).1
          // });
          // let e2 = CanonicalFormAnalysis::extract_canonical(&self.egraph, class_2_id).unwrap_or_else(||{
          //   extractor.find_best(class_2_id).1
          // });
          // let (_, e1) = extractor.find_best(class_1_id);
          // let (_, e2) = extractor.find_best(class_2_id);

          // let new_egraph = self.egraph.clone();

          let exprs = get_all_expressions(&self.egraph, vec![class_1_id, class_2_id]);

          // let mut exprs: HashMap<Id, Vec<Expr>> = vec![(class_1_id, vec![]), (class_2_id, vec![])]
          //   .into_iter()
          //   .collect();
          // exprs.insert(class_1_id, vec!(e1.clone()));
          // exprs.insert(class_2_id, vec!(e2.clone()));
          let (_new_rewrites, _new_rewrite_names, new_rewrite_eqs) = self.make_rewrites_from(class_1_id, class_2_id, vec!(), exprs, state, false);
          // let rewrites = self.reductions.iter().chain(new_rewrites.values());
          // let mut runner = Runner::default()
          //   .with_explanations_enabled()
          //   .with_egraph(new_egraph)
          //   .run(rewrites);
          // let (explanation, valid) = Goal::get_explanation_and_validity(&self.eq, &mut runner.egraph);
          // if valid && explanation.is_none() {
          //   println!("Skipping useful CC lemma {} = {} because no explanation came from its use", e1, e2);
          // }

          let fresh_name = format!("fresh_{}", self.egraph.total_size());
          let generalized_eqs = new_rewrite_eqs.iter().flat_map(|new_rewrite_eq| find_generalizations_raw_eq(&new_rewrite_eq, self.global_context, fresh_name.clone()));

          lemmas.extend(generalized_eqs);
          lemmas.extend(new_rewrite_eqs);
          // if new_rewrite_names.len() > 0 {
          // // if let Some(_) = explanation {
          //   // Another method would be to try finding all possible lemmas from these two e-classes
          //   // and then try to prove each, but this would be cumbersome and I figure that since
          //   // they're all equivalent the lemmas are probably equivalent too.
          //   //
          //   // let cc_lemmas: HashSet<Symbol> = exp.make_flat_explanation().iter().flat_map(|flat_term|{
          //   //   flat_term.backward_rule.or(flat_term.forward_rule).and_then(|name|{
          //   //     if name.to_string().starts_with(CC_LEMMA_PREFIX) {
          //   //       Some(name)
          //   //     } else {
          //   //       None
          //   //     }
          //   //   })
          //   // }).collect();
          //   // We assume that if we proved something with this CC lemma, then
          //   // there must be a new rewrite - and therefore a new name.
          //   let rw = new_rewrites.get(&new_rewrite_names[0]).unwrap();
          //   let lhs_vars: HashSet<Var> = rw.searcher.vars().iter().cloned().collect();
          //   let rhs_vars: HashSet<Var> = rw.applier.vars().iter().cloned().collect();
          //   let cc_lemma_params: Vec<(Symbol, Type)> = lhs_vars.union(&rhs_vars).map(|var|{
          //     let var_str = var.to_string();
          //     let mut var_name = var_str.chars();
          //     // Remove leading ? from var name
          //     var_name.next();
          //     let var_symb = Symbol::from(var_name.collect::<String>());
          //     let var_ty = self.local_context.get(&var_symb).unwrap();
          //     (var_symb, var_ty.clone())
          //   }).collect();
          //   let cc_lemma_eq = RawEquation::from_exprs(&e1, &e2);
          //   let mut new_goal = Goal::top(
          //     &rw.name.to_string(),
          //     &cc_lemma_eq,
          //     &None,
          //     cc_lemma_params.clone(),
          //     self.env,
          //     self.global_context,
          //     self.reductions,
          //     self.cvec_reductions,
          //     self.defns,
          //   );
          //   new_goal.egraph.analysis.cvec_analysis.saturate();
          //   let new_goal_lhs_cvec = &new_goal.egraph[new_goal.eq.lhs.id].data.cvec_data;
          //   let new_goal_rhs_cvec = &new_goal.egraph[new_goal.eq.rhs.id].data.cvec_data;
          //   if let Some(true) = cvecs_equal(&new_goal.egraph.analysis.cvec_analysis, &new_goal_lhs_cvec, &new_goal_rhs_cvec) {
          //     lemmas.push(RawEqWithParams::new(cc_lemma_eq.clone(), cc_lemma_params));
          //   }
          //   // println!("CC lemma: {} = {}", e1, e2);
          //   // let (outcome, _) = prove(new_goal, state.depth + 1, state.lemmas_state.clone());
          //   // if let Outcome::Valid = outcome {
          //   //   println!("Proved");
          //   //   // Add the new lemmas
          //   //   // found_lemmas.extend(new_rewrite_names.iter().map(|rw_name| (rw_name.clone(), new_rewrites.get(rw_name).unwrap().clone())));
          //   // }
          // } else {
          //   // println!("CC lemma not useful: {} = {}", e1, e2);
          // }

          // if runner.egraph.find(self.eq.lhs.id) == runner.egraph.find(self.eq.rhs.id) {
          //   // let new_goal = Goal::top(
          //   //   &raw_goal.name,
          //   //   &raw_goal.equation,
          //   //   None,
          //   //   raw_goal.params.clone(),
          //   //   self.env,
          //   //   self.global_context,
          //   //   self.reductions,
          //   //   self.cvec_reductions,
          //   //   self.defns,
          //   // );
          //   println!("CC lemma: {} = {}", e1, e2);
          //   found_lemma = true;
          // }
          // self.egraph.union_trusted(class_1_id, class_2_id, "CC lemma search");
          // self.egraph.rebuild();
        }
      }
    }
    lemmas
  }

  fn look_for_generalizations(&self) {
    println!("Proving {} failed, egraph is of size {}, looking for generalizations...", self.name, self.egraph.total_size());
    let lhs_id = self.egraph.find(self.eq.lhs.id);
    let rhs_id = self.egraph.find(self.eq.rhs.id);

    let exprs = get_all_expressions(&self.egraph, vec![lhs_id, rhs_id]);

    for lhs_expr in exprs.get(&lhs_id).unwrap() {
      if CONFIG.irreducible_only && self.is_reducible(lhs_expr) {
        continue;
      }
      let lhs_sexp = parser::parse_str(&lhs_expr.to_string()).unwrap();
      let lhs_nontrivial_subexprs = nontrivial_sexp_subexpressions_containing_vars(&lhs_sexp);
      for rhs_expr in exprs.get(&rhs_id).unwrap() {
        if CONFIG.irreducible_only && self.is_reducible(rhs_expr) {
          continue;
        }
        let rhs_sexp = parser::parse_str(&rhs_expr.to_string()).unwrap();
        let rhs_nontrivial_subexprs = nontrivial_sexp_subexpressions_containing_vars(&rhs_sexp);
        for (rhs_subexpr_str, subexpr) in &rhs_nontrivial_subexprs {
          // should be the same subexpr so we don't need to bind it
          if let Some(_) = lhs_nontrivial_subexprs.get(rhs_subexpr_str) {
            let generalized = Sexp::String("FRESH".to_string());
            println!("Candidate: {} === {}", substitute_sexp(&rhs_sexp, subexpr, &generalized), substitute_sexp(&lhs_sexp, subexpr, &generalized));
          }
        }
      }
    }
  }

  fn look_for_generalizations_2(&self) {
    let mut lhs_parents = HashMap::default();
    self.compute_parents(self.eq.lhs.id, &mut lhs_parents, &mut HashSet::default());
    let mut rhs_parents = HashMap::default();
    self.compute_parents(self.eq.rhs.id, &mut rhs_parents, &mut HashSet::default());
    let var_classes = self.scrutinees.iter().flat_map(|(var, _)| self.egraph.lookup(SymbolLang::leaf(*var)).map(|class| (*var, class)));
    let fresh_name = format!("fresh_{}", self.name.len());
    let mut gs: HashMap<String, RawEquation> = HashMap::default();
    for (_var_name, var_class) in var_classes {
      let generalizations = Goal::best_generalizations(var_class, &lhs_parents, &rhs_parents, &mut HashSet::default());
      for (gen_class, _gen_index) in generalizations {
        let mut copy_egraph = self.egraph.clone();
        let fresh_var_id = copy_egraph.add(SymbolLang::leaf(Symbol::new(&fresh_name)));
        copy_egraph.union_trusted(gen_class, fresh_var_id, format!("generalize {}", gen_class));
        copy_egraph.rebuild();
        let extractor = Extractor::new(&copy_egraph, AstSize);
        let new_lhs = extractor.find_best(self.eq.lhs.id).1;
        let new_rhs = extractor.find_best(self.eq.rhs.id).1;
        let new_lhs_sexp = parser::parse_str(&new_lhs.to_string()).unwrap();
        let new_rhs_sexp = parser::parse_str(&new_rhs.to_string()).unwrap();
        let raw_eq = RawEquation::from_exprs(&new_lhs, &new_rhs);
        gs.insert(format!("{} = {}", raw_eq.lhs, raw_eq.rhs), raw_eq);
      }
    }
    for g in gs.keys() {
      println!("Generalization: {}", g);
    }
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

  fn best_generalizations(class: Id, lhs_parents: &HashMap<Id, HashSet<(Id, usize)>>, rhs_parents: &HashMap<Id, HashSet<(Id, usize)>>, seen: &mut HashSet<Id>) -> HashSet<(Id, usize)> {
    if seen.contains(&class) {
      return HashSet::default();
    }
    seen.insert(class);
    let lhs_candidates = lhs_parents.get(&class);
    let rhs_candidates = rhs_parents.get(&class);
    match (lhs_candidates, rhs_candidates) {
      (Some(lhs_candidates), Some(rhs_candidates)) => {
        lhs_candidates.intersection(&rhs_candidates).flat_map(|(parent_class, parent_node_index)|{
          let new_generalizations = Goal::best_generalizations(*parent_class, lhs_parents, rhs_parents, seen);
          if new_generalizations.is_empty() {
            vec!((*parent_class, *parent_node_index)).into_iter().collect()
          } else {
            new_generalizations
          }
        }).collect()
      }
      _ => {
        HashSet::default()
      }
    }
  }

  /// Have we found a counterexample that makes the LHS and RHS inequal?
  fn has_cvec_counterexample(&mut self) -> Option<bool> {
    // self.saturate_cvecs();
    let cv_eq = cvecs_equal(&self.egraph.analysis.cvec_analysis, &self.egraph[self.eq.lhs.id].data.cvec_data, &self.egraph[self.eq.rhs.id].data.cvec_data);
    cv_eq.map(|b| !b)
  }

  fn print_lhs_rhs(&self) {
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

  fn make_generalized_goal(&self, class: Id) -> Option<(RawEqWithParams, Goal)> {
    // Get an op (function/constructor/var) that is a representative of this class.
    let class_op = self.egraph[class].data.canonical_form_data.get_enode().op;
    // NOTE We're assuming that we don't have to deal with higher-order
    // functions for generalizations, because we never will inspect a function's
    // value when pattern matching. However, a more correct analysis would take
    // into consideration how many arguments there are in the enode and from
    // those construct the appropriate (possibly higher-order) type.
    let (_, class_ty) = self.global_context.get(&class_op).or_else(||self.local_context.get(&class_op)).unwrap().args_ret();
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
    let params: Vec<(Symbol, Type)> = get_vars(&lhs_expr).union(&get_vars(&rhs_expr)).into_iter().map(|var| {
      let var_ty = if var == &fresh_symb {
        class_ty.clone()
      } else {
        self.local_context.get(var).unwrap().clone()
      };
      (*var, var_ty)
    }).collect();
    let eq = RawEquation::from_exprs(&lhs_expr, &rhs_expr);
    let mut new_goal = Goal::top(&format!("{}_gen", self.name),
                             &eq,
                             &None,
                             params.clone(),
                             self.env,
                             self.global_context,
                             self.reductions,
                             self.cvec_reductions,
                             self.defns,
                             self.searchers,
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
      Some((RawEqWithParams::new(eq, params), new_goal))
    } else {

      // println!("cvecs disagree for {} === {}", lhs_expr, rhs_expr);
      None
    }
  }

  // fn try_prove_generalized_goal(&self, blocking_exprs: &HashSet<Id>, state: &ProofState) -> bool {
  //   blocking_exprs.iter().any(|blocking_expr| {
  //     self.make_generalized_goal(*blocking_expr).map(|(_raw_eq_with_params, new_goal)|{
  //       // println!("Trying to prove generalized goal {}", new_goal.eq);
  //       // return false;
  //       let (outcome, _) = prove(new_goal, state.depth + 1);
  //       outcome == Outcome::Valid
  //     }).unwrap_or(false)
  //   })
  // }

  fn find_generalized_goals(&self, blocking_exprs: &HashSet<Id>) -> Vec<RawEqWithParams> {
    blocking_exprs.iter().flat_map(|blocking_expr| {
      self.make_generalized_goal(*blocking_expr).map(|(raw_eq_with_params, _new_goal)|{
        raw_eq_with_params
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

#[derive(Default, Clone)]
pub struct LemmasState {
  pub proven_lemmas: MinElements<RawEqWithParams>,
  pub invalid_lemmas: MaxElements<RawEqWithParams>,
  pub possible_lemmas: ChainSet<RawEqWithParams>,
  pub lemma_rewrites: HashMap<String, Rw>,
  pub cyclic_lemmas: ChainSet<RawEqWithParams>,
  pub cyclic_lemma_rewrites: HashMap<String, Rw>,
}

impl LemmasState {
  pub fn add_possible_lemmas<I: IntoIterator<Item = RawEqWithParams>>(&mut self, iter: I) {
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

/// A proof state is a list of subgoals,
/// all of which have to be discharged
pub struct ProofState<'a> {
  pub goals: VecDeque<Goal<'a>>,
  pub solved_goal_explanation_and_context: HashMap<String, (Explanation<SymbolLang>, Context)>,
  pub proof: HashMap<String, ProofTerm>,
  pub start_time: Instant,
  pub proof_depth: usize,
  pub lemmas_state: LemmasState,
  pub case_split_depth: usize,
  // pub cc_lemmas: HashMap<String, Rw>,
}

impl<'a> ProofState<'a> {
  // Has timeout been reached?
  pub fn timeout(&self) -> bool {
    CONFIG.timeout.is_some()
      && self.start_time.elapsed() > Duration::new(CONFIG.timeout.unwrap(), 0)
  }

  /// Try to prove all of the lemmas we've collected so far.
  pub fn try_prove_lemmas(&mut self, goal: &mut Goal) -> bool {
    // println!("Try prove lemmas for goal {}", goal.name);
    for chain in self.lemmas_state.possible_lemmas.chains.iter() {
      // println!("chain lemmas: {}", chain.chain.iter().map(|e| format!("{} = {}", e.eq.lhs, e.eq.rhs)).join(","));
      for (i, raw_eq_with_params) in chain.chain.iter().enumerate() {
        if self.timeout() {
          return false;
        }
        // Is the lemma already proven or subsumed by a cyclic lemma?
        if self.lemmas_state.proven_lemmas.contains_leq(&raw_eq_with_params) || self.lemmas_state.cyclic_lemmas.contains_leq(&raw_eq_with_params) {
          continue;
        }
        // Is the lemma invalid?
        // if self.lemmas_state.invalid_lemmas.contains_geq(&raw_eq_with_params) {
        //   continue;
        // }
        let goal_name = format!("lemma-{}={}", raw_eq_with_params.eq.lhs, raw_eq_with_params.eq.rhs);
        let mut new_goal = Goal::top(&goal_name,
                                 &raw_eq_with_params.eq,
                                 &None,
                                 raw_eq_with_params.params.clone(),
                                 goal.env,
                                 goal.global_context,
                                 goal.reductions,
                                 goal.cvec_reductions,
                                 goal.defns,
                                 goal.searchers,
        );
        let try1 = new_goal.cvecs_valid();
        let mut new_goal_2 = Goal::top(&goal_name,
                                 &raw_eq_with_params.eq,
                                 &None,
                                 raw_eq_with_params.params.clone(),
                                 goal.env,
                                 goal.global_context,
                                 goal.reductions,
                                 goal.cvec_reductions,
                                 goal.defns,
                                 goal.searchers,
        );
        let try2 = new_goal_2.cvecs_valid();
        if try1 && !try2 {
          // println!("Second try helped");
          // println!("Invalidated lemma {} = {}", raw_eq_with_params.eq.lhs, raw_eq_with_params.eq.rhs);
        }
        if !try1 || !try2 {
          warn!("Invalidated lemma {} = {}", raw_eq_with_params.eq.lhs, raw_eq_with_params.eq.rhs);
          self.lemmas_state.invalid_lemmas.insert(raw_eq_with_params.clone());
          continue;
        } else {
          println!("Trying to prove lemma: {} = {}", raw_eq_with_params.eq.lhs, raw_eq_with_params.eq.rhs);
          // println!("proven lemmas so far: {}", self.lemmas_state.proven_lemmas.elems.iter().map(|e| format!("{} = {}", e.eq.lhs, e.eq.rhs)).join(","));
          // print_cvec(&new_goal.egraph.analysis.cvec_analysis, new_goal_lhs_cvec)
        }
        let lhs_id = new_goal.eq.lhs.id;
        let rhs_id = new_goal.eq.rhs.id;
        let mut exprs: HashMap<Id, Vec<Expr>> = vec![(lhs_id, vec![]), (rhs_id, vec![])]
          .into_iter()
          .collect();
        exprs.insert(lhs_id, vec!(new_goal.eq.lhs.expr.clone()));
        exprs.insert(rhs_id, vec!(new_goal.eq.rhs.expr.clone()));
        let (rws, _, _) = new_goal.make_rewrites_from(lhs_id, rhs_id, new_goal.premises.clone(), exprs, &self, false);
        let mut new_lemmas_state = self.lemmas_state.clone();

        // HACK: Optimization to proving lemmas
        // We will always try to prove the most general lemma we've theorized so far, but thereafter
        // we require that the lemma be actually useful to us if we are going to try and prove it.
        //
        // This eliminates us spending time trying to prove a junk lemma like
        // (mult (S n) Z) = (plus (mult (S n) Z) Z)
        // when we already failed to prove the more general lemma
        // (mult n Z) = (plus (mult n Z) Z)
        //
        // Really we should have more sophisticated lemma filtering - the junk
        // lemma in this case is really no easier to prove than the first lemma
        // (since we will try to prove it eventually when we case split the first),
        // so we shouldn't consider it in the first place.
        //
        // Hence why I consider this optimization a hack, even though it
        // probably avoids some lemmas which are junky in a more complicated
        // way. I imagine it might rarely pass on interesting and useful lemmas.
        // This is because sometimes you need more than one lemma to prove a goal.
        if i > 0 {
          let goal_egraph_copy = goal.egraph.clone();
          let rewrites = goal.reductions.iter().chain(goal.lemmas.values()).chain(rws.values()).chain(self.lemmas_state.lemma_rewrites.values());
          let runner = Runner::default()
            // .with_explanations_enabled()
            .with_egraph(goal_egraph_copy)
            .run(rewrites);
          if runner.egraph.find(goal.eq.lhs.id) != runner.egraph.find(goal.eq.rhs.id) {
            break;
          }
        }

        // Zero out the possible lemmas and cyclic lemmas, we only want
        // to carry forward what we've proven already.
        new_lemmas_state.possible_lemmas = ChainSet::new();
        new_lemmas_state.cyclic_lemmas = ChainSet::new();
        new_lemmas_state.cyclic_lemma_rewrites = HashMap::new();
        let (outcome, ps) = prove(new_goal, self.proof_depth + 1, new_lemmas_state);
        // Steal the lemmas we got from the recursive proving.
        self.lemmas_state.proven_lemmas.extend(ps.lemmas_state.proven_lemmas.elems);
        self.lemmas_state.invalid_lemmas.extend(ps.lemmas_state.invalid_lemmas.elems);
        self.lemmas_state.lemma_rewrites.extend(ps.lemmas_state.lemma_rewrites);
        if outcome == Outcome::Valid {
          println!("proved");
          // TODO: This comes for free in the proven lemmas we get, so we
          // probably don't need to insert it.
          self.lemmas_state.proven_lemmas.insert(raw_eq_with_params.clone());
          self.lemmas_state.lemma_rewrites.extend(rws);
          // Add any cyclic lemmas we proved too
          self.lemmas_state.proven_lemmas.extend(ps.lemmas_state.cyclic_lemmas.chains.into_iter().flat_map(|chain| chain.chain.into_iter()));
          self.lemmas_state.lemma_rewrites.extend(ps.lemmas_state.cyclic_lemma_rewrites);
          goal.saturate(&self.lemmas_state.lemma_rewrites);
          if goal.check_validity() {
            return true;
          }
          break;
        }
        // TODO: We want to record that all of the previous lemmas including
        // this are invalid, but for now we won't record anything.
        if outcome == Outcome::Invalid {
          self.lemmas_state.invalid_lemmas.insert(raw_eq_with_params.clone());
        } else {
          // NOTE: We don't try to prove a lemma twice, but actually we might
          // be able to if we have another lemma.
          // self.lemmas_state.proven_lemmas.insert(raw_eq_with_params.clone());
        }
      }
    }
    false
  }

  pub fn add_cyclic_lemmas(&mut self, goal: &Goal) {
    // FIXME: add premises properly
    if !goal.premises.is_empty() {
      return;
    }
    let (rws, rewrite_eqs) = goal.make_cyclic_lemmas(self, false);
    self.lemmas_state.cyclic_lemmas.extend(rewrite_eqs);
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

/// Top-level interface to the theorem prover.
pub fn prove(mut goal: Goal, depth: usize, mut lemmas_state: LemmasState) -> (Outcome, ProofState) {
  let goal_name = goal.name.clone();
  let goal_eq = RawEquation::new(goal.eq.lhs.sexp.clone(), goal.eq.rhs.sexp.clone());
  let goal_eq_with_params = RawEqWithParams::new(goal_eq, goal.params.iter().cloned().map(|param| (param, goal.local_context.get(&param).unwrap().clone())).collect());
  // We won't attempt to prove the goal again (it isn't actually proven).
  lemmas_state.proven_lemmas.insert(goal_eq_with_params);
  let mut state = ProofState {
    goals: vec![goal].into(),
    solved_goal_explanation_and_context: HashMap::default(),
    proof: HashMap::default(),
    start_time: Instant::now(),
    proof_depth: depth,
    lemmas_state,
    case_split_depth: 0,
  };
  // FIXME: put in config
  if state.proof_depth == 3 {
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
    let is_valid = goal.check_validity();
    if let Some(mut explanation) = goal.explanation {
      // This goal has been discharged, proceed to the next goal
      if CONFIG.verbose {
        println!("{} {}", "Proved case".bright_blue(), goal.name);
        println!("{}", explanation.get_flat_string());
      }
      state
        .solved_goal_explanation_and_context
        .insert(goal.name, (explanation, goal.local_context));
      continue;
    }
    if is_valid {
      if CONFIG.verbose {
        println!("{} {}", "Proved case by contradiction".bright_blue(), goal.name);
        println!("(no explanation for now)");
      }
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
        (goal.scrutinees.iter().map(|(v, _)| v).cloned().collect(), HashSet::default())
      } else {
        let (blocking_vars, blocking_exprs) = goal.find_blocking();
        if CONFIG.verbose {
          println!("blocking vars: {:?}", blocking_vars);
        }
        (blocking_vars, blocking_exprs)
      };

    state.lemmas_state.add_possible_lemmas(goal.find_generalized_goals(&blocking_exprs));
    state.lemmas_state.add_possible_lemmas(goal.search_for_cc_lemmas(&state));
    // This ends up being really slow so we'll just take the lemma duplication for now
    // It's unclear that it lets us prove that much more anyway.
    // state.add_cyclic_lemmas(&goal);

    goal.searchers.iter().for_each(|searcher: &ConditionalSearcher<Pattern<SymbolLang>, Pattern<SymbolLang>>| {
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

    // if state.update_depth(goal.scrutinees.front().unwrap().1) {
    //   // This goal could be further split, but we have reached the maximum depth,
    //   // we cannot prove or disprove the conjecture
    //   if CONFIG.verbose {
    //     for remaining_goal in &state.goals {
    //       println!("{} {}", "Remaining case".yellow(), remaining_goal.name);
    //     }
    //   }
    //   if state.handle_depth_exceeded_failure(goal) {
    //     continue;
    //   }
    //   return (Outcome::Unknown, state);
    // }
    // let depth_at_front = goal.scrutinees.front().unwrap().1;
    if let Some((scrutinee, depth)) = goal.next_scrutinee(blocking_vars) {
      // let d = depth.max(depth_at_front);
      if depth > state.case_split_depth {
        state.case_split_depth = depth;
        if state.try_prove_lemmas(&mut goal) {
          continue;
        }
      }
      if state.case_split_depth > CONFIG.max_split_depth + state.proof_depth {
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
          scrutinee.to_string().purple()
        );
      }
      goal.case_split(scrutinee, depth, &mut state);
    } else {
      if CONFIG.verbose {
        println!("{}", "Cannot case split: no blocking variables found".red());
        for remaining_goal in &state.goals {
          println!("{} {}", "Remaining case".yellow(), remaining_goal.name);
        }
      }
      if goal.scrutinees.iter().any(|(_, depth)| *depth > CONFIG.max_split_depth + state.proof_depth) {
        if state.try_prove_lemmas(&mut goal) {
          continue;
        }
        // println!("Failed to prove case {}, trying CC lemmas", goal.name);
        // // goal.print_lhs_rhs();
        // if goal.try_prove_generalized_goal(&blocking_exprs, &state) {
        //   continue;
        // }
        // let lemmas = goal.search_for_cc_lemmas(&state);
        // if !lemmas.
        //   // state.cc_lemmas.extend(lemmas);
        //   continue;
        // }
        // // goal.look_for_generalizations_2();

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
