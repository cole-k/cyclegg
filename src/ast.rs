use egg::*;
use lazy_static::lazy_static;

use indexmap::IndexMap;
use std::{collections::{HashMap, HashSet}, fmt::Display, str::FromStr};
use symbolic_expressions::{Sexp, SexpError};

use crate::config::CONFIG;

pub type SSubst = HashMap<String, Sexp>;
// This is almost like egg's Subst but iterable
pub type IdSubst = IndexMap<Symbol, Id>;

#[derive(Debug, Clone, PartialEq)]
pub struct Type {
  pub repr: Sexp,
}

impl Type {
  pub fn new(repr: Sexp) -> Self {
    Self { repr }
  }

  /// If this type is a datatype, returns its name and arguments in order (if it
  /// has any) and otherwise return error.
  pub fn datatype(&self) -> Result<(&String, Vec<Type>), SexpError> {
    match &self.repr {
      Sexp::String(s) => Ok((s, Vec::default())), // This type is a D
      Sexp::List(lst) => {
        let mut lst_iter = lst.iter();
        let dt = lst_iter.next().unwrap().string()?;
        if dt == ARROW {
          return Err(SexpError::Other("datatype: unexpected arrow".to_string()));
        }
        let arg_types = lst_iter.map(|arg| Type::new(arg.clone())).collect();
        Ok((dt, arg_types))
      }
      _ => panic!("arity: type is empty"),
    }
  }

  /// Split a type into arguments and return value
  /// (arguments are empty if the type is not an arrow)
  pub fn args_ret(&self) -> (Vec<Type>, Type) {
    match &self.repr {
      Sexp::String(_) => (vec![], self.clone()), // This type is a D
      Sexp::List(xs) => {
        // This is a type constructor application
        match xs[0].string().unwrap().as_str() {
          ARROW => {
            let args = xs[1]
              .list()
              .unwrap()
              .iter()
              .map(|x| Type::new(x.clone()))
              .collect();
            (args, Type::new(xs[2].clone()))
          }
          _ => (vec![], self.clone()),
        }
      }
      _ => panic!("arity: type is empty"),
    }
  }

  pub fn is_arrow(&self) -> bool {
    match &self.repr {
      Sexp::List(xs) => {
        xs[0].string().unwrap().as_str() == ARROW
      }
      _ => false
    }
  }

}

impl FromStr for Type {
  type Err = SexpError;

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    Ok(Type::new(symbolic_expressions::parser::parse_str(s)?))
  }
}

impl Display for Type {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    write!(f, "{}", self.repr)
  }
}

// Expressions
pub type Expr = RecExpr<SymbolLang>;
pub type Pat = Pattern<SymbolLang>;

pub fn mangle_name(name: &str) -> String {
  // We never mangle symbols. The cases we have are:
  //   $  (function application)
  //   -> (type arrows)
  //   ?x (variable names)
  if name
    .chars()
    .next()
    .map(|c| !c.is_alphabetic())
    .unwrap_or(true)
  {
    return name.to_string();
  }
  if CONFIG.mangle_names {
    if name.chars().next().unwrap().is_ascii_uppercase() {
      format!("Cyclegg_{}", name)
    } else {
      format!("cyclegg_{}", name)
    }
  } else {
    name.to_string()
  }
}

pub fn mangle_sexp(sexp: &Sexp) -> Sexp {
  map_sexp(|elem| Sexp::String(mangle_name(elem)), sexp)
}

// Constants
lazy_static! {
  pub static ref BOOL_TYPE: String = mangle_name("Bool");
  pub static ref ITE: String = mangle_name("ite");
  pub static ref TRUE: String = mangle_name("True");
  pub static ref FALSE: String = mangle_name("False");
}
pub const ARROW: &str = "->";
pub const APPLY: &str = "$";
pub const GUARD_PREFIX: &str = "g_";

pub fn var_depth(var_name: &str) -> usize {
  var_name.matches('_').count()
}

pub fn is_descendant(var_name: &str, ancestor_name: &str) -> bool {
  var_name.starts_with(ancestor_name)
    && var_name.len() > ancestor_name.len()
    && var_name.chars().nth(ancestor_name.len()).unwrap() == '_'
}

#[derive(PartialEq, PartialOrd, Ord, Eq, Debug)]
pub enum StructuralComparison {
  /// Strictly less than
  LT,
  /// Not greater than
  LE,
  /// Don't know - we reject these
  Incomparable,
}

/// Check if sub is a subterm of sup
pub fn is_subterm(sub: &Expr, sup: &Expr) -> StructuralComparison {
  // Convert both expressions to strings and check if one is a substring of the other
  let sub_str = sub.to_string();
  let sup_str = sup.to_string();
  if sup_str.contains(&sub_str) {
    if sub_str.len() < sup_str.len() {
      StructuralComparison::LT
    } else {
      StructuralComparison::LE
    }
  } else {
    StructuralComparison::Incomparable
  }
}

/// Replace one variable with another in a RecExpr;
/// also returns whether the variable was found
pub fn replace_var(expr: &Expr, var: Symbol, replacement: Symbol) -> (Expr, bool) {
  let mut new_expr = vec![];
  let mut found = false;
  for node in expr.as_ref() {
    if node.op == var {
      new_expr.push(SymbolLang::leaf(replacement));
      found = true;
    } else {
      new_expr.push(node.clone());
    }
  }
  (new_expr.into(), found)
}

pub fn map_sexp<F>(f: F, sexp: &Sexp) -> Sexp
where
  F: Copy + Fn(&str) -> Sexp,
{
  match sexp {
    Sexp::Empty => Sexp::Empty,
    Sexp::String(str) => f(str),
    Sexp::List(list) => Sexp::List(list.iter().map(|s| map_sexp(f, s)).collect()),
  }
}


/// Unlike map_sexp, this substitutes Sexp -> Sexp, so the base case is when f
/// returns Some(new_sexp), which replaces the Sexp entirely.
pub fn map_sexp_sexp<F>(f: F, sexp: &Sexp) -> Sexp
where
  F: Copy + Fn(&Sexp) -> Option<Sexp>,
{
  f(sexp).unwrap_or_else(|| {
    match sexp {
      // Recursive case, try mapping over each child
      Sexp::List(list) => Sexp::List(list.iter().map(|s| map_sexp_sexp(f, s)).collect()),
      // Base case, f doesn't apply so just return the sexp unchanged
      _ => sexp.clone(),
    }
  })
}

/// Iterates over every sub-sexp in the sexp, substituting it entirely if it
/// matches the substitution.
pub fn substitute_sexp(sexp: &Sexp, from: &Sexp, to: &Sexp) -> Sexp {
  map_sexp_sexp(|interior_sexp| {
    if interior_sexp == from {
      Some(to.clone())
    } else {
      None
    }
  }, sexp)
}

/// Returns every subexpression in the sexp that contains a var, ignoring base
/// cases. This is basically every subexpression we would consider to
/// generalize.
///
/// Since Sexps can't be hashed we hack the set using their string
/// representation...
pub fn nontrivial_sexp_subexpressions_containing_vars(sexp: &Sexp) -> HashMap<String, Sexp> {
  let mut subexprs = HashMap::default();
  add_sexp_subexpressions(sexp, &mut subexprs);
  subexprs
}

fn add_sexp_subexpressions(sexp: &Sexp, subexprs: &mut HashMap<String, Sexp>) -> bool {
  let mut any_child_has_var = false;
  match sexp {
    Sexp::List(children) => {
      let mut child_iter = children.iter();
      // The root is a function so we shouldn't add it
      child_iter.next();
      child_iter.for_each(|child| {any_child_has_var |= add_sexp_subexpressions(child, subexprs);});
    }
    Sexp::String(s) if is_var(s) => {
      // We won't add the variable, but we will add every subexpression
      // containing it.
      return true;
    }
    _ => {},
  }
  // If there's a variable in this sexp, we can generalize it.
  if any_child_has_var {
    subexprs.insert(sexp.to_string(), sexp.clone());
  }
  any_child_has_var
}

pub fn contains_function(sexp: &Sexp) -> bool {
  match sexp {
    Sexp::List(list) => {
      if !list.is_empty() {
        if let Sexp::String(str) = &list[0] {
          if !is_constructor(str) {
            return true;
          }
        }
      }
      list.iter().any(contains_function)
    }
    _ => false,
  }
}

fn find_instantiations_helper(proto: &Sexp, actual: &Sexp, instantiations_map: &mut SSubst) -> bool {
  match (proto, actual) {
    (Sexp::Empty, _) | (_, Sexp::Empty) => unreachable!(),
    (Sexp::String(proto_str), actual_sexp) => {
      if is_var(proto_str) {
        // It's a type variable so we can instantiate it
        let instantiation = actual_sexp.clone();
        if let Some(existing_instantiation) = instantiations_map.get(proto_str) {
          // Past instantiations must agree
          &instantiation == existing_instantiation
        } else {
          instantiations_map.insert(proto_str.clone(), instantiation);
          true
        }
      } else {
        // Otherwise, it must match the actual
        proto == actual
      }
    }
    (Sexp::List(proto_list), actual_sexp) => {
      // The actual must match the proto
      if !actual_sexp.is_list() {
        return false;
      }
      let actual_list = actual_sexp.list().unwrap();
      // Including lengths.
      if proto_list.len() != actual_list.len() {
        return false;
      }
      proto_list
        .iter()
        .zip(actual_list.iter())
        .all(|(sub_proto, sub_actual)| {
          find_instantiations_helper(sub_proto, sub_actual, instantiations_map)
        })
    }
  }
}

/// Find the instantiations of proto needed to obtain actual
///
/// ex: proto  = (Pair a (Pair b b))
///     actual = (Pair (List x) (Pair Nat Nat))
///
///     instantiations = {a: (List x), b: Nat}
///
/// actual is assumed to be a valid instantiation of proto.
pub fn find_instantiations(proto: &Sexp, actual: &Sexp) -> Option<SSubst> {
  let mut instantiations = HashMap::new();
  let successful_instantiation = find_instantiations_helper(&proto, &actual, &mut instantiations);
  if successful_instantiation {
    Some(instantiations)
  } else{
    // The instantiations are bogus/partial if it is not successful
    None
  }
}

/// Resolves a Sexp using instantiations, but does not recursively resolve it.
///
/// Ex: sexp:           (List a)
///     instantiations: {a: (List b), b: Nat}
///
///     returns:        (List b)
pub fn resolve_sexp(sexp: &Sexp, instantiations: &SSubst) -> Sexp {
  map_sexp(
    |v| {
      instantiations
        .get(v)
        .cloned()
        .unwrap_or_else(|| Sexp::String(v.to_string()))
    },
    sexp,
  )
}

/// Recursively resolves a Sexp using instantiations.
///
/// Ex: sexp:           (List a)
///     instantiations: {a: (List b), b: Nat}
///
///     returns:        (List Nat)
pub fn recursively_resolve_sexp(sexp: &Sexp, instantiations: &SSubst) -> Sexp {
  map_sexp(|v| recursively_resolve_variable(v, instantiations), sexp)
}

/// Requires that there are no cycles in instantiations.
pub fn recursively_resolve_variable(var: &str, instantiations: &SSubst) -> Sexp {
  instantiations
    .get(var)
    .map(|sexp| map_sexp(|v| recursively_resolve_variable(v, instantiations), sexp))
    .unwrap_or_else(|| Sexp::String(var.to_string()))
}

pub fn is_constructor(var_name: &str) -> bool {
  var_name.chars().next().unwrap().is_uppercase()
}

pub fn is_var(var_name: &str) -> bool {
  var_name.chars().next().unwrap().is_lowercase()
}

pub fn get_vars(e: &Expr) -> HashSet<Symbol>
{
  let mut vars = HashSet::new();
  for n in e.as_ref() {
    if n.is_leaf() && is_var(&n.op.to_string()) {
      vars.insert(n.op);
    }
  }
  vars
}

// Convert a symbol into a wildcard by prepending a '?' to it
pub fn to_wildcard(s: &Symbol) -> Var {
  format!("?{}", s).parse().unwrap()
}

// Does this pattern contain a wildcard derived from a guard variable?
// If so, we don't want to use it in a lemma because it cannot possibly be applied in a useful way.
pub fn has_guard_wildcards(p: &Pat) -> bool {
  p.vars().iter().any(|v| {
    v.to_string()
      .starts_with(format!("?{}", GUARD_PREFIX).as_str())
  })
}

// Convert e into a pattern by replacing all symbols where is_var holds with wildcards
pub fn to_pattern<'a, P>(e: &'a Expr, is_var: P) -> Pat
where
  P: Fn(&'a Symbol) -> bool,
{
  let mut pattern_ast = PatternAst::default();
  for n in e.as_ref() {
    if is_var(&n.op) {
      pattern_ast.add(ENodeOrVar::Var(to_wildcard(&n.op)));
    } else {
      pattern_ast.add(ENodeOrVar::ENode(n.clone()));
    }
  }
  Pattern::from(pattern_ast)
}

/// Create a Subst by looking up the given variables in the given egraph
pub fn lookup_vars<'a, I: Iterator<Item = &'a Symbol>, A: Analysis<SymbolLang>>(
  egraph: &EGraph<SymbolLang, A>,
  vars: I,
) -> IdSubst {
  let mut subst = IndexMap::new();
  for var in vars {
    match egraph.lookup(SymbolLang::leaf(*var)) {
      Some(id) => subst.insert(*var, id),
      None => panic!("lookup_vars: variable {} not found in egraph", var),
    };
  }
  subst
}

// Environment: for now just a map from datatype names to constructor names
pub type Env = HashMap<Symbol, (Vec<String>, Vec<Symbol>)>;

// Type context
pub type Context = HashMap<Symbol, Type>;

// Function definitions
pub type Defns = HashMap<String, Vec<(Sexp, Sexp)>>;

pub fn mk_context(descr: &[(&str, &str)]) -> Context {
  let mut ctx = Context::new();
  for (name, ty) in descr {
    ctx.insert(Symbol::from(*name), ty.parse().unwrap());
  }
  ctx
}

#[derive(Clone)]
pub struct RawEquation {
  pub lhs: Sexp,
  pub rhs: Sexp,
}

impl RawEquation {

  /// Creates a RawEquation, ensuring that it is in the right order
  pub fn new(lhs: Sexp, rhs: Sexp) -> Self {
    if lhs.to_string() < rhs.to_string() {
      Self {
        lhs, rhs
      }
    } else {
      Self {
        lhs: rhs,
        rhs: lhs,
      }
    }
  }

  /// Creates a RawEquation from exprs, ensuring that it is in the right order
  pub fn from_exprs(lhs: &Expr, rhs: &Expr) -> Self {
    let lhs_string = lhs.to_string();
    let rhs_string = rhs.to_string();
    let lhs = symbolic_expressions::parser::parse_str(&lhs_string).unwrap();
    let rhs = symbolic_expressions::parser::parse_str(&rhs_string).unwrap();
    if lhs_string < rhs_string {
      RawEquation {
        lhs, rhs
      }
    } else {
      RawEquation {
        lhs: rhs,
        rhs: lhs
      }
    }
  }


}

impl PartialEq for RawEquation {
    fn eq(&self, other: &Self) -> bool {
      self.partial_cmp(other) == Some(std::cmp::Ordering::Equal)
    }
}

// Can the vars of this expression be instantiated to the other expression?
fn cmp_sexp(sexp1: &Sexp, sexp2: &Sexp) -> Option<std::cmp::Ordering> {
  let sexp1_leq_sexp2 = find_instantiations(sexp1, sexp2).is_some();
  let sexp2_leq_sexp1 = find_instantiations(sexp2, sexp1).is_some();
  match (sexp1_leq_sexp2, sexp2_leq_sexp1) {
    (true, true) => Some(std::cmp::Ordering::Equal),
    (true, false) => Some(std::cmp::Ordering::Less),
    (false, true) => Some(std::cmp::Ordering::Greater),
    (false, false) => None,
  }
}

impl PartialOrd for RawEquation {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
      let lhs_cmp = cmp_sexp(&self.lhs, &other.lhs);
      let rhs_cmp = cmp_sexp(&self.rhs, &other.rhs);
      // They should be the same result, otherwise, they aren't equal
      if lhs_cmp == rhs_cmp {
        lhs_cmp
      } else {
        None
      }
    }
}

#[derive(Clone)]
pub struct RawEqWithParams {
  pub eq: RawEquation,
  pub params: Vec<(Symbol, Type)>
}

impl RawEqWithParams {
    pub fn new(eq: RawEquation, params: Vec<(Symbol, Type)>) -> Self { Self { eq, params } }

}

impl PartialEq for RawEqWithParams {
    fn eq(&self, other: &Self) -> bool {
        self.eq.eq(&other.eq)
    }
}

impl PartialOrd for RawEqWithParams {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
      self.eq.partial_cmp(&other.eq)
    }
}

// CK: Function is unused and I didn't feel like extending it to account for the change from
//     Env = HashMap<Symbol, Vec<Symbol>>
// to
//     Env = HashMap<Symbol, (Vec<String>, Vec<Symbol>)>
//
// pub fn mk_env(descr: &[(&str, &str)]) -> Env {
//   let mut env = Env::new();
//   for (name, cons) in descr {
//     env.insert(Symbol::from(*name), cons.split_whitespace().map(|s| Symbol::from(s)).collect());
//   }
//   env
// }
