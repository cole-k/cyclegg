use egg::*;
use lazy_static::lazy_static;

use std::{collections::HashMap, fmt::Display, str::FromStr, iter::zip};
use symbolic_expressions::{Sexp, SexpError};

use crate::config::CONFIG;

pub type SSubst = HashMap<String, Sexp>;

#[derive(Debug, Clone, PartialEq)]
pub struct Type {
  pub repr: Sexp,
}

impl Type {
  pub fn new(repr: Sexp) -> Self {
    Self { repr }
  }

  /// Is the type an arrow?
  pub fn is_arrow(&self) -> bool {
    match &self.repr {
      Sexp::String(_) => false,
      // Is the head (which should be a string) equal to ARROW?
      Sexp::List(xs) => xs[0].string().unwrap().as_str() == ARROW,
      _ => panic!("arity: type is empty"),
    }
  }

  /// If this type is a datatype, returns its name and otherwise return error.
  pub fn datatype(&self) -> Result<&String, SexpError> {
    match &self.repr {
      Sexp::String(s) => Ok(s), // This type is a D
      Sexp::List(xs) => {
        // This type is a type constructor application
        match xs[0].string()?.as_str() {
          ARROW => Err(SexpError::Other(
            "expected datatype and got arrow".to_string(),
          )),
          _ => xs[0].string(),
        }
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

fn starts_uppercase(string: &str) -> bool {
  string
    .chars()
    .next()
    .map(|c| c.is_ascii_uppercase())
    .unwrap_or(false)
}

fn find_instantiations_helper(proto: &Sexp, actual: &Sexp, instantiations_map: &mut SSubst) {
  match (proto, actual) {
    (Sexp::Empty, _) | (_, Sexp::Empty) => unreachable!(),
    (Sexp::String(proto_str), actual_sexp) => {
      if starts_uppercase(proto_str) {
        // It's a constant in the proto, which means it should be a constant
        // (i.e. a string with the same value) in the actual
        assert!(actual_sexp.is_string());
        assert_eq!(proto_str, actual_sexp.string().unwrap());
      } else {
        // Otherwise, it's a type variable so we can instantiate it
        let instantiation = actual_sexp.clone();
        if let Some(existing_instantiation) = instantiations_map.get(proto_str) {
          // Past instantiations must agree
          assert_eq!(&instantiation, existing_instantiation);
        } else {
          instantiations_map.insert(proto_str.clone(), instantiation);
        }
      }
    }
    (Sexp::List(proto_list), actual_sexp) => {
      // The actual must match the proto
      assert!(actual_sexp.is_list());
      let actual_list = actual_sexp.list().unwrap();
      // Including lengths.
      assert_eq!(proto_list.len(), actual_list.len());
      proto_list
        .iter()
        .zip(actual_list.iter())
        .for_each(|(sub_proto, sub_actual)| {
          find_instantiations_helper(sub_proto, sub_actual, instantiations_map)
        });
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
pub fn find_instantiations(proto: &Type, actual: &Type) -> SSubst {
  let mut instantiations = HashMap::new();
  find_instantiations_helper(&proto.repr, &actual.repr, &mut instantiations);
  instantiations
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

// FIXME: we should track down where these singletons are coming from and
// prevent them instead of fixing them
pub fn fix_singletons(sexp: Sexp) -> Sexp {
  match sexp {
    Sexp::List(list) => {
      if list.len() == 1 {
        fix_singletons(list[0].to_owned())
      } else {
        Sexp::List(list.into_iter().map(fix_singletons).collect())
      }
    }
    _ => sexp,
  }
}

fn structural_comparison_list(child: &Sexp, ancestors: &[Sexp]) -> StructuralComparison {
  let mut ancestor_comparison_results = ancestors
    .iter()
    .map(|ancestor_elem| structural_comparision(child, ancestor_elem));
  // Ignore the constructor
  ancestor_comparison_results.next();
  for ancestor_comparison_result in ancestor_comparison_results {
    // If any part is LE/LT, then it is LT because there is additional
    // structure on the RHS (the constructor).
    if ancestor_comparison_result == StructuralComparison::LE
      || ancestor_comparison_result == StructuralComparison::LT
    {
      return StructuralComparison::LT;
    }
  }
  StructuralComparison::Incomparable
}

pub fn structural_comparision(child: &Sexp, ancestor: &Sexp) -> StructuralComparison {
  match (child, ancestor) {
    (Sexp::String(child_name), Sexp::String(ancestor_name)) => {
      // If they are both constructors, they must match
      if is_constructor(child_name) && is_constructor(ancestor_name) {
        if child_name == ancestor_name {
          StructuralComparison::LE
        } else {
          StructuralComparison::Incomparable
        }
      }
      // If just the child is a constructor, then it is smaller
      // If they are both variables and the child is a descendent, it is smaller
      else if is_constructor(child_name) || is_descendant(child_name, ancestor_name) {
        StructuralComparison::LT
      } else if !is_constructor(ancestor_name) && child_name == ancestor_name {
        StructuralComparison::LE
      }
      // Otherwise, we don't know how to compare them
      else {
        StructuralComparison::Incomparable
      }
    }
    (Sexp::List(child_list), Sexp::List(ancestor_list)) => {
      // Try to compare the two as if they matched
      let mut result = StructuralComparison::LE;
      let elem_comparison_results = child_list
        .iter()
        .zip(ancestor_list.iter())
        .map(|(child_elem, ancestor_elem)| structural_comparision(child_elem, ancestor_elem));
      for elem_comparison_result in elem_comparison_results {
        // If any part is incomparable, the entire thing is.
        if elem_comparison_result == StructuralComparison::Incomparable {
          result = StructuralComparison::Incomparable;
          break;
        }
        result = std::cmp::min(result, elem_comparison_result);
      }
      // If that fails, try to compare the two as if the child is in any
      // substructure.
      if result != StructuralComparison::LT {
        result = std::cmp::min(result, structural_comparison_list(child, ancestor_list))
      }
      result
    }
    (Sexp::Empty, Sexp::Empty) => StructuralComparison::LE,
    (Sexp::String(_), Sexp::List(ancestor_list)) => {
      structural_comparison_list(child, ancestor_list)
    }
    // Consider the (List, String) case?
    // Does (Empty, _) need to return LE/LT?
    _ => StructuralComparison::Incomparable,
  }
}

pub fn is_constructor(var_name: &str) -> bool {
  var_name.chars().next().unwrap().is_uppercase()
}

pub fn is_function(e: &SymbolLang) -> bool {
  if e.is_leaf() {
    return false;
  }
  // Constructors begin with an uppercase, functions with a lowercase
  e.op.as_str().chars().next().unwrap().is_lowercase()
}

/// This is an ad-hoc struct made to try and only ever extract functions
/// from an e-class at the top level, extracting something else otherwise.
///
/// In practice, using this allows us to figure out via extraction whether
/// an e-class contains only vars/constructors.
///
/// The "is function" analysis _only_ applies at the top level (i.e. among the
/// enodes in the e-class you're extracting from)! The extraction is otherwise
/// just AstSize.
pub struct AstSizePreferFunction;
impl CostFunction<SymbolLang> for AstSizePreferFunction {
  type Cost = (bool, usize);
  fn cost<C>(&mut self, enode: &SymbolLang, mut costs: C) -> Self::Cost
  where
      C: FnMut(Id) -> Self::Cost,
  {
    let is_not_function = !is_function(enode);
    let cost = enode.fold(1, |sum: usize, id| sum.saturating_add(costs(id).1));
    (is_not_function, cost)
  }
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

pub struct DataTypeSize {
  pub min_size: usize,
  // No max means that it's unbounded (i.e. recursive). Most datatypes will have
  // an unbounded max_size.
  pub max_size: Option<usize>,
}

impl Default for DataTypeSize {
  fn default() -> Self {
    DataTypeSize {
      min_size: 0,
      max_size: Some(0),
    }
  }
}

impl DataTypeSize {
  /// Merges by adding the sizes (since max_size = None is infinity, we use
  /// and_then)
  pub fn merge_add(&self, other: &Self) -> Self {
    Self {
      min_size: self.min_size + other.min_size,
      max_size: self.max_size.and_then(|self_max_size| other.max_size.and_then(|other_max_size| Some(self_max_size + other_max_size))),
    }
  }

  /// Merges by taking the minimum of the min_size and maximum of the max_size
  pub fn merge_min_max(&self, other:&Self) -> Self {
    Self {
      min_size: std::cmp::min(self.min_size, other.min_size),
      max_size: self.max_size.and_then(|self_max_size| other.max_size.and_then(|other_max_size| Some(std::cmp::max(self_max_size, other_max_size)))),
    }
  }
}

/// The size returned represents the minimum and maximum sizes
/// achievable across all constructors
///
/// e.g.
/// data Unit = Unit :: Unit
///
/// data Tree a
///   = Leaf :: Tree a
///   | Node :: Tree a -> a -> Tree a -> Tree a
///
/// data_type_size(Unit) = DataTypeSize {
///   min_size: 1,
///   max_size: Some(1),
/// }
///
/// data_type_size(Tree Unit) = DataTypeSize {
///   min_size: 1,
///   max_size: None
/// }
///
pub fn data_type_size(ty: &Type, env:&Env, ctx: &Context) -> DataTypeSize {
  data_type_sizes(ty, env, ctx).iter().fold(DataTypeSize::default(), |acc, (_cons, size)| {
    acc.merge_min_max(size)
  })
}

/// Returns a vec of (Constructor, DataTypeSize)
pub fn data_type_sizes(ty: &Type, env: &Env, ctx: &Context) -> Vec<(Symbol, DataTypeSize)> {
  if ty.is_arrow() {
    panic!("data_type_sizes: Type {} is unsupported (arrow types not allowed)", ty);
  }

  // Extract a datatype from a type as well as the types of its arguments
  //
  // e.g.
  //
  // Bool -> (Bool, [])
  // List (Tree a) -> (List, [Tree a])
  let (dt, arg_types) = match &ty.repr {
    Sexp::String(dt) => {
      (dt, Vec::default())
    }
    Sexp::List(lst) => {
      let mut lst_iter = lst.iter();
      let dt = lst_iter.next().unwrap().string().unwrap();
      let arg_types = lst_iter.map(|arg| Type::new(arg.clone())).collect();
      (dt, arg_types)
    }
    Sexp::Empty => {
      panic!("data_type_sizes: Empty type");
    }
  };
  let (vars, cons) = env.get(&Symbol::from_str(dt).unwrap()).unwrap();

  // Match the vars with the args so we know what we need to substitute
  let type_var_map: HashMap<String, Type> = zip(vars.iter().cloned(), arg_types).collect();
  cons.iter().map(|con| {
    let con_type = ctx.get(con).unwrap();
    // Base case: nullary constructors, e.g. those in
    //
    // data Bool
    //   = True :: Bool
    //   | False :: Bool
    //
    // We don't check that the type matches the datatype,
    // but it really should.
    if !con_type.is_arrow() {
        return (*con, DataTypeSize {
          min_size: 1,
          max_size: Some(1),
        })
    }

    // Ignore the return type, we'll again assume
    // that it matches the datatype.
    let (arg_types, _ret) = con_type.args_ret();
    // The starting values of 1 accounts for the fact that the constructor is its own base case.
    let total_size = arg_types.iter().fold(DataTypeSize { min_size: 1, max_size: Some(1) }, |acc, arg_type| {
      let arg_type = match &arg_type.repr {
        // If it's a type variable, it'll be in the map, so resolve it
        Sexp::String(var) if var.chars().next().unwrap().is_ascii_lowercase() => {
          type_var_map.get(var).unwrap()
        }
        // Otherwise, don't change it
        _ => arg_type,
      };
      //FIXME: will infinitely loop for any recursive type. need to find the
      // minimum among the base cases to put as the minimum and put the maximum
      // as None.
      let arg_size = data_type_size(arg_type, env, ctx);
      acc.merge_add(&arg_size)
    });

    (*con, total_size)

  }).collect()
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
