use egg::*;
use indexmap::IndexMap;
use indexmap::IndexSet;
use std::char;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fs::File;
use std::io::{Read, Write};
use std::vec;
use symbolic_expressions::*;

use crate::ast::*;
use crate::goal::*;

fn make_rewrite_for_defn(name: &str, args: &Sexp, value: &Sexp) -> Rw {
  let name_sexp = Sexp::String(name.to_string());
  let pattern_with_name = match args {
    Sexp::Empty => name_sexp,
    Sexp::List(args) => {
      let mut new_list = vec![name_sexp];
      new_list.extend(args.iter().cloned());
      Sexp::List(new_list)
    }
    arg @ Sexp::String(_) => Sexp::List(vec![name_sexp, arg.clone()]),
  };
  let lhs = pattern_with_name.to_string();
  let rhs = value.to_string();
  println!("rewrite rule {} : {} => {}", name, lhs, rhs);
  let searcher: Pattern<SymbolLang> = lhs.parse().unwrap();
  let applier: Pattern<SymbolLang> = rhs.parse().unwrap();
  Rewrite::new(lhs, searcher, applier).unwrap()
}

pub struct RawEquation {
  pub lhs: Sexp,
  pub rhs: Sexp,
}

pub struct RawGoal {
  pub name: String,
  pub equation: RawEquation,
  pub premise: Option<RawEquation>,
  pub params: Vec<(Symbol, Type)>,
  pub local_rules: Vec<Rw>,
}

#[derive(Default)]
pub struct ParserState {
  pub env: Env,
  pub context: Context,
  pub defns: Defns,
  pub rules: Vec<Rw>,
  pub raw_goals: Vec<RawGoal>,
}

impl ParserState {
  /// Return all function definitions used in exprs,
  /// including the functions transitively used in those definitions.
  fn used_names_and_definitions(&self, exprs: &Vec<Expr>) -> (HashSet<Symbol>, Vec<Rw>) {
    let mut used_names = HashSet::new();
    let mut used_defs = vec![];
    let mut worklist = vec![];
    for expr in exprs {
      let expr_as_nodes_or_var: Vec<ENodeOrVar<SymbolLang>> = expr
        .as_ref()
        .iter()
        .map(|n| ENodeOrVar::ENode(n.clone()))
        .collect();
      let expr_as_pattern: PatternAst<SymbolLang> = PatternAst::from(expr_as_nodes_or_var);
      self.add_functions(&expr_as_pattern, &mut used_names, &mut worklist);
    }
    while let Some(s) = worklist.pop() {
      let def_rules = self.definition(&s);
      for rule in def_rules {
        used_defs.push(rule.clone());
        let rhs = rule.applier.get_pattern_ast().unwrap();
        self.add_functions(rhs, &mut used_names, &mut worklist);
      }
    }
    (used_names, used_defs)
  }

  /// Add all functions mentioned in e to used_names and worklist.
  fn add_functions(
    &self,
    e: &PatternAst<SymbolLang>,
    used_names: &mut HashSet<Symbol>,
    worklist: &mut Vec<Symbol>,
  ) {
    for node_or_var in e.as_ref() {
      if let ENodeOrVar::ENode(node) = node_or_var {
        let s = node.op;
        if self.context.contains_key(&s)
          && !is_constructor(&s.to_string())
          && !used_names.contains(&s)
        {
          used_names.insert(s);
          worklist.push(s);
        }
      }
    }
  }

  /// Name of the rule that converts a partial application of name into a first-order application.
  fn part_app_rule(name: &Symbol) -> String {
    format!("apply-{}", name)
  }

  /// Return all rules that define the function name,
  /// including the rule that defines conversion from partial to first-order application.
  fn definition(&self, name: &Symbol) -> Vec<&Rw> {
    let mut res = Vec::new();
    for r in &self.rules {
      if r.name.to_string() == ParserState::part_app_rule(name) {
        res.push(r);
      } else {
        let lhs_pat = r.searcher.get_pattern_ast().unwrap();
        let lhs_head = lhs_pat.as_ref().iter().last().unwrap();
        if let ENodeOrVar::ENode(n) = lhs_head {
          if n.op == *name {
            res.push(r);
          }
        }
      }
    }
    res
  }

  /// If type_ is an arrow type, return a rewrite that allows converting partial applications into regular first-order applications,
  /// that is: ($ ... ($ name ?x0) ... ?xn) => (name ?x0 ... ?xn).
  fn partial_application(name: &Symbol, type_: &Type) -> Option<Rw> {
    let (args, _) = type_.args_ret();
    if args.is_empty() {
      // This is not a function, so we can't partially apply it
      None
    } else {
      let wildcard = |i: usize| format!("?x{}", i).parse().unwrap();
      // RHS is a full first-order application of name to as many wildcards as there are arguments:
      let rhs: Pat = format!(
        "({} {})",
        name,
        (0..args.len())
          .map(wildcard)
          .collect::<Vec<String>>()
          .join(" ")
      )
      .parse()
      .unwrap();
      // LHS is looks like this "($ ... ($ name ?x0) ... ?xn)":
      let mut lhs_str: String = format!("({} {} ?x0)", APPLY, name);
      for i in (0..args.len()).skip(1) {
        lhs_str = format!("({} {} ?x{})", APPLY, lhs_str, i);
      }
      let lhs: Pat = lhs_str.parse().unwrap();
      Some(Rewrite::new(ParserState::part_app_rule(name), lhs, rhs).unwrap())
    }
  }

  /// This is done after parsing because that way the order we parse does not
  /// affect whether a goal has all definitions in scope.
  pub fn get_reductions_and_definitions(
    &self,
    goal: &RawGoal,
    local_rules: Vec<Rw>,
  ) -> (Vec<Rw>, Defns) {
    let lhs: Expr = goal.equation.lhs.to_string().parse().unwrap();
    let rhs: Expr = goal.equation.rhs.to_string().parse().unwrap();
    let mut roots = vec![lhs, rhs];
    if let Some(premise) = &goal.premise {
      let premise_lhs: Expr = premise.lhs.to_string().parse().unwrap();
      let premise_rhs: Expr = premise.rhs.to_string().parse().unwrap();
      roots.push(premise_lhs);
      roots.push(premise_rhs);
    }
    let (names, mut rules) = self.used_names_and_definitions(&roots);
    let filtered_defns = self
      .defns
      .iter()
      .filter_map(|(defn_name, defn_cases)| {
        if names.contains(&Symbol::from(defn_name)) {
          Some((defn_name.clone(), defn_cases.clone()))
        } else {
          None
        }
      })
      .collect();
    rules.extend(local_rules);
    (rules, filtered_defns)
  }
}

fn validate_identifier(identifier: &str) {
  // Important: we disallow the use of underscore in our identifiers so that
  // autogenerated names like for guards or variable splits will not conflict
  // with variable names.
  assert!(!identifier.contains('_'));
}

fn validate_datatype(datatype: &str) {
  validate_identifier(datatype);
  assert!(datatype.starts_with(char::is_uppercase));
}

fn validate_variable(variable: &str) {
  validate_identifier(variable);
  assert!(variable.starts_with(char::is_lowercase));
}

/// Parsing the file returns the whole parser state.
///
/// There are two advantages to this from the previous approach, which was returning a Vec<Goal>.
///
/// 1. We can now put propositions anywhere in the file and not worry about
///    definitions being missed since we parse all definitions before we create
///    goals for props.
/// 2. We can now avoid a lot of cloning that happens when we create new sub-goals because several
///    global items that we use (such as the global context) can now be passed as references.
///
/// but most of the work is done ahead of time.
pub fn parse_ceg_file(filename: &str) -> Result<ParserState, SexpError> {
  let mut state = ParserState::default();
  let sexpr = parser::parse_file(filename).unwrap();

  // println!("sexpr: {:#?}", sexpr);

  // return Ok(state);

  for decl in sexpr.list()? {
    let decl_kind = decl.list()?[0].string()?.as_str();
    match decl_kind {
      "data" => {
        // This is a datatype declaration: parse name, type variables, and constructor list:
        let name = decl.list()?[1].string()?;
        let mut cons_index = 2;
        // We'll allow no type variables to be given, in which case the second
        // argument must be the constructor list.
        let mangled_type_var_names = if decl.list()?.len() == 3 {
          vec![]
        } else {
          // The length should be 4.
          assert_eq!(decl.list()?.len(), 4);
          cons_index += 1;
          let type_vars = decl.list()?[2].list()?;
          type_vars
            .iter()
            .map(|x| {
              let var_name = x.string()?;
              validate_variable(var_name);
              // FIXME: We should really only mangle names in the emitted
              // explanations. If this is fixed, please change the config so
              // that it does not implicitly adjust the maximum split depth to
              // account for the additional underscore.
              Ok(mangle_name(var_name))
            })
            .collect::<Result<Vec<String>, SexpError>>()?
        };
        let cons = decl.list()?[cons_index].list()?;
        let mangled_cons_symbs = cons
          .iter()
          .map(|x| {
            let cons_name = x.string()?;
            validate_datatype(cons_name);
            Ok(Symbol::from(&mangle_name(cons_name)))
          })
          .collect::<Result<Vec<Symbol>, SexpError>>()?;
        validate_datatype(name);
        // println!(
        //   "{:?}, {:?}, {:?}",
        //   name, mangled_type_var_names, mangled_cons_symbs
        // );
        state.env.insert(
          Symbol::from(&mangle_name(name)),
          (mangled_type_var_names, mangled_cons_symbs),
        );
      }
      "::" => {
        // This is a type binding: parse name and type:
        let name = decl.list()?[1].string()?;
        // This could be either a function or a datatype.
        validate_identifier(name);
        let mangled_name = Symbol::from(&mangle_name(name));
        // Mangle each of the elements in the sexp.
        // println!("{:?}", decl.list()?[2]);
        let mangled_type = Type::new(mangle_sexp(&decl.list()?[2]));
        if let Some(rw) = ParserState::partial_application(&mangled_name, &mangled_type) {
          state.rules.push(rw);
        }
        state.context.insert(mangled_name, mangled_type);
      }
      "let" => {
        // This is a definition
        let name = decl.list()?[1].string()?;
        validate_variable(name);
        let mangled_name = mangle_name(name);
        // Extract the args and value
        let mangled_args = mangle_sexp(&decl.list()?[2]);
        let mangled_value = mangle_sexp(&decl.list()?[3]);
        // Add to the rewrites
        state.rules.push(make_rewrite_for_defn(
          &mangled_name,
          &mangled_args,
          &mangled_value,
        ));
        // Add to the hashmap
        if let Some(cases) = state.defns.get_mut(&mangled_name) {
          cases.push((mangled_args, mangled_value));
        } else {
          state
            .defns
            .insert(mangled_name, vec![(mangled_args, mangled_value)]);
        }
      }
      "===" | "==>" => {
        // This is a goal: parse name, parameter names, parameter types;
        // if the goal is conditional, parse the lhs and rhs of the premise;
        // then parse the lhs and rhs of the goal;
        // finally, if there's more elements, parse a list of lemmas.
        //
        // Goal names are allowed to have underscores so we won't validate them. The
        // worst this can do is have a goal wrongly match a variable name, which should
        // hopefully never happen.
        let name = decl.list()?[1].string()?.to_string();
        let param_name_list = decl.list()?[2].list()?;
        let mangled_param_names = param_name_list
          .iter()
          .map(|x| {
            let var_name = x.string()?;
            validate_variable(var_name);
            Ok(Symbol::from(&mangle_name(var_name)))
          })
          .collect::<Result<Vec<Symbol>, SexpError>>()?;
        let param_type_list = decl.list()?[3].list()?;
        let mangled_param_types = param_type_list.iter().map(|x| Type::new(mangle_sexp(x)));
        let params = mangled_param_names
          .into_iter()
          .zip(mangled_param_types)
          .collect();

        let mut index = 4;
        let premise = if decl_kind == "==>" {
          let lhs: Sexp = mangle_sexp(&decl.list()?[index]);
          let rhs: Sexp = mangle_sexp(&decl.list()?[index + 1]);
          index += 2;
          Some(RawEquation { lhs, rhs })
        } else {
          None
        };

        let lhs: Sexp = mangle_sexp(&decl.list()?[index]);
        let rhs: Sexp = mangle_sexp(&decl.list()?[index + 1]);
        index += 2;
        let equation = RawEquation { lhs, rhs };

        let mut local_rules = vec![];
        // If there's more to parse, these must be lemmas.
        if decl.list()?.len() > index {
          // Lemmas we are using to aid this proof
          for rule_sexp in decl.list()?[index].list()? {
            let lhs = mangle_sexp(&rule_sexp.list()?[1]);
            let rhs = mangle_sexp(&rule_sexp.list()?[2]);
            let searcher: Pattern<SymbolLang> = lhs.to_string().parse().unwrap();
            let applier: Pattern<SymbolLang> = rhs.to_string().parse().unwrap();
            // check if this is a bidirectional rewrite
            match rule_sexp.list()?[0].string()?.as_str() {
              "=>" => {
                let rw = Rewrite::new(
                  format!("hyp-lemma-{}", lhs),
                  searcher.clone(),
                  applier.clone(),
                )
                .unwrap();
                local_rules.push(rw);
                // println!("adding rewrite rule: {} => {}", lhs, rhs);
              }
              "<=>" => {
                let rw = Rewrite::new(
                  format!("hyp-lemma-{}", lhs),
                  searcher.clone(),
                  applier.clone(),
                )
                .unwrap();
                local_rules.push(rw);
                let rw = Rewrite::new(
                  format!("hyp-lemma-{}", rhs),
                  applier.clone(),
                  searcher.clone(),
                )
                .unwrap();
                local_rules.push(rw);
              }
              _ => panic!("unknown rewrite rules: {}", rule_sexp),
            }
          }
        }

        let raw_goal = RawGoal {
          name,
          premise,
          equation,
          params,
          local_rules,
        };
        state.raw_goals.push(raw_goal);
      }
      "//" => {
        // comment
      }
      _ => panic!("unknown declaration: {}", decl),
    }
  }
  Ok(state)
}

/// Parse smtlib version 2.6 files
pub fn parse_smtlib_file(filename: &str) -> Result<ParserState, SexpError> {
  println!("parsing smtlib file: {}", filename);
  add_parantheses_to_file(filename).unwrap();

  let mut state = parse_ceg_file("examples/defns.ceg").unwrap();
  let sexpr = parser::parse_file(filename).unwrap();

  // println!("sexpr: {:#?}", sexpr);
  // need a set of sorts
  let mut sort_set: IndexSet<String> = IndexSet::new();
  let mut fixed_names: HashMap<String, String> = HashMap::new();

  fixed_names.insert("true".to_string(), "True".to_string());
  fixed_names.insert("false".to_string(), "False".to_string());
  fixed_names.insert("not".to_string(), "not".to_string());
  fixed_names.insert("and".to_string(), "and".to_string());
  fixed_names.insert("or".to_string(), "or".to_string());
  fixed_names.insert("ite".to_string(), "ite".to_string());

  for decl in sexpr.list()?.clone().iter_mut() {
    // println!("decl: {:#?}", decl);
    let decl_kind = decl.list()?[0].string()?.as_str();
    match decl_kind {
      "declare-datatypes" => {
        // This is a datatype declaration: parse name, type variables, and constructor list:
        // println!("datatype decl");
        let mut type_vars: HashSet<String> = HashSet::new();
        let mut constructors: Vec<Symbol> = vec![];
        // for some reason, the smtlib format has a lot of extra parentheses
        // so we sometimes have to go a few levels deep to get the stuff we want
        let index = 1;
        let mut name_sexp = &decl.list()?[index];
        while name_sexp.list()?.len() == 1 && name_sexp.list()?[0].is_list() {
          name_sexp = &name_sexp.list()?[0];
        }

        let mut dt_name = name_sexp.list()?[0].string()?;
        if !dt_name.starts_with(char::is_uppercase) {
          fixed_names.insert(dt_name.to_string(), format!("D{}", dt_name));
        } else {
          fixed_names.insert(dt_name.to_string(), dt_name.to_string());
        }
        let tmp = fixed_names.to_owned();
        dt_name = tmp.get(dt_name).unwrap();

        // println!("!!!DT name: {}", dt_name);

        // after parsing name and arity we can get the constructor list
        // a constructor can have arity 0 or more
        let cons_index = 2;
        // index 2 consists entirely of constructor lists
        let mut cons_list = &decl.list()?[cons_index];
        // println!("cons list: {:#?}", cons_list);
        // while cons_list.list()?.len() == 1 && cons_list.list()?[0].is_list() {
        cons_list = &cons_list.list()?[0];
        // }
        // cons list is now a list of constructors
        let conss = cons_list.list()?;
        // println!("conss: {:#?}", conss);
        for mut x in conss {
          // each constructor is a list of the form (param_name <optional type> <optional type> ...). the return type is just the name of the datatype
          // the types themselves consist of a name and a type
          // println!("x: {}", x);
          let x_tmp = &fix_all_names(&x, &fixed_names);
          x = x_tmp;
          let x_list = x.list().unwrap();
          let mut cons_name = x_list[0].string().unwrap();
          // add a capital X to the beginning of the name if it begins with a lowercase
          if !cons_name.starts_with(char::is_uppercase) {
            fixed_names.insert(cons_name.to_string(), format!("C{}", cons_name));
          } else {
            fixed_names.insert(cons_name.to_string(), cons_name.to_string());
          }
          cons_name = fixed_names.get(cons_name).unwrap();
          constructors.push(Symbol::from(&mangle_name(cons_name)));

          // everything after the first element is a type
          for y in &x_list[1..] {
            let y_list = y.list().unwrap();
            let param_type = &y_list[1];
            // println!("param name: {}", param_name);
            // println!("param type: {}", param_type);

            // TODO: if any of the param types are sorts, we need to add it to the type_vars

            if sort_set.contains(param_type.string()?) {
              // validate_variable(&param_type);
              type_vars.insert(mangle_sexp(&param_type).to_string());
            }
          }

          let mut dt_with_type_vars = Sexp::String(dt_name.to_string());
          if !type_vars.is_empty() {
            dt_with_type_vars = Sexp::List(
              [
                vec![Sexp::String(dt_name.to_string())],
                type_vars
                  .iter()
                  .map(|s| Sexp::String(s.to_string()))
                  .collect(),
              ]
              .concat(),
            );
          }
          // construct the arrow type for the constructor
          // let mut type_with_arrow = vec![Sexp::String(ARROW.to_string())];
          let typs: Vec<Sexp> = x_list[1..]
            .iter()
            .map(|y| {
              let y_tmp = fix_all_names(y, &fixed_names);
              let y_list = y_tmp.list().unwrap();
              let param_type = y_list[1].string().unwrap();
              // println!("param name: {}, cons name: {}", param_type, cons_name);
              if param_type == dt_name && !type_vars.is_empty() {
                dt_with_type_vars.clone()
              } else {
                y_list[1].clone()
              }
            })
            .collect();

          let mut type_with_arrow: Sexp = Sexp::Empty;
          if !typs.is_empty() {
            let mut tmpvec = vec![Sexp::String(ARROW.to_string())];
            tmpvec.push(Sexp::List(typs));
            tmpvec.push(dt_with_type_vars.clone());
            type_with_arrow = Sexp::List(tmpvec);
          } else {
            type_with_arrow = dt_with_type_vars.clone();
          }
          // type_with_arrow.push(Sexp::String(dt_name.to_string()));
          let mangled_type = Type::new(mangle_sexp(&type_with_arrow));
          state
            .context
            .insert(Symbol::from(&mangle_name(cons_name)), mangled_type);
        }
        // println!("{}, {:?}, {:?}", dt_name, type_vars, constructors);
        state.env.insert(
          Symbol::from(&mangle_name(dt_name)),
          (type_vars.into_iter().collect(), constructors),
        );
      }
      "declare-sort" => {
        // This is a sort declaration: parse name
        // println!("sort decl");
        // println!("{:?}", decl);
        let name = &decl.list()?[1].string()?;
        // println!("name: {}", name);
        // the arity is always zero so we don't care
        sort_set.insert(name.to_string());
      }
      "declare-fun" => {
        // this just defines an uninterepreted function
        // println!("declare-fun");
        // println!("{:?}", decl);
        *decl = fix_all_names(&decl, &fixed_names);
        // println!("{}", decl);

        let name = decl.list()?[1].string()?;
        fixed_names.insert(name.to_string(), name.to_string());
        validate_identifier(name);
        let mangled_name = Symbol::from(&mangle_name(name));
        // create a new sexp with an arrow type
        let type_with_arrow = Sexp::List(vec![
          Sexp::String(ARROW.to_string()),
          decl.list()?[2].clone(),
          decl.list()?[3].clone(),
        ]);
        let mangled_type = Type::new(mangle_sexp(&type_with_arrow));
        state.context.insert(mangled_name, mangled_type);
      }
      "declare-const" => {
        let name = decl.list()?[1].string()?;
        fixed_names.insert(name.to_string(), name.to_string());
      }
      "define-fun-rec" | "define-fun" => {
        // println!("define-fun");
        // this is the most challenging bit
        // we need to parse the function name, the parameters, and the body
        // the body could have match expressions, and we need to parse those and turn them into rewrite rules
        // also important is that the function name could also be something like |-2| which smtlib actually allows
        // so we need to mangle the name
        // println!("{:#?}", decl);
        let declc = decl.clone();
        let name = declc.list()?[1].string()?;
        if !name.starts_with(char::is_lowercase) {
          fixed_names.insert(name.to_string(), format!("f{}", name));
        } else {
          fixed_names.insert(name.to_string(), name.to_string());
        }
        *decl = fix_all_names(&decl, &fixed_names);
        // println!("function defn: {}", decl);
        validate_identifier(fixed_names.get(name).unwrap());
        let mangled_name = Symbol::from(mangle_name(fixed_names.get(name).unwrap()));

        let mut arg_type_map = HashMap::new();

        let mut args_list: Vec<Sexp> = vec![];
        let args = decl.list()?[2].list()?;
        let mut arg_values: IndexMap<String, Sexp> = IndexMap::new();
        for arg in args {
          arg_values.insert(
            arg.list()?[0].string()?.to_string(),
            Sexp::String("?".to_string() + &arg.list()?[0].string()?.to_string()),
          );
          let arg_typ_tmp = arg.list()?[1].clone();
          let mut arg_typ = arg_typ_tmp.clone();
          if arg_typ_tmp.is_string() {
            // println!("arg typ: {}", arg_typ);
            // println!("{:?}", state.env);
            if let Some(x) = state
              .env
              .get(&Symbol::from(&mangle_name(&arg_typ_tmp.string()?)))
            {
              // if it has type stuff add it
              if !x.0.is_empty() {
                let mut tmp = vec![arg_typ_tmp.clone()];
                tmp.append(&mut x.0.iter().map(|x1| Sexp::String(x1.to_string())).collect());
                // args_list.push(Sexp::List(tmp));
                arg_typ = Sexp::List(tmp);
              }
            }
          }
          args_list.push(arg_typ.clone());
          arg_type_map.insert(arg.list()?[0].string()?.to_string(), arg_typ);
        }

        // println!("argvals: {:#?}", arg_values);

        let mut ret = decl.list()?[3].clone();
        if ret.is_string() {
          if let Some(x) = state.env.get(&Symbol::from(&mangle_name(&ret.string()?))) {
            // if it has type stuff add it
            if !x.0.is_empty() {
              let mut tmp = vec![ret.clone()];
              tmp.append(&mut x.0.iter().map(|x1| Sexp::String(x1.to_string())).collect());
              ret = Sexp::List(tmp);
            }
          }
        }
        let type_with_arrow = Sexp::List(vec![
          Sexp::String(ARROW.to_string()),
          Sexp::List(args_list),
          ret,
        ]);
        // println!("type with arrow: {}", type_with_arrow);
        let mangled_type = Type::new(mangle_sexp(&type_with_arrow));
        state.context.insert(mangled_name, mangled_type);

        // now we need to parse the body
        // the body is either a match or a let

        // let mut rules: Vec<Rw> = vec![];
        let body = decl.list()?[4].list()?;

        let _ = parse_func_body(
          mangled_name.into(),
          body,
          &arg_type_map,
          &fixed_names,
          &mut arg_values,
          &mut HashMap::new(),
          &mut state,
        );
      }
      "define-funs-rec" => {
        // mutually recursive functions
        // let mut declc = decl.clone();
        *decl = fix_all_names(&decl, &fixed_names);
        // println!("function defn: {}", decl);
        let fn_names = decl.list()?[1].list()?;
        // println!("fn_names: {:#?}", fn_names);
        let fn_bodies = decl.list()?[2].list()?;
        assert_eq!(fn_names.len(), fn_bodies.len());

        //put all the names in fixed_names first since we use it for other stuff
        for i in 0..fn_names.len() {
          // println!("i: {}", i);
          // let fnames = fn_names.clone();
          let name = fn_names[i].list()?[0].string()?;
          // println!("name: {}", name);
          if !name.starts_with(char::is_lowercase) {
            fixed_names.insert(name.to_string(), format!("f{}", name));
          } else {
            fixed_names.insert(name.to_string(), name.to_string());
          }
        }

        for i in 0..fn_names.len() {
          // println!("i: {}", i);
          let fnames = fn_names.clone();
          let fbodies = fn_bodies.clone();
          let name = fnames[i].list()?[0].string()?;

          // println!("function defn: {}", decl);
          validate_identifier(fixed_names.get(name).unwrap());
          let mangled_name = Symbol::from(mangle_name(fixed_names.get(name).unwrap()));

          let mut arg_type_map = HashMap::new();

          let mut args_list: Vec<Sexp> = vec![];
          let args = fnames[i].list()?[1].list()?;
          let mut arg_values: IndexMap<String, Sexp> = IndexMap::new();
          for arg in args {
            arg_values.insert(
              arg.list()?[0].string()?.to_string(),
              Sexp::String("?".to_string() + &arg.list()?[0].string()?.to_string()),
            );
            let arg_typ_tmp = arg.list()?[1].clone();
            let mut arg_typ = arg_typ_tmp.clone();
            if arg_typ_tmp.is_string() {
              // println!("arg typ: {}", arg_typ);
              // println!("{:?}", state.env);
              if let Some(x) = state
                .env
                .get(&Symbol::from(&mangle_name(&arg_typ_tmp.string()?)))
              {
                // if it has type stuff add it
                if !x.0.is_empty() {
                  let mut tmp = vec![arg_typ_tmp.clone()];
                  tmp.append(&mut x.0.iter().map(|x1| Sexp::String(x1.to_string())).collect());
                  // args_list.push(Sexp::List(tmp));
                  arg_typ = Sexp::List(tmp);
                }
              }
            }
            args_list.push(arg_typ.clone());
            arg_type_map.insert(arg.list()?[0].string()?.to_string(), arg_typ);
          }

          // println!("argvals: {:#?}", arg_values);

          let mut ret = fnames[i].list()?[2].clone();
          if ret.is_string() {
            if let Some(x) = state.env.get(&Symbol::from(&mangle_name(&ret.string()?))) {
              // if it has type stuff add it
              if !x.0.is_empty() {
                let mut tmp = vec![ret.clone()];
                tmp.append(&mut x.0.iter().map(|x1| Sexp::String(x1.to_string())).collect());
                ret = Sexp::List(tmp);
              }
            }
          }
          let type_with_arrow = Sexp::List(vec![
            Sexp::String(ARROW.to_string()),
            Sexp::List(args_list),
            ret,
          ]);
          // println!("type with arrow: {}", type_with_arrow);
          let mangled_type = Type::new(mangle_sexp(&type_with_arrow));
          state.context.insert(mangled_name, mangled_type);

          // now we need to parse the body
          // the body is either a match or a let

          // let mut rules: Vec<Rw> = vec![];
          let body = fbodies[i].list()?;

          let _ = parse_func_body(
            mangled_name.into(),
            body,
            &arg_type_map,
            &fixed_names,
            &mut arg_values,
            &mut HashMap::new(),
            &mut state,
          );
        }
      }

      "assert" => {
        // println!("assert");
        *decl = fix_all_names(&decl, &fixed_names);
        let local_rules = vec![];
        let mut assertion = decl.list()?[1].list()?;
        // println!("assertion1: {:#?}", assertion);
        if assertion[0] != Sexp::String("not".to_string()) {
          continue;
        }
        assertion = assertion[1].list()?;
        assert!(assertion[0] == Sexp::String("forall".to_string()));

        // assertion[1] is the list of variables / parameters
        let param_name_list = assertion[1].list()?;
        let params: Vec<(Symbol, Type)> = param_name_list
          .iter()
          .map(|var_and_type| {
            let v = var_and_type.list().unwrap()[0].string().unwrap();
            let tmp_t = &var_and_type.list().unwrap()[1];
            (
              Symbol::from(&mangle_name(v)),
              Type::new(mangle_sexp(&tmp_t)),
            )
          })
          .collect();
        // println!("assertion2: {:#?}", assertion[2]);
        let mut premise: Option<RawEquation> = None;
        let assertion_type = assertion[2].list()?[0].string()?;
        if assertion_type == "=>" {
          let equation: RawEquation;
          let mut premise_sexp = assertion[2].list()?[1].clone();
          premise_sexp = fix_all_names(&premise_sexp, &fixed_names);
          if premise_sexp.list().unwrap()[0].string()? == "=" {
            let lhs = mangle_sexp(&premise_sexp.list().unwrap()[1]);
            let rhs = mangle_sexp(&premise_sexp.list().unwrap()[2]);
            premise = Some(RawEquation { lhs, rhs });
          } else {
            let lhs = mangle_sexp(&premise_sexp);
            let rhs = mangle_sexp(&Sexp::String("True".to_string()));
            // println!("lhs: {}", lhs);
            // println!("rhs: {}", rhs);
            premise = Some(RawEquation { lhs, rhs });
          }
          let mut assertion_sexp = assertion[2].list()?[2].clone();
          assertion_sexp = fix_all_names(&assertion_sexp, &fixed_names);
          if assertion_sexp.list().unwrap()[0].string()? == "=" {
            let lhs = mangle_sexp(&assertion_sexp.list().unwrap()[1]);
            let rhs = mangle_sexp(&assertion_sexp.list().unwrap()[2]);
            equation = RawEquation { lhs, rhs };
          } else {
            let lhs = mangle_sexp(&assertion_sexp);
            let rhs = mangle_sexp(&Sexp::String("True".to_string()));
            equation = RawEquation { lhs, rhs };
          }
          let raw_goal = RawGoal {
            name: "assert".to_string(),
            premise,
            equation,
            params,
            local_rules,
          };
          // println!("premise: {}, equation: {}", premise, equation);
          state.raw_goals.push(raw_goal);
        } else if assertion_type == "=" {
          let mut lhs = mangle_sexp(&assertion[2].list().unwrap()[1]);
          let mut rhs = mangle_sexp(&assertion[2].list().unwrap()[2]);
          lhs = fix_all_names(&lhs, &fixed_names);
          rhs = fix_all_names(&rhs, &fixed_names);

          let equation = RawEquation { lhs, rhs };
          let raw_goal = RawGoal {
            name: "assert".to_string(),
            premise,
            equation,
            params,
            local_rules,
          };
          state.raw_goals.push(raw_goal);
        } else {
          // wrap it in a = True
          let mut lhs = mangle_sexp(&assertion[2]);
          lhs = fix_all_names(&lhs, &fixed_names);
          // println!("lhs: {}", lhs);
          let rhs = mangle_sexp(&Sexp::String("True".to_string()));
          let equation = RawEquation { lhs, rhs };
          let raw_goal = RawGoal {
            name: "assert".to_string(),
            premise,
            equation,
            params,
            local_rules,
          };
          state.raw_goals.push(raw_goal);
        }
      }
      "check-sat" => {}
      _ => panic!("unknown declaration: {}", decl),
    }
  }

  Ok(state)
}

/// Wraps the entire contents in parentheses so that it can be read as one big Sexp
fn add_parantheses_to_file(filename: &str) -> std::io::Result<()> {
  let mut file = File::open(filename)?;
  let mut contents = String::new();
  file.read_to_string(&mut contents)?;

  if contents.as_str().chars().nth(1).unwrap() == '(' {
    // The file already has parentheses
    return Ok(());
  }

  // Wrap the contents in parentheses
  let modified_contents = format!("({})", contents);

  let mut file = File::create(filename)?;
  file.write_all(modified_contents.as_bytes())?;

  Ok(())
}

///A recursive function to parse smtlib function definition bodies
// The body can be either a match or a let
// If it's a match, we parse each case, and each case gives us a rewrite rule
fn parse_func_body(
  name: &str,
  body: &Vec<Sexp>,
  type_info: &HashMap<String, Sexp>,
  fixed_names: &HashMap<String, String>,
  arg_values: &mut IndexMap<String, Sexp>,
  lets: &mut HashMap<String, Sexp>,
  state: &mut ParserState,
) -> Result<(), SexpError> {
  let body_kind = body[0].string()?.as_str();

  // println!("parsing body: {:?}", body);
  match body_kind {
    "match" => {
      let var_matched = body[1].string()?;
      let mut matched_constructors: Vec<Symbol> = vec![];
      let mut cases = body[2].list()?.clone();
      let new_cases = expand_cases_in_match(cases, state, var_matched, type_info, fixed_names);
      // each list in cases is a case
      for case in new_cases {
        let case_list = case.list()?;
        let mut case_lhs = case_list[0].clone();
        let mut case_rhs = case_list[1].clone();
        // println!("case lhs: {:#?}", case_lhs);
        // println!("case rhs: {:#?}", case_rhs);
        match case_lhs {
          Sexp::String(ref s) => {
            // if the case lhs is a string, it's a constructor
            // we need to fix the name
            // case_lhs = Sexp::String(fixed_names.get(&s).unwrap_or(&s).to_string());
            arg_values.insert(var_matched.to_string(), case_lhs.clone());
            matched_constructors.push(Symbol::from(&mangle_name(s)));
          }
          Sexp::List(ref _l) => {
            // replace each variable by ?variable
            add_question_marks(&mut case_lhs, fixed_names);
            arg_values.insert(var_matched.to_string(), case_lhs.clone());
            matched_constructors.push(Symbol::from(&mangle_name(case_lhs.list()?[0].string()?)));
          }
          _ => panic!("unknown case lhs: {}", case_lhs),
        }
        // now we need to parse the rhs
        // the rhs could be a match, a let, or just a value
        match case_rhs {
          Sexp::String(ref _s) => {
            // if the rhs is a string, it's a constructor
            // we need to fix the name
            // println!("HERE");
            let lhs_vec = arg_values
              .iter()
              .map(|(_, v)| v.clone())
              .collect::<Vec<Sexp>>();

            // reset the arg values to the original
            for (k, v) in arg_values.iter_mut() {
              if k == var_matched {
                *v = Sexp::String("?".to_string() + k);
              }
            }
            panic_if_native_stuff(&mut case_rhs);
            fix_bools(&mut case_rhs);
            replace_lets(&mut case_rhs, lets);
            add_question_marks(&mut case_rhs, fixed_names);

            state.rules.push(make_rewrite_for_defn(
              &mangle_name(name),
              &Sexp::List(lhs_vec),
              &case_rhs,
            ));
          }
          Sexp::List(ref l) => {
            let hd = l[0].string()?;
            if hd == "match" || hd == "let" {
              let _ = parse_func_body(name, l, type_info, fixed_names, arg_values, lets, state);
            } else {
              // the first element should be a constructor (or function?) name, lookup the fixed name and fix it
              let lhs_vec = arg_values
                .iter()
                .map(|(_, v)| v.clone())
                .collect::<Vec<Sexp>>();
              // reset the arg values to the original
              for (k, v) in arg_values.iter_mut() {
                if k == var_matched {
                  *v = Sexp::String("?".to_string() + k);
                }
              }
              panic_if_native_stuff(&mut case_rhs);
              fix_bools(&mut case_rhs);
              replace_lets(&mut case_rhs, lets);
              add_question_marks(&mut case_rhs, fixed_names);
              state.rules.push(make_rewrite_for_defn(
                &mangle_name(name),
                &Sexp::List(lhs_vec),
                &case_rhs,
              ));
            }
          }
          _ => panic!("unknown case rhs: {}", case_rhs),
        }
      }
      return Ok(());
    }
    "let" => {
      // println!("let");
      // println!("{:#?}", body);
      let var_name = body[1].string()?;
      let var_value = body[2].clone();
      lets.insert(var_name.to_string(), var_value);
      let _ = parse_func_body(
        name,
        body[3].list().unwrap(),
        type_info,
        fixed_names,
        arg_values,
        lets,
        state,
      );
      return Ok(());
    }
    _ => {
      // anything else is probably a function or a value
      // if it's a function, we want to parse each argument and then apply the function
      Ok(())
    }
  }
}

/// Ensures that all names are valid, i.e.
/// - all variables and function names start with a lowercase letter
/// - all datatypes and constructors start with an uppercase letter
///
fn fix_all_names(sexpr: &Sexp, fixed_names: &HashMap<String, String>) -> Sexp {
  match sexpr {
    Sexp::String(s) => Sexp::String(fixed_names.get(s).unwrap_or(s).to_string()),
    Sexp::List(l) => Sexp::List(l.iter().map(|x| fix_all_names(x, fixed_names)).collect()),
    _ => sexpr.clone(),
  }
}

fn add_question_marks(sexp: &mut Sexp, fixed_names: &HashMap<String, String>) {
  // println!("fixed names: {:?}", fixed_names);
  match sexp {
    Sexp::String(ref s) if s.starts_with(char::is_alphanumeric) => {
      if !fixed_names.values().any(|y| y == s) {
        *sexp = Sexp::String("?".to_string() + s);
      } else {
        *sexp = Sexp::String(s.to_string());
      };
    }
    Sexp::List(ref mut l) => {
      for x in l {
        add_question_marks(x, fixed_names);
      }
    }
    _ => (),
  }
}

fn replace_lets(sexp: &mut Sexp, lets: &HashMap<String, Sexp>) {
  match sexp {
    Sexp::String(ref s) => {
      if let Some(x) = lets.get(s) {
        *sexp = x.clone();
      }
    }
    Sexp::List(ref mut l) => {
      for x in l {
        replace_lets(x, lets);
      }
    }
    _ => (),
  }
}

fn panic_if_native_stuff(sexp: &Sexp) {
  match sexp {
    Sexp::String(ref s) => {
      if !s.starts_with(char::is_alphabetic) && !s.starts_with("=") {
        panic!("we can't use native stuff: {}", s);
      }
    }
    Sexp::List(ref l) => {
      for x in l {
        panic_if_native_stuff(x);
      }
    }
    _ => (),
  }
}

fn fix_bools(sexp: &mut Sexp) {
  match sexp {
    Sexp::String(ref s) => {
      if s == "true" {
        *sexp = Sexp::String("True".to_string());
      } else if s == "false" {
        *sexp = Sexp::String("False".to_string());
      }
    }
    Sexp::List(ref mut l) => {
      for x in l {
        fix_bools(x);
      }
    }
    _ => (),
  }
}

fn replace_all_occurrences(sexp: &mut Sexp, old: &Sexp, new: &Sexp) {
  if sexp == old {
    *sexp = new.clone();
  } else {
    match sexp {
      Sexp::String(_) => (),
      Sexp::List(ref mut l) => {
        for x in l {
          replace_all_occurrences(x, old, new);
        }
      }
      _ => (),
    }
  }
}

fn expand_cases_in_match(
  cases: Vec<Sexp>,
  state: &ParserState,
  var_matched: &String,
  type_info: &HashMap<String, Sexp>,
  fixed_names: &HashMap<String, String>,
) -> Vec<Sexp> {
  let mut new_cases: Vec<Sexp> = vec![];
  let mut matched_constructors: Vec<Symbol> = vec![];
  for case in cases {
    // println!("case: {:?}", case);
    let case_list = case.list().unwrap();
    let mut case_lhs = case_list[0].clone();
    let mut case_rhs = case_list[1].clone();

    match case_lhs {
      Sexp::String(ref s) => {
        // if the case lhs is a string, it's a constructor
        // we need to fix the name
        // case_lhs = Sexp::String(fixed_names.get(&s).unwrap_or(&s).to_string());
        if s != "_" {
          new_cases.push(case.clone());
          matched_constructors.push(Symbol::from(&mangle_name(s)));
        } else {
          // for each unmatched constructor we need to add a rewrite rule. add this to cases directly
          // println!("matched constructors: {:?}", matched_constructors);
          let mut unmatched_constructors: Vec<Symbol> = vec![];
          // get the type of this variable first
          let type_info = type_info.get(var_matched).unwrap();
          // println!("type info: {}", type_info);
          let vtype = if type_info.is_string() {
            type_info.string().unwrap().to_string()
          } else {
            type_info.list().unwrap()[0].string().unwrap().to_string()
          };
          // println!("{}", type_info.list()?[1]);
          if let Some(x) = state.env.get(&Symbol::from(&mangle_name(&vtype))) {
            for c in &x.1 {
              if !matched_constructors.contains(c) {
                unmatched_constructors.push(c.clone());
              }
            }
          }
          // println!("unmatched constructors: {:?}", unmatched_constructors);
          // for each unmatched constructor, we need to add a case to cases
          for c in unmatched_constructors {
            // get the type of this constructor from the context
            let mut typ: Sexp;
            let mut case_lhs_tmp: Sexp;
            let mut case_rhs_tmp: Sexp;
            let x = state.context.get(&c).unwrap();
            typ = x.repr.clone();

            if typ.is_string() {
              case_lhs_tmp = Sexp::String(c.to_string());
              case_rhs_tmp = case_rhs.clone();
              replace_all_occurrences(
                &mut case_rhs_tmp,
                &Sexp::String(var_matched.to_string()),
                &case_lhs_tmp,
              );
            } else {
              // arrow type, so get the params and for each param create a fresh variable
              let params = typ.list().unwrap()[1].list().unwrap();
              // let mut arg_values_tmp = arg_values.clone();
              let mut lhsvec = vec![Sexp::String(c.to_string())];
              for i in 0..params.len() {
                let param_name = params[i].string().unwrap();
                let fresh_var =
                  Sexp::String("".to_string() + &param_name.to_ascii_lowercase() + &i.to_string());
                lhsvec.push(fresh_var.clone());
                // arg_values.insert(param_name.to_string(), fresh_var);
              }
              case_lhs_tmp = Sexp::List(lhsvec);
              case_rhs_tmp = case_rhs.clone();
              replace_all_occurrences(
                &mut case_rhs_tmp,
                &Sexp::String(var_matched.to_string()),
                &case_lhs_tmp,
              );
            }

            // now add this case to cases
            let case_tmp = vec![case_lhs_tmp, case_rhs_tmp];
            new_cases.push(Sexp::List(case_tmp));
          }
        }
      }
      Sexp::List(ref _l) => {
        // replace each variable by ?variable
        // add_question_marks(&mut case_lhs, fixed_names);
        // arg_values.insert(var_matched.to_string(), case_lhs.clone());
        matched_constructors.push(Symbol::from(&mangle_name(
          case_lhs.list().unwrap()[0].string().unwrap(),
        )));
        new_cases.push(case.clone());
      }
      _ => panic!("unknown case lhs: {}", case_lhs),
    }
  }
  new_cases
}
