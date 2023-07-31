use egg::*;
use symbolic_expressions::Sexp;
use std::collections::HashMap;
use itertools::{Itertools, EitherOrBoth};

use crate::ast::{Type, Expr};
use crate::goal::{ProofState, ProofTerm};
use crate::config::CONFIG;

/// Constants from (Liquid)Haskell
const EQUALS: &str = "=";
const LH_EQUALS: &str = "==.";
const USING_LEMMA: &str = "?";
const AND_THEN: &str = "***";
const QED: &str = "QED";
const TAB_WIDTH: usize = 2;
const PROOF: &str = "Proof";

const LH_TYPE_BEGIN: &str = "{-@";
const LH_TYPE_END: &str = "@-}";
const COMMENT: &str = "--";
const HAS_TYPE: &str = "::";

/// Constants from cyclegg
const APPLY: &str = "$";
const ARROW: &str = "->";
const FORWARD_ARROW: &str = "=>";
const BACKWARD_ARROW: &str = "<=";
const IH_EQUALITY: &str = "ih-equality-";

/// A rewrite can be forward or backward, this specifies which direction it
/// goes.
enum RwDirection {
    Forward,
    Backward
}

// TODO: Add functions and data declarations
pub fn explain_top(goal: String, state: &mut ProofState, lhs: Expr, rhs: Expr, top_level_vars: HashMap<Symbol, Type>) -> String {
    let mut str_explanation = String::new();
    // (arg name, arg type)
    let args: Vec<(String, String)> =
        top_level_vars.into_iter().map(|(symbol, ty)| (symbol.to_string(), convert_ty(ty.repr))).collect();

    // LH type
    str_explanation.push_str(LH_TYPE_BEGIN);
    str_explanation.push_str(&goal);
    str_explanation.push_str(HAS_TYPE);
    // Join with arrows each of the arguments
    let args_str = args.iter()
                       .map(|(arg_name, arg_ty)| format!("{}: {}", arg_name, arg_ty))
                       .collect::<Vec<String>>().join(ARROW);
    str_explanation.push_str(&args_str);
    // Refined type of the proof
    let proof_str = format!("{{ {} = {} }}", lhs, rhs);
    str_explanation.push_str(ARROW);
    str_explanation.push_str(&proof_str);
    str_explanation.push_str(LH_TYPE_END);
    str_explanation.push('\n');

    // Haskell type
    str_explanation.push_str(&goal);
    str_explanation.push_str(HAS_TYPE);
    // Same deal as with the LH type but now we just include the types
    let arg_tys_str = args.iter()
                       .map(|(_, arg_ty)| arg_ty.to_string())
                       .collect::<Vec<String>>().join(ARROW);
    str_explanation.push_str(&arg_tys_str);
    str_explanation.push_str(ARROW);
    // This time we just use the Proof type
    str_explanation.push_str(&PROOF);
    str_explanation.push('\n');

    // Haskell function definition
    str_explanation.push_str(&goal);
    str_explanation.push(' ');
    // Now we include just the arguments and separate by spaces
    let arg_names_str = args.iter()
                       .map(|(arg_name, _)| arg_name.to_string())
                       .collect::<Vec<String>>().join(" ");
    str_explanation.push_str(&arg_names_str);
    str_explanation.push_str(&EQUALS);
    str_explanation.push('\n');

    // Finally, we can do the proof explanation
    let proof_exp = explain_proof(1, goal.clone(), state, &goal);
    str_explanation.push_str(&proof_exp);
    str_explanation
}

fn explain_proof(depth: usize, goal: String, state: &mut ProofState, top_goal_name: &String) -> String {
    // If it's not in the proof tree, it must be a leaf.
    if !state.proof.contains_key(&goal) {
        // The explanation should be in solved_goal_explanations. If it isn't,
        // we must be trying to explain an incomplete proof which is an error.
        return explain_goal(depth, state.solved_goal_explanations.get_mut(&goal).unwrap(), top_goal_name);
    }
    // Need to clone to avoid borrowing... unfortunately this is all because we need
    // a mutable reference to the explanations for some annoying reason
    let proof_term = state.proof.get(&goal).unwrap().clone();
    let mut str_explanation = String::new();
    let mut proof_depth = depth;
    let mut case_depth = depth + 1;
    if let ProofTerm::ITESplit(var, condition, _) = &proof_term {
        add_indentation(&mut str_explanation, proof_depth);
        str_explanation.push_str(&format!("let {} = {} in", var, condition));
        str_explanation.push('\n');
        case_depth += 1;
        proof_depth += 1;
    };
    match &proof_term {
        ProofTerm::CaseSplit(var, cases) | ProofTerm::ITESplit(var, _, cases) => {
            add_indentation(&mut str_explanation, proof_depth);
            str_explanation.push_str(&format!("case {} of", var));
            str_explanation.push('\n');
            for (case_constr, case_goal) in cases {
                add_indentation(&mut str_explanation, case_depth);
                str_explanation.push_str(&format!("{} ->", case_constr));
                str_explanation.push('\n');
                // Recursively explain the proof
                str_explanation.push_str(&explain_proof(case_depth + 1, case_goal.clone(), state, &top_goal_name));
            }
            str_explanation
        }
    }
}

fn explain_goal(depth: usize, explanation: &mut Explanation<SymbolLang>, top_goal_name: &String) -> String {
    // TODO: Add lemma justification with USING_LEMMA
    let mut str_explanation: String = String::new();
    let flat_terms = explanation.make_flat_explanation();
    let next_flat_term_iter = flat_terms.iter().skip(1);
    let flat_term_and_next = flat_terms.into_iter().zip_longest(next_flat_term_iter);
    // Render each of the terms in the explanation
    let flat_strings: Vec<String> = flat_term_and_next.map(|flat_term_and_next| {
        let (flat_term, next_term_opt) = match flat_term_and_next {
            EitherOrBoth::Both(flat_term, next_term) => (flat_term, Some(next_term)),
            EitherOrBoth::Left(flat_term) => (flat_term, None),
            EitherOrBoth::Right(_) => unreachable!("next_flat_term_iter somehow is longer than flat_term_iter"),
        };
        let mut str = String::new();
        if CONFIG.verbose_proofs {
            if let Some(rule_name) = &extract_rule_name(flat_term) {
                add_indentation(&mut str, depth);
                str.push_str(COMMENT);
                str.push(' ');
                str.push_str(&rule_name);
                str.push('\n')
            }
        }
        add_indentation(&mut str, depth);
        str.push_str(&flat_term_to_sexp(flat_term).to_string());
        if let Some(next_term) = next_term_opt {
            if let Some(rule_name) = &extract_rule_name(next_term) {
                if rule_name.starts_with(IH_EQUALITY) {
                    let args = extract_ih_arguments(rule_name);
                    add_indentation(&mut str, depth);
                    str.push_str(USING_LEMMA);
                    str.push(' ');
                    str.push_str(top_goal_name);
                    str.push(' ');
                    str.push_str(&args.join(" "));
                }
            }
        }
        str
    }).collect();
    // Construct a joiner that intersperses newlines and properly spaced
    // LH_EQUALS operators.
    let mut joiner = "\n".to_string();
    add_indentation(&mut joiner, depth);
    joiner.push_str(LH_EQUALS);
    joiner.push('\n');

    // The bulk of our proof is the individual terms joined by LH_EQUALS.
    str_explanation.push_str(&flat_strings.join(&joiner));
    str_explanation.push('\n');
    add_indentation(&mut str_explanation, depth);
    // This is just required by LH to finish it.
    str_explanation.push_str(AND_THEN);
    str_explanation.push('\n');
    add_indentation(&mut str_explanation, depth);
    str_explanation.push_str(QED);
    str_explanation.push('\n');
    str_explanation
}

fn add_indentation(s: &mut String, depth: usize) {
    s.push_str(&" ".repeat(depth * TAB_WIDTH));
}

fn flat_term_to_sexp(flat_term: &FlatTerm<SymbolLang>) -> Sexp {
    // This is a leaf
    if flat_term.node.children.is_empty() {
        convert_op(flat_term.node.op)
    // This is an interior node
    } else {
        let mut child_sexps: Vec<Sexp> = vec!(convert_op(flat_term.node.op));
        for child in &flat_term.children {
            child_sexps.push(flat_term_to_sexp(child));
        }
        Sexp::List(child_sexps)
    }
}

// TODO: return a custom struct indicating what direction it is and
// use that to determine where to put the lemma invocation.
fn extract_rule_name(flat_term: &FlatTerm<SymbolLang>) -> Option<String> {
    let forward = flat_term.forward_rule.map(|rule| rule.to_string() + " " + FORWARD_ARROW);
    let backward = flat_term.backward_rule.map(|rule| BACKWARD_ARROW.to_string() + " " + &rule.to_string());
    let rule_from_child = flat_term.children.iter().map(extract_rule_name).collect();
    forward.or(backward).or(rule_from_child)
}

fn convert_op(op: Symbol) -> Sexp {
    let op_str = op.to_string();
    // Special case for converting `$`, which is used internally in cyclegg for
    // partial application, to the corresponding prefix operator `($)` in
    // Haskell.
    if op_str == APPLY {
        // This is a really ugly hack to wrap `$` in parens.
        Sexp::List(vec!(Sexp::String(op_str)))
    } else {
        Sexp::String(op_str)
    }
}

/// Basically the same as ty.repr.to_string() but we make arrows infix
fn convert_ty(ty: Sexp) -> String {
    match ty {
        Sexp::String(str) => str,
        Sexp::List(children) => {
            // Handle the arrow case, making it infix
            if children.len() == 3 {
                if let Sexp::String(op) = &children[0] {
                    if op == &ARROW {
                        // FIXME: remove clones
                        if let Sexp::List(args) = children[1].clone() {
                            let mut arg_tys: Vec<String> = args.into_iter().map(convert_ty).collect();
                            let return_ty = convert_ty(children[2].clone());
                            arg_tys.push(return_ty);
                            return format!("({})", arg_tys.join(ARROW));
                        }
                    }
                }
            }
            let converted: String = children.into_iter().map(convert_ty).collect::<Vec<String>>().join(" ");
            format!("({})", converted)
        },
        Sexp::Empty => String::new(),
    }
}

fn extract_ih_arguments(rule_name: &String) -> Vec<String> {
    rule_name.strip_prefix(IH_EQUALITY).unwrap().split(',').into_iter().map(|pair|{
        println!("{}", pair);
        let args: Vec<&str> = pair.split('=').into_iter().collect();
        // This should just be x=(Constructor c1 c2 c3)
        assert_eq!(args.len(), 2);
        args[1].to_string()
    }).collect()
}

// TODO: Lemma generation.
// How to do lemmas:
// 1.
// 2. Anti-unficiation between terms to figure out:
//   1. What lemma was used?
//   2. What were its arguments? Specifically, for each variable
//      used in the lemma x, what term t is x mapped to in this invocation?
// 3. (If the lemma is the base induction hypothesis, simply call
//    it. -- this is probably unnecessary and is generalized by the following method).
//    Otherwise, look up the explanation for how its LHS relates to the goal
//    LHS and its RHS relates to the goal RHS. Use the argument map to instantiate
//    the explanations with concrete arguments. Inline the lemma as follows:
//    (LHS ==. proof of LHS -> goal LHS ? inductionHypothesis ==. proof of goal RHS -> RHS ==. RHS)
//    it might require some thinking to determine the relationship between the lemma's arguments
//    and the arguments to the induction hypothesis.
