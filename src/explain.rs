use egg::*;
use indexmap::IndexMap;
use std::collections::HashMap;
use symbolic_expressions::Sexp;

use crate::ast::{Expr, Type};
use crate::goal::{ProofState, ProofTerm};

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
const HAS_TYPE: &str = "::";

/// Constants from cyclegg
const APPLY: &str = "$";
const ARROW: &str = "->";

const LEMMA: &str = "lemma-";

/// A rewrite can be forward or backward, this specifies which direction it
/// goes.
enum RwDirection {
    Forward,
    Backward,
}

// TODO: Add functions and data declarations
pub fn explain_top(
    goal: String,
    state: &mut ProofState,
    lhs: Expr,
    rhs: Expr,
    top_level_vars: HashMap<Symbol, Type>,
) -> String {
    let mut str_explanation = String::new();
    // (arg name, arg type)
    let args: Vec<(String, String)> = top_level_vars
        .into_iter()
        .map(|(symbol, ty)| (symbol.to_string(), convert_ty(ty.repr)))
        .collect();

    // LH type
    str_explanation.push_str(LH_TYPE_BEGIN);
    str_explanation.push_str(&goal);
    str_explanation.push_str(HAS_TYPE);
    // Join with arrows each of the arguments
    let args_str = args
        .iter()
        .map(|(arg_name, arg_ty)| format!("{}: {}", arg_name, arg_ty))
        .collect::<Vec<String>>()
        .join(ARROW);
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
    let arg_tys_str = args
        .iter()
        .map(|(_, arg_ty)| arg_ty.to_string())
        .collect::<Vec<String>>()
        .join(ARROW);
    str_explanation.push_str(&arg_tys_str);
    str_explanation.push_str(ARROW);
    // This time we just use the Proof type
    str_explanation.push_str(&PROOF);
    str_explanation.push('\n');

    // Haskell function definition
    str_explanation.push_str(&goal);
    str_explanation.push(' ');
    // Now we include just the arguments and separate by spaces
    let arg_names_str = args
        .iter()
        .map(|(arg_name, _)| arg_name.to_string())
        .collect::<Vec<String>>()
        .join(" ");
    str_explanation.push_str(&arg_names_str);
    str_explanation.push_str(&EQUALS);
    str_explanation.push('\n');

    // Finally, we can do the proof explanation
    let proof_exp = explain_proof(1, goal, state);
    str_explanation.push_str(&proof_exp);
    str_explanation
}

fn explain_proof(depth: usize, goal: String, state: &mut ProofState) -> String {
    // If it's not in the proof tree, it must be a leaf.
    if !state.proof.contains_key(&goal) {
        // The explanation should be in solved_goal_explanations. If it isn't,
        // we must be trying to explain an incomplete proof which is an error.
        return explain_goal(
            depth,
            state.solved_goal_explanations.get_mut(&goal).unwrap(),
        );
    }
    // Need to clone to avoid borrowing... unfortunately this is all because we need
    // a mutable reference to the explanations for some annoying reason
    match state.proof.get(&goal).unwrap().clone() {
        ProofTerm::CaseSplit(var, cases) => {
            let mut str_explanation = String::new();
            add_indentation(&mut str_explanation, depth);
            str_explanation.push_str(&format!("case {} of", var));
            str_explanation.push('\n');
            let case_depth = depth + 1;
            for (case_constr, case_goal) in cases {
                add_indentation(&mut str_explanation, case_depth);
                str_explanation.push_str(&format!("{} ->", case_constr));
                str_explanation.push('\n');
                // Recursively explain the proof
                str_explanation.push_str(&explain_proof(
                    case_depth + 1,
                    case_goal.to_string(),
                    state,
                ));
            }
            str_explanation
        }
    }
}

fn explain_goal(depth: usize, explanation: &mut Explanation<SymbolLang>) -> String {
    let mut str_explanation: String = String::new();
    let flat_terms = explanation.make_flat_explanation();

    // Render each of the terms in the explanation
    let flat_strings: &mut Vec<String> = &mut vec![];

    let mut flat_terms_iter = flat_terms.iter().peekable();

    while let Some(curr_term) = flat_terms_iter.next() {
        let mut lemma_str = String::new();
        let rewrite_pos: &mut Vec<i32> = &mut vec![];

        // if there is a next term, there must be a rewrite from this term to the next
        if let Some(next_term) = flat_terms_iter.peek() {
            let trace = find_rewritten_term(rewrite_pos, next_term).unwrap();
            let rewritten_to = get_flat_term_from_trace(&trace, &next_term);
            let rewritten_from = get_flat_term_from_trace(&trace, &curr_term);

            let rwdir = if rewritten_to.backward_rule.is_some() {
                RwDirection::Backward
            } else {
                RwDirection::Forward
            };

            let rule = rewritten_to
                .backward_rule
                .or(rewritten_to.forward_rule)
                .unwrap();

            let rule_str = rule.to_string();
            if rule_str.starts_with(LEMMA) {
                let lemma: Vec<&str> = rule_str.split(LEMMA).collect::<Vec<&str>>()[1]
                    .split("=")
                    .collect();

                let mut lhsmap =
                    map_variables(lemma[0], &flat_term_to_sexp(&rewritten_from).to_string());
                let rhsmap = map_variables(lemma[1], &flat_term_to_sexp(&rewritten_to).to_string());

                match rwdir {
                    RwDirection::Backward => {
                        assert!(lhsmap
                            .iter()
                            .all(|(key, value)| rhsmap.get(key) == Some(value)))
                    }
                    RwDirection::Forward => {
                        assert!(rhsmap
                            .iter()
                            .all(|(key, value)| lhsmap.get(key) == Some(value)))
                    }
                }

                // take the union of both maps
                lhsmap.extend(rhsmap);

                lemma_str.push('\n');
                add_indentation(&mut lemma_str, depth);
                lemma_str.push_str(USING_LEMMA);
                lemma_str.push(' ');
                lemma_str.push_str(&rule_str);

                // add the lemma arguments
                for (_, value) in lhsmap {
                    lemma_str.push_str(&format!(" {}", value));
                }
            }
        }

        let mut str = String::new();
        add_indentation(&mut str, depth);
        str.push_str(&flat_term_to_sexp(curr_term).to_string());
        str.push_str(&lemma_str);
        flat_strings.push(str);
    }

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
        let mut child_sexps: Vec<Sexp> = vec![convert_op(flat_term.node.op)];
        for child in &flat_term.children {
            child_sexps.push(flat_term_to_sexp(child));
        }
        Sexp::List(child_sexps)
    }
}

fn convert_op(op: Symbol) -> Sexp {
    let op_str = op.to_string();
    // Special case for converting `$`, which is used internally in cyclegg for
    // partial application, to the corresponding prefix operator `($)` in
    // Haskell.
    if op_str == APPLY {
        // This is a really ugly hack to wrap `$` in parens.
        Sexp::List(vec![Sexp::String(op_str)])
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
                            let mut arg_tys: Vec<String> =
                                args.into_iter().map(convert_ty).collect();
                            let return_ty = convert_ty(children[2].clone());
                            arg_tys.push(return_ty);
                            return format!("({})", arg_tys.join(ARROW));
                        }
                    }
                }
            }
            let converted: String = children
                .into_iter()
                .map(convert_ty)
                .collect::<Vec<String>>()
                .join(" ");
            format!("({})", converted)
        }
        Sexp::Empty => String::new(),
    }
}

/// Given a FlatTerm, locates the subterm that was rewritten by looking for a backward / forward rule
/// and returns a trace of indices to that term.
fn find_rewritten_term(trace: &mut Vec<i32>, flat_term: &FlatTerm<SymbolLang>) -> Option<Vec<i32>> {
    if flat_term.backward_rule.is_some() || flat_term.forward_rule.is_some() {
        Some(trace.to_vec())
    } else {
        for (i, child) in flat_term.children.iter().enumerate() {
            if child.has_rewrite_backward() || child.has_rewrite_forward() {
                trace.push(i as i32);
                return find_rewritten_term(trace, child);
            }
        }
        None
    }
}

fn get_flat_term_from_trace(
    trace: &Vec<i32>,
    flat_term: &FlatTerm<SymbolLang>,
) -> FlatTerm<SymbolLang> {
    let mut current_flat_term = flat_term;
    for i in trace {
        current_flat_term = &current_flat_term.children[*i as usize];
    }
    current_flat_term.clone()
}

/// Given two strings, s1 and s2, where s1 is a pattern and s2 is a string
/// returns a map from the variables in s1 to the corresponding substrings in s2.
fn map_variables(s1: &str, s2: &str) -> IndexMap<String, String> {
    let mut result_map = IndexMap::new();
    // let mut stack = Vec::new();
    let mut s1_iter = s1.chars().peekable();
    let mut s2_iter = s2.chars().peekable();

    while let Some(&c1) = s1_iter.peek() {
        let c2 = s2_iter.peek().unwrap();
        match c1 {
            '?' => {
                let mut temp_str = String::new();
                let mut nested_paren_count = 0;

                while let Some(&next_char) = s2_iter.peek() {
                    match next_char {
                        '(' if nested_paren_count > 0 => {
                            temp_str.push(next_char);
                            nested_paren_count += 1;
                        }
                        '(' => nested_paren_count += 1,
                        ')' if nested_paren_count > 1 => {
                            temp_str.push(next_char);
                            nested_paren_count -= 1;
                        }
                        ')' => break,
                        ' ' if nested_paren_count == 0 => break,
                        _ => temp_str.push(next_char),
                    }
                    s2_iter.next();
                }

                if !temp_str.is_empty() {
                    let mut extracted_str = String::new();
                    s1_iter.next();
                    while let Some(&next_char) = s1_iter.peek() {
                        if next_char.is_whitespace() || next_char == ')' {
                            break;
                        }
                        extracted_str.push(next_char);
                        s1_iter.next();
                    }

                    s1_iter.next();

                    result_map.insert(extracted_str, temp_str);
                }
            }
            _ if c1 == *c2 => {
                s1_iter.next();
            }
            _ => {
                break;
            }
        }
        s2_iter.next();
    }

    result_map
}
