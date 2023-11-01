use std::collections::VecDeque;

use egg::*;
use log::warn;

fn cartesian_product_helper<T: Clone>(
  vector: &[Vec<T>],
  index: usize,
  current_combination: Vec<T>,
  result: &mut Vec<Vec<T>>,
) {
  if index == vector.len() {
    result.push(current_combination);
  } else {
    for elem in &vector[index] {
      let mut new_combination = current_combination.clone();
      new_combination.push(elem.clone());
      cartesian_product_helper(vector, index + 1, new_combination, result);
    }
  }
}

/// Given a vector of vectors, generates the "cartesian product" of all the vectors.
/// TODO: figure out how to use multi_cartesian_product from itertools instead of writing our own
pub fn cartesian_product<T: Clone>(vector: &[Vec<T>]) -> Vec<Vec<T>> {
  let mut result = Vec::new();
  cartesian_product_helper(vector, 0, Vec::new(), &mut result);
  result
}

/// prints all the expressions in the eclass with the given id
pub fn print_expressions_in_eclass<L: egg::Language + std::fmt::Display, N: egg::Analysis<L>>(
  egraph: &EGraph<L, N>,
  id: Id,
) {
  let extractor = egg::Extractor::new(&egraph, AstSize);

  for node in egraph[id].nodes.iter() {
    let child_rec_exprs: String = node
      .children()
      .iter()
      .map(|child_id| {
        let (_, best_rec_expr) = extractor.find_best(*child_id);
        best_rec_expr.to_string()
      })
      .collect::<Vec<String>>()
      .join(" ");
    if child_rec_exprs.is_empty() {
      println!("({})", node);
    } else {
      println!("({} {})", node, child_rec_exprs);
    }
  }
}

#[derive(Clone, Debug)]
pub struct ChainSet<T>
where T: PartialOrd + PartialEq + Clone {
  pub chains: Vec<Chain<T>>
}

impl<T> Default for ChainSet<T>
where T: PartialOrd + PartialEq + Clone {
    fn default() -> Self {
        Self { chains: Default::default() }
    }
}

/// Chainsets contain (usually) disjoint chains (total orders) in the partial
/// order.
///
/// Ideally we would have a proper partial order data structure, but for now we
/// fake this by duplicating an element in the rare case that it is comparable
/// with multiple chains.
impl<T> ChainSet<T>
where T: PartialOrd + PartialEq + Clone {
  pub fn new() -> Self {
    ChainSet {
      chains: vec!(),
    }
  }

  pub fn insert(&mut self, elem: T) {
    let mut num_inserts = 0;
    for chain in self.chains.iter_mut() {
      if chain.first().partial_cmp(&elem).is_some() {
        chain.insert(elem.clone());
        num_inserts += 1;
      }
    }
    if num_inserts == 0 {
      self.chains.push(Chain::new(elem))
    } else if num_inserts > 1 {
      warn!("Inserted an element {} times in the chain set.", num_inserts);
    }
  }

  pub fn contains(&self, elem: &T) -> bool {
    self.chains.iter().any(|chain| chain.contains(elem))
  }

  pub fn contains_leq(&self, elem: &T) -> bool {
    self.chains.iter().any(|chain| chain.contains_leq(elem))
  }

  pub fn take_up_to(&mut self, chain_index: usize, chain_elem_index: usize) {
    self.chains[chain_index].chain.truncate(chain_elem_index);
    if self.chains[chain_index].chain.is_empty() {
      self.chains.remove(chain_index);
    }
  }

  pub fn drop_from(&mut self, chain_index: usize, chain_elem_index: usize) {
    let mut new_chain = self.chains[chain_index].chain.split_off(chain_elem_index);
    new_chain.pop_front();

    if new_chain.is_empty() {
      self.chains.remove(chain_index);
    } else {
      self.chains[chain_index] = Chain { chain: new_chain }
    }
  }
}

impl<T> Extend<T> for ChainSet<T>
where T: PartialOrd + PartialEq + Clone {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
      for i in iter {
        self.insert(i);
      }
    }
}

/// Chains are nonempty sets in sorted order
#[derive(Clone, Debug)]
pub struct Chain<T>
where T: PartialOrd + PartialEq {
  pub chain: VecDeque<T>
}

impl<T> Default for Chain<T>
where T: PartialOrd + PartialEq {
    fn default() -> Self {
        Self { chain: Default::default() }
    }
}

impl<T> Chain<T>
where T: PartialOrd + PartialEq {
  pub fn new(elem: T) -> Self {
    Self {
      chain: vec!(elem).into(),
    }
  }
  pub fn insert(&mut self, elem: T) -> bool {
    for (i, self_elem) in self.chain.iter().enumerate() {
      match elem.partial_cmp(self_elem) {
        // Incomparable or already present
        None | Some(std::cmp::Ordering::Equal) => {
          return false;
        }
        Some(std::cmp::Ordering::Less) => {
          self.chain.insert(i, elem);
          return true;
        }
        Some(std::cmp::Ordering::Greater) => {}
      }
    }
    // It must be the greatest element
    self.chain.push_back(elem);
    true
  }

  pub fn contains(&self, elem: &T) -> bool {
    for e in self.chain.iter() {
      match e.partial_cmp(elem) {
        None => {
          return false;
        }
        Some(std::cmp::Ordering::Equal) => {
          return true;
        }
        _ => {}
      }
    }
    false
  }

  pub fn contains_leq(&self, elem: &T) -> bool {
    match self.first().partial_cmp(elem) {
      Some(std::cmp::Ordering::Less) | Some(std::cmp::Ordering::Equal) => {
        true
      }
      _ => false,
    }
  }

  pub fn first(&self) -> &T {
    &self.chain.front().unwrap()
  }

}
