use std::cmp::{Ordering, Reverse};
use std::collections::{HashMap, HashSet, VecDeque};
use itertools::Unique;
use crate::ast::sexp_size;
use crate::goal::Goal;
use crate::goal_graph::GraphProveStatus::{Subsumed, Unknown, Valid};

#[derive(PartialEq, Eq, Debug)]
pub enum GraphProveStatus {
    Unknown, Valid, Invalid, Subsumed
}

#[derive(Hash, Eq, PartialEq, Clone, Debug)]
pub struct GoalInfo {
    pub name: String,
    pub lemma_id: usize,
    pub full_exp: String,
    pub size: usize
}

impl GoalInfo {
    pub fn new(goal: &Goal, lemma_id: usize) -> Self{
        GoalInfo {
            name: goal.name.clone(),
            lemma_id,
            full_exp: goal.full_expr.to_string(),
            size: sexp_size(&goal.full_expr.lhs) + sexp_size(&goal.full_expr.rhs)
        }
    }
}

impl PartialOrd for GoalInfo {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Reverse(self.size).partial_cmp(&Reverse(other.size))
    }
}

impl Ord for GoalInfo {
    fn cmp(&self, other: &Self) -> Ordering {
        Reverse(self.size).cmp(&Reverse(other.size))
    }
}

pub struct GoalNode {
    info: GoalInfo,
    split_children: Option<Vec<GoalInfo>>,
    father: Option<GoalInfo>,
    pub status: GraphProveStatus,
    related_lemmas: HashSet<usize>
}

impl GoalNode {
    fn new(info: &GoalInfo, father: Option<&GoalInfo>) -> GoalNode {
        GoalNode {
            info: info.clone(),
            split_children: None,
            father: father.cloned(),
            status: GraphProveStatus::Unknown,
            related_lemmas: HashSet::default()
        }
    }
}

pub struct LemmaNode {
    pub goals: Vec<GoalInfo>,
    lemma_id: usize,
    status: GraphProveStatus
}

impl LemmaNode {
    fn new(root: &GoalInfo) -> LemmaNode {
        LemmaNode {
            goals: vec![root.clone()],
            lemma_id: root.lemma_id,
            status: GraphProveStatus::Unknown
        }
    }
}

#[derive(Default)]
pub struct GoalGraph {
    goal_index_map: HashMap<GoalInfo, GoalNode>,
    lemma_index_map: HashMap<usize, LemmaNode>
}

impl GoalGraph {
    fn get_goal_mut(&mut self, info: &GoalInfo) -> &mut GoalNode {
        self.goal_index_map.get_mut(info).unwrap()
    }
    fn get_lemma_mut(&mut self, id: usize) -> &mut LemmaNode {
        self.lemma_index_map.get_mut(&id).unwrap()
    }
    pub fn get_goal(&self, info: &GoalInfo) -> &GoalNode {
        self.goal_index_map.get(info).unwrap()
    }
    pub fn get_lemma(&self, id: usize) -> &LemmaNode {
        self.lemma_index_map.get(&id).unwrap()
    }

    fn new_goal(&mut self, info: &GoalInfo, father: Option<&GoalInfo>)  {
        self.goal_index_map.insert(
            info.clone(),
            GoalNode::new(info, father)
        );
    }
    pub fn new_lemma(&mut self, root: &GoalInfo) {
        self.new_goal(root, None);
        self.lemma_index_map.insert(
            root.lemma_id,
            LemmaNode::new(root)
        );
    }
    pub fn record_case_split(&mut self, from: &GoalInfo, to: &Vec<GoalInfo>) {
        self.get_goal_mut(from).split_children = Some(to.clone());
        for child in to.iter() {
            self.new_goal(child, Some(from));
            self.get_lemma_mut(from.lemma_id).goals.push(child.clone())
        }
    }
    pub fn record_related_lemmas(&mut self, from: &GoalInfo, lemmas: &Vec<GoalInfo>) {
        for lemma_root in lemmas.iter() {
            if !self.lemma_index_map.contains_key(&lemma_root.lemma_id) {
                self.new_lemma(lemma_root);
            }
        }
        let node = self.get_goal_mut(from);
        for lemma_root in lemmas.iter() {
            node.related_lemmas.insert(lemma_root.lemma_id);
        }
    }

    fn check_split_finished(&mut self, info: &GoalInfo) {
        let node = self.get_goal(info);
        if node.status != Unknown {return;}
        let father = node.father.clone();
        let children = node.split_children.clone().unwrap();

        if children.into_iter().all(|child| self.get_goal(&child).status == GraphProveStatus::Valid) {
            self.get_goal_mut(info).status = GraphProveStatus::Valid;
            if father.is_some() {
                self.check_split_finished(&father.unwrap());
            }
        }
    }

    pub fn record_node_status(&mut self, node: &GoalInfo, status: GraphProveStatus) {
        assert!(status == GraphProveStatus::Valid || status == GraphProveStatus::Invalid);

        if status == GraphProveStatus::Invalid {
            self.get_lemma_mut(node.lemma_id).status = GraphProveStatus::Invalid;
            return;
        }

        let goal_node = self.get_goal_mut(node);
        if goal_node.status != Unknown {return;}
        goal_node.status = status;

        let mut queue = VecDeque::new();
        queue.push_back(node.clone());

        while let Some(info) = queue.pop_front() {
            if let Some(children) = self.get_goal(&info).split_children.clone() {
                for child in children {
                    self.get_goal_mut(&child).status = Subsumed;
                    queue.push_back(child);
                }
            }
        }

        if let Some(father) = self.get_goal(node).father.clone() {
            self.check_split_finished(&father);
        }
    }

    pub fn send_subsumed_check(&self) -> Vec<usize> {
        self.lemma_index_map.iter().filter_map(
            |(id, node)| {
                if node.status == Unknown {Some(*id)} else {None}
            }
        ).collect()
    }

    pub fn receive_subsumed_check(&mut self, subsumed_lemmas: Vec<usize>) {
        for lemma_id in subsumed_lemmas {
            self.get_lemma_mut(lemma_id).status = Subsumed;
        }
    }

    fn get_working_goals(&self) -> (Vec<GoalInfo>, Vec<GoalInfo>) {
        let mut visited_lemmas = HashSet::new();
        let mut queue = VecDeque::new();
        let mut frontier_goals = Vec::new();
        let mut waiting_goals = Vec::new();
        queue.push_back(self.get_lemma(0).goals[0].clone());
        visited_lemmas.insert(0usize);

        while let Some(current_goal) = queue.pop_front() {
            let node = self.get_goal(&current_goal);
            // println!("goal [{}] {} {:?} {}", node.info.lemma_id, node.info.full_exp, node.status, node.split_children.is_none());
            if node.status != Unknown {continue;}
            for related_lemma in node.related_lemmas.iter() {
                let lemma_node = self.get_lemma(*related_lemma);
                if lemma_node.status != Unknown || visited_lemmas.contains(related_lemma) {
                    continue;
                }
                visited_lemmas.insert(*related_lemma);
                queue.push_back(lemma_node.goals[0].clone());
            }
            if node.split_children.is_none() {
                frontier_goals.push(current_goal);
            } else {
                waiting_goals.push(current_goal);
                for child in node.split_children.as_ref().unwrap() {
                    queue.push_back(child.clone())
                }
            }
        }
        (waiting_goals, frontier_goals)
    }

    pub fn get_frontier_goals(&self) -> Vec<GoalInfo> {
        self.get_working_goals().1
    }

    pub fn get_waiting_goals(&self) -> Vec<GoalInfo> {
        self.get_working_goals().0
    }

    pub fn is_lemma_proved(&self, lemma_id: usize) -> bool {
        let root_info = &self.get_lemma(lemma_id).goals[0];
        self.get_goal(root_info).status == Valid
        /*let mut queue = VecDeque::new();
        queue.push_back(&self.get_lemma(lemma_id).goals[0]);

        while let Some(info) = queue.pop_front() {
            let goal_node = self.get_goal(info);
            if goal_node.status == Unknown {
                if goal_node.split_children.is_none() {return false;}
                for child in goal_node.split_children.as_ref().unwrap() {
                    queue.push_back(child);
                }
            } else if goal_node.status == GraphProveStatus::Valid {
                continue;
            } else {
                return false;
            }
        }
        return true;*/
    }

    pub fn set_lemma_res(&mut self, lemma_id: usize, status: GraphProveStatus) {
        self.get_lemma_mut(lemma_id).status = status;
    }
}