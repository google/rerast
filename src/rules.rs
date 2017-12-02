use syntax::ast::NodeId;
use syntax::symbol::Symbol;
use std::vec::Vec;
use std::collections::{HashMap, HashSet};
use rustc::hir;
use rule_finder::StartMatch;

#[derive(Debug)]
pub(crate) struct Rule<'gcx, T: StartMatch + 'gcx> {
    pub(crate) search: &'gcx T,
    pub(crate) replace: &'gcx T,
    // The method in which the rule is defined.
    pub(crate) body_id: hir::BodyId,
    // Maps from the names of declared variables (which must be unique within the search pattern) to
    // their NodeId. This is used to pair up variables in the search pattern with their counterparts
    // in the replacement pattern. This is necessary since as far as rustc is concerned, they're
    // completely unrelated definitions. It isn't needed for expression placeholders since they're
    // declared as arguments to the function, so the search and replace pattern can both reference
    // the same placeholder variable.
    pub(crate) declared_name_node_ids: HashMap<Symbol, NodeId>,
    // IDs of the arguments to the function in which the rule was declared. When references to these
    // NodeIds are encountered in the search pattern, they should be treated as placeholders.
    pub(crate) placeholder_ids: HashSet<NodeId>,
}

#[derive(Debug)]
pub(crate) struct Rules<'gcx> {
    pub(crate) expr_rules: Vec<Rule<'gcx, hir::Expr>>,
    pub(crate) pattern_rules: Vec<Rule<'gcx, hir::Pat>>,
    pub(crate) type_rules: Vec<Rule<'gcx, hir::Ty>>,
    pub(crate) trait_ref_rules: Vec<Rule<'gcx, hir::TraitRef>>,
}

impl<'gcx> Rules<'gcx> {
    pub(crate) fn new() -> Rules<'gcx> {
        Rules {
            expr_rules: Vec::new(),
            pattern_rules: Vec::new(),
            type_rules: Vec::new(),
            trait_ref_rules: Vec::new(),
        }
    }

    pub(crate) fn len(&self) -> usize {
        self.expr_rules.len() + self.pattern_rules.len() + self.type_rules.len()
            + self.trait_ref_rules.len()
    }
}
