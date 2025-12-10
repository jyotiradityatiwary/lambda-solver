use std::collections::HashMap;

use crate::{ExpressionTree, Rule};

/// Hold aliases for [crate::ExpressionTreeBuilder]
pub struct AliasStore {
    name_to_tree: HashMap<String, ExpressionTree>,
}

pub const DEFAULT_ALIASES: [(&str, &str); 6] = [
    // Logic
    ("TRUE", "λx.λy.x"),
    ("FALSE", "λx.λy.y"),
    ("AND", "λp.λq.p q p"),
    ("OR", "λp.λq.p p q"),
    ("NOT", "λp.p FALSE TRUE"),
    ("IFTHENELSE", "λp.λa.λb.p a b"),
];

impl AliasStore {
    pub fn new() -> Self {
        Self {
            name_to_tree: HashMap::new(),
        }
    }

    pub fn from_pair_iterator<'a>(
        iterator: impl Iterator<Item = &'a (&'a str, &'a str)>,
    ) -> Result<Self, pest::error::Error<Rule>> {
        let mut aliases = Self::new();
        for &(k, v) in iterator {
            let tree = ExpressionTree::from_line_with_aliases(v, &aliases)?;
            aliases.set(String::from(k), tree);
        }
        Ok(aliases)
    }

    /// Get an instance with [DEFAULT_ALIASES]
    ///
    /// ```rust
    /// use lambda_solver::AliasStore;
    ///
    /// let aliases = AliasStore::with_defaults();
    /// ```
    pub fn with_defaults() -> Self {
        Self::from_pair_iterator(DEFAULT_ALIASES.iter()).expect("Failed to parse default aliases")
    }

    pub fn set(&mut self, name: String, expression: ExpressionTree) -> Option<ExpressionTree> {
        self.name_to_tree.insert(name, expression)
    }

    pub fn delete(&mut self, name: &str) -> Option<ExpressionTree> {
        self.name_to_tree.remove(name)
    }

    pub fn get(&self, name: &str) -> Option<&ExpressionTree> {
        self.name_to_tree.get(name)
    }

    pub fn reverse_lookup(&self, tree: &ExpressionTree) -> impl Iterator<Item = &String> {
        self.name_to_tree
            .iter()
            .filter_map(move |(name, value)| if value == tree { Some(name) } else { None })
    }
}
