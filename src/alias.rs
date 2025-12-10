use std::collections::HashMap;

use crate::ExpressionTree;

/// Hold aliases for [crate::ExpressionTreeBuilder]
pub struct AliasStore {
    name_to_tree: HashMap<String, ExpressionTree>,
}

pub const DEFAULT_ALIASES: [(&str, &str); 2] = [("TRUE", "λx.λy.x"), ("FALSE", "λx.λy.y")];

impl AliasStore {
    pub fn new() -> Self {
        Self {
            name_to_tree: HashMap::new(),
        }
    }

    pub fn from_pair_iterator<'a>(iterator: impl Iterator<Item = &'a (&'a str, &'a str)>) -> Self {
        let mut aliases = Self::new();
        for &(k, v) in iterator {
            aliases.set(String::from(k), ExpressionTree::from_line(v).unwrap());
        }
        aliases
    }

    /// Get an instance with [DEFAULT_ALIASES]
    ///
    /// ```rust
    /// use lambda_solver::AliasStore;
    ///
    /// let aliases = AliasStore::with_defaults();
    /// ```
    pub fn with_defaults() -> Self {
        Self::from_pair_iterator(DEFAULT_ALIASES.iter())
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
