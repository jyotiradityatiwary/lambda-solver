use pest::{Parser, iterators::Pair};
use std::{collections::HashMap, rc::Rc};

use crate::{ExpressionTree, alias::AliasStore, expression_node::ExpressionNode, parser};

/// Can be used to repeatedly build expression trees from string representation without re-allocating resources.
///
/// ## Usage:
/// ```rust
/// use lambda_solver::{AliasStore, ExpressionTreeBuilder};
///
/// let alias_store = AliasStore::new();
/// let mut builder = ExpressionTreeBuilder::new(&alias_store);
///
/// let tree1 = builder.build("a->b").unwrap();
/// let tree2 = builder.build("a->a").unwrap();
///
/// assert_eq!(tree1.to_expression_str().unwrap(), "(a->b)");
/// ```
pub struct ExpressionTreeBuilder<'a> {
    /// maps the name of a bound variable to it's depth (in terms of lambda functions) in the expression tree
    bound_variables: HashMap<String, usize>,
    alias_store: &'a AliasStore,
}

impl<'a> ExpressionTreeBuilder<'a> {
    pub fn new(alias_store: &'a AliasStore) -> Self {
        Self {
            bound_variables: HashMap::new(),
            alias_store,
        }
    }

    fn node_from_pair(
        &mut self,
        pair: Pair<parser::Rule>,
        lambda_depth: usize,
    ) -> Rc<ExpressionNode> {
        let variable_name = pair.as_str();
        match pair.as_rule() {
            parser::Rule::variable => match self.bound_variables.get(variable_name) {
                Some(binding_depth) => {
                    Rc::new(ExpressionNode::BoundVariable(lambda_depth - binding_depth))
                }
                None => match self.alias_store.get(variable_name) {
                    Some(tree) => Rc::clone(&tree.root),
                    None => Rc::new(ExpressionNode::FreeVariable(String::from(variable_name))),
                },
            },
            parser::Rule::application => {
                let mut pairs = pair.into_inner();
                let function_pair = pairs.next().unwrap();
                let argument_pair = pairs.next().unwrap();
                Rc::new(ExpressionNode::Application {
                    function: self.node_from_pair(function_pair, lambda_depth),
                    argument: self.node_from_pair(argument_pair, lambda_depth),
                })
            }
            parser::Rule::abstraction => {
                let mut pairs = pair.into_inner();
                let parameter_pair = pairs.next().unwrap();
                let body_pair = pairs.next().unwrap();
                let parameter_str = parameter_pair.as_str();
                let old_binding_depth = self
                    .bound_variables
                    .insert(String::from(parameter_str), lambda_depth);
                let body = self.node_from_pair(body_pair, lambda_depth + 1);
                if let Some(old_binding_depth) = old_binding_depth {
                    self.bound_variables
                        .insert(String::from(parameter_str), old_binding_depth);
                } else {
                    self.bound_variables.remove(parameter_str);
                }
                Rc::new(ExpressionNode::Abstraction {
                    parameter: String::from(parameter_pair.as_str()),
                    body,
                })
            }
            parser::Rule::EOI
            | parser::Rule::WHITESPACE
            | parser::Rule::variable_start
            | parser::Rule::parameter
            | parser::Rule::arrow
            | parser::Rule::body
            | parser::Rule::function
            | parser::Rule::argument
            | parser::Rule::expression
            | parser::Rule::bracketed_expression
            | parser::Rule::full_string => unreachable!(),
        }
    }

    fn node_from_line(
        &mut self,
        line: &str,
    ) -> Result<Rc<ExpressionNode>, pest::error::Error<parser::Rule>> {
        Ok(self.node_from_pair(
            parser::LambdaParser::parse(parser::Rule::full_string, line)?
                .next()
                .unwrap(),
            0,
        ))
    }

    pub fn build(
        &mut self,
        line: &str,
    ) -> Result<ExpressionTree, pest::error::Error<parser::Rule>> {
        Ok(ExpressionTree {
            root: self.node_from_line(line)?,
        })
    }
}
