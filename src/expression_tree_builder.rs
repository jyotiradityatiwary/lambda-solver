use pest::{Parser, iterators::Pair};
use std::{collections::HashMap, rc::Rc};

use crate::{expression_node::ExpressionNode, parser};

pub struct ExpressionTreeBuilder {
    /// maps the name of a bound variable to it's depth (in terms of lambda functions) in the expression tree
    bound_variables: HashMap<String, usize>,
}

impl ExpressionTreeBuilder {
    pub fn new() -> Self {
        Self {
            bound_variables: HashMap::new(),
        }
    }

    pub fn node_from_pair(
        &mut self,
        pair: Pair<parser::Rule>,
        lambda_depth: usize,
    ) -> ExpressionNode {
        match pair.as_rule() {
            parser::Rule::variable => match self.bound_variables.get(pair.as_str()) {
                Some(binding_depth) => ExpressionNode::BoundVariable(lambda_depth - binding_depth),
                None => ExpressionNode::FreeVariable(String::from(pair.as_str())),
            },
            parser::Rule::application => {
                let mut pairs = pair.into_inner();
                let function_pair = pairs.next().unwrap();
                let argument_pair = pairs.next().unwrap();
                ExpressionNode::Application {
                    function: Rc::new(self.node_from_pair(function_pair, lambda_depth)),
                    argument: Rc::new(self.node_from_pair(argument_pair, lambda_depth)),
                }
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
                ExpressionNode::Abstraction {
                    parameter: String::from(parameter_pair.as_str()),
                    body: Rc::new(body),
                }
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

    pub fn node_from_line(
        &mut self,
        line: &str,
    ) -> Result<ExpressionNode, pest::error::Error<parser::Rule>> {
        Ok(self.node_from_pair(
            parser::LambdaParser::parse(parser::Rule::full_string, line)?
                .next()
                .unwrap(),
            0,
        ))
    }
}
