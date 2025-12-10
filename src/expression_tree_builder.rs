use pest::{
    Parser,
    iterators::{Pair, Pairs},
};
use pest_derive::Parser;
use std::{collections::HashMap, rc::Rc};

use crate::{ExpressionTree, alias::AliasStore, expression_node::ExpressionNode};

#[derive(Parser)]
#[grammar = "lambda_grammar.pest"]
struct LambdaParser;

struct AbstractionParsingState<'a> {
    parameters: Pairs<'a, Rule>,
    body: Pairs<'a, Rule>,
    lambda_depth: usize,
}

/// Can be used to repeatedly build expression trees from string representation without re-allocating resources.
///
/// For single use, [ExpressionTree::from_line] provides a convinient abstraction. For repeated use, if you want to minimize resource allocation, use this directly.
///
/// ## Usage:
/// ```rust
/// use lambda_solver::{AliasStore, ExpressionTreeBuilder};
///
/// let alias_store = AliasStore::new();
/// let mut builder = ExpressionTreeBuilder::new(&alias_store);
///
/// let tree1 = builder.build("λa.b").unwrap();
/// let tree2 = builder.build("λa.a").unwrap();
///
/// assert_eq!(tree1.to_expression_str().unwrap(), "(λa.b)");
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

    fn parse_abstraction(&mut self, mut state: AbstractionParsingState) -> Rc<ExpressionNode> {
        match state.parameters.next() {
            // if there are parameters yet to be parsed, parse them recursively
            Some(parameter_pair) => {
                let parameter_name_str = parameter_pair.as_str();
                let parameter_name = String::from(parameter_name_str);

                // if the same parameter name was used in a parent abstraction,
                // cache it's binding depth
                let old_binding_depth = self
                    .bound_variables
                    .insert(parameter_name.clone(), state.lambda_depth);

                // now, anything parsed will be inside one more abstraction
                // (this abstraction) so increment lambda depth
                state.lambda_depth += 1;

                // parse the remaining parameter list
                let body = self.parse_abstraction(state);

                if let Some(old_binding_depth) = old_binding_depth {
                    // if we did override an existing bound variable, restore it
                    self.bound_variables
                        .insert(parameter_name.clone(), old_binding_depth);
                } else {
                    // otherwise delete the entry we added
                    self.bound_variables.remove(parameter_name_str);
                }

                Rc::new(ExpressionNode::Abstraction {
                    parameter: parameter_name,
                    body,
                })
            }

            // if state.parameters iterator is exhausted, return the body
            None => self
                .node_from_pairs(state.body, state.lambda_depth)
                .expect("Matched abstraction must contain a body"),
        }
    }

    fn node_from_pair(&mut self, pair: Pair<Rule>, lambda_depth: usize) -> Rc<ExpressionNode> {
        let variable_name = pair.as_str();
        match pair.as_rule() {
            Rule::variable => match self.bound_variables.get(variable_name) {
                Some(binding_depth) => {
                    Rc::new(ExpressionNode::BoundVariable(lambda_depth - binding_depth))
                }
                None => match self.alias_store.get(variable_name) {
                    Some(tree) => Rc::clone(&tree.root),
                    None => Rc::new(ExpressionNode::FreeVariable(String::from(variable_name))),
                },
            },
            Rule::abstraction => {
                    let mut pairs = pair.into_inner();
                    let parameter_list_pair = pairs
                        .next()
                        .expect("Matched abstraction must contain a parameter list");
                    self.parse_abstraction(AbstractionParsingState {
                        parameters: parameter_list_pair.into_inner(),
                        body: pairs,
                        lambda_depth,
                    })
            }
            Rule::bracketed_expression => self
                .node_from_pairs(pair.into_inner(), lambda_depth)
                .expect("Matched bracketed expression must contain at least once variable or abstraction"),
            Rule::parameters => unreachable!("Parameters matched in unexpected location. Should be the first match inside an abstraction"),
            Rule::root_expression => unreachable!("This function recieved a root expression match. The full string match will contain only one root expression match, whose inner pairs must be supploed to this impl's from_pairs function."),
            Rule::EOI
            | Rule::WHITESPACE
            | Rule::variable_start
            | Rule::expression
            | Rule::atom
            | Rule::full_string
            | Rule::variable_list => unreachable!("Silent token produced a match")
        }
    }

    fn node_from_pairs(
        &mut self,
        mut pairs: Pairs<Rule>,
        lambda_depth: usize,
    ) -> Option<Rc<ExpressionNode>> {
        pairs.next_back().map(|right_pair| {
            let right_arm = self.node_from_pair(right_pair, lambda_depth);
            match self.node_from_pairs(pairs, lambda_depth) {
                Some(left_arm) => Rc::new(ExpressionNode::Application {
                    function: left_arm,
                    argument: right_arm,
                }),
                None => right_arm,
            }
        })
    }

    fn node_from_line(
        &mut self,
        line: &str,
    ) -> Result<Rc<ExpressionNode>, pest::error::Error<Rule>> {
        Ok(self
            .node_from_pairs(
                LambdaParser::parse(Rule::full_string, line)?
                    .next()
                    .expect("full string match not found")
                    .into_inner(),
                0,
            )
            .expect(
                "Matched full string must contain atleast one variable, abstraction or abstraction",
            ))
    }

    pub fn build(&mut self, line: &str) -> Result<ExpressionTree, pest::error::Error<Rule>> {
        Ok(ExpressionTree {
            root: self.node_from_line(line)?,
        })
    }
}

// fn new(pair: Pair<'a, Rule>, lambda_depth: usize) -> Self {
// }

// }
