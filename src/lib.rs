use pest::{Parser, iterators::Pair};
use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "lambda_grammar.pest"]
struct LambdaParser;

enum ExpressionNode {
    Variable(String),
    Application {
        function: Box<ExpressionNode>,
        argument: Box<ExpressionNode>,
    },
    Abstraction {
        parameter: String,
        body: Box<ExpressionNode>,
    },
}

impl ExpressionNode {
    fn from_pair(pair: Pair<Rule>) -> ExpressionNode {
        match pair.as_rule() {
            Rule::variable => ExpressionNode::Variable(String::from(pair.as_str())),
            Rule::application => {
                let mut pairs = pair.into_inner();
                let function_pair = pairs.next().unwrap();
                let argument_pair = pairs.next().unwrap();
                ExpressionNode::Application {
                    function: Box::new(ExpressionNode::from_pair(function_pair)),
                    argument: Box::new(ExpressionNode::from_pair(argument_pair)),
                }
            }
            Rule::abstraction => {
                let mut pairs = pair.into_inner();
                let parameter_pair = pairs.next().unwrap();
                let body_pair = pairs.next().unwrap();
                ExpressionNode::Abstraction {
                    parameter: String::from(parameter_pair.as_str()),
                    body: Box::new(ExpressionNode::from_pair(body_pair)),
                }
            }
            Rule::EOI
            | Rule::WHITESPACE
            | Rule::variable_start
            | Rule::parameter
            | Rule::arrow
            | Rule::body
            | Rule::function
            | Rule::argument
            | Rule::expression
            | Rule::bracketed_expression
            | Rule::full_string => unreachable!(),
        }
    }

    pub fn to_expression_str(&self) -> String {
        let mut expr = String::new();

        match self {
            ExpressionNode::Variable(name) => expr.push_str(name),
            ExpressionNode::Application { function, argument } => {
                expr.push('(');
                expr.push_str(&function.to_expression_str());
                expr.push(' ');
                expr.push_str(&argument.to_expression_str());
                expr.push(')');
            }
            ExpressionNode::Abstraction { parameter, body } => {
                expr.push('(');
                expr.push_str(&parameter);
                expr.push('-');
                expr.push('>');
                expr.push_str(&body.to_expression_str());
                expr.push(')')
            }
        };

        expr
    }
}

pub struct ExpressionTree {
    root: ExpressionNode,
}

impl ExpressionTree {
    pub fn from_line(line: &str) -> Result<ExpressionTree, pest::error::Error<Rule>> {
        Ok(ExpressionTree {
            root: ExpressionNode::from_pair(
                LambdaParser::parse(Rule::full_string, line)?
                    .next()
                    .unwrap(),
            ),
        })
    }

    pub fn to_expression_str(&self) -> String {
        self.root.to_expression_str()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn build_expression_tree_and_convert_to_str() {
        fn check(input: &str, expected_output: &str) {
            let expr_tree = ExpressionTree::from_line(input).unwrap();
            let output = expr_tree.to_expression_str();
            assert_eq!(output, expected_output);
        }

        check("a", "a");
        check("a b", "(a b)");
        check("a    ->b", "(a->b)");
        check("( a -> ( b -> a ) )((b))", "((a->(b->a)) b)");
    }

    #[test]
    fn reject_invalid_expression_string() {
        fn check(input: &str) {
            let result = ExpressionTree::from_line(input);
            assert!(result.is_err());
        }

        check("a->");
        check("(a ");
        check("( a -> ( b -> a ) )(())");
    }
}
