use std::mem;

use pest::{Parser, iterators::Pair};
use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "lambda_grammar.pest"]
struct LambdaParser;

#[derive(Clone)]
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
    fn from_pair(pair: Pair<Rule>) -> Self {
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

    fn to_expression_str(&self) -> String {
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

    fn search_and_beta_reduce(&mut self) -> bool {
        match self {
            ExpressionNode::Variable(_) => false,
            ExpressionNode::Abstraction { parameter: _, body } => body.search_and_beta_reduce(),
            ExpressionNode::Application { function, argument } => {
                if let ExpressionNode::Abstraction { parameter, body } = &mut **function {
                    body.substitute(&parameter, &argument);
                    *self = mem::replace(&mut **body, ExpressionNode::Variable(String::new()));
                    true
                } else {
                    function.search_and_beta_reduce() || argument.search_and_beta_reduce()
                }
            }
        }
    }

    fn substitute(&mut self, bound_variable: &str, target_expr: &Self) {
        match self {
            ExpressionNode::Variable(name) => {
                if name == bound_variable {
                    *self = target_expr.clone();
                }
            }
            ExpressionNode::Application { function, argument } => {
                function.substitute(bound_variable, target_expr);
                argument.substitute(bound_variable, target_expr);
            }
            ExpressionNode::Abstraction { parameter, body } => {
                if parameter != bound_variable {
                    body.substitute(bound_variable, target_expr);
                }
            }
        }
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

    pub fn beta_reduce(&mut self) -> bool {
        self.root.search_and_beta_reduce()
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

    #[test]
    fn test_deep_cloning() {
        let node = ExpressionNode::Abstraction {
            parameter: String::from("a"),
            body: Box::new(ExpressionNode::Abstraction {
                parameter: String::from("b"),
                body: Box::new(ExpressionNode::Variable(String::from("c"))),
            }),
        };
        assert_eq!(node.to_expression_str(), String::from("(a->(b->c))"));
        let mut node2 = node.clone();
        assert_eq!(
            node2.to_expression_str(),
            String::from("(a->(b->c))"),
            "Node changed on clone"
        );
        if let ExpressionNode::Abstraction { parameter: _, body } = &mut node2 {
            if let ExpressionNode::Abstraction { parameter: _, body } = &mut **body {
                *body = Box::new(ExpressionNode::Variable(String::from("d")))
            }
        }
        assert_eq!(
            node.to_expression_str(),
            String::from("(a->(b->c))"),
            "Original node changed"
        );
        assert_eq!(
            node2.to_expression_str(),
            String::from("(a->(b->d))"),
            "Cloned node did not change"
        );
    }

    #[test]
    fn substitution() {
        fn check_substitution(
            src: &str,
            bound_variable: &str,
            target_expr: &str,
            expected_expr: &str,
        ) {
            let mut tree = ExpressionTree::from_line(src).expect("Failed to parse expression tree");
            tree.root.substitute(
                bound_variable,
                &ExpressionTree::from_line(target_expr)
                    .expect("Failed to parse target expression tree")
                    .root,
            );
            assert_eq!(
                tree.to_expression_str(),
                expected_expr,
                "Substituted expression incorrect"
            );
        }
        check_substitution("(a->b)c", "b", "x y", "((a->(x y)) c)");
        check_substitution("(a->b) (b->c)", "b", "(d->c)", "((a->(d->c)) (b->c))");
    }

    #[test]
    fn beta_reduction() {
        fn iteratively_reduce_and_check(steps: Vec<&str>) {
            let mut tree =
                ExpressionTree::from_line(steps[0]).expect("Failed to parse expression tree");
            for step in steps[1..].iter() {
                assert!(tree.beta_reduce(), "Expression tree did not reduce");
                assert_eq!(
                    tree.to_expression_str(),
                    *step,
                    "Reduced expression tree does not match expected reduction"
                )
            }
            assert!(
                !tree.beta_reduce(),
                "Expression tree reduced when no reduction was expected"
            );
            assert_eq!(
                tree.to_expression_str(),
                steps[steps.len() - 1],
                "Expression tree changed when no reduction was expected"
            )
        }
        iteratively_reduce_and_check(vec!["a"]);
        iteratively_reduce_and_check(vec!["(a (a->b))"]);
        iteratively_reduce_and_check(vec!["((a->a) b)", "b"]);
        iteratively_reduce_and_check(vec!["((a->c) b)", "c"]);
        iteratively_reduce_and_check(vec!["(((a->(b->(a b))) c) d)", "((b->(c b)) d)", "(c d)"]);
        iteratively_reduce_and_check(vec![
            "(((a->(a b))c) ((a->(a b)) c))",
            "((c b) ((a->(a b)) c))",
            "((c b) (c b))",
        ]);
    }
}
