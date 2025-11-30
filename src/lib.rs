use std::rc::Rc;

use pest::{Parser, iterators::Pair};
use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "lambda_grammar.pest"]
struct LambdaParser;

#[derive(Clone)]
enum ExpressionNode {
    Variable(String),
    Application {
        function: Rc<ExpressionNode>,
        argument: Rc<ExpressionNode>,
    },
    Abstraction {
        parameter: String,
        body: Rc<ExpressionNode>,
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
                    function: Rc::new(ExpressionNode::from_pair(function_pair)),
                    argument: Rc::new(ExpressionNode::from_pair(argument_pair)),
                }
            }
            Rule::abstraction => {
                let mut pairs = pair.into_inner();
                let parameter_pair = pairs.next().unwrap();
                let body_pair = pairs.next().unwrap();
                ExpressionNode::Abstraction {
                    parameter: String::from(parameter_pair.as_str()),
                    body: Rc::new(ExpressionNode::from_pair(body_pair)),
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

    fn search_and_beta_reduce(self: &Rc<Self>) -> Option<Rc<Self>> {
        match self.as_ref() {
            ExpressionNode::Variable(_) => None,
            ExpressionNode::Abstraction { parameter, body } => {
                body.search_and_beta_reduce().map(|body| {
                    Rc::new(ExpressionNode::Abstraction {
                        parameter: parameter.clone(),
                        body: body,
                    })
                })
            }
            ExpressionNode::Application { function, argument } => {
                if let ExpressionNode::Abstraction { parameter, body } = function.as_ref() {
                    Some(body.substitute(parameter, argument))
                } else if let Some(reduced_function) = function.search_and_beta_reduce() {
                    Some(Rc::new(ExpressionNode::Application {
                        function: reduced_function,
                        argument: Rc::clone(argument),
                    }))
                } else if let Some(reduced_argument) = argument.search_and_beta_reduce() {
                    Some(Rc::new(ExpressionNode::Application {
                        function: Rc::clone(function),
                        argument: reduced_argument,
                    }))
                } else {
                    None
                }
            }
        }
    }

    fn substitute(self: &Rc<Self>, bound_variable: &str, target_expr: &Rc<Self>) -> Rc<Self> {
        match self.as_ref() {
            ExpressionNode::Variable(name) => {
                if name == bound_variable {
                    Rc::clone(target_expr)
                } else {
                    Rc::clone(self)
                }
            }
            ExpressionNode::Application { function, argument } => {
                Rc::new(ExpressionNode::Application {
                    function: function.substitute(bound_variable, target_expr),
                    argument: argument.substitute(bound_variable, target_expr),
                })
            }
            ExpressionNode::Abstraction { parameter, body } => {
                if parameter != bound_variable {
                    Rc::new(ExpressionNode::Abstraction {
                        parameter: parameter.clone(),
                        body: body.substitute(bound_variable, target_expr),
                    })
                } else {
                    Rc::clone(self)
                }
            }
        }
    }
}

pub struct ExpressionTree {
    root: Rc<ExpressionNode>,
}

impl ExpressionTree {
    pub fn from_line(line: &str) -> Result<ExpressionTree, pest::error::Error<Rule>> {
        Ok(ExpressionTree {
            root: Rc::new(ExpressionNode::from_pair(
                LambdaParser::parse(Rule::full_string, line)?
                    .next()
                    .unwrap(),
            )),
        })
    }

    pub fn to_expression_str(&self) -> String {
        self.root.to_expression_str()
    }

    pub fn beta_reduce(&mut self) -> bool {
        match self.root.search_and_beta_reduce() {
            Some(exp) => {
                self.root = exp;
                true
            }
            None => false,
        }
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
            body: Rc::new(ExpressionNode::Abstraction {
                parameter: String::from("b"),
                body: Rc::new(ExpressionNode::Variable(String::from("c"))),
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
            if let ExpressionNode::Abstraction { parameter: _, body } = Rc::make_mut(body) {
                *body = Rc::new(ExpressionNode::Variable(String::from("d")))
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
            let exp = ExpressionTree::from_line(src)
                .expect("Failed to parse expression tree")
                .root;
            let substituted_exp = exp.substitute(
                bound_variable,
                &ExpressionTree::from_line(target_expr)
                    .expect("Failed to parse target expression tree")
                    .root,
            );
            assert_eq!(
                substituted_exp.to_expression_str(),
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

    #[test]
    fn rc_clones() {
        let mut tree =
            ExpressionTree::from_line("((a->((a a) (a a))) b)").expect("Failed to parse tree");
        while tree.beta_reduce() {}
        if let ExpressionNode::Application {
            function,
            argument: _,
        } = tree.root.as_ref()
        {
            if let ExpressionNode::Application {
                function,
                argument: _,
            } = function.as_ref()
            {
                if let ExpressionNode::Variable(name) = function.as_ref() {
                    assert_eq!(name, "b", "Unexpected variable name")
                } else {
                    panic!("ExpressionNode is not a variable")
                }
                assert_eq!(
                    Rc::strong_count(function),
                    4,
                    "Unexpected reference count of variable \"b\""
                )
            } else {
                panic!("Function of tree root is not an application")
            }
        } else {
            panic!("Tree root is not an abstraction!")
        }
    }
}
