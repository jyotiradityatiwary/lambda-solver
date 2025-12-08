use std::{fmt, rc::Rc};

pub use crate::alias::{AliasStore, DEFAULT_ALIASES};
use crate::expression_node::ExpressionNode;
pub use crate::expression_tree_builder::ExpressionTreeBuilder;
pub use crate::stringifier::ExpressionNodeStringifierError;

mod parser {
    use pest_derive::Parser;

    #[derive(Parser)]
    #[grammar = "lambda_grammar.pest"]
    pub struct LambdaParser;
}

mod alias;
mod expression_node;
mod expression_tree_builder;
mod stringifier;

/// A lambda-expression represented using De Bruijn indices.
///
/// ## Equality
///
/// `ExpressionTree` implements `PartialEq`, where equality (`==`)
/// corresponds to **alpha-equivalence**: two expressions are considered equal
/// if they differ only by consistent renaming of bound variables.
///
/// This comparison is structural and based on the De Bruijn
/// representation of the expression.
///
/// ```rust
/// use lambda_solver::ExpressionTree;
///
/// let a = ExpressionTree::from_line("(a->a)");
/// let b = ExpressionTree::from_line("(b->b)");
/// assert_eq!(a, b); // alpha-equivalent
/// ```
#[derive(PartialEq, Eq)]
pub struct ExpressionTree {
    root: Rc<ExpressionNode>,
}

impl ExpressionTree {
    /// Build expression tree from string representation
    ///
    /// ```rust
    /// use lambda_solver::ExpressionTree;
    ///
    /// let tree = ExpressionTree::from_line("((a->b) c)").unwrap();
    /// ```
    pub fn from_line(line: &str) -> Result<ExpressionTree, pest::error::Error<parser::Rule>> {
        let alias_store = AliasStore::new();
        Self::from_line_with_aliases(line, &alias_store)
    }

    /// Build expression tree from string representation
    ///
    /// ```rust
    /// use lambda_solver::{ExpressionTree, AliasStore};
    ///
    /// let mut aliases = AliasStore::new();
    /// aliases.set(String::from("x"), ExpressionTree::from_line("a->b").unwrap());
    /// let tree = ExpressionTree::from_line_with_aliases("(x c)", &aliases).unwrap();
    ///
    /// assert_eq!(tree, ExpressionTree::from_line("((a->b) c)").unwrap()); // should substitute the alias
    /// ```
    pub fn from_line_with_aliases(
        line: &str,
        alias_store: &AliasStore,
    ) -> Result<ExpressionTree, pest::error::Error<parser::Rule>> {
        ExpressionTreeBuilder::new(&alias_store).build(line)
    }

    /// Generate a string representation of the expression tree
    ///
    /// ```rust
    /// use lambda_solver::ExpressionTree;
    ///
    /// let tree = ExpressionTree::from_line("((a->b) c)").unwrap();
    /// assert_eq!(tree.to_expression_str().unwrap(), "((a->b) c)");
    /// ```
    pub fn to_expression_str(&self) -> Result<String, ExpressionNodeStringifierError> {
        self.root.to_expression_str()
    }

    /// Generate a string representation of the expression tree, with bound variables represented an De Brujin indices
    ///
    /// ```rust
    /// use lambda_solver::ExpressionTree;
    ///
    /// let tree = ExpressionTree::from_line("((a->b) c)").unwrap();
    /// assert_eq!(tree.to_expression_str_de_brujin(), "((λ b) c)");
    /// ```
    pub fn to_expression_str_de_brujin(&self) -> String {
        self.root.to_expression_str_de_brujin()
    }

    /// Perform beta reduction (one step) on the lambda expression and returns a boolean stating if the tree was beta reduced
    ///
    /// ```rust
    /// use lambda_solver::ExpressionTree;
    ///
    /// let mut tree = ExpressionTree::from_line("((a->a) b)").unwrap();
    /// while (tree.beta_reduce()) {
    ///     // you can access the intermediate state of the tree between steps of the beta reduction
    ///     println!("{}", tree.to_expression_str().unwrap());
    /// }
    ///
    /// assert_eq!(tree, ExpressionTree::from_line("b").unwrap());
    /// ```
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

/// Gives De Brujin representation of expression tree. Not stable. Use [ExpressionTree::to_expression_str_de_brujin] to get de brujin representation deterministically
impl fmt::Debug for ExpressionTree {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ExpressionTree {}", self.to_expression_str_de_brujin())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn build_expression_tree_and_convert_to_str() {
        fn check(input: &str, expected_output: &str) {
            let expr_tree = ExpressionTree::from_line(input).unwrap();
            let output = expr_tree
                .to_expression_str()
                .unwrap_or_else(|e| panic!("Failed to build string representation of expression tree. Input: {}. Error: {:?}", input, e));
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
    fn beta_reduction() {
        fn iteratively_reduce_and_check(steps: Vec<&str>) {
            let mut tree =
                ExpressionTree::from_line(steps[0]).expect("Failed to parse expression tree");
            for step in steps[1..].iter() {
                assert!(tree.beta_reduce(), "Expression tree did not reduce");
                assert_eq!(
                    tree.to_expression_str().unwrap(),
                    *step,
                    "Reduced expression tree does not match expected reduction"
                )
            }
            assert!(
                !tree.beta_reduce(),
                "Expression tree reduced when no reduction was expected"
            );
            assert_eq!(
                tree.to_expression_str().unwrap(),
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
        iteratively_reduce_and_check(vec!["(((a->(b->(a b))) b) c)", "((b->(b b)) c)", "(b c)"]);
    }
}
