//! An untyped lambda calculus library

use std::{fmt, rc::Rc};

pub use crate::alias::{AliasStore, DEFAULT_ALIASES};
use crate::expression_node::ExpressionNode;
pub use crate::expression_tree_builder::{ExpressionTreeBuilder, Rule};
pub use crate::stringifier::ExpressionNodeStringifierError;

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
/// let a = ExpressionTree::from_line("λa.a");
/// let b = ExpressionTree::from_line("λb.b");
/// assert_eq!(a, b); // alpha-equivalent
/// ```
///
/// ## Note on the λ (lambda) symbol
///
/// It can be inconvinient to type the lambda symbol on the keyboard. As a
/// workaround, you can alias it as a sequence which is easier to type, before
/// passing the expression string to [ExpressionTree::from_line] or to
/// [ExpressionTreeBuilder]. For example, you can alias `λ` as `\l`
/// (demonstrated below)
///
/// ```rust
/// use lambda_solver::ExpressionTree;
///
/// let expression = r"\l a.a";
/// let tree = ExpressionTree::from_line(expression); // will fail
/// assert!(tree.is_err());
///
/// let expression = &expression.replace(r"\l", "λ"); // replace `\l` with `λ`
/// let tree = ExpressionTree::from_line(expression).unwrap(); // won't fail
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
    /// let tree = ExpressionTree::from_line("(λa.b) c").unwrap();
    /// ```
    pub fn from_line(line: &str) -> Result<ExpressionTree, pest::error::Error<Rule>> {
        let alias_store = AliasStore::new();
        Self::from_line_with_aliases(line, &alias_store)
    }

    /// Build expression tree from string representation
    ///
    /// ```rust
    /// use lambda_solver::{ExpressionTree, AliasStore};
    ///
    /// let mut aliases = AliasStore::new();
    /// aliases.set(String::from("x"), ExpressionTree::from_line("λa.b").unwrap());
    /// let tree = ExpressionTree::from_line_with_aliases("(x c)", &aliases).unwrap();
    ///
    /// assert_eq!(tree, ExpressionTree::from_line("(λa.b) c").unwrap());
    /// ```
    pub fn from_line_with_aliases(
        line: &str,
        alias_store: &AliasStore,
    ) -> Result<ExpressionTree, pest::error::Error<Rule>> {
        ExpressionTreeBuilder::new(&alias_store).build(line)
    }

    /// Generate a string representation of the expression tree
    ///
    /// ```rust
    /// use lambda_solver::ExpressionTree;
    ///
    /// let tree = ExpressionTree::from_line("(λa.b) c").unwrap();
    /// assert_eq!(tree.to_expression_str().unwrap(), "((λa.b) c)");
    /// ```
    pub fn to_expression_str(&self) -> Result<String, ExpressionNodeStringifierError> {
        self.root.to_expression_str()
    }

    /// Generate a string representation of the expression tree, with bound variables represented an De Brujin indices
    ///
    /// ```rust
    /// use lambda_solver::ExpressionTree;
    ///
    /// let tree = ExpressionTree::from_line("(λa.b) c").unwrap();
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
    /// let mut tree = ExpressionTree::from_line("(λa.a) b").unwrap();
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
        check("λa    .b", "(λa.b)");
        check("(λ a . ( λ  b.a ) )((b))", "((λa.(λb.a)) b)");
        check("λa.λb.c", "(λa.(λb.c))");
        check("λa b c.b", "(λa.(λb.(λc.b)))");
    }

    #[test]
    fn reject_invalid_expression_string() {
        fn check(input: &str) {
            let result = ExpressionTree::from_line(input);
            assert!(result.is_err());
        }

        check("λa.");
        check("(a ");
        check("( λ a . ( λb . a ) )(())");
    }

    #[test]
    fn beta_reduction() {
        fn beta_reduce_and_check(builder: &mut ExpressionTreeBuilder, start: &str, end: &str) {
            let mut tree = builder
                .build(start)
                .expect("Failed to parse start expression");
            while tree.beta_reduce() {}
            assert_eq!(
                tree,
                builder
                    .build(end)
                    .expect("Failed to parse target (end) tree"),
                "Reduced expression does not match expected end expression",
            )
        }

        let aliases = AliasStore::with_defaults();
        let mut builder = ExpressionTreeBuilder::new(&aliases);
        beta_reduce_and_check(&mut builder, "NOT TRUE", "FALSE");
        beta_reduce_and_check(&mut builder, "NOT FALSE", "TRUE");
        beta_reduce_and_check(&mut builder, "AND TRUE TRUE", "TRUE");
        beta_reduce_and_check(&mut builder, "AND FALSE TRUE", "FALSE");
        beta_reduce_and_check(&mut builder, "OR TRUE FALSE", "TRUE");
        beta_reduce_and_check(&mut builder, "OR FALSE FALSE", "FALSE");
    }

    #[test]
    fn iterative_beta_reduction() {
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
        iteratively_reduce_and_check(vec!["(a (λa.b))"]);
        iteratively_reduce_and_check(vec!["((λa.a) b)", "b"]);
        iteratively_reduce_and_check(vec!["((λa.c) b)", "c"]);
        iteratively_reduce_and_check(vec!["(((λa.(λb.(a b))) c) d)", "((λb.(c b)) d)", "(c d)"]);
        iteratively_reduce_and_check(vec![
            "(((λa.(a b))c) ((λa.(a b)) c))",
            "((c b) ((λa.(a b)) c))",
            "((c b) (c b))",
        ]);
        iteratively_reduce_and_check(vec!["(((λa.(λb.(a b))) b) c)", "((λb.(b b)) c)", "(b c)"]);
    }
}
