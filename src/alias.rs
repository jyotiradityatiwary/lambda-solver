use std::collections::HashMap;

use crate::{ExpressionTree, Rule};

/// Hold aliases for [ExpressionTreeBuilder](crate::ExpressionTreeBuilder)
pub struct AliasStore {
    name_to_tree: HashMap<String, ExpressionTree>,
}

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

    /// Get an instance with [DEFAULT_ALIASES] pre-loaded
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

/// A collection of standard combinators and aliases for logic and arithmetic
/// encoded using the untyped lambda calculus (Church encoding).
///
/// This is an array of tuples of type `(name: &str, expression: &str)`
///
/// ## Logic Aliases
///
/// * **TRUE**: `λx.λy.x`
///     * The logical value *True*. It is a function that takes two arguments and returns the **first** one.
///     * Usage: `TRUE a b` evaluates to `a`.
/// * **FALSE**: `λx.λy.y`
///     * The logical value *False*. It is a function that takes two arguments and returns the **second** one.
///     * Usage: `FALSE a b` evaluates to `b`.
/// * **AND**: `λp.λq.p q p`
///     * Logical **AND**. It takes two boolean values, `p` and `q`, and returns `TRUE` only if both are `TRUE`.
///     * Usage: `AND TRUE FALSE` evaluates to `FALSE`. `AND TRUE TRUE` evaluates to `TRUE`.
/// * **OR**: `λp.λq.p p q`
///     * Logical **OR**. It takes two boolean values, `p` and `q`, and returns `TRUE` if at least one is `TRUE`.
///     * Usage: `OR TRUE FALSE` evaluates to `TRUE`. `OR FALSE FALSE` evaluates to `FALSE`.
/// * **NOT**: `λp.p FALSE TRUE`
///     * Logical **NOT**. It takes a boolean value `p` and inverts it.
///     * Usage: `NOT TRUE` evaluates to `FALSE`. `NOT FALSE` evaluates to `TRUE`.
/// * **IFTHENELSE**: `λp.λa.λb.p a b`
///     * The conditional **IF-THEN-ELSE**. It takes a boolean value `p` (the condition), and two other terms `a` (the 'then' branch) and `b` (the 'else' branch)
///         * if `p == TRUE`, it returns `a`
///         * else (if `p == FALSE`), it returns `b`
///     * Usage: `IFTHENELSE TRUE 5 10` evaluates to `5`. `IFTHENELSE FALSE 5 10` evaluates to `10`.
///     * Note that the application of this function is same as directly writing `p a b` (since `TRUE` and `FALSE` themselves are selectors for the first and second argument respectively). So, `IFTHENELSE TRUE 5 10` is the same as `TRUE 5 10` (in fact the latter is the former's beta-reduced form), and both evaluate to `5`.
///
/// ## Arithmetic Aliases (Church Numerals)
///
/// Church numerals n are represented as `λf. λx. f^n(x)`, a function that
/// takes a function f and an argument x, and applies f to x exactly n times.
/// Conversion of numeric input into church numerals is automatically handled
/// at the time of parsing (e.g. using [ExpressionTree::from_line] or
/// [ExpressionTreeBuilder](crate::ExpressionTreeBuilder))
///
/// * **SUCC**: `λn.λf.λx.f (n f x)`
///     * The **Successor** function. It takes a Church numeral `n` and returns the Church numeral for `n + 1`.
///     * Usage: `SUCC 2` evaluates to `3`.
/// * **PLUS**: `λm.λn.λf.λx.m f (n f x)`
///     * **Addition**. It takes two Church numerals `m` and `n` and returns their sum `m + n`.
///     * Usage: `PLUS 2 3` evaluates to `5`.
/// * **MULT**: `λm.λn.λf.m (n f)`
///     * **Multiplication**. It takes two Church numerals `m` and `n` and returns their product `m * n`.
///     * Usage: `MULT 2 3` evaluates to `6`.
/// * **POW**: `λb.λn.n b`
///     * **Exponentiation** (power). This alias computes `m^n` (base m, power n) where `m` and `n` are Church numerals.
///     * Usage: `POW 2 3` evaluates to the numeral representing 8 (i.e., 2^3).
/// * **PRED**: `λn.λf.λx.n (λg.λh.h (g f)) (λu.x) (λu.u)`
///     * The **Predecessor** function. It takes a Church numeral `n` and :
///         * if `n > 0`, returns `n - 1`
///         * else (for `n == 0`), returns to `0`.
///     * Usage: `PRED 3` evaluates to `2`.
/// * **SUB**: `λm.λn.n PRED m`
///     * **Subtraction**. It takes two Church numerals `m` and `n` and :
///         * if `m >= n`, returns `m-n`.
///         * else returns `0`.
///     * It performs n applications of the `PRED` function to m
///     * Usage: `SUB 5 3` evaluates to `2`.
pub const DEFAULT_ALIASES: [(&str, &str); 12] = [
    // Logic
    ("TRUE", "λx.λy.x"),
    ("FALSE", "λx.λy.y"),
    ("AND", "λp.λq.p q p"),
    ("OR", "λp.λq.p p q"),
    ("NOT", "λp.p FALSE TRUE"),
    ("IFTHENELSE", "λp.λa.λb.p a b"),
    // Arithmetic
    ("SUCC", "λn.λf.λx.f (n f x)"),
    ("PLUS", "λm.λn.λf.λx.m f (n f x)"),
    ("MULT", "λm.λn.λf.m (n f)"),
    ("POW", "λb.λn.n b"),
    ("PRED", "λn.λf.λx.n (λg.λh.h (g f)) (λu.x) (λu.u)"),
    ("SUB", "λm.λn.n PRED m"),
];

#[cfg(test)]
mod test {
    use crate::{AliasStore, ExpressionTreeBuilder};

    fn beta_reduce_and_check(builder: &mut ExpressionTreeBuilder, start: &str, end: &str) {
        let mut tree = builder
            .build(start)
            .expect("Failed to parse start expression");
        println!("initial: {tree:?}");
        while tree.beta_reduce() {
            println!("beta reduced: {tree:?}");
        }
        assert_eq!(
            tree,
            builder
                .build(end)
                .expect("Failed to parse target (end) tree"),
            "Reduced expression does not match expected end expression",
        )
    }

    /// Compute beta-eta-normal form for both expressions and compare if equal
    fn check_benf(builder: &mut ExpressionTreeBuilder, a: &str, end: &str) {
        let mut a_tree = builder.build(a).expect("Failed to parse start expression");
        println!("`a` initial: {a_tree:?}");
        while a_tree.beta_reduce() {
            println!("beta reduced: {a_tree:?}");
        }
        while a_tree.eta_reduce() {
            println!("eta reduced: {a_tree:?}");
        }

        let mut b_tree = builder
            .build(end)
            .expect("Failed to parse target (end) tree.");
        println!("`b` initial: {b_tree:?}");
        while b_tree.beta_reduce() {
            println!("beta reduced: {b_tree:?}");
        }
        while b_tree.eta_reduce() {
            println!("eta reduced: {b_tree:?}");
        }
        assert_eq!(
            a_tree, b_tree,
            "Reduced expression does not match expected end expression",
        )
    }

    #[test]
    fn logic() {
        let aliases = AliasStore::with_defaults();
        let mut builder = ExpressionTreeBuilder::new(&aliases);

        // logic
        beta_reduce_and_check(&mut builder, "NOT TRUE", "FALSE");
        beta_reduce_and_check(&mut builder, "NOT FALSE", "TRUE");
        beta_reduce_and_check(&mut builder, "AND TRUE TRUE", "TRUE");
        beta_reduce_and_check(&mut builder, "AND FALSE TRUE", "FALSE");
        beta_reduce_and_check(&mut builder, "OR TRUE FALSE", "TRUE");
        beta_reduce_and_check(&mut builder, "OR FALSE FALSE", "FALSE");
    }

    #[test]
    fn church_numerals() {
        let aliases = AliasStore::with_defaults();
        let mut builder = ExpressionTreeBuilder::new(&aliases);

        beta_reduce_and_check(&mut builder, "0 a b", "b");
        beta_reduce_and_check(&mut builder, "0 a (b c d)", "b c d");
        beta_reduce_and_check(&mut builder, "3 (x y) z", "(x y (x y (x y z)))");
    }

    #[test]
    fn succ() {
        let aliases = AliasStore::with_defaults();
        let mut builder = ExpressionTreeBuilder::new(&aliases);

        beta_reduce_and_check(&mut builder, "SUCC 0", "1");
        beta_reduce_and_check(&mut builder, "SUCC 1", "2");
        beta_reduce_and_check(&mut builder, "SUCC 3", "4");
    }

    #[test]
    fn plus() {
        let aliases = AliasStore::with_defaults();
        let mut builder = ExpressionTreeBuilder::new(&aliases);

        beta_reduce_and_check(&mut builder, "PLUS 0 0", "0");
        beta_reduce_and_check(&mut builder, "PLUS 1 2", "3");
        beta_reduce_and_check(&mut builder, "PLUS 3 0", "3");
        beta_reduce_and_check(&mut builder, "PLUS 3 2", "5");
    }

    #[test]
    fn mult() {
        let aliases = AliasStore::with_defaults();
        let mut builder = ExpressionTreeBuilder::new(&aliases);

        beta_reduce_and_check(&mut builder, "MULT 0 5", "0");
        beta_reduce_and_check(&mut builder, "MULT 5 0", "0");
        beta_reduce_and_check(&mut builder, "MULT 1 1", "1");
        beta_reduce_and_check(&mut builder, "MULT 1 4", "4");
        beta_reduce_and_check(&mut builder, "MULT 2 3", "6");
    }

    #[test]
    fn pow() {
        let aliases = AliasStore::with_defaults();
        let mut builder = ExpressionTreeBuilder::new(&aliases);

        check_benf(&mut builder, "POW 2 3", "8");
        check_benf(&mut builder, "POW 3 2", "9");
        check_benf(&mut builder, "POW 5 1", "5");
        check_benf(&mut builder, "POW 5 0", "1");
    }

    #[test]
    fn pred() {
        let aliases = AliasStore::with_defaults();
        let mut builder = ExpressionTreeBuilder::new(&aliases);

        beta_reduce_and_check(&mut builder, "PRED 1", "0");
        // beta_reduce_and_check(&mut builder, "PRED 3", "2");
        // beta_reduce_and_check(&mut builder, "PRED 0", "0"); // underflow case
    }

    #[test]
    fn sub() {
        let aliases = AliasStore::with_defaults();
        let mut builder = ExpressionTreeBuilder::new(&aliases);

        beta_reduce_and_check(&mut builder, "SUB 5 2", "3");
        beta_reduce_and_check(&mut builder, "SUB 5 5", "0");
        beta_reduce_and_check(&mut builder, "SUB 2 5", "0"); // underflow case
    }
}
