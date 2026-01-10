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
///
/// ## Comparison Aliases
///
/// * **ISZERO**: `λn.n (λx.FALSE) TRUE`
///     * **Is Zero**. It takes a single Church numeral argument `n` and :
///         * if `n > 0`: returns `FALSE`.
///         * else (`n == 0`): returns `TRUE`.
///     * Usage: `ISZERO 0` evaluates to `TRUE`.
///     * Extensions: Can be used with the `NOT` operator to check if a numeral is not zero. For example, `NOT (ISZERO 0)` evaluates to `FALSE`.
/// * **LEQ**: `λm.λn.ISZERO (SUB m n)`
///     * **Less than or Equal to**. It takes two Church numerals `m` and `n`, and :
///         * if `m <= n`: returns `TRUE`.
///         * else (i.e. `m > n`) returns `FALSE`.
///     * Usage: `LEQ 1 2` evaluates to `TRUE`.
///     * Extensions:
///         * Greater than or equal to: Same functionality can be acheived by reversing the order of arguments and using `LEQ`, since `a >= b <=> b <= a`. So, for example, to check if `2 > 1`, use `LEQ 1 2`.
///         * Greater than: `a > b <=> NOT (a <= b)`. For example, to check if `2 > 1`, use `NOT (LEQ 2 1)`.
///         * Less than: Same as greater than, with reversed order of arguments. For example, to check `1 < 2`, use `NOT (LEQ 2 1)`.
///
/// ## Pair Aliases
///
/// * **PAIR**: `λx.λy.λf.f x y`
///     * **Pair** encapsulates a tuple of 2 values. For example, `PAIR 1 2`.
///     * Use handler functions `FIRST` and `SECOND` to extract values from a `PAIR` instance.
///     * Can be chained to build a linked list.
/// * **FIRST**: `λp.p (λx.λy.x)`
///     * **First** returns the first element of a pair.
///     * Usage: `FIRST (PAIR 1 2)` evaluates to `1`.
/// * **SECOND**: `λp.p (λx.λy.y)`
///     * **Second** returns the second element of a pair.
///     * Usage: `SECOND (PAIR 1 2)` evaluates to `2`.
///
/// ## Linked List Aliases
///
/// Linked lists can be built by chaining `PAIR`s, with a `NIL` to indicate the
/// end of the list. For example, `PAIR 1 (PAIR 2 (PAIR 3 (PAIR 4 (PAIR 5 (PAIR
/// 6 NIL)))))` represents the linked list: `1, 2, 3, 4, 5, 6`.
///
/// To access an element at index `i` (where `i` is any Church numeral such that
/// `0 <= i < size_of_list`), in a linked list `l`, we can use `FIRST (i SECOND
/// l)`. So, for example, `FIRST (3 SECOND (PAIR 1 (PAIR 2 (PAIR 3 (PAIR 4 (PAIR
/// 5 (PAIR 6 NIL)))))))` evaluates to `4` (which is the 4th element of the
/// linked list). Note that using this method for indexing implies that the
/// linked list is zero-indexed (i.e. the first element corresponds to `i=0`)
///
/// * **NIL**: `λf.TRUE`
///     * **Nil** is used to represent an empty linked list (or the end of a linked list).
/// * **NULL**: `λp.p (λx.λy.FALSE)`
///     * **Null** is used to check for an empty linked list.
///     * Usage: `NULL (6 SECOND (PAIR 1 (PAIR 2 (PAIR 3 (PAIR 4 (PAIR 5 (PAIR 6 NIL)))))))` evaluates to `TRUE`.
///
/// ## Recursive Aliases
///
/// * **Y**: `λf.(λx.f (x x)) (λx.f (x x))`
///     * **Y Combinator**: enables recursion in pure lambda calculus by computing a fixed point of a function: `Y F → F (Y F)`.
///     * Usage: See definition of `FACTORIAL`
/// * **FACTORIAL**: `Y (λf.λn.ISZERO n 1 (MULT n (f (PRED n))))`
///     * **Factorial** corresponds to the mathematical factorial function: `Factorial(n) = n * Factorial(n - 1)` for `n > 0` and `Factorial(0) = 1`
///     * Usage: `FACTORIAL 5` evaluates to `120`
pub const DEFAULT_ALIASES: [(&str, &str); 21] = [
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
    // Comparison
    ("ISZERO", "λn.n (λx.FALSE) TRUE"),
    ("LEQ", "λm.λn.ISZERO (SUB m n)"),
    // Pairs
    ("PAIR", "λx.λy.λf.f x y"),
    ("FIRST", "λp.p (λx.λy.x)"),
    ("SECOND", "λp.p (λx.λy.y)"),
    // Linked list
    ("NIL", "λf.TRUE"),
    ("NULL", "λp.p (λx.λy.FALSE)"),
    // Recursive
    ("Y", "λf.(λx.f (x x)) (λx.f (x x))"),
    (
        "FACTORIAL",
        "Y (
            λf.λn.
                ISZERO n
                1
                (MULT n (f (PRED n)))
        )",
    ),
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
        beta_reduce_and_check(&mut builder, "PRED 3", "2");
        beta_reduce_and_check(&mut builder, "PRED 0", "0"); // underflow case
    }

    #[test]
    fn sub() {
        let aliases = AliasStore::with_defaults();
        let mut builder = ExpressionTreeBuilder::new(&aliases);

        beta_reduce_and_check(&mut builder, "SUB 5 2", "3");
        beta_reduce_and_check(&mut builder, "SUB 5 5", "0");
        beta_reduce_and_check(&mut builder, "SUB 2 5", "0"); // underflow case
    }

    #[test]
    fn iszero() {
        let aliases = AliasStore::with_defaults();
        let mut builder = ExpressionTreeBuilder::new(&aliases);

        beta_reduce_and_check(&mut builder, "ISZERO 0", "TRUE");
        beta_reduce_and_check(&mut builder, "ISZERO 1", "FALSE");
        beta_reduce_and_check(&mut builder, "ISZERO 8", "FALSE");
        beta_reduce_and_check(&mut builder, "ISZERO 5", "FALSE");
    }

    #[test]
    fn leq() {
        let aliases = AliasStore::with_defaults();
        let mut builder = ExpressionTreeBuilder::new(&aliases);

        beta_reduce_and_check(&mut builder, "LEQ 5 5", "TRUE");
        beta_reduce_and_check(&mut builder, "LEQ 3 10", "TRUE");
        beta_reduce_and_check(&mut builder, "LEQ 0 0", "TRUE");
        beta_reduce_and_check(&mut builder, "LEQ 1 0", "FALSE");
        beta_reduce_and_check(&mut builder, "LEQ 10 5", "FALSE");
    }

    #[test]
    fn pair() {
        let aliases = AliasStore::with_defaults();
        let mut builder = ExpressionTreeBuilder::new(&aliases);

        beta_reduce_and_check(&mut builder, "FIRST (PAIR 1 2)", "1");
        beta_reduce_and_check(&mut builder, "SECOND (PAIR 3 0)", "0");
        beta_reduce_and_check(
            &mut builder,
            "FIRST (SECOND (PAIR (PAIR 1 2) (PAIR 3 4)))",
            "3",
        );
    }

    #[test]
    fn linked_list() {
        let aliases = AliasStore::with_defaults();
        let mut builder = ExpressionTreeBuilder::new(&aliases);

        beta_reduce_and_check(&mut builder, "NULL NIL", "TRUE");
        beta_reduce_and_check(&mut builder, "NULL (PAIR 1 NIL)", "FALSE");
        beta_reduce_and_check(
            &mut builder,
            "FIRST (4 SECOND (PAIR 1 (PAIR 2 (PAIR 3 (PAIR 4 (PAIR 5 (PAIR 6 NIL)))))))",
            "5",
        );
        beta_reduce_and_check(
            &mut builder,
            "FIRST (0 SECOND (PAIR 1 (PAIR 2 (PAIR 3 (PAIR 4 (PAIR 5 (PAIR 6 NIL)))))))",
            "1",
        );
        beta_reduce_and_check(
            &mut builder,
            "FIRST (3 SECOND (PAIR 1 (PAIR 2 (PAIR 3 (PAIR 4 (PAIR 5 (PAIR 6 NIL)))))))",
            "4",
        );
        beta_reduce_and_check(
            &mut builder,
            "NULL (3 SECOND (PAIR 1 (PAIR 2 (PAIR 3 (PAIR 4 (PAIR 5 (PAIR 6 NIL)))))))",
            "FALSE",
        );
        beta_reduce_and_check(
            &mut builder,
            "NULL (6 SECOND (PAIR 1 (PAIR 2 (PAIR 3 (PAIR 4 (PAIR 5 (PAIR 6 NIL)))))))",
            "TRUE",
        );
    }

    #[test]
    fn factorial() {
        let aliases = AliasStore::with_defaults();
        let mut builder = ExpressionTreeBuilder::new(&aliases);

        beta_reduce_and_check(&mut builder, "FACTORIAL 0", "1");
        beta_reduce_and_check(&mut builder, "FACTORIAL 1", "1");
        beta_reduce_and_check(&mut builder, "FACTORIAL 2", "2");
        beta_reduce_and_check(&mut builder, "FACTORIAL 3", "6");
        beta_reduce_and_check(&mut builder, "FACTORIAL 5", "120");
    }
}
