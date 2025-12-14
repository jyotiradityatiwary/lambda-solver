use std::{collections::HashMap, fmt, rc::Rc};

use crate::{
    ExpressionNodeStringifierError,
    stringifier::{ExpNodeStringifierDeBrujin, ExpressionNodeStringifier},
};

#[derive(Clone)]
pub enum ExpressionNode {
    /// Holds the name of the free variable
    FreeVariable(String),
    /// Holds the DeBrujin index to the binding lambda abstraction
    BoundVariable(usize),
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
    pub fn to_expression_str(&self) -> Result<String, ExpressionNodeStringifierError> {
        ExpressionNodeStringifier::new().build(self)
    }

    pub fn to_expression_str_de_brujin(&self) -> String {
        ExpNodeStringifierDeBrujin::new().build(self)
    }

    pub fn search_and_beta_reduce(self: &Rc<Self>) -> Option<Rc<Self>> {
        match self.as_ref() {
            ExpressionNode::FreeVariable(_) | ExpressionNode::BoundVariable(_) => None,
            ExpressionNode::Abstraction { parameter, body } => {
                body.search_and_beta_reduce().map(|body| {
                    Rc::new(ExpressionNode::Abstraction {
                        parameter: parameter.clone(),
                        body: body,
                    })
                })
            }
            ExpressionNode::Application { function, argument } => {
                if let ExpressionNode::Abstraction { parameter: _, body } = function.as_ref() {
                    Some(body.substitute(argument))
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

    fn _substitute(
        self: &Rc<Self>,
        arg_dbi_shifter: &mut ArgDbiShifter,
        relative_lambda_depth: usize,
    ) -> Rc<Self> {
        match self.as_ref() {
            ExpressionNode::FreeVariable(_) => Rc::clone(self),
            ExpressionNode::BoundVariable(idx) => {
                match idx.cmp(&relative_lambda_depth) {
                    // idx < relative_lambda_depth
                    // => This variable is bound to an abstraction that is
                    // contained entirely within the abstraction being
                    // beta-reduced
                    // => No need to touch this
                    std::cmp::Ordering::Less => Rc::clone(self),
                    // idx == relative_lambda_depth
                    // => This variable is bound to the abstraction being reduced
                    // => Substitute here, with appropriate shifting of De
                    //     Brujin's indices inside the argument expression
                    std::cmp::Ordering::Equal => arg_dbi_shifter.shift(relative_lambda_depth),
                    // idx > relative_lambda_depth
                    // => This variable is bound to an abstraction outside the
                    //    one being reduced.
                    // => One less abstraction between this bound variable and
                    //    it's abstraction after beta reduction is complete
                    // => Reduce it's De Brujin Index by 1
                    std::cmp::Ordering::Greater => Rc::new(ExpressionNode::BoundVariable(idx - 1)),
                }
            }
            ExpressionNode::Application { function, argument } => {
                Rc::new(ExpressionNode::Application {
                    function: function._substitute(arg_dbi_shifter, relative_lambda_depth),
                    argument: argument._substitute(arg_dbi_shifter, relative_lambda_depth),
                })
            }
            ExpressionNode::Abstraction { parameter, body } => {
                Rc::new(ExpressionNode::Abstraction {
                    parameter: parameter.clone(),
                    body: body._substitute(arg_dbi_shifter, relative_lambda_depth + 1),
                })
            }
        }
    }

    fn substitute(self: &Rc<Self>, target_expr: &Rc<Self>) -> Rc<Self> {
        let mut db_index_shifter = ArgDbiShifter::new(target_expr);
        self._substitute(&mut db_index_shifter, 1)
    }

    pub fn eta_reduce(&self) -> Option<Rc<Self>> {
        match self {
            ExpressionNode::FreeVariable(_) => None,
            ExpressionNode::BoundVariable(_) => None,
            ExpressionNode::Application { function, argument } => match function.eta_reduce() {
                Some(reduced_function) => Some(Rc::new(ExpressionNode::Application {
                    function: reduced_function,
                    argument: Rc::clone(argument),
                })),
                None => argument.eta_reduce().map(|reduced_argument| {
                    Rc::new(ExpressionNode::Application {
                        function: Rc::clone(function),
                        argument: reduced_argument,
                    })
                }),
            },
            ExpressionNode::Abstraction { parameter, body } => {
                if let ExpressionNode::Application { function, argument } = body.as_ref() {
                    if let ExpressionNode::BoundVariable(db_index) = argument.as_ref() {
                        if *db_index == 1 {
                            return function.shift_for_eta_if_independent(1);
                        }
                    }
                }
                body.eta_reduce().map(|reduced_body| {
                    Rc::new(ExpressionNode::Abstraction {
                        parameter: parameter.clone(),
                        body: reduced_body,
                    })
                })
            }
        }
    }

    /// Returns an appropriately shifted expression for eta reduction if the
    /// given expression (`self`) is independent of it's parent abstraction,
    /// else returns [None]
    fn shift_for_eta_if_independent(
        self: &Rc<Self>,
        relative_lambda_depth: usize,
    ) -> Option<Rc<ExpressionNode>> {
        match self.as_ref() {
            ExpressionNode::FreeVariable(_) => Some(Rc::clone(self)),
            ExpressionNode::BoundVariable(db_index) => match db_index.cmp(&relative_lambda_depth) {
                std::cmp::Ordering::Less => Some(Rc::clone(&self)),
                std::cmp::Ordering::Equal => None,
                std::cmp::Ordering::Greater => {
                    Some(Rc::new(ExpressionNode::BoundVariable(db_index - 1)))
                }
            },
            ExpressionNode::Application { function, argument } => {
                match function.shift_for_eta_if_independent(relative_lambda_depth) {
                    Some(reduced_function) => argument
                        .shift_for_eta_if_independent(relative_lambda_depth)
                        .map(|reduced_argument| {
                            Rc::new(ExpressionNode::Application {
                                function: reduced_function,
                                argument: reduced_argument,
                            })
                        }),
                    None => None,
                }
            }
            ExpressionNode::Abstraction { parameter, body } => body
                .shift_for_eta_if_independent(relative_lambda_depth + 1)
                .map(|shifted_body| {
                    Rc::new(ExpressionNode::Abstraction {
                        parameter: parameter.clone(),
                        body: shifted_body,
                    })
                }),
        }
    }
}

impl fmt::Debug for ExpressionNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ExpressionNode: {}", self.to_expression_str_de_brujin())
    }
}

/// Equality (`==`) for `Expr` tests alpha-equivalence. So differences in the `parameter` of [ExpressionNode::Abstraction] is ignored.
///
/// Since `Expr` uses De Bruijn indices, this corresponds to structural comparison modulo variable renaming
impl PartialEq for ExpressionNode {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::FreeVariable(l0), Self::FreeVariable(r0)) => l0 == r0,
            (Self::BoundVariable(l0), Self::BoundVariable(r0)) => l0 == r0,
            (
                Self::Application {
                    function: l_function,
                    argument: l_argument,
                },
                Self::Application {
                    function: r_function,
                    argument: r_argument,
                },
            ) => l_function == r_function && l_argument == r_argument,
            (
                Self::Abstraction {
                    parameter: _,
                    body: l_body,
                },
                Self::Abstraction {
                    parameter: _,
                    body: r_body,
                },
            ) => l_body == r_body,
            _ => false,
        }
    }
}

impl Eq for ExpressionNode {}

enum ArgDbiShifterState {
    Unknown,
    NoBoundVariables,
    HasBoundVariables {
        relative_idx_to_shifted_tree: HashMap<usize, Rc<ExpressionNode>>,
    },
}

/// Argument "DBI" (De Brujin Index) Shifter
///
/// To shift the "DBI" of externally bound variables in an argument. See more
/// about externally bound variables in the documentation of
/// [search_exbv_and_shift]
struct ArgDbiShifter<'a> {
    target_node: &'a Rc<ExpressionNode>,
    state: ArgDbiShifterState,
}

impl<'a> ArgDbiShifter<'a> {
    fn new(target_node: &'a Rc<ExpressionNode>) -> Self {
        Self {
            target_node,
            state: ArgDbiShifterState::Unknown,
        }
    }

    fn shift(&mut self, current_relative_lambda_depth: usize) -> Rc<ExpressionNode> {
        debug_assert!(current_relative_lambda_depth != 0, "Relative index is zero");
        match &mut self.state {
            ArgDbiShifterState::Unknown => {
                if current_relative_lambda_depth == 1 {
                    Rc::clone(self.target_node)
                } else {
                    match search_exbv_and_shift(self.target_node, current_relative_lambda_depth, 0)
                    {
                        Some(shifted_tree) => {
                            let mut map = HashMap::new();
                            map.insert(current_relative_lambda_depth, Rc::clone(&shifted_tree));
                            self.state = ArgDbiShifterState::HasBoundVariables {
                                relative_idx_to_shifted_tree: map,
                            };
                            shifted_tree
                        }
                        None => {
                            self.state = ArgDbiShifterState::NoBoundVariables;
                            Rc::clone(self.target_node)
                        }
                    }
                }
            }
            ArgDbiShifterState::NoBoundVariables => Rc::clone(self.target_node),
            ArgDbiShifterState::HasBoundVariables {
                relative_idx_to_shifted_tree,
            } => {
                let tree = relative_idx_to_shifted_tree.entry(current_relative_lambda_depth).or_insert_with(
                    || search_exbv_and_shift(
                        self.target_node,
                        current_relative_lambda_depth,
                        0
                    ).expect(
                        "DbIndexShifterState is set to HasBoundVariable but searching yielded no externally bound variables"
                    )
                );
                Rc::clone(tree)
            }
        }
    }
}

/// Search `exbv` ("externally bound variables") and shift the De Brujin's index
/// of each exbv relative to the lambda depth at the substitution site so that
/// the binding does not change.
///
/// A [ExpressionNode::BoundVariable] is externally bound if it's De Brujin's
/// index is greater than it's relative lambda depth (number of nested
/// abstractions it is contained in, relative to the given target node in
/// [Self::new])
///
/// ## Parameters:
/// * `node`: the node we are searching and shifting
/// * `rld_ss`: Relative lambda depth of substitution site inside the abstraction (inclusive of this abstraction). Equal to the De Brujin's index of the bound variable being substituted.
/// * `rld_node`: Relative lambda depth of node (the parameter to this function) inside the target node (argument expression)
///
/// ## Returns:
/// * Option:
///     * Some(tree): If the subtree did contain externally bound variables, an appropriately shifted tree is returned
///     * None: If the tree did not contain bound variables, `None` which means that the subtree should be placed 'as-is' at the substitution site
fn search_exbv_and_shift(
    node: &Rc<ExpressionNode>,
    rld_ss: usize,
    rld_node: usize,
) -> Option<Rc<ExpressionNode>> {
    debug_assert!(
        rld_ss != 0,
        "Unexpectedd value of rld_ss (Relative lambda depth of substitution site inside the abstraction being beta reduced). Substitution site must lie inside at least one abstraction."
    );
    debug_assert!(
        rld_ss != 1,
        "Shift and search called when the substitution site is under only one abstraction (the one it is being substituted into). No need for shifting."
    );
    match node.as_ref() {
        ExpressionNode::FreeVariable(_) => None,
        ExpressionNode::BoundVariable(db_idx) => {
            let is_externally_bound = *db_idx > rld_node;
            if is_externally_bound {
                Some(Rc::new(ExpressionNode::BoundVariable({
                    // how far externally bound this variable is? (i.e.
                    // this maps to which lambda abstraction, relative
                    // to the root of the target expressio
                    let externality_offset = *db_idx - rld_node;
                    // we need to shift by one less than the relative
                    // lambda depth of the expression being substituted
                    let shift_idx = rld_ss - 1;

                    externality_offset + shift_idx
                })))
            } else {
                None
            }
        }
        ExpressionNode::Application { function, argument } => {
            let shifted_function = search_exbv_and_shift(function, rld_ss, rld_node);
            let shifted_argument = search_exbv_and_shift(argument, rld_ss, rld_node);
            if shifted_function.is_some() || shifted_argument.is_some() {
                Some(Rc::new(ExpressionNode::Application {
                    function: shifted_function.unwrap_or_else(|| Rc::clone(function)),
                    argument: shifted_argument.unwrap_or_else(|| Rc::clone(argument)),
                }))
            } else {
                None
            }
        }
        ExpressionNode::Abstraction { parameter, body } => {
            search_exbv_and_shift(body, rld_ss, rld_node + 1).map(|shifted_body| {
                Rc::new(ExpressionNode::Abstraction {
                    parameter: parameter.clone(),
                    body: shifted_body,
                })
            })
        }
    }
}

#[cfg(test)]
mod test {
    use crate::ExpressionTree;

    use super::*;

    fn node_from_str(expression_str: &str) -> ExpressionNode {
        Rc::try_unwrap(
            ExpressionTree::from_line(expression_str)
                .expect("Should parse")
                .root,
        )
        .expect("Should have only one strong reference")
    }

    #[test]
    fn test_deep_cloning() {
        let node = ExpressionNode::Abstraction {
            parameter: String::from("a"),
            body: Rc::new(ExpressionNode::Abstraction {
                parameter: String::from("b"),
                body: Rc::new(ExpressionNode::FreeVariable(String::from("c"))),
            }),
        };
        let original = "λa.λb.c";
        let modified = "λa.λb.d";
        assert_eq!(
            node,
            node_from_str(original),
            "Node did not build correctly"
        );
        let mut node2 = node.clone();
        assert_eq!(node2, node_from_str(original), "Node changed on clone");
        if let ExpressionNode::Abstraction { parameter: _, body } = &mut node2 {
            if let ExpressionNode::Abstraction { parameter: _, body } = Rc::make_mut(body) {
                *body = Rc::new(ExpressionNode::FreeVariable(String::from("d")))
            }
        }
        assert_eq!(node, node_from_str(original), "Original node changed");
        assert_eq!(node2, node_from_str(modified), "Cloned node did not change");
    }

    #[test]
    fn substitution() {
        fn check_substitution(src: ExpressionNode, target_expr: &str, expected_expr: &str) {
            let target_expr_node = ExpressionTree::from_line(target_expr)
                .expect("Failed to parse target expression")
                .root;
            let substituted_exp = Rc::new(src).substitute(&target_expr_node);
            let expected = ExpressionTree::from_line(expected_expr)
                .expect("Failed to parse expected expression")
                .root;
            assert_eq!(
                substituted_exp, expected,
                "Substituted expression incorrect"
            );
        }
        check_substitution(
            ExpressionNode::Application {
                function: Rc::new(ExpressionNode::Abstraction {
                    parameter: String::from("a"),
                    body: Rc::new(ExpressionNode::BoundVariable(2)),
                }),
                argument: Rc::new(ExpressionNode::FreeVariable(String::from("c"))),
            },
            "x y",
            "((λa.x y) c)",
        );
        check_substitution(
            ExpressionNode::Application {
                function: Rc::new(ExpressionNode::Abstraction {
                    parameter: String::from("a"),
                    body: Rc::new(ExpressionNode::BoundVariable(2)),
                }),
                argument: Rc::new(ExpressionNode::Abstraction {
                    parameter: String::from("c"),
                    body: Rc::new(ExpressionNode::FreeVariable(String::from("d"))),
                }),
            },
            "λd.c",
            "(λa.λd.c) (λc.d)",
        );
    }

    #[test]
    fn rc_clones() {
        let mut node1 = ExpressionTree::from_line("(λa.(a a) (a a)) b")
            .expect("Failed to parse tree")
            .root;
        while let Some(exp) = node1.search_and_beta_reduce() {
            node1 = exp
        }
        if let ExpressionNode::Application {
            function,
            argument: _,
        } = node1.as_ref()
        {
            if let ExpressionNode::Application {
                function,
                argument: _,
            } = function.as_ref()
            {
                if let ExpressionNode::FreeVariable(name) = function.as_ref() {
                    assert_eq!(name, "b", "Unexpected variable name")
                } else {
                    panic!("ExpressionNode is not a free variable")
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
