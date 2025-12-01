use crate::ExpressionNode;

/// Returned when an error is encountered when trying to build a string expression from an expression tree
#[derive(Debug)]
pub enum ExpressionNodeStringifierError {
    /// The de brujin index of a bound variable was greater than or equal to the number of lambda abstractions it was nested in
    NegativeRelativeIndex,
    /// Trying to access lambda abstraction at a depth greater than has been parsed. Can happen if the de brujin index of a variable is zero
    OutOfBoundsRelativeIndex,
}

pub struct ExpressionNodeStringifier {
    /// index corresponds to lambda function depth, value corresponds to parameter name
    bound_variable_names: Vec<String>,
    string_expr: String,
}

impl ExpressionNodeStringifier {
    pub fn new() -> Self {
        Self {
            bound_variable_names: Vec::new(),
            string_expr: String::new(),
        }
    }

    fn stringify(
        &mut self,
        node: &ExpressionNode,
        lambda_depth: usize,
    ) -> Result<(), ExpressionNodeStringifierError> {
        match node {
            ExpressionNode::FreeVariable(name) => {
                self.string_expr.push_str(name);
                Ok(())
            }
            ExpressionNode::BoundVariable(idx) => {
                if lambda_depth < *idx {
                    Err(ExpressionNodeStringifierError::NegativeRelativeIndex)
                } else {
                    match &self.bound_variable_names.get(lambda_depth - idx) {
                        Some(name) => {
                            self.string_expr.push_str(name);
                            Ok(())
                        }
                        None => Err(ExpressionNodeStringifierError::OutOfBoundsRelativeIndex),
                    }
                }
            }
            ExpressionNode::Application { function, argument } => {
                self.string_expr.push('(');
                self.stringify(function, lambda_depth)?;
                self.string_expr.push(' ');
                self.stringify(argument, lambda_depth)?;
                self.string_expr.push(')');
                Ok(())
            }
            ExpressionNode::Abstraction { parameter, body } => {
                self.string_expr.push('(');
                self.string_expr.push_str(&parameter);
                self.string_expr.push('-');
                self.string_expr.push('>');
                self.bound_variable_names
                    .insert(lambda_depth, String::from(parameter));
                self.stringify(body, lambda_depth + 1)?;
                self.bound_variable_names.remove(lambda_depth);
                self.string_expr.push(')');
                Ok(())
            }
        }
    }

    pub fn build(
        mut self,
        node: &ExpressionNode,
    ) -> Result<String, ExpressionNodeStringifierError> {
        self.stringify(node, 0)?;
        Ok(self.string_expr)
    }
}

pub struct ExpNodeStringifierDeBrujin {
    string_expr: String,
}

impl ExpNodeStringifierDeBrujin {
    pub fn new() -> Self {
        Self {
            string_expr: String::new(),
        }
    }

    fn stringify(&mut self, node: &ExpressionNode) {
        match node {
            ExpressionNode::FreeVariable(name) => {
                self.string_expr.push_str(name);
            }
            ExpressionNode::BoundVariable(idx) => {
                self.string_expr.push('$');
                self.string_expr.push_str(&idx.to_string());
            }
            ExpressionNode::Application { function, argument } => {
                self.string_expr.push('(');
                self.stringify(function);
                self.string_expr.push(' ');
                self.stringify(argument);
                self.string_expr.push(')');
            }
            ExpressionNode::Abstraction { parameter: _, body } => {
                self.string_expr.push('(');
                self.string_expr.push('λ');
                self.string_expr.push(' ');
                self.stringify(body);
                self.string_expr.push(')');
            }
        }
    }

    pub fn build(mut self, node: &ExpressionNode) -> String {
        self.stringify(node);
        self.string_expr
    }
}
