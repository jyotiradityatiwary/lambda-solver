# Lambda Solver

Untyped lambda calculus library.

## Features

- parsing string expression
  - handles associativity and precedence
  - auto converts numbers into church numerals and expands named aliases
- beta reduction
- eta reduction
- alpha equivalence tests
- string output (using retained variable names from input, or with De Brujin indices)
- named aliases for lambda expressions (with builtin defaults for standard logic and arithmetic operators)

## Documentation

Opens detailed API documentation with usage examples locally in a web browser
```sh
cargo doc --open
```

## Unit Tests

```sh
cargo test
```

## Todo

- Builtin aliases `PRED` and `SUB` do not work. corresponding failing unit tests - `alias::test::pred` and `alias::test::sub`
- Allow reversing expressions into aliases (Right now, we can only expand named aliases into full expression trees)
- Add usage examples to project level rustdoc
- Add an Iterator wrapper for `ExpressionTree::beta_reduce` and `ExpressionTree::eta_reduce`
