# The Logician

This program will take as input a boolean expression and then attempt to
simplify it as much as possible. That is, find a form with minimal tree nodes
(symbols excluding parentheses). No form restrictions (such as sum of products
form) are imposed on the output. Output will be printed to the terminal.

## Usage

*Build*

``` sh
cargo build --release
```

*Run*

``` sh
./target/release/logician "~(A & B) | B"
```

*Build & Run*

``` sh
cargo run --release -- "~(A & B) | B"
```

## The Algorithm

There are known methods to simplify boolean expressions when the end form is
restricted (for example to sum of products or product of sums) such as the
Karnaugh map method or its n-variable generalization, the Quine-McCluskey
algorithm. It seems there are no known methods to guarantee finding the simplest
form with no restructions. To deal with this, we use a randomized algorithm to
derive a good solution in most cases. Specifically, we perform simulated
annealing upon the expression and mutate it using boolean equivalence rules.
