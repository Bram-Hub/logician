# The Logician

This program will take as input a Boolean expression and then attempt to
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
./target/release/logician simplify "~(A & B) | B"
```

## Decision

This method can also be used as a pseudo decision algorithm. It might be able to
prove an argument (but not disprove one). It can do this by taking the conjunct
of all the premises along with the negation of the conclusion, then trying to
simplify that long expression. If the argument is valid, the expression should
eventually simplify to a contradiction. If the argument is invalid, it will fail
to derive a contradiction. However, failure to simplify is not proof that the
argument is invalid. It may also be the case that it is beyond the capabilities
of the program to simplify to that degree. This algorithm is capable of deciding
most simple arguments.

To decide an argument, use the following

``` sh
./target/release/logician decide argument.txt
```

Where the last line of argument.txt is the conclusion, and all preceding lines
are the premises.


## The Algorithm

There are known methods to simplify Boolean expressions when the end form is
restricted (for example to sum of products or product of sums) such as the
Karnaugh map method or its n-variable generalization, the Quine-McCluskey
algorithm. It seems there are no known methods to guarantee finding the simplest
form with no restrictions. To deal with this, we use a randomized algorithm to
derive a good solution in most cases. Specifically, we perform simulated
annealing upon the expression and mutate it using Boolean equivalence rules.
