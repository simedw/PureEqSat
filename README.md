# Equality Saturation

This work has been done for the course Frontiers of Programming
Languages during the month of September in 2010. It presents a novel way
of doing optimizations in the style of equality saturation. This explores
the space of equivalent terms to and the best i.e. the optimized term. In
d to other approaches all terms will be saved and can be used to and new equivalent terms.

## How to build

```
stack setup
stack build
```

## How to use

To try an example program to optimize first build the project and then run
```
stack exec -- PureEqSat -f examples/ex1.pes
```

To see the various flags PureEqSat accepts run the program with --help

**WORD OF CAUTION**: _ex6.pes_ and _ex7.pes_ are examples where the rule engine don't cut it.
Waiting for the results can lead to the end of the universe...

## Examples

```
stack exec -- PureEqSat -f ex1.pes
From: 0 + x
To : x

stack exec -- PureEqSat -f ex2.pes
From: x + y == y + x
To : True

stack exec -- PureEqSat -f ex3.pes
From: if v then x * (a + b) else x * a + x * b
To : x * (a + b)

stack exec -- PureEqSat -f ex4.pes
From: 45 * b + 19 * c + (12 * b + 15 * c)
To : b * 57 + c * 34

stack exec -- PureEqSat -f ex5.pes
From: x + y == z + x
To : y == z
```
