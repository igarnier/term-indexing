# term-indexing

`term-indexing` provides facilities to perform term rewriting and term indexing.

Look no further for the [documentation](https://igarnier.github.io/term-indexing/term-indexing/index.html).

## Term indexing

The library implements [substitution trees](https://dl.acm.org/doi/10.5555/647194.720822), a data structure allowing to efficiently
store a set of first-order terms and perform the following queries:
- iterate on all terms unifiable with a given query term
- iterate on all terms generalizing a given query term
- iterate on all terms specializing a given query term

## Term rewriting

The library implements basic facilities to enumerate matches for given patterns
and perform substitutions. It also exposes facilities to solve unification problems.

## TODO

- Deletion operation on substitution trees
- Discrimination trees
