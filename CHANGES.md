## 0.0.2
- add `Term.destruct2`
- add `Pattern.var_any`
- add `Zipper` module
- add `Unification.unfold`
- remove `Path` module, use `Zipper` instead where possible
- normalize `fold` signatures
- fast path for `Term.map_variables` on ground terms
- comment fixes
- move `Unification` out of `Subst` module

## 0.0.1
- First release of `term-indexing`, a library to index and rewrite sets of first-order terms.
