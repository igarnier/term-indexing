(lang dune 3.0)
(name term-indexing)
(version 0.0.1)
(generate_opam_files true)
(source (uri git+https://github.com/igarnier/term-indexing))
(bug_reports http://github.com/igarnier/term-indexing)
(homepage http://github.com/igarnier/term-indexing)
(authors "Ilias Garnier")
(maintainers "igarnier@protonmail.com")
(implicit_transitive_deps false)

(package
 (name term-indexing)
 (synopsis "Term indexing library")
 (description "A library for term indexing. It allows to represent set of first-order terms and to perform queries such as iterating on terms unifiable with, specializing or generalizing a given query term.")
 (license MIT)
 (tags (symbolics rewriting))
 (depends
  (ocaml (>= 4.14))
  (prbnmcn-cgrph (= 0.0.2))
  (hashcons (>= 1.4.0))
  (containers (>= 3.13.1))
  (printbox (>= 0.11))
  (printbox-text (>= 0.9.0))))
