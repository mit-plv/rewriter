Rewriter
=====

Building
-----
[![Build Status](https://travis-ci.com/mit-plv/rewriter.svg?branch=master)](https://travis-ci.com/mit-plv/rewriter)

This repository requires Coq 8.9 or later, and requires that the version of OCaml used to build Coq be installed and accessible on the system.

Git submodules are used for some dependencies. If you did not clone with `--recursive`, run

    git submodule update --init --recursive

To build:

    make

Usage
-----

The entry point is [`src/Rewriter/Util/plugins/RewriterBuild.v`](./src/Rewriter/Util/plugins/RewriterBuild.v).
(Better entry point coming in the future.)
There are some examples in [`src/Rewriter/Rewriter/Examples.v`](./src/Rewriter/Rewriter/Examples.v).

The examples from the paper are in [`src/Rewriter/Rewriter/Examples/PerfTesting/`](./src/Rewriter/Rewriter/Examples/PerfTesting/).
On the branch with performance data, the `perf-*.txt` files in the top-level directory contain selected performance data in two-column format, while the `perf*.csv` files contain all performance data in CSV format.
The logs with raw timing data live in the subdirectories of [`src/Rewriter/Rewriter/Examples/PerfTesting/`](./src/Rewriter/Rewriter/Examples/PerfTesting/), and were made with the targets `perf-SuperFast`, `perf-Fast`, and `perf-Medium` targets.
The text and csv files were generated with `make perf-csv`.
(The targets `perf-Slow` and `perf-VerySlow` exist but take a very, very, very long time to run.)

Reading The Code
----------------

### Actual Synthesis Pipeline

The entry point for clients of the PHOAS expressions we use is
`Language/API.v`.  Refer to comments in that file for an explanation
of the interface; the following text describes how the expressions are
generated, not how to interact with them.

The ordering of files (eliding `*Proofs.v` files) is:

```
Language/*.v
    ↑
Rewriter/*.v
```

Within each directory, the dependency graphs (again eliding `*Proofs.v` and related files) are:

Within `Language/`:
```
  PreCommon.v ←─────────── Pre.v
    ↑                        ↑
Language.v ←── IdentifiersBasicLibrary.v ←──── IdentifiersBasicGenerate.v
    ↑                        ↑
    ├────────────────┐       └────────────────────────────┐
UnderLets.v    IdentifiersLibrary.v ←──────────── IdentifiersGenerate.v
                     ↑                                       ↑
              IdentifiersLibraryProofs.v ←─── IdentifiersGenerateProofs.v
```

We will come back to the `Rewriter/*` files shortly.

The files contain:

- `Rewriter/*.v`: rewrite rules, rewriting.

- Inside `Language/`:

  + `PreCommon.v`: A few definitions which are used in writing out
    rewrite rules and the interpretations of PHOAS identifiers, e.g.,
    `ident.cast`, `ident.eagerly`, etc.

  + `Pre.v`: A few definitions which are used in writing out rewrite
    rules, which are not used in the parameterized rewriter, only in
    reifying rewrite rules.

  + `Language.v`: Defines parts of the PHOAS basic infrastructure
        parameterized over base types and identifiers including:
    . PHOAS
    . reification
    . denotation/intepretation
    . utilities for inverting PHOAS exprs
    . default/dummy values of PHOAS exprs
    . default instantiation of generic PHOAS types
    . gallina reification of ground terms
    . Flat/indexed syntax trees, and conversions to and from PHOAS

    Defines the passes:
    . ToFlat
    . FromFlat
    . GeneralizeVar

  + `IdentifiersBasicLibrary.v`: Defines the package type holding basic
    identifier definitions.

  + `IdentifiersBasicGenerate.v`: Defines the tactics that generate
    all of the identifier-list-specific definitions used by the PHOAS
    machinery, in addition to defining the tactics that do reification
    based on the generated package.

  + `UnderLets.v`: the UnderLets monad, a pass that does substitution
    of var-like things, a pass that inserts let-binders in the
    next-to-last line of code, substituting away var-like things (this
    is used to ensure that when we output C code, aliasing the input
    and the output arrays doesn't cause issues).
    Defines the passes:
    . SubstVar
    . SubstVarLike
    . SubstVarOrIdent

  The following files in `Language/` are used only by the rewriter:

  + `IdentifiersLibrary.v`: Some definitions about identifiers and
    pattern identifiers and raw identifiers.  Some of these
    definitions take generated definitions as arguments. Also defines
    a package record to hold all of the generated definitions.

  + `IdentifiersGenerate.v`: Tactics to generate definitions about
    untyped and pattern versions of identifiers for the rewriter.
    Culminates in a tactic which inhabits the package type defined in
    `IdentifiersLibrary.v`

  + `IdentifiersLibraryProofs.v`: proofs about definitions in
    IdentifiersLibrary.  Also defines a package to hold generated
    proofs that require destructing inductives not yet defined in this
    file.

  + `IdentifiersGenerateProofs.v`: tactics to prove lemmas to inhabit
    the package defined in `IdentifiersLibraryProofs.v`

The files defined in `Rewriter/` are split up into the following
dependency graph (including some files from `Language/` at the top):
```
IdentifiersLibrary.v ←───────────────────────── IdentifiersGenerate.v
    ↑ ↑                                                   ↑
    │ └──────────────── IdentifiersLibraryProofs.v ←──────┴─ IdentifiersGenerateProofs.v
    │                                     ↑
    │                                     │
    │                                     │
    │                                     │
    │                                     │
Rewriter.v ←────────────────────── ProofsCommon.v ←──────────────────── ProofsCommonTactics.v
    ↑                                 ↗        ↖                                ↑
Reify.v ←──────────────┐           Wf.v   InterpProofs.v                        │
                       │              ↖        ↗                                │
                       └──────────── AllTactics.v ──────────────────────────────┘
```

- `Rewriter.v`: Defines the rewriter machinery.  In particular, all of
  the rewriter definitions that have non-rewrite-rule-specific proofs
  about them are found in this file.

- `RewrierReify.v`: Defines reification of rewrite rules, continuing on
  from `Rewriter.v`, and culminates in the tactic
  `RewriteRules.Tactic.Build_RewriterT` and the tactic notation
  `make_Rewriter` which define a package of type
  `RewriteRules.GoalType.RewriterT`.  The `Build_*` tactic returns a
  `constr`, while the `make_*` tactic notation refines that `constr`
  in the goal.  Both tactics take two arguments: first a boolean
  `include_interp` which specifies whether (`true`) or not (`false`)
  to prefix the list of rewrite rules with the reduction-to-literal
  rewrite rules; and second a list of `bool * Prop` which is the list
  of rewrite rule types to reify, each paired with a boolean saying
  whether or not to try rewriting again in the output of the
  replacement for that rule.

- `ProofsCommon.v`: Defines the notion of interp-goodness and wf-goodness
  for rewrite rules, defines tactics to prove these notions, and
  contains a semi-arbitrary collection of proofs and definitions that
  are mostly shared between the wf proofs and the interp proofs.
  Importantly, this file defines everything needed to state and prove
  that specific rewrite rules are correct.  Additionally defines a
  package `RewriteRules.GoalType.VerifiedRewriter` which describes the
  type of the overall specialized rewriter together with its `Wf` and
  `Interp` proofs. (This package should perhaps move to another file?)

- `ProofsCommonTactics.v`: Defines the actual tactics used to prove that
  specific rewrite rules are correct, and to inhabit the packages
  defined in `ProofsCommon.v`.

- `Wf.v`: Proves wf-preservation of the generic rewriter,
  taking in wf-goodness of rewrite rules as a hypothesis.

- `InterpProofs.v`: Proves interp-correctness of the generic
  rewriter, taking in interp-goodness of rewrite rules as a
  hypothesis.

- `AllTactics.v`: Defines the tactic
  `RewriteRules.Tactic.make_rewriter` (and a similar tactic notation)
  which build the entire `VerifiedRewriter`.  They take in the
  `include_interp` as in `Rewriter.v` tactics, as well as an hlist of
  proofs of rewrite rules indexed over a `list (bool * Prop)` of
  rewrite rule types.  This is the primary interface for defining a
  rewriter from a list of rewrite rules.

Proofs files:
For `Language.v`, there is a semi-arbitrary split between two files
`Language.Inversion` and `Language.Wf`.
- `Inversion.v`:
  + classifies equality of type codes and exprs
  + type codes have decidable equality
  + correctness of the various type-transport definitions
  + correctness lemmas for the various `expr.invert_*` definitions
  + correctness lemmas for the various `reify_*` definitions in `Language.v`
  + `inversion_type`, which inverts equality of type codes
  + `type_beq_to_eq`, which converts boolean equality of types to
    Leibniz equality
  + `rewrite_type_transport_correct`, which rewrites with the
    correctness lemmas of the various type-transport definitions
  + `type.invert_one e` which does case analysis on any inductive type
     indexed over type codes, in a way that preserves information
     about the type of `e`, and generally works even when the goal is
     dependently typed over `e` and/or its type
  + `ident.invert`, which does case-anaylsis on idents whose type has
    structure (i.e., is not a var)
  + `ident.invert_match`, which does case-analysis on idents appearing as
    the discriminee of a `match` in the goal or in any hypothesis
  + `expr.invert`, which does case-anaylsis on exprs whose type has
    structure (i.e., is not a var)
  + `expr.invert_match`, which does case-analysis on exprs appearing as
    the discriminee of a `match` in the goal or in any hypothesis
  + `expr.invert_subst`, which does case-analysis on exprs which show up
    in hypotheses of the form `expr.invert_* _ = Some _`
  + `expr.inversion_expr`, which inverts equalities of exprs

- `Wf.v`: Depends on `Inversion.v`
  Defines:
  + expr.wf, expr.Wf, expr.wf3, expr.Wf3
  + GeneralizeVar.Flat.wf
  + `expr.inversion_wf` (and variants), which invert `wf` hypotheses
  + `expr.wf_t` (and variants wf_unsafe_t and wf_safe_t) which make
     progress on `wf` goals; `wf_safe_t` should never turn a provable
     goal into an unprovable one, while `wf_unsafe_t` might.
  + `expr.interp_t` (and variants), which should make progress on
    equivalence-of-interp hypotheses and goals, but is not used much
    (mainly because I forgot I had defined it)
  + `prove_Wf`, which proves wf goals on concrete syntax trees in a more
    optimized way than `repeat constructor`
  Proves:
  + funext → (type.eqv ↔ Logic.eq) (`eqv_iff_eq_of_funext`)
  + type.related and type.eqv are PERs
  + Proper instances for `type.app_curried`, `type.and_for_each_lhs_of_arrow`
  + `type.is_not_higher_order` → Reflexive (type.and_for_each_lhs_of_arrow type.eqv)
  + iff between `type.related{,_hetero}` and related of `type.app_curried`
  + various properties of `type.and{,b_bool}for_each_lhs_of_arrow`
  + various properties of `type.eqv` and `ident.{gen_,}interp`
  + various properties of `ident.cast`
  + various properties of `expr.wf` (particularly of things defined in `Language.v`)
  + interp and wf proofs for the passes to/from Flat

- `UnderLetsProofs.v`: wf and interp lemmas for the various passes defined in `UnderLets.v`
