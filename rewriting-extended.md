# Rewriter

## Introduction

- The goal of the rewriter is to take an abstract syntax tree and perform reduction or rewriting.
- There are three things that happen in rewriting: beta reduction, let-lifting, and replacement of rewrite patterns with their substitutions
  - Beta reduction is replacing `(λ x. F) y` with `F[x ⇒ y]`.
    We do this with a normalization-by-evaluation strategy.
  - Let-lifting involves replacing `f (let x := y in z)` with `let x := y in f x`.
    Note that for higher-order functions, we push lets under lambads, rather than lifting them;
      we replace `f (let x := y in (λ z. w))` with `f (λ z. let x := y in w)`.
    This is done for the convenience of not having to track the let-binding-structure at every level of arrow.
  - Replacing rewriting patterns with substitutions involves, for example, replacing `x + 0` with `x`.
  - There's actually a fourth thing, which happens during let-lifting:
      some let binders get inlined:
      In particular, any let-bound value which is a combination of variables, literals, and the identifiers `nil`, `cons`, `pair`, `fst`, `snd`, `Z.opp`, `Z.cast`, and `Z.cast2` gets inlined.
    If the let-bound variable contains any lambdas, lets, or applications of identifiers other than the above, then it is not inlined.

## Beta-Reduction and Let-Lifting
- We use the following data-type:
  ```coq
  Fixpoint value' (with_lets : bool) (t : type)
    := match t with
       | type.base t
         => if with_lets then UnderLets (expr t) else expr t
       | type.arrow s d
         => value' false s -> value' true d
       end.
  Definition value := value' false.
  Definition value_with_lets := value' true.
  ```
- Here are some examples:
  - `value Z := UnderLets (expr Z)`
  - `value (Z -> Z) := expr Z -> UnderLets (expr Z)`
  - `value (Z -> Z -> Z) := expr Z -> expr Z -> UnderLets (expr Z)`
  - `value ((Z -> Z) -> Z) := (expr Z -> UnderLets (expr Z)) -> UnderLets (expr Z)`
- By converting expressions to values and using normalization-by-evaluation, we get beta reduction in the standard way.
- We use a couple of splicing combinators to perform let-lifting:
  - `Fixpoint splice {A B} (x : UnderLets A) (e : A -> UnderLets B) : UnderLets B`
  - `Fixpoint splice_list {A B} (ls : list (UnderLets A)) (e : list A -> UnderLets B) : UnderLets B`
  - `Fixpoint splice_under_lets_with_value {T t} (x : UnderLets T) : (T -> value_with_lets t) -> value_with_lets t`
  - `Definition splice_value_with_lets {t t'} : value_with_lets t -> (value t -> value_with_lets t') -> value_with_lets t'`
- There's one additional building block, which is responsible for deciding which lets to inline:
  - `Fixpoint reify_and_let_binds_base_cps {t : base.type} : expr t -> forall T, (expr t -> UnderLets T) -> UnderLets T`
- As is typical for NBE, we make use of a reify-reflect pair of functions:
  ```coq
  Fixpoint reify {with_lets} {t} : value' with_lets t -> expr t
  with reflect {with_lets} {t} : expr t -> value' with_lets t
  ```
- The NBE part of the rewriter, responsible for beta reduction and let-lifting, is now expressible:
  ```coq
  Local Notation "e <---- e' ; f" := (splice_value_with_lets e' (fun e => f%under_lets)) : under_lets_scope.
  Local Notation "e <----- e' ; f" := (splice_under_lets_with_value e' (fun e => f%under_lets)) : under_lets_scope.

  Fixpoint rewrite_bottomup {t} (e : @expr value t) : value_with_lets t
    := match e with
       | expr.Ident t idc
         => rewrite_head _ idc
       | expr.App s d f x => let f : value s -> value_with_lets d := @rewrite_bottomup _ f in x <---- @rewrite_bottomup _ x; f x
       | expr.LetIn A B x f => x <---- @rewrite_bottomup A x;
                                 xv <----- reify_and_let_binds_cps x _ UnderLets.Base;
                                 @rewrite_bottomup B (f (reflect xv))
       | expr.Var t v => Base_value v
       | expr.Abs s d f => fun x : value s => @rewrite_bottomup d (f x)
       end%under_lets.
  ```

## Rewriting
### There are three parts and one additional detail to rewriting:
- Pattern matching compilation
- Decision tree evaluation
- Rewriting with a particular rewrite rule
- Rewriting again in the output of a rewrite rule

### Overview
- Rewrite rules are patterns (things like `?? + #?` meaning "any variable added to any literal") paired with dependently typed replacement values indexed over the pattern.
  The replacement value takes in types for each type variable, `value`s for each variable (`??`), and interpreted values for each literal wildcard.
  Additionally, any identifier that takes extra parameters will result in the parameters being passed into the rewrite rule.
  The return type for replacement values is an option UnderLets expr of the correct type.
- A list of rewrite rules is compiled into (a) a decision tree, and (b) a rewriter that functions by evaluating that decision tree.

### The small extra detail: Rewriting again in the output of a rewrite rule
- We tie the entire rewriter together with a fueled repeat_rewrite;
   the fuel is set to the length of the list of rewrite rules.
  This means that as long as the intended rewrite sequences form a DAG, then the rewriter will find all occurrences.
  ```coq
  Notation nbe := (@rewrite_bottomup (fun t idc => reflect (expr.Ident idc))).

  Fixpoint repeat_rewrite
           (rewrite_head : forall (do_again : forall t : base.type, @expr value (type.base t) -> UnderLets (@expr var (type.base t)))
                                      t (idc : ident t), value_with_lets t)
           (fuel : nat) {t} e : value_with_lets t
    := @rewrite_bottomup
         (rewrite_head
            (fun t' e'
             => match fuel with
                | Datatypes.O => nbe e'
                | Datatypes.S fuel' => @repeat_rewrite rewrite_head fuel' (type.base t') e'
                end%under_lets))
         t e.
  ```
- This feature is used to rewrite again with the literal-list append rule (appending two lists of cons cells results in a single list of cons cells) in the output of the `flat_map` rule (`flat_map` on a literal list of cons cells maps the function over the list and joins the resulting lists with `List.app`).

### Pattern matching compilation
- This part of the rewriter does not need to be verified, because the rewriter-compiler is proven correct independent of the decision tree used.
  Note that we could avoid this stage all together, and simply try each rewrite rule in sequence.
  We include this for efficiency.
  TODO: perf comparison of this method.
- We follow *Compiling Pattern Matching to Good Decision Trees* by Luc Maranget (http://moscova.inria.fr/~maranget/papers/ml05e-maranget.pdf), which describes compilation of pattern matches in OCaml to a decision tree that eliminates needless repeated work (for example, decomposing an expression into `x + y + z` only once even if two different rules match on that pattern).
- We do *not* bother implementing the optimizations that they describe for finding minimal decision trees.
  TODO: Mention something about future work?  Perf testing?
- The type of decision trees
  - A `decision_tree` describes how to match a vector (or list) of patterns against a vector of expressions. The cases of a `decision_tree` are:
    - `TryLeaf k onfailure`: Try the kth rewrite rule; if it fails, keep going with `onfailure`
    - `Failure`: Abort; nothing left to try
    - `Switch icases app_case default`: With the first element of the vector, match on its kind; if it is an identifier matching something in `icases`, remove the first element of the vector run that decision tree; if it is an application and `app_case` is not `None`, try the `app_case` decision_tree, replacing the first element of each vector with the two elements of the function and the argument its applied to; otherwise, don't modify the vectors, and use the `default` decision tree.
    - `Swap i cont`: Swap the first element of the vector with the ith element, and keep going with `cont`
  - The inductive type:
    ```coq
    Inductive decision_tree :=
    | TryLeaf (k : nat) (onfailure : decision_tree)
    | Failure
    | Switch (icases : list (raw_pident * decision_tree))
             (app_case : option decision_tree)
             (default : decision_tree)
    | Swap (i : nat) (cont : decision_tree).
    ```
- Raw identifiers
  - Note that the type of `icases`, the list of identifier cases in the `Switch` constructor above, maps what we call a `raw_pident` ("p" for "pattern") to a decision tree.  The rewriter is parameterized over a type of `raw_pident`s, which is instantiated with a python-generated inductive type which names all of the identifiers we care about, except without any arguments.  We call them "raw" because they are not type-indexed.
  - An example where this is important: We want to be able to express a decision tree for the pattern `fst (x, y)`.  This involves an application of the identifier `fst` to a pair.  We want to be able to talk about "`fst`, of any type" in the decision tree, without needing to list out all of the possible type arguments to `fst`.
- Swap vs indices
  - One design decision we copy from *Compiling Pattern Matching to Good Decision Trees* is to have a `Swap` case.  We could instead augment each `Switch` with the index in the vector being examined.  If we did this, we'd need to talk about splicing a new list into the middle of an existing list, which is harder than talking about swapping two indices of a list.
  - Note that swapping is *significantly* more painful over typed patterns and terms than over untyped ones.  If we index our vectors over a list of types, then we need to swap the types, and later swap them back (when reconstructing the term for evaluation), and then we need to unswap the terms in a way that has unswap (swap ls) on the term level *judgmentally* indexed on the type level over the same index-list as ls.  This is painful, and is an example of pain caused by picking the wrong abstraction, in a way that causes exponential blow-up with each extra layer of dependency added.
- The type of patterns
  - Patterns describe the LHS of rewrite rules, or the LHS of cases of a match statement.  We index patterns over their type:
    ```coq
    Inductive pattern.base.type := var (p : positive) | type_base (t : Compilers.base.type.base) | prod (A B : type) | list (A : type).
    ```
  - The type of a pattern is either an arrow or a pattern.base.type, and a pattern.base.type is either a positive-indexed type-variable (written '1, '2, ...), or a product, a list, or a standard base.type (with no type-variables)
  - A pattern is either a wildcard, an identifier, or an application of patterns.  Note that our rewriter only handles fully applied patterns, i.e., only things of type `pattern (type.base t)`, not things of type `pattern t`.  (This is not actually true.  The rewriter can kind-of handle non-fully-applied patterns, but the Gallina won't reduce in the right places, so we restrict ourselves to fully-applied patterns.)
    ```coq
    Inductive pattern {ident : type -> Type} : type -> Type :=
    | Wildcard (t : type) : pattern t
    | Ident {t} (idc : ident t) : pattern t
    | App {s d} (f : pattern (s -> d)) (x : pattern s) : pattern d.
    ```
  - Pattern matching *compilation* to decision trees actually uses a more raw version of patterns, which come from these patterns:
    ```coq
    Module Raw.
      Inductive pattern {ident : Type} :=
      | Wildcard
      | Ident (idc : ident)
      | App (f x : pattern).
    End Raw.
    ```
    - This is because the pattern matching compilation algorithm is morally done over untyped patterns and terms.
- The definitions
  - TODO: How much detail should I include about intermediate things?
  - Pattern matching compilation at the top-level, takes in a list of patterns, and spits out a decision tree.  Note that each `TryLeaf` node in the decision tree has an index `k`, which denotes the index in this initial list of patterns of the chosen rewrite rule.
  - The workhorse of pattern matching compilation is `Fixpoint compile_rewrites' (fuel : nat) (pattern_matrix : list (nat * list rawpattern)) : option decision_tree`.  This takes the list rows of the matrix of patterns, each one containing a list (vector in the original source paper) of patterns to match against, and the original index of the rewrite rule that this list of patterns came from.  Note that all of these lists are in fact the same length, but we do not track this invariant anywhere, because it would add additional overhead for little-to-no gain.
    - The `compile_rewrites'` procedure operates as follows:
      - If we are out of fuel, then we fail (return `None`)
      - If the `pattern_matrix` is empty, we indicate `Failure` to match
      - If the first row is made up entirely of wildcards, we indicate to `TryLeaf` with the rewrite rule corresponding to the first row, and then to continue on with the decision tree corresponding to the rest of the rows.
      - If the first element of the first row is a wildcard, we `Swap` the first element with the index `i` of the first non-wildcard pattern in the first row.  We then swap the first element with the `i`th element in every row of the matrix, and continue on with the result of compiling that matrix.
      - If the first element of the first row is not a wildcard, we issue a `Switch`.  We first split the pattern matrix by finding the first row where the first element in that row is a wildcard, and aggregating that row and all rows after it into the `default_pattern_matrix`.  We partition the rows before that row into the ones where the first element is an application node and the ones where the first element is an identifier node.  The application nodes get split into the pattern for the function, and the pattern for the argument, and these two are prepended to the row.  We group the rows that start with identifier patterns into groups according to the pattern identifier at the beginning of the row, and then take the tail of each of these rows.  We then compile all of these decision trees to make up the Switch case.
      - In code, this looks like:
        ```coq
        Definition compile_rewrites_step
                   (compile_rewrites : list (nat * list rawpattern) -> option decision_tree)
                   (pattern_matrix : list (nat * list rawpattern))
          : option decision_tree
          := match pattern_matrix with
             | nil => Some Failure
             | (n1, p1) :: ps
               => match get_index_of_first_non_wildcard p1 with
                 | None (* p1 is all wildcards *)
                   => (onfailure <- compile_rewrites ps;
                        Some (TryLeaf n1 onfailure))
                 | Some Datatypes.O
                   => let '(pattern_matrix, default_pattern_matrix) := split_at_first_pattern_wildcard pattern_matrix in
                      default_case <- compile_rewrites default_pattern_matrix;
                        app_case <- (if contains_pattern_app pattern_matrix
                                     then option_map Some (compile_rewrites (Option.List.map filter_pattern_app pattern_matrix))
                                     else Some None);
                        let pidcs := get_unique_pattern_ident pattern_matrix in
                        let icases := Option.List.map
                                        (fun pidc => option_map (pair pidc) (compile_rewrites (Option.List.map (filter_pattern_pident pidc) pattern_matrix)))
                                        pidcs in
                        Some (Switch icases app_case default_case)
                 | Some i
                   => let pattern_matrix'
                         := List.map
                              (fun '(n, ps)
                               => (n,
                                  match swap_list 0 i ps with
                                  | Some ps' => ps'
                                  | None => nil (* should be impossible *)
                                  end))
                              pattern_matrix in
                     d <- compile_rewrites pattern_matrix';
                       Some (Swap i d)
                 end
             end%option.
        ```
    - We wrap `compile_rewrites'` in a definition `compile_rewrites` which extracts the well-typed patterns from a list of rewrite rules, associates them to indices, and strips the typing information off of the patterns to create raw (untyped) patterns.

### Decision Tree Evaluation
- The next step in rewriting is to evaluate the decision tree to construct Gallina procedure that takes in an unknown (at rewrite-rule-compile-time) AST and performs the rewrite.  This is broken up into two steps.  The first step is to create the `match` structure that exposes all of the relevant information in the AST, and picks which rewrite rules to try in which order, and glues together failure and success of rewriting.  The second step is to actually try to rewrite with a given rule, under the assumption that enough structure has been exposed.
- Because we have multiple phases of compilation, we need to track which information we have (and therefore can perform reduction on) when we know only the patterns but not the AST being rewritten in, and which reductions have to wait until we know the AST.  The way we track this information is by creating a wrapper type for ASTs.  Note that the wrapper type is not indexed over type codes, because pattern matching compilation naturally operates over untyped terms, and adjusting it to work when indexed over a vector of types is painful.
- The wrapper type, and revealing structure
  - Because different rewrite rules require different amounts of structure, we want to feed in only as much structure as is required for a given rewrite rule.  For example, if we have one rewrite rule that is looking at `(? + ?) + ?`, and another that is looking at `? + 0`, we want to feed in the argument to the top-level `+` into the second rewrite rule, not a reassembled version of all of the different things an expression might be after checking for `+`-like structure of the first argument.  If we did not do this, every rewrite rule replacement pattern would end up being as complicated as the deepest rewrite rule being considered, and we expect this would incur performance overhead.  TODO: Perf testing?
  - Because we want our rewrite-rule-compilation to happen by reduction in Coq, we define many operations in CPS-style, so that we can carefully manage the exact judgmental structures of the discriminees of `match` statements.
  - An `Inductive rawexpr : Type` is one of the following things:
    ```coq
    Inductive rawexpr : Type :=
    | rIdent (known : bool) {t} (idc : ident t) {t'} (alt : expr t')
    | rApp (f x : rawexpr) {t} (alt : expr t)
    | rExpr {t} (e : expr t)
    | rValue {t} (e : value t).
    ```
    - `rIdent known t idc t' alt` - an identifier `idc : ident t`, whose unrevealed structure is `alt : expr t'`.  The boolean `known` indicates if the identifier is known to be simple enough that we can fully reduce matching on its type arguments during rewrite-rule-compilation-time.  For example, if we know an identifier to be `Z.add` (perhaps because we have matched on it already), we can reduce equality tests against the type.  However, if an identifier is `nil T`, we are not guaranteed to know the type of the list judgmentally, and so we do not want to reduce type-equality tests against the list.  Note that type-equality tests and type-transports are introduced as the least-evil thing we could find to cross the broken abstraction barrier between the untyped terms of pattern matching compilation, and the typed PHOASTs that we are operating on.
    - `rApp f x t alt` is the application of the `rawexpr` `f` to the `rawexpr` `x`, whose unrevealed structure is `alt : expr t`.
    - `rExpr t e` is a not-as-yet revealed expression `e : expr t`.
    - `rValue t e` is an unrevealed value `e : value t`.  Such NBE-style values may contain thunked computation, such as deferred rewriting opportunities.  This is essential for fully evaluating rewriting in expressions such as `map (fun x => x + x + 0) ls`, where you want to rewrite away the `map` (when `ls` is a concrete list of cons cells), the `+ 0` (always), and the `x + x` whenever `x` is a literal (which you do not know until you have distributed the function over the list).  Allowing thunked computation in the ASTs allows us to do all of this rewriting in a single pass.
  - Revealing structure: `Definition reveal_rawexpr_cps (e : rawexpr) : ~> rawexpr`
    - For the sake of proofs, we actually define a slightly more general version of revealing structure, which allows us to specify whether or not we have already matched against the putative identifier at the top-level of the `rawexpr`.
    - The code:
      ```coq
      Definition reveal_rawexpr_cps_gen (assume_known : option bool)
                 (e : rawexpr) : ~> rawexpr
        := fun T k
           => match e, assume_known with
              | rExpr _ e as r, _
              | rValue (type.base _) e as r, _
                => match e with
                   | expr.Ident t idc => k (rIdent (match assume_known with Some known => known | _ => false end) idc e)
                   | expr.App s d f x => k (rApp (rExpr f) (rExpr x) e)
                   | _ => k r
                   end
              | rIdent _ t idc t' alt, Some known => k (rIdent known idc alt)
              | e', _ => k e'
              end.
      ```
    - To reveal a `rawexpr`, CPS-style, we first match on the `rawexpr`.
      - If it is an `rExpr`, or a `rValue` at a base type (and thus just an expression), we then match on the resulting expression.
        - If it is an identifier or an application node, we encode that, and then invoke the continuation
        - Otherwise, we invoke the continuation with the existing `rExpr` or `rValue`, because there was no more accessible structure to reveal; we do not allow matching on lambdas syntactically.
      - If it is an identifier and we are hard-coding the `known` status about if matches on the type of the identifier can be reduced, then we re-assemble the `rIdent` node with the new `known` status and invoke the continuation.
      - Otherwise, we just invoke the continuation on the reassembled `rawexpr`.
    - Correctness conditions
      - There are a couple of properties that must hold of `reveal_rawexpr_cps`.
      - The first is a `cps_id` rule, which says that applying `reveal_rawexpr_cps` to any continuation is the same as invoking the continuation with `reveal_rawexpr_cps` applied to the identity continuation.
      - The next rule talks about a property we call `rawexpr_types_ok`.  To say that this property holds is to say that the `rawexper`s are well-typed in accordance with the unrevealed expressions stored in the tree.
        - Code:
          ```coq
          Fixpoint rawexpr_types_ok (r : @rawexpr var) (t : type) : Prop
            := match r with
               | rExpr t' _
               | rValue t' _
                 => t' = t
               | rIdent _ t1 _ t2 _
                 => t1 = t /\ t2 = t
               | rApp f x t' alt
                 => t' = t
                    /\ match alt with
                       | expr.App s d _ _
                         => rawexpr_types_ok f (type.arrow s d)
                            /\ rawexpr_types_ok x s
                       | _ => False
                       end
               end.
          ```
        - We must then have that a `rawexpr` is `rawexpr_types_ok` if and only if the result of revealing one layer of structure via `reveal_rawexpr_cps` is `rawexpr_types_ok`.
      - We also define a relation `rawexpr_equiv` which says that two `rawexpr`s represent the same expression, up to different amounts of revealed structure.
        - Code:
          ```coq
          Local Notation "e1 === e2" := (existT expr _ e1 = existT expr _ e2) : type_scope.

          Fixpoint rawexpr_equiv_expr {t0} (e1 : expr t0) (r2 : rawexpr) {struct r2} : Prop
            := match r2 with
               | rIdent _ t idc t' alt
                 => alt === e1 /\ expr.Ident idc === e1
               | rApp f x t alt
                 => alt === e1
                    /\ match e1 with
                       | expr.App _ _ f' x'
                         => rawexpr_equiv_expr f' f /\ rawexpr_equiv_expr x' x
                       | _ => False
                       end
               | rExpr t e
               | rValue (type.base t) e
                 => e === e1
               | rValue t e => False
               end.

          Fixpoint rawexpr_equiv (r1 r2 : rawexpr) : Prop
            := match r1, r2 with
               | rExpr t e, r
               | r, rExpr t e
               | rValue (type.base t) e, r
               | r, rValue (type.base t) e
                 => rawexpr_equiv_expr e r
               | rValue t1 e1, rValue t2 e2
                 => existT _ t1 e1 = existT _ t2 e2
               | rIdent _ t1 idc1 t'1 alt1, rIdent _ t2 idc2 t'2 alt2
                 => alt1 === alt2
                    /\ (existT ident _ idc1 = existT ident _ idc2)
               | rApp f1 x1 t1 alt1, rApp f2 x2 t2 alt2
                 => alt1 === alt2
                    /\ rawexpr_equiv f1 f2
                    /\ rawexpr_equiv x1 x2
               | rValue _ _, _
               | rIdent _ _ _ _ _, _
               | rApp _ _ _ _, _
                 => False
               end.
          ```
        - The relation `rawexpr_equiv` is effectively the recursive closure of `reveal_rawexpr_cps`, and we must prove that `reveal_rawexpr e` and `e` are `rawexpr_equiv`.
      <!---
      - Finally, we define a notation of `wf` for `rawexpr`s called `wf_rawexpr`, and we prove that if two `rawexpr`s are `wf_rawexpr`-related, then the results of calling `reveal_rawexpr` on both of them are `wf_rawexpr`-related.
        - The definition of `wf_rawexpr` is:
          ```coq
          Inductive wf_rawexpr : list { t : type & var1 t * var2 t }%type -> forall {t}, @rawexpr var1 -> @expr var1 t -> @rawexpr var2 -> @expr var2 t -> Prop :=
          | Wf_rIdent {t} G known (idc : ident t) : wf_rawexpr G (rIdent known idc (expr.Ident idc)) (expr.Ident idc) (rIdent known idc (expr.Ident idc)) (expr.Ident idc)
          | Wf_rApp {s d} G
                    f1 (f1e : @expr var1 (s -> d)) x1 (x1e : @expr var1 s)
                    f2 (f2e : @expr var2 (s -> d)) x2 (x2e : @expr var2 s)
            : wf_rawexpr G f1 f1e f2 f2e
              -> wf_rawexpr G x1 x1e x2 x2e
              -> wf_rawexpr G
                            (rApp f1 x1 (expr.App f1e x1e)) (expr.App f1e x1e)
                            (rApp f2 x2 (expr.App f2e x2e)) (expr.App f2e x2e)
          | Wf_rExpr {t} G (e1 e2 : expr t)
            : expr.wf G e1 e2 -> wf_rawexpr G (rExpr e1) e1 (rExpr e2) e2
          | Wf_rValue {t} G (v1 v2 : value t)
            : wf_value G v1 v2
              -> wf_rawexpr G (rValue v1) (reify v1) (rValue v2) (reify v2).
          ```
          --->
- Evaluating the decision tree
  - Decision tree evaluation is performed by a single monolithic recursive function: `Fixpoint eval_decision_tree {T} (ctx : list rawexpr) (d : decision_tree) (cont : nat -> list rawexpr -> option T) {struct d} : option T`
    ```coq
    Fixpoint eval_decision_tree {T} (ctx : list rawexpr) (d : decision_tree) (cont : nat -> list rawexpr -> option T) {struct d} : option T
      := match d with
         | TryLeaf k onfailure
           => let res := cont k ctx in
              match onfailure with
              | Failure => res
              | _ => res ;; (@eval_decision_tree T ctx onfailure cont)
              end
         | Failure => None
         | Switch icases app_case default_case
           => match ctx with
              | nil => None
              | ctx0 :: ctx'
                => let res
                       := reveal_rawexpr_cps
                            ctx0 _
                            (fun ctx0'
                             => match ctx0' with
                                | rIdent known t idc t' alt
                                  => fold_right
                                       (fun '(pidc, icase) rest
                                        => let res
                                               := if known
                                                  then
                                                    (args <- invert_bind_args _ idc pidc;
                                                       @eval_decision_tree
                                                         T ctx' icase
                                                         (fun k ctx''
                                                          => cont k (rIdent
                                                                       (raw_pident_is_simple pidc)
                                                                       (raw_pident_to_typed pidc args) alt :: ctx'')))
                                                  else
                                                    @eval_decision_tree
                                                      T ctx' icase
                                                      (fun k ctx''
                                                       => option_bind'
                                                            (invert_bind_args_unknown _ idc pidc)
                                                            (fun args
                                                             => cont k (rIdent
                                                                          (raw_pident_is_simple pidc)
                                                                          (raw_pident_to_typed pidc args) alt :: ctx'')))
                                           in
                                           match rest with
                                           | None => Some res
                                           | Some rest => Some (res ;; rest)
                                           end)
                                       None
                                       icases;;;
                                       None
                                | rApp f x t alt
                                  => match app_case with
                                     | Some app_case
                                       => @eval_decision_tree
                                            T (f :: x :: ctx') app_case
                                            (fun k ctx''
                                             => match ctx'' with
                                                | f' :: x' :: ctx'''
                                                  => cont k (rApp f' x' alt :: ctx''')
                                                | _ => None
                                                end)
                                     | None => None
                                     end
                                | rExpr t e
                                | rValue t e
                                  => None
                                end) in
                   match default_case with
                   | Failure => res
                   | _ => res ;; (@eval_decision_tree T ctx default_case cont)
                   end
              end
         | Swap i d'
           => match swap_list 0 i ctx with
              | Some ctx'
                => @eval_decision_tree
                     T ctx' d'
                     (fun k ctx''
                      => match swap_list 0 i ctx'' with
                         | Some ctx''' => cont k ctx'''
                         | None => None
                         end)
              | None => None
              end
         end%option.
    ```
  - This function takes a list (vector in the original source paper) `ctx` of `rawexpr`s to match against, a `decision_tree` `d` to evaluate, and a "continuation" `cont` which tries a given rewrite rule based on the index of the rewrite rule (in the original list of rewrite rules) and the list of `rawexpr`s to feed into the rewrite rule.  This continuation is threaded through the decision tree evaluation procedure, and each time we split up the structure of the pattern matrix (virtually, in the decision tree) and the list of `rawexpr`s (concretely, as an argument), we add a bit to the continuation that "undoes" the splitting.  In the end, the top-level "continuation" gets fed a singleton list containing a `rawexpr` with enough structure for the rewrite rule it is trying.  TODO: Figure out how to be more clear here; I anticipate this is unclear, and I'm not sure how to fix it except by randomly throwing more sentences in to try to explain it in various different ways.
  - Correctness conditions
    - There are two correctness conditions for `eval_decision_tree`: one for `wf`, and the other for `Interp`.
      - The interpretation-correctness rule says that either `eval_decision_tree` returns `None`, or it returns the result of calling the continuation on some index and with some list of `rawexpr`s which is element-wise `rawexpr_equiv` to the input list.  In other words, `eval_decision_tree` does nothing more than revealing some structure, and then eventually calling the continuation (which is to be filled in with "rewrite with this rule") on the revealed `rawexpr`.
    - The `wf` correctness condition is significantly more verbose to state, but it boils down to saying that as long as the continuation behaves "the same" (for some parameterized notion of "the same") on `wf_rawexpr`-related `rawexpr`s, then `eval_decision_tree` will similarly behave "the same" on element-wise `wf_rawexpr`-related lists of `rawexpr`s.
      <!---
      - TODO: Decide whether or not to include code:
        ```coq
        Lemma wf_eval_decision_tree {T1 T2} G d (P : option T1 -> option T2 -> Prop) (HPNone : P None None)
          : forall (ctx1 : list (@rawexpr var1))
                   (ctx2 : list (@rawexpr var2))
                   (ctxe : list { t : type & @expr var1 t * @expr var2 t }%type)
                   (Hctx1 : length ctx1 = length ctxe)
                   (Hctx2 : length ctx2 = length ctxe)
                   (Hwf : forall t re1 e1 re2 e2,
                       List.In ((re1, re2), existT _ t (e1, e2)) (List.combine (List.combine ctx1 ctx2) ctxe)
                       -> @wf_rawexpr G t re1 e1 re2 e2)
                   cont1 cont2
                   (Hcont : forall n ls1 ls2,
                       length ls1 = length ctxe
                       -> length ls2 = length ctxe
                       -> (forall t re1 e1 re2 e2,
                              List.In ((re1, re2), existT _ t (e1, e2)) (List.combine (List.combine ls1 ls2) ctxe)
                              -> @wf_rawexpr G t re1 e1 re2 e2)
                       -> (cont1 n ls1 = None <-> cont2 n ls2 = None)
                          /\ P (cont1 n ls1) (cont2 n ls2)),
            P (@eval_decision_tree var1 T1 ctx1 d cont1) (@eval_decision_tree var2 T2 ctx2 d cont2).
        ```
        --->
  - Definition
    - The `eval_decision_tree` procedure proceeds recursively on the structure of the `decision_tree`.
      - If the decision tree is a `TryLeaf k onfailure`, then we try the continuation on the `k`th rewrite rule.  If it fails (by returning `None`), we proceed with `onfailure`.  In the code, there is a bit of extra care taken to simplify the resulting output code when `onfailure` is just `Failure`, i.e., no remaining matches to try.  This probably does not impact performance, but it makes the output of the rewrite-rule-compilation procedure slightly easier to read and debug.
      - If the decision tree is `Failure` return `None`, i.e., we did not succeed in rewriting.
      - If the decision tree starts with `Swap i d'`, we swap the first element with the `i`th element in the list of `rawexpr`s we are matching on (to mirror the swapping in the pattern matrix that happened when compiling the decision tree), and then continue on evaluating `d'`.  We augment the continuation by reversing the swap in the list of `rawexpr`s passed in at the beginning, to cancel out the swap we did "on the outside" before continuing with evaluation of the decision tree.  Note that here we are jumping through some extra hoops to get the right reduction behavior at rewrite-rule-compilation time.
      - If none of the above match, the decision tree must begin with `Switch icases app_case default_case`.  In this case, we start by revealing the structure of the first element of the list of `rawexpr`s.  (If there is no first element, which should never happen, we indicate failure by returning `None`.)  In the continuation of `reveal_rawexpr_cps`, we check which sort of `rawexpr` we have.  Note that in all cases of failure below, we try again with the `default_case`.
        - If we have no accessible structure (`rExpr` or `rValue`), then we fail with `None`.
        - If we have an application, we take the two arguments of `rApp`, the function and its argument, and prepend them to the tail of the list of `rawexpr`s.  We then continue evaluation with `app_case` (if it is non-`None`), and, in the continuation, we reassemble the `rawexpr` by taking the first two elements of the passed-in-list, and combining them in a new `rApp` node.  We keep the unrevealed structure in `alt` the same as it was in the `rApp` that we started with.
        - If we have an identifier, then we look at `icases`.  We fold through the list of identifiers, looking to see if any of them match the identifier that we have.  If the identifier is `known`, then we perform the match before evaluating the corresponding decision tree, because we want to avoid revealing useless structure.  If the identifier is not `known`, then first we reveal all of the necessary structure for this identifier by continuing decision tree evaluation, and only then in the continuation do we try to match against the identifier.
          - In both cases, we drop the first element of the list of `rawexpr`s being matched against when continuing evaluation, to mirror the dropping that happens in compilation of the decision tree.  We then prepend a re-built identifier onto the head of the list inside the continuation.  We have a table of which pattern identifiers have `known` types, and we have conversion functions between pattern identifiers and PHOAST identifiers (autogenerated in Python) which allow us to extract the arguments from the PHOAST identifier and re-insert them into the pattern identifier.  For example, this will extract the list type from `nil` (because the pattern-identifier version does not specify what the type of the list is---we will say more about this in the next section), or the literal value from the `Literal` identifier, and allow recreating the fully-typed identifier from the pattern-identifier with these arguments.  This allows more rewriter-compile-time reduction opportunities which allows us to deduplicate matches against the same identifier.  Note that we have two different constants that we use for binding these arguments; they do the same thing, but one is reduced away completely at rewrite-rule-compilation time, and the other is preserved.

### Rewriting with a particular rewrite rule
- The final big piece of the rewriter is to rewrite with a particular rule, given a `rawexpr` with enough revealed structure, a `pattern` against which we bind arguments, and a replacement rule which is a function indexed over the `pattern`.  We saw above the inductive type of patterns.  Let us now discuss the structure of the replacement rules.
- Replacement rule types
  - The data for a replacement rule is indexed over a pattern-type `t` and a `p : pattern t`.  It has three options, in addition to the actual replacement rule:
    ```coq
    Record rewrite_rule_data {t} {p : pattern t} :=
      { rew_should_do_again : bool;
        rew_with_opt : bool;
        rew_under_lets : bool;
        rew_replacement : @with_unif_rewrite_ruleTP_gen value t p rew_should_do_again rew_with_opt rew_under_lets }.
    ```
    - `rew_should_do_again` determines whether or not to rewrite again in the output of this rewrite rule.  For example, the rewrite rule for `flat_map` on a concrete list of cons cells maps the function over the list, and joins the resulting list of lists with append.  We want to rewrite again with the rule for `List.app` in the output of this replacement.
    - `rew_with_opt` determines whether or not the rewrite rule might fail.  For example, rewrite rules like `x + 0 ~> x` are encoded by talking about the pattern of a wildcard added to a literal, and say that the rewrite only succeeds if the literal is 0.  Additionally, as another example, all rewrite rules involving casts fail if bounds on the input do not line up; in the pattern `Z.cast @ ((Z.cast @ ??) + (Z.cast @ ??))` the cast node in front of an addition must be loose enough to hold the sum of the ranges taken from the two cast nodes in front of each of the wildcards.
    - `rew_under_lets` determines whether or not the replacement rule returns an explicit `UnderLets` structure.  This can be used for let-binding a part of the replacement value.
  - The rewrite rule replacement itself is a function.  It takes in first all type variables which are mentioned in the pattern, and then, in an in-order traversal of the pattern syntax tree, the non-type arguments for each identifier (e.g., interpreted values of literals, ranges of cast nodes) and a `value (pattern.type.subst_default t evm)` for each wildcard of type `t` (that is, we plug in the known type variables into the pattern-type, and use `unit` for any unknown type variables).  It may return a thing in the `option` and/or `UnderLets` monads, depending on `rew_with_opt` and `rew_under_lets`.  Underneath these possible monads, it returns an `expr` of the correct type (we substitute the type variables we take in into the type of the pattern), whose `var` type is either `@value var` (if `rew_should_do_again`) or `var` (if not `rew_should_do_again`).  The different `var` types are primarily to make the type of the output of the rewrite rule line up with the expression type that is fed into the rewriter as a whole.  We have a number of definitions that describe this in a dependently typed mess:
    - We aggregate the type variables into a `PositiveSet.t` with `Fixpoint pattern.base.collect_vars (t : base.type) : PositiveSet.t` and `Fixpoint pattern.type.collect_vars (t : type) : PositiveSet.t`:
      ```coq
      Module base.
        Fixpoint collect_vars (t : type) : PositiveSet.t
          := match t with
             | type.var p => PositiveSet.add p PositiveSet.empty
             | type.type_base t => PositiveSet.empty
             | type.prod A B => PositiveSet.union (collect_vars A) (collect_vars B)
             | type.list A => collect_vars A
             end.
      End base.
      Module type.
          Fixpoint collect_vars (t : type) : PositiveSet.t
            := match t with
               | type.base t => base.collect_vars t
               | type.arrow s d => PositiveSet.union (collect_vars s) (collect_vars d)
               end.
      End type.
      ```
    - We quantify over type variables for each of the numbers in the `PositiveSet.t` and aggregate the bound types into a `PositiveMap.t` with `pattern.type.forall_vars`.  Note that we use the possibly ill-chosen abbreviation `EvarMap` for `PositiveMap.t Compilers.base.type`.
      ```coq
      Local Notation forall_vars_body K LS EVM0
        := (fold_right
              (fun i k evm => forall t : Compilers.base.type, k (PositiveMap.add i t evm))
              K
              LS
              EVM0).

      Definition forall_vars (p : PositiveSet.t) (k : EvarMap -> Type)
        := forall_vars_body k (List.rev (PositiveSet.elements p)) (PositiveMap.empty _).
      ```
    - We take in the context variable `pident_arg_types : forall t, pident t -> list Type` which describes the arguments bound for a given pattern identifier.
    - We then quantify over identifier arguments and wildcard values with `with_unification_resultT`:
      ```coq
      Local Notation type_of_list_cps
        := (fold_right (fun a K => a -> K)).

      Fixpoint with_unification_resultT' {var} {t} (p : pattern t) (evm : EvarMap) (K : Type) : Type
        := match p return Type with
           | pattern.Wildcard t => var (pattern.type.subst_default t evm) -> K
           | pattern.Ident t idc => type_of_list_cps K (pident_arg_types t idc)
           | pattern.App s d f x
             => @with_unification_resultT' var _ f evm (@with_unification_resultT' var _ x evm K)
           end%type.

      Definition with_unification_resultT {var t} (p : pattern t) (K : type -> Type) : Type
        := pattern.type.forall_vars
             (@pattern.collect_vars _ t p)
             (fun evm => @with_unification_resultT' var t p evm (K (pattern.type.subst_default t evm))).
      ```
    - Finally, we can define the type of rewrite replacement rules:
      ```coq
      Local Notation deep_rewrite_ruleTP_gen' should_do_again with_opt under_lets t
        := (match (@expr.expr base.type ident (if should_do_again then value else var) t) with
            | x0 => match (if under_lets then UnderLets x0 else x0) with
                    | x1 => if with_opt then option x1 else x1
                    end
            end).

      Definition deep_rewrite_ruleTP_gen (should_do_again : bool) (with_opt : bool) (under_lets : bool) t
        := deep_rewrite_ruleTP_gen' should_do_again with_opt under_lets t.

      Definition with_unif_rewrite_ruleTP_gen {var t} (p : pattern t) (should_do_again : bool) (with_opt : bool) (under_lets : bool)
        := @with_unification_resultT var t p (fun t => deep_rewrite_ruleTP_gen' should_do_again with_opt under_lets t).
      ```
      Whence we have
      ```coq
      rew_replacement : @with_unif_rewrite_ruleTP_gen value t p rew_should_do_again rew_with_opt rew_under_lets
      ```
- There are two steps to rewriting with a rule, both conceptually simple but in practice complicated by dependent types.  We must unify a pattern with an expression, gathering binding data for the replacement rule as we go; and we must apply the replacement rule to the binding data (which is non-trivial because the rewrite rules are expressed as curried dependently-typed towers indexed over the rewrite rule pattern).  In order to state the correctness conditions for gathering binding data, we must first talk about applying replacement rules to binding data.
- Applying binding data
  - The general strategy for applying binding data is to define an uncurried package (sigma type, or dependent pair) holding all of the arguments, and to define an application function that applies the replacement rule (at various stages of construction) to the binding data package.
  - The uncurried package types
    - To turn a list of Types into a Type, we define `Local Notation type_of_list := (fold_right (fun a b => prod a b) unit)`.
    - The type `unification_resultT'` describes the binding data for a pattern, given a map of pattern type variables to types:
      ```coq
      Fixpoint unification_resultT' {var} {t} (p : pattern t) (evm : EvarMap) : Type
        := match p return Type with
           | pattern.Wildcard t => var (pattern.type.subst_default t evm)
           | pattern.Ident t idc => type_of_list (pident_arg_types t idc)
           | pattern.App s d f x
             => @unification_resultT' var _ f evm * @unification_resultT' var _ x evm
           end%type.
      ```
    - A `unification_resultT` packages up the type variable replacement map with the bound values:
      ```coq
      Definition unification_resultT {var t} (p : pattern t) : Type
        := { evm : EvarMap & @unification_resultT' var t p evm }.
      ```
  - The application functions
    - The definition `app_type_of_list` applies a CPS-type `type_of_list_cps` function to uncurried arguments:
      ```coq
      Definition app_type_of_list {K} {ls : list Type} (f : type_of_list_cps K ls) (args : type_of_list ls) : K
        := list_rect
             (fun ls
              => type_of_list_cps K ls -> type_of_list ls -> K)
             (fun v _ => v)
             (fun T Ts rec f x
              => rec (f (fst x)) (snd x))
             ls
             f args.
      ```
    - Given two different maps of type variables (another instance of abstraction-barrier-breaking), we can apply a `with_unification_resultT'` to a `unification_resultT'` by inserting casts in the appropriate places:
      ```coq
      (** TODO: Maybe have a fancier version of this that doesn't
           actually need to insert casts, by doing a fixpoint on the
           list of elements / the evar map *)
      Fixpoint app_transport_with_unification_resultT'_cps {var t p evm1 evm2 K} {struct p}
        : @with_unification_resultT' var t p evm1 K -> @unification_resultT' var t p evm2 -> forall T, (K -> option T) -> option T
        := fun f x T k
           => match p return with_unification_resultT' p evm1 K -> unification_resultT' p evm2 -> option T with
              | pattern.Wildcard t
                => fun f x
                   => (tr <- type.try_make_transport_cps base.try_make_transport_cps var _ _;
                         (tr <- tr;
                            k (f (tr x)))%option)%cps
           | pattern.Ident t idc => fun f x => k (app_type_of_list f x)
           | pattern.App s d f x
             => fun F (xy : unification_resultT' f _ * unification_resultT' x _)
                => @app_transport_with_unification_resultT'_cps
                     _ _ f _ _ _ F (fst xy) T
                     (fun F'
                      => @app_transport_with_unification_resultT'_cps
                           _ _ x _ _ _ F' (snd xy) T
                           (fun x' => k x'))
           end%option f x.
      ```
    - We can apply a `forall_vars` tower over the type variables in a pattern to a particular mapping of type variables to types, with a headache of dependently typed code:
      ```coq
      Fixpoint app_forall_vars_gen {k : EvarMap -> Type}
                 (evm : EvarMap)
                 (ls : list PositiveMap.key)
        : forall evm0, forall_vars_body k ls evm0
                       -> option (k (fold_right (fun i k evm'
                                                 => k (match PositiveMap.find i evm with Some v => PositiveMap.add i v evm' | None => evm' end))
                                                (fun evm => evm)
                                                ls
                                                evm0))
        := match ls return forall evm0, forall_vars_body k ls evm0
                                        -> option (k (fold_right (fun i k evm'
                                                                  => k (match PositiveMap.find i evm with Some v => PositiveMap.add i v evm' | None => evm' end))
                                                                 (fun evm => evm)
                                                                 ls
                                                                 evm0)) with
           | nil => fun evm0 val => Some val
           | cons x xs
             => match PositiveMap.find x evm as xt
                      return (forall evm0,
                                 (forall t, fold_right _ k xs (PositiveMap.add x t evm0))
                                 -> option (k (fold_right
                                                 _ _ xs
                                                 match xt with
                                                 | Some v => PositiveMap.add x v evm0
                                                 | None => evm0
                                                 end)))
                with
                | Some v => fun evm0 val => @app_forall_vars_gen k evm xs _ (val v)
                | None => fun evm0 val => None
                end
           end.

      Definition app_forall_vars {p : PositiveSet.t} {k : EvarMap -> Type}
                 (f : forall_vars p k)
                 (evm : EvarMap)
        : option (k (fold_right (fun i k evm'
                                 => k (match PositiveMap.find i evm with Some v => PositiveMap.add i v evm' | None => evm' end))
                                (fun evm => evm)
                                (List.rev (PositiveSet.elements p))
                                (PositiveMap.empty _)))
        := @app_forall_vars_gen
             k evm
             (List.rev (PositiveSet.elements p))
             (PositiveMap.empty _)
             f.
      ```
    - Finally, we can apply a `with_unification_resultT` to a `unification_resultT` package in the obvious way, inserting casts as needed:
      ```coq
      Definition app_with_unification_resultT_cps {var t p K}
        : @with_unification_resultT var t p K -> @unification_resultT var t p -> forall T, ({ evm' : _ & K (pattern.type.subst_default t evm') } -> option T) -> option T
        := fun f x T k
           => (f' <- pattern.type.app_forall_vars f (projT1 x);
                 app_transport_with_unification_resultT'_cps
                   f' (projT2 x) _
                   (fun fx
                    => k (existT _ _ fx)))%option.
      ```
- Unifying patterns with expressions
  - First, we unify the types, in continuation-passing-style, returning an optional `PositiveMap.t` from type variable indices to types.
    - This is actually done in two steps, so that rewrite-rule-compilation can reduce away all occurrences of patterns.  First, we check that the expression has the right structure, and extract all of the relevant types both from the pattern and from the expression.  Then we connect the types with `type.arrow` (used simply for convenience, so we don't have to unify lists of types, only individual types), and we unify the two resulting types, extracting a `PositiveMap.t` describing the assignments resulting from the unification problem.
      - We first define a few helper definitions that should be self-explanatory:
        - The function `type_of_rawexpr` gets the type of a `rawexpr`:
          ```coq
          Definition type_of_rawexpr (e : rawexpr) : type
            := match e with
               | rIdent _ t idc t' alt => t'
               | rApp f x t alt => t
               | rExpr t e => t
               | rValue t e => t
               end.
          ```
        - The functions `pattern.base.relax` and `pattern.type.relax` take a PHOAST type and turn it into a pattern type, which just happens to have no pattern type variables.
          ```
          Module base.
            Fixpoint relax (t : Compilers.base.type) : type
              := match t with
                 | Compilers.base.type.type_base t => type.type_base t
                 | Compilers.base.type.prod A B => type.prod (relax A) (relax B)
                 | Compilers.base.type.list A => type.list (relax A)
                 end.
          End base.
          Module type.
            Fixpoint relax (t : type.type Compilers.base.type) : type
              := match t with
                 | type.base t => type.base (base.relax t)
                 | type.arrow s d => type.arrow (relax s) (relax d)
                 end.
          End type.
          ```
      - The function responsible for checking the structure of patterns and extracting the types to be unified is `preunify_types {t} (e : rawexpr) (p : pattern t) :  option (option (ptype * type))`.  It will return `None` if the structure does not match, `Some None` if the type of an identifier of known type in the `rawexpr` does not match the type of the identifier in the pattern (which is guaranteed to always be known, and thus this comparison is safe to perform at rewriter-rule-compilation time), and will return `Some (Some (t1, t2))` if the structures match, where `t1` and `t2` are the types to be unified.
        ```coq
        Fixpoint preunify_types {t} (e : rawexpr) (p : pattern t) {struct p}
          : option (option (ptype * type))
          := match p, e with
             | pattern.Wildcard t, _
               => Some (Some (t, type_of_rawexpr e))
             | pattern.Ident pt pidc, rIdent known t idc _ _
               => if andb known (type.type_beq _ pattern.base.type.type_beq pt (pattern.type.relax t)) (* relies on evaluating to `false` if `known` is `false` *)
                  then Some None
                  else Some (Some (pt, t))
             | pattern.App s d pf px, rApp f x _ _
               => (resa <- @preunify_types _ f pf;
                     resb <- @preunify_types _ x px;
                     Some match resa, resb with
                          | None, None => None
                          | None, Some t
                          | Some t, None => Some t
                          | Some (a, a'), Some (b, b')
                            => Some (type.arrow a b, type.arrow a' b')
                          end)
             | pattern.Ident _ _, _
             | pattern.App _ _ _ _, _
               => None
             end%option.
        ```
      - We have two correctness conditions on `preunify_types`.
        - The `wf` correctness condition says that if two `rawexpr`s are `wf_rawexpr`-related, then the result of pre-unifying one of them with a pattern `p` is the same as the result of pre-unifying the other with the same pattern `p`.
        - Second, for interpretation-correctness, we define a recursive proposition encoding the well-matching of patterns with `rawexpr`s under a given map of pattern type variables to types:
          ```coq
          Fixpoint types_match_with (evm : EvarMap) {t} (e : rawexpr) (p : pattern t) {struct p} : Prop
            := match p, e with
               | pattern.Wildcard t, e
                 => pattern.type.subst t evm = Some (type_of_rawexpr e)
               | pattern.Ident t idc, rIdent known t' _ _ _
                 => pattern.type.subst t evm = Some t'
               | pattern.App s d f x, rApp f' x' _ _
                 => @types_match_with evm _ f' f
                    /\ @types_match_with evm _ x' x
               | pattern.Ident _ _, _
               | pattern.App _ _ _ _, _
                 => False
               end.
          ```
        - Then we prove that for any map `evm` of pattern type variables to types, if `preunify_types re p` returns `Some (Some (pt, t'))`, and the result of substituting into `pt` the pattern type variables in the given map is `t'`, then `types_match_with evm re p` holds.  Symbolically, this is
          ```coq
          Lemma preunify_types_to_match_with {t re p evm}
            : match @preunify_types ident var pident t re p with
              | Some None => True
              | Some (Some (pt, t')) => pattern.type.subst pt evm = Some t'
              | None => False
              end
              -> types_match_with evm re p.
          ```
      - In a possibly-gratuitous use of dependent typing to ensure that no uses of `PositiveMap.t` remain after rewrite-rule-compilation, we define a dependently typed data structure indexed over the pattern type which holds the mapping of each pattern type variable to a corresponding type.  This step cannot be fully reduced at rewrite-rule-compilation time, because we may not know enough type structure in the `rawexpr`.  We then collect these variables into a `PositiveMap.t`; this step *can* be fully reduced at rewrite-rule-compilation time, because the pattern always has a well-defined type structure, and so we know *which* type variables will have assignments in the `PositiveMap.t`, even if we don't necessarily know concretely (at rewrite-rule-compilation time) *what* those type variables will be assigned to.  We must also add a final check that substituting into the pattern type according the resulting `PositiveMap.t` actually does give the expected type; we do not want `'1 -> '1` and `nat -> bool` to unify.  We could check at each addition to the `PositiveMap.t` that we are not replacing one type with a different type.  However, the proofs are much simpler if we simply do a wholesale check at the very end.  We eventually perform this check in `unify_types`.
        - We thus define the dependently typed structures:
          ```
          Module base.
            Fixpoint var_types_of (t : type) : Set
              := match t with
                 | type.var _ => Compilers.base.type
                 | type.type_base _ => unit
                 | type.prod A B => var_types_of A * var_types_of B
                 | type.list A => var_types_of A
                 end%type.

            Fixpoint add_var_types_cps {t : type} (v : var_types_of t) (evm : EvarMap) : ~> EvarMap
              := fun T k
                 => match t return var_types_of t -> T with
                    | type.var p
                      => fun t => k (PositiveMap.add p t evm)
                    | type.prod A B
                      => fun '(a, b) => @add_var_types_cps A a evm _ (fun evm => @add_var_types_cps B b evm _ k)
                    | type.list A => fun t => @add_var_types_cps A t evm _ k
                    | type.type_base _ => fun _ => k evm
                    end v.
          End base.
          Module type.
            Fixpoint var_types_of (t : type) : Set
              := match t with
                 | type.base t => base.var_types_of t
                 | type.arrow s d => var_types_of s * var_types_of d
                 end%type.

            Fixpoint add_var_types_cps {t : type} (v : var_types_of t) (evm : EvarMap) : ~> EvarMap
              := fun T k
                 => match t return var_types_of t -> T with
                    | type.base t => fun v => @base.add_var_types_cps t v evm _ k
                    | type.arrow A B
                      => fun '(a, b) => @add_var_types_cps A a evm _ (fun evm => @add_var_types_cps B b evm _ k)
                    end v.
          End type.
          ```
        - We can now write down the unifier that produces `var_types_of` from a unification problem; it is straightforward:
          ```
          Module base.
            Fixpoint unify_extracted
                     (ptype : type) (etype : Compilers.base.type)
              : option (var_types_of ptype)
              := match ptype, etype return option (var_types_of ptype) with
                 | type.var p, _ => Some etype
                 | type.type_base t, Compilers.base.type.type_base t'
                   => if base.type.base_beq t t'
                      then Some tt
                      else None
                 | type.prod A B, Compilers.base.type.prod A' B'
                   => a <- unify_extracted A A';
                        b <- unify_extracted B B';
                        Some (a, b)
                 | type.list A, Compilers.base.type.list A'
                   => unify_extracted A A'
                 | type.type_base _, _
                 | type.prod _ _, _
                 | type.list _, _
                   => None
                 end%option.
          End base.
          Module type.
            Fixpoint unify_extracted
                     (ptype : type) (etype : type.type Compilers.base.type)
              : option (var_types_of ptype)
              := match ptype, etype return option (var_types_of ptype) with
                 | type.base t, type.base t'
                   => base.unify_extracted t t'
                 | type.arrow A B, type.arrow A' B'
                   => a <- unify_extracted A A';
                        b <- unify_extracted B B';
                        Some (a, b)
                 | type.base _, _
                 | type.arrow _ _, _
                   => None
                 end%option.
          End type.
          ```
      - Finally, we can write down the type-unifier for patterns and `rawexpr`s.  Note that the final equality check, described and motivated above, is performed in this function.
        ```coq
        (* for unfolding help *)
        Definition option_type_type_beq := option_beq (type.type_beq _ base.type.type_beq).

        Definition unify_types {t} (e : rawexpr) (p : pattern t) : ~> option EvarMap
          := fun T k
             => match preunify_types e p with
                | Some (Some (pt, t))
                  => match pattern.type.unify_extracted pt t with
                     | Some vars
                       => pattern.type.add_var_types_cps
                            vars (PositiveMap.empty _) _
                            (fun evm
                             => (* there might be multiple type variables which map to incompatible types; we check for that here *)
                               if option_type_type_beq (pattern.type.subst pt evm) (Some t)
                               then k (Some evm)
                               else k None)
                     | None => k None
                     end
                | Some None
                  => k (Some (PositiveMap.empty _))
                | None => k None
                end.
        ```
  - Now that we have unified the types and gotten a `PositiveMap.t` of pattern type variables to types, we are ready to unify the patterns, and extract the identifier arguments and `value`s from the `rawexpr`.  Because it would be entirely too painful to track at the type-level that the type unifier guarantees a match on structure and types, we instead sprinkle type transports all over this definition to get the types to line up.  Here we pay the price of an imperfect abstraction barrier (that we have types lying around, and we rely in some places on types lining up, but do not track everywhere that types line up).  Most of the other complications in this function come from (a) working in continuation-passing-style (for getting the right reduction behavior) or (b) tracking the differences between things we can reduce at rewrite-rule-compilation time, and things we can't.
    - We first describe some helper definitions and context variables.
      - The context variable `pident_arg_types : forall t, pident t -> list Type` describes for each pattern identifier what arguments should be bound for it.
      - The context variables `(pident_unify pident_unify_unknown : forall t t' (idc : pident t) (idc' : ident t'), option (type_of_list (pident_arg_types t idc)))` are the to-be-unfolded and not-to-be-unfolded versions of unifying a pattern identifier with a PHOAST identifier.
      - We can convert a `rawexpr` into a `value` or an `expr`:
        ```coq
        Definition expr_of_rawexpr (e : rawexpr) : expr (type_of_rawexpr e)
          := match e with
             | rIdent _ t idc t' alt => alt
             | rApp f x t alt => alt
             | rExpr t e => e
             | rValue t e => reify e
             end.
        Definition value_of_rawexpr (e : rawexpr) : value (type_of_rawexpr e)
          := Eval cbv `expr_of_rawexpr` in
              match e with
              | rValue t e => e
              | e => reflect (expr_of_rawexpr e)
              end.
        ```
    - We can now write down the pattern-expression-unifier:
      ```coq
      Definition option_bind' {A B} := @Option.bind A B. (* for help with unfolding *)

      Fixpoint unify_pattern' {t} (e : rawexpr) (p : pattern t) (evm : EvarMap) {struct p}
        : forall T, (unification_resultT' p evm -> option T) -> option T
        := match p, e return forall T, (unification_resultT' p evm -> option T) -> option T with
           | pattern.Wildcard t', _
             => fun T k
                => (tro <- type.try_make_transport_cps (@base.try_make_transport_cps) value (type_of_rawexpr e) (pattern.type.subst_default t' evm);
                      (tr <- tro;
                         _ <- pattern.type.subst t' evm; (* ensure that we did not fall into the default case *)
                         (k (tr (value_of_rawexpr e))))%option)%cps
           | pattern.Ident t pidc, rIdent known _ idc _ _
             => fun T k
                => (if known
                    then Option.bind (pident_unify _ _ pidc idc)
                    else option_bind' (pident_unify_unknown _ _ pidc idc))
                     k
           | pattern.App s d pf px, rApp f x _ _
             => fun T k
                => @unify_pattern'
                     _ f pf evm T
                     (fun fv
                      => @unify_pattern'
                           _ x px evm T
                           (fun xv
                            => k (fv, xv)))
           | pattern.Ident _ _, _
           | pattern.App _ _ _ _, _
             => fun _ k => None
           end%option.
      ```
      - We have three correctness conditions on `unify_pattern'`:
        - It must be the case that if we invoke `unify_pattern'` with any continuation, the result is the same as invoking it with the continuation `Some`, binding the result in the option monad, and then invoking the continuation on the bound value.
        - There is the `wf` correctness condition, which says that if two `rawexpr`s are `wf_rawexpr`-related, then invoking `unify_pattern'` with the continuation `Some` either results in `None` on both of them, or it results in two `wf_unification_resultT'`-related results.  We define `wf_unification_resultT'` as
          ```coq
          Fixpoint wf_value' {with_lets : bool} G {t : type} : value'1 with_lets t -> value'2 with_lets t -> Prop
            := match t, with_lets with
               | type.base t, true => UnderLets.wf (fun G' => expr.wf G') G
               | type.base t, false => expr.wf G
               | type.arrow s d, _
                 => fun f1 f2
                    => (forall seg G' v1 v2,
                           G' = (seg ++ G)%list
                           -> @wf_value' false seg s v1 v2
                           -> @wf_value' true G' d (f1 v1) (f2 v2))
               end.

          Definition wf_value G {t} : value1 t -> value2 t -> Prop := @wf_value' false G t.
          Definition wf_value_with_lets G {t} : value_with_lets1 t -> value_with_lets2 t -> Prop := @wf_value' true G t.

          Fixpoint related_unification_resultT' {var1 var2} (R : forall t, var1 t -> var2 t -> Prop) {t p evm}
            : @unification_resultT' var1 t p evm -> @unification_resultT' var2 t p evm -> Prop
            := match p in pattern.pattern t return @unification_resultT' var1 t p evm -> @unification_resultT' var2 t p evm -> Prop with
               | pattern.Wildcard t => R _
               | pattern.Ident t idc => eq
               | pattern.App s d f x
                 => fun (v1 : unification_resultT' f evm * unification_resultT' x evm)
                        (v2 : unification_resultT' f evm * unification_resultT' x evm)
                    => @related_unification_resultT' _ _ R _ _ _ (fst v1) (fst v2)
                       /\ @related_unification_resultT' _ _ R _ _ _ (snd v1) (snd v2)
               end.

          Definition wf_unification_resultT' (G : list {t1 : type & (var1 t1 * var2 t1)%type}) {t p evm}
            : @unification_resultT' value t p evm -> @unification_resultT' value t p evm -> Prop
            := @related_unification_resultT' _ _ (fun _ => wf_value G) t p evm.
          ```
        - The interp-correctness condition is (a bit more than) a bit of a mouthful, and requires some auxiliary definitions.
          - It is a bit hard to say what makes an expression interp-related to an interpreted value.  Under the assumption of function extensionality, an expression is interp-related to a interpreted value if and only if the interpretation of the expression is equal to the interpreted value.  Thus `expr.interp_related` is an attempt to avoid function extensionality that is not fully successful, likely because I cannot say in words what exactly it is supposed to mean.  The definition is
            ```coq
            Section with_interp.
              Context {base_type : Type}
                      {ident : type base_type -> Type}
                      {interp_base_type : base_type -> Type}
                      (interp_ident : forall t, ident t -> type.interp interp_base_type t).

              Fixpoint interp_related_gen
                       {var : type base_type -> Type}
                       (R : forall t, var t -> type.interp interp_base_type t -> Prop)
                       {t} (e : @expr base_type ident var t)
                : type.interp interp_base_type t -> Prop
                := match e in expr t return type.interp interp_base_type t -> Prop with
                   | expr.Var t v1 => R t v1
                   | expr.App s d f x
                     => fun v2
                        => exists fv xv,
                            @interp_related_gen var R _ f fv
                            /\ @interp_related_gen var R _ x xv
                            /\ fv xv = v2
                   | expr.Ident t idc
                     => fun v2 => interp_ident _ idc == v2
                   | expr.Abs s d f1
                     => fun f2
                        => forall x1 x2,
                            R _ x1 x2
                            -> @interp_related_gen var R d (f1 x1) (f2 x2)
                   | expr.LetIn s d x f (* combine the App rule with the Abs rule *)
                     => fun v2
                        => exists fv xv,
                            @interp_related_gen var R _ x xv
                            /\ (forall x1 x2,
                                   R _ x1 x2
                                   -> @interp_related_gen var R d (f x1) (fv x2))
                            /\ fv xv = v2
                   end.

              Definition interp_related {t} (e : @expr base_type ident (type.interp interp_base_type) t) : type.interp interp_base_type t -> Prop
                := @interp_related_gen (type.interp interp_base_type) (@type.eqv) t e.
            End with_interp.
            ```
          - A term in the `UnderLets` monad is `UnderLets.interp_related` to an interpreted value `v` if and only if converting the `UnderLets` expression to an `expr` (by replacing all of the `UnderLets`-let-binders with `expr`-let-binders) results in an expression that is `expr.interp_related` to `v`.
          - A `value` is `value_interp_related` to an interpreted value `v` whenever it sends `interp_related` things to `interp_related` things (the arrow case), and satisfies the appropriate notion of `interp_related` in the base case:
            ```coq
            Fixpoint value_interp_related {t with_lets} : @value' var with_lets t -> type.interp base.interp t -> Prop
              := match t, with_lets with
                 | type.base _, true => UnderLets_interp_related
                 | type.base _, false => expr_interp_related
                 | type.arrow s d, _
                   => fun (f1 : @value' _ _ s -> @value' _ _ d) (f2 : type.interp _ s -> type.interp _ d)
                      => forall x1 x2,
                          @value_interp_related s _ x1 x2
                          -> @value_interp_related d _ (f1 x1) (f2 x2)
                 end.
            ```
          - A `rawexpr` is `rawexpr_interp_related` to an interpreted value `v` if both the revealed and unrevealed structures are appropriately `interp_related` to `v`.  This one, too, is a bit hard to explain in any detail without simply displaying the code:
            ```coq
            Fixpoint rawexpr_interp_related (r1 : rawexpr) : type.interp base.interp (type_of_rawexpr r1) -> Prop
              := match r1 return type.interp base.interp (type_of_rawexpr r1) -> Prop with
                 | rExpr _ e1
                 | rValue (type.base _) e1
                   => expr_interp_related e1
                 | rValue t1 v1
                   => value_interp_related v1
                 | rIdent _ t1 idc1 t'1 alt1
                   => fun v2
                      => expr.interp ident_interp alt1 == v2
                         /\ existT expr t1 (expr.Ident idc1) = existT expr t'1 alt1
                 | rApp f1 x1 t1 alt1
                   => match alt1 in expr.expr t return type.interp base.interp t -> Prop with
                      | expr.App s d af ax
                        => fun v2
                           => exists fv xv (pff : type.arrow s d = type_of_rawexpr f1) (pfx : s = type_of_rawexpr x1),
                               @expr_interp_related _ af fv
                               /\ @expr_interp_related _ ax xv
                               /\ @rawexpr_interp_related f1 (rew pff in fv)
                               /\ @rawexpr_interp_related x1 (rew pfx in xv)
                               /\ fv xv = v2
                      | _ => fun _ => False
                      end
                 end.
            ```
          - We can say when a `unification_resultT'` returning an `expr` whose `var` type is `@value (type.interp base.interp)` is interp-related to a `unification_resultT'` returning an `expr` whose `var` type is `type.interp base.interp` in the semi-obvious way:
            ```coq
            Local Notation var := (type.interp base.interp) (only parsing).

            Definition unification_resultT'_interp_related {t p evm}
              : @unification_resultT' (@value var) t p evm -> @unification_resultT' var t p evm -> Prop
              := related_unification_resultT' (fun t => value_interp_related).
            ```

          - We say that a `rawexpr`'s types are ok if the revealed and unrevealed structure match on the type level:
            ```coq
            Fixpoint rawexpr_types_ok (r : @rawexpr var) (t : type) : Prop
              := match r with
                 | rExpr t' _
                 | rValue t' _
                   => t' = t
                 | rIdent _ t1 _ t2 _
                   => t1 = t /\ t2 = t
                 | rApp f x t' alt
                   => t' = t
                      /\ match alt with
                         | expr.App s d _ _
                           => rawexpr_types_ok f (type.arrow s d)
                              /\ rawexpr_types_ok x s
                         | _ => False
                         end
                 end.
            ```
          - We can define a transformation that takes in a `PositiveMap.t` of pattern type variables to types, together with a `PositiveSet.t` of type variables that we care about, and re-creates a new `PositiveMap.t` in accordance with the `PositiveSet.t`.  This is required to get some theorem types to line up, and is possibly an indication of a leaky abstraction barrier.
            ```coq
            Local Notation mk_new_evm0 evm ls
              := (fold_right
                    (fun i k evm'
                     => k match PositiveMap.find i evm with
                          | Some v => PositiveMap.add i v evm'
                          | None => evm'
                          end) (fun evm' => evm')
                    (List.rev ls)) (only parsing).

            Local Notation mk_new_evm' evm ps
              := (mk_new_evm0
                    evm
                    (PositiveSet.elements ps)) (only parsing).

            Local Notation mk_new_evm evm ps
              := (mk_new_evm' evm ps (PositiveMap.empty _)) (only parsing).
            ```
          - Given a proof of `@types_match_with evm t re p` that the types of `re : rawexpr` and `p : pattern t` line up under the mapping `evm`, and a proof of `rawexpr_types_ok re (type_of_rawexpr re)`, we can prove that `type_of_rawexpr re = pattern.type.subst_default t mk_new_evm evm (pattern_collect_vars p)`.  We call this theorem `eq_type_of_rawexpr_of_types_match_with'`.
          - The final and perhaps most important auxiliary component is the notation of the default interpretation of a pattern.  This is a `with_unification_resultT'` which returns the obvious interpreted value after getting all of its data; application nodes become applications, identifiers get interpreted, wildcards are passed through.
            - This definition itself needs a few auxiliary definitions and context variables.
            - We have a context variable `(pident_to_typed : forall t (idc : pident t) (evm : EvarMap), type_of_list (pident_arg_types t idc) -> ident (pattern.type.subst_default t evm))` which takes in a pattern identifier, a mapping of type variables to types, and the arguments bound for that identifier, and returns a PHOAST identifier of the correct type.  We require that all type-instantiations of type variables of pattern identifiers be valid; this means that it doesn't matter if some type variables are missing from the mapping and we fill them in with `unit` instead.
            - We define `lam_type_of_list` to convert between the `cps` and non-cps versions of type lists:
              ```coq
              Local Notation type_of_list
                := (fold_right (fun a b => prod a b) unit).
              Local Notation type_of_list_cps
                := (fold_right (fun a K => a -> K)).

              Definition lam_type_of_list {ls K} : (type_of_list ls -> K) -> type_of_list_cps K ls
                := list_rect
                     (fun ls => (type_of_list ls -> K) -> type_of_list_cps K ls)
                     (fun f => f tt)
                     (fun T Ts rec k t => rec (fun ts => k (t, ts)))
                     ls.
              ```
            - We may now define the default interpretation:
              ```coq
              Fixpoint pattern_default_interp' {K t} (p : pattern t) evm {struct p} : (var (pattern.type.subst_default t evm) -> K) -> @with_unification_resultT' var t p evm K
                := match p in pattern.pattern t return (var (pattern.type.subst_default t evm) -> K) -> @with_unification_resultT' var t p evm K with
                   | pattern.Wildcard t => fun k v => k v
                   | pattern.Ident t idc
                     => fun k
                        => lam_type_of_list (fun args => k (ident_interp _(pident_to_typed _ idc _ args)))
                   | pattern.App s d f x
                     => fun k
                        => @pattern_default_interp'
                             _ _ f evm
                             (fun ef
                              => @pattern_default_interp'
                                   _ _ x evm
                                   (fun ex
                                    => k (ef ex)))
                   end.
              ```
            - To define the unprimed version, which also accounts for the type variables, we must first define the lambda of `forall_vars`:
              ```coq
              Fixpoint lam_forall_vars_gen {k : EvarMap -> Type}
                       (f : forall evm, k evm)
                       (ls : list PositiveMap.key)
                : forall evm0, forall_vars_body k ls evm0
                := match ls return forall evm0, forall_vars_body k ls evm0 with
                   | nil => f
                   | cons x xs => fun evm t => @lam_forall_vars_gen k f xs _
                   end.

              Definition lam_forall_vars {p : PositiveSet.t} {k : EvarMap -> Type}
                         (f : forall evm, k evm)
                : forall_vars p k
                := @lam_forall_vars_gen k f _ _.
              ```
            - Now we can define the default interpretation as a `with_unification_resultT`:
              ```coq
              Definition pattern_default_interp {t} (p : pattern t)
                : @with_unification_resultT var t p var
                := pattern.type.lam_forall_vars
                     (fun evm
                      => pattern_default_interp' p evm id).
              ```
          - Now, finally, we may state the interp-correctness condition of the pattern unifier:
            ```coq
            Lemma interp_unify_pattern' {t re p evm res v}
                  (Hre : rawexpr_interp_related re v)
                  (H : @unify_pattern' t re p evm _ (@Some _) = Some res)
                  (Ht : @types_match_with evm t re p)
                  (Ht' : rawexpr_types_ok re (type_of_rawexpr re))
                  (evm' := mk_new_evm evm (pattern_collect_vars p))
                  (Hty : type_of_rawexpr re = pattern.type.subst_default t evm'
                   := eq_type_of_rawexpr_of_types_match_with' Ht Ht')
              : exists resv : _,
                  unification_resultT'_interp_related res resv
                  /\ app_transport_with_unification_resultT'_cps
                       (pattern_default_interp' p evm' id) resv _ (@Some _)
                     = Some (rew Hty in v).
            ```
    - We can now glue the type pattern-unifier with the expression pattern-unifier in a straightforward way.  Note that this pattern unifier also has three correctness conditions.
      ```coq
      Definition unify_pattern {t} (e : rawexpr) (p : pattern t)
        : forall T, (unification_resultT p -> option T) -> option T
        := fun T cont
           => unify_types
                e p _
                (fun evm
                 => evm <- evm;
                      unify_pattern'
                        e p evm T (fun v => cont (existT _ _ v)))%option.
      ```
      - The first correctness condition is again the cps-identity rule: if you invoke `unify_pattern` with any continuation, that must be the same as invoking it with `Some`, binding the value in the option monad, and then invoking the continuation on the bound value.
      - The `wf` correctness condition requires us to define a notion of `wf` for `unification_resultT`.
        - We say that two `unification_resultT`s are `wf`-related if their type-variable-maps are equal, and their identifier-arguments and wildcard binding values are appropriately `wf`-related:
          ```coq
          Definition related_sigT_by_eq {A P1 P2} (R : forall x : A, P1 x -> P2 x -> Prop)
                     (x : @sigT A P1) (y : @sigT A P2)
            : Prop
            := { pf : projT1 x = projT1 y
               | R _ (rew pf in projT2 x) (projT2 y) }.

                    Definition related_unification_resultT {var1 var2} (R : forall t, var1 t -> var2 t -> Prop) {t p}
                      : @unification_resultT _ t p -> @unification_resultT _ t p -> Prop
                      := related_sigT_by_eq (@related_unification_resultT' _ _ R t p).

                    Definition wf_unification_resultT (G : list {t1 : type & (var1 t1 * var2 t1)%type}) {t p}
                      : @unification_resultT (@value var1) t p -> @unification_resultT (@value var2) t p -> Prop
                      := @related_unification_resultT _ _ (fun _ => wf_value G) t p.
          ```
        - The `wf` correctness condition is then that if we have two `wf_rawexpr`-related `rawexpr`s, invoking `unify_pattern` on each `rawexpr` to unify it with a singular pattern `p`, with continuation `Some`, results either in `None` in both cases, or in two `unification_resultT`s which are `wf_unification_resultT`-related.
        - The interpretation correctness condition is a bit of a mouthful.
          - We say that two `unification_resultT`s are interp-related if their mappings of type variables to types are equal, and their packages of non-type binding data are appropriately interp-related.
            ```coq
            Local Notation var := (type.interp base.interp) (only parsing).

            Definition unification_resultT_interp_related {t p}
              : @unification_resultT (@value var) t p -> @unification_resultT var t p -> Prop
              := related_unification_resultT (fun t => value_interp_related).
            ```
          - We can now state the interpretation correctness condition, which is a bit hard for me to meaningfully talk about in English words except by saying "it does the right thing for a good notion of 'right'":
            ```coq
            Lemma interp_unify_pattern {t re p v res}
                  (Hre : rawexpr_interp_related re v)
                  (Ht' : rawexpr_types_ok re (type_of_rawexpr re))
                  (H : @unify_pattern t re p _ (@Some _) = Some res)
                  (evm' := mk_new_evm (projT1 res) (pattern_collect_vars p))
              : exists resv,
                unification_resultT_interp_related res resv
                /\ exists Hty, (app_with_unification_resultT_cps (@pattern_default_interp t p) resv _ (@Some _) = Some (existT (fun evm => type.interp base.interp (pattern.type.subst_default t evm)) evm' (rew Hty in v))).
            ```
- Plugging in the arguments to a rewrite rule: Take 2
  - There is one more definition before we put all of the rewrite replacement rule pieces together: we describe a way to handle the fact that we are underneath zero, one, or two monads.  The way we handle this is by just assuming that we are underneath two monads, and issuing monad-return statements as necessary to correct:
    ```coq
    Definition normalize_deep_rewrite_rule {should_do_again with_opt under_lets t}
      : deep_rewrite_ruleTP_gen should_do_again with_opt under_lets t
        -> deep_rewrite_ruleTP_gen should_do_again true true t
      := match with_opt, under_lets with
         | true , true  => fun x => x
         | false, true  => fun x => Some x
         | true , false => fun x => (x <- x; Some (UnderLets.Base x))%option
         | false, false => fun x => Some (UnderLets.Base x)
         end%cps.
    ```
    - The `wf` correctness condition, unsurprisingly, just says that if two rewrite replacement rules are appropriately `wf`-related, then their normalizations are too.  This is quite verbose to state, though, because it requires traversing multiple layers of monads and pesky dependent types.  TODO: should this code actually be included?
      ```coq
      Definition wf_maybe_do_again_expr
                 {t}
                 {rew_should_do_again1 rew_should_do_again2 : bool}
                 (G : list {t : _ & (var1 t * var2 t)%type})
        : expr (var:=if rew_should_do_again1 then @value var1 else var1) t
          -> expr (var:=if rew_should_do_again2 then @value var2 else var2) t
          -> Prop
        := match rew_should_do_again1, rew_should_do_again2
                 return expr (var:=if rew_should_do_again1 then @value var1 else var1) t
                        -> expr (var:=if rew_should_do_again2 then @value var2 else var2) t
                        -> Prop
           with
           | true, true
             => fun e1 e2
                => exists G',
                    (forall t' v1' v2', List.In (existT _ t' (v1', v2')) G' -> wf_value G v1' v2')
                    /\ expr.wf G' e1 e2
           | false, false => expr.wf G
           | _, _ => fun _ _ => False
           end.

      Definition wf_maybe_under_lets_expr
                 {T1 T2}
                 (P : list {t : _ & (var1 t * var2 t)%type} -> T1 -> T2 -> Prop)
                 (G : list {t : _ & (var1 t * var2 t)%type})
                 {rew_under_lets1 rew_under_lets2 : bool}
        : (if rew_under_lets1 then UnderLets var1 T1 else T1)
          -> (if rew_under_lets2 then UnderLets var2 T2 else T2)
          -> Prop
        := match rew_under_lets1, rew_under_lets2
                 return (if rew_under_lets1 then UnderLets var1 T1 else T1)
                        -> (if rew_under_lets2 then UnderLets var2 T2 else T2)
                        -> Prop
           with
           | true, true
             => UnderLets.wf P G
           | false, false
             => P G
           | _, _ => fun _ _ => False
           end.

      Definition maybe_option_eq {A B} {opt1 opt2 : bool} (R : A -> B -> Prop)
        : (if opt1 then option A else A) -> (if opt2 then option B else B) -> Prop
        := match opt1, opt2 with
           | true, true => option_eq R
           | false, false => R
           | _, _ => fun _ _ => False
           end.

      Definition wf_deep_rewrite_ruleTP_gen
                 (G : list {t : _ & (var1 t * var2 t)%type})
                 {t}
                 {rew_should_do_again1 rew_with_opt1 rew_under_lets1 : bool}
                 {rew_should_do_again2 rew_with_opt2 rew_under_lets2 : bool}
        : deep_rewrite_ruleTP_gen1 rew_should_do_again1 rew_with_opt1 rew_under_lets1 t
          -> deep_rewrite_ruleTP_gen2 rew_should_do_again2 rew_with_opt2 rew_under_lets2 t
          -> Prop
        := maybe_option_eq
             (wf_maybe_under_lets_expr
                wf_maybe_do_again_expr
                G).

      Lemma wf_normalize_deep_rewrite_rule
            {G}
            {t}
            {should_do_again1 with_opt1 under_lets1}
            {should_do_again2 with_opt2 under_lets2}
            {r1 r2}
            (Hwf : @wf_deep_rewrite_ruleTP_gen G t should_do_again1 with_opt1 under_lets1 should_do_again2 with_opt2 under_lets2 r1 r2)
        : option_eq
            (UnderLets.wf (fun G' => wf_maybe_do_again_expr G') G)
            (normalize_deep_rewrite_rule r1) (normalize_deep_rewrite_rule r2).
      ```
    - We do not require any interp-correctness condition on `normalize_deep_rewrite_rule`.  Instead, we bake `normalize_deep_rewrite_rule` into the per-rewrite-rule correctness conditions that a user must prove of every individual rewrite rule.
  - Actually, I lied.  We need to define the type of a rewrite rule before we can say what it means for one to be correct.
    - An `anypattern` is a dynamically-typed pattern.  This is used so that we can talk about `list`s of rewrite rules.
      ```coq
      Record > anypattern {ident : type -> Type}
        := { type_of_anypattern : type;
             pattern_of_anypattern :> @pattern ident type_of_anypattern }.
      ```
    - A `rewrite_ruleT` is just a sigma of a pattern of any type, with `rewrite_rule_data` over that pattern:
      ```coq
      Definition rewrite_ruleTP
        := (fun p : anypattern => @rewrite_rule_data _ (pattern.pattern_of_anypattern p)).
      Definition rewrite_ruleT := sigT rewrite_ruleTP.
      Definition rewrite_rulesT
        := (list rewrite_ruleT).
      ```
  - We now define a helper definition to support rewriting again in the output of a rewrite rule.  This is a separate definition mostly to make dependent types slightly less painful.
    ```coq
    Definition maybe_do_againT (should_do_again : bool) (t : base.type)
      := ((@expr.expr base.type ident (if should_do_again then value else var) t) -> UnderLets (expr t)).
    Definition maybe_do_again
               (do_again : forall t : base.type, @expr.expr base.type ident value t -> UnderLets (expr t))
               (should_do_again : bool) (t : base.type)
      := if should_do_again return maybe_do_againT should_do_again t
         then do_again t
         else UnderLets.Base.
    ```
    - You might think that the correctness condition for this is trivial.  And, indeed, the `wf` correctness condition is straightforward.  In fact, we have already seen it above in `wf_maybe_do_again_expr`, as there is no proof, only a definition of what it means for things to be related depending on whether or not we are rewriting again.
    - The interpretation correctness rule, on the other hand, is surprisingly subtle.  You may have noticed above that `expr.interp_related` is parameterized on an arbitrary `var` type, and an arbitrary relation between the `var` type and `type.interp base.interp`.  I said that it is equivalent to equality of interpretation under the assumption of function extensionality, but that is only the case if `var` is instantiated to `type.interp` and the relation is equality or pointwise/extensional equivalence.  Here, we must instantiate the `var` type with `@value var`, and the relation with `value_interp_related`.  We then prove that for any "good" notion of rewriting again, if our input value is interp-related to an interpreted value, the result of maybe rewriting again is also interp-related to that interpreted value.
      ```coq
      Lemma interp_maybe_do_again
            (do_again : forall t : base.type, @expr.expr base.type ident value t -> UnderLets (expr t))
            (Hdo_again : forall t e v,
                expr.interp_related_gen ident_interp (fun t => value_interp_related) e v
                -> UnderLets_interp_related (do_again t e) v)
            {should_do_again : bool} {t e v}
            (He : (if should_do_again return @expr.expr _ _ (if should_do_again then _ else _) _ -> _
                   then expr.interp_related_gen ident_interp (fun t => value_interp_related)
                   else expr_interp_related) e v)
        : UnderLets_interp_related (@maybe_do_again _ _ do_again should_do_again t e) v.
      ```
  - For the purposes of ensuring that reduction does not get blocked where it should not, we only allow rewrite rules to match on fully applied patterns, and to return base-typed expressions.  We patch this broken abstraction barrier with
    ```coq
    Local Notation base_type_of t
      := (match t with type.base t' => t' | type.arrow _ __ => base.type.unit end).
    ```
  - Finally, we can define what it means to rewrite with a particular rewrite rule.  It is messy primarily due to continuation passing style, optional values, and type casts.  Note that we use `<-` to mean "bind in whatever monad is the top-most scope".  Other than these complications, it just unifies the pattern with the `rawexpr` to get binding data, applies the rewrite replacement rule to the binding data, normalizes the applied rewrite replacement rule, calls the rewriter again on the output if it should, and returns the result.
    ```coq
    Definition rewrite_with_rule {t} e' (pf : rewrite_ruleT)
      : option (UnderLets (expr t))
      := let 'existT p f := pf in
         let should_do_again := rew_should_do_again f in
         unify_pattern
           e' (pattern.pattern_of_anypattern p) _
           (fun x
            => app_with_unification_resultT_cps
                 (rew_replacement f) x _
                 (fun f'
                  => (tr <- type.try_make_transport_cps (@base.try_make_transport_cps) _ _ _;
                        (tr <- tr;
                           (tr' <- type.try_make_transport_cps (@base.try_make_transport_cps) _ _ _;
                              (tr' <- tr';
                                 option_bind'
                                   (normalize_deep_rewrite_rule (projT2 f'))
                                   (fun fv
                                    => Some (fv <-- fv;
                                               fv <-- maybe_do_again should_do_again (base_type_of (type_of_rawexpr e')) (tr fv);
                                               UnderLets.Base (tr' fv))%under_lets))%option)%cps)%option)%cps)%cps).```
    - We once again do not have any `wf` correctness condition for `rewrite_with_rule`; we merely unfold it as needed.
    - To write down the correctness condition for `rewrite_with_rule`, we must first define what it means for `rewrite_rule_data` to be "good".
      - Here is where we use `normalize_deep_rewrite_rule`.  Replacement rule data is good with respect to an interpretation value if normalizing it gives an appropriately interp-related thing to that interpretation value:
        ```coq
        Local Notation var := (type.interp base.interp) (only parsing).

        Definition deep_rewrite_ruleTP_gen_good_relation
                   {should_do_again with_opt under_lets : bool} {t}
                   (v1 : @deep_rewrite_ruleTP_gen should_do_again with_opt under_lets t)
                   (v2 : var t)
          : Prop
          := let v1 := normalize_deep_rewrite_rule v1 in
             match v1 with
             | None => True
             | Some v1 => UnderLets.interp_related
                            ident_interp
                            (if should_do_again
                                return (@expr.expr base.type ident (if should_do_again then @value var else var) t) -> _
                             then expr.interp_related_gen ident_interp (fun t => value_interp_related)
                             else expr_interp_related)
                            v1
                            v2
             end.
        ```
      - Rewrite rule data is good if, for any interp-related binding data, the replacement function applied to the value-binding-data is interp-related to the default interpretation of the pattern applied to the interpreted-value-binding-data:
        ```coq
        Definition rewrite_rule_data_interp_goodT
                   {t} {p : pattern t} (r : @rewrite_rule_data t p)
          : Prop
          := forall x y,
            related_unification_resultT (fun t => value_interp_related) x y
            -> option_eq
                 (fun fx gy
                  => related_sigT_by_eq
                       (fun evm
                        => @deep_rewrite_ruleTP_gen_good_relation
                             (rew_should_do_again r) (rew_with_opt r) (rew_under_lets r) (pattern.type.subst_default t evm))
                       fx gy)
                 (app_with_unification_resultT_cps (rew_replacement r) x _ (@Some _))
                 (app_with_unification_resultT_cps (pattern_default_interp p) y _ (@Some _)).
        ```
      - The interpretation correctness condition then says that if the rewrite rule is good, the `rawexpr` `re` has ok types, the "rewrite again" function is good, and `rewrite_with_rule` succeeds and outputs an expression `v1`, then `v1` is interp-related to any interpreted value which `re` is interp-related to:
        ```coq
        Lemma interp_rewrite_with_rule
              (do_again : forall t : base.type, @expr.expr base.type ident value t -> UnderLets (expr t))
              (Hdo_again : forall t e v,
                  expr.interp_related_gen ident_interp (fun t => value_interp_related) e v
                  -> UnderLets_interp_related (do_again t e) v)
              (rewr : rewrite_ruleT)
              (Hrewr : rewrite_rule_data_interp_goodT (projT2 rewr))
              t e re v1 v2
              (Ht : t = type_of_rawexpr re)
              (Ht' : rawexpr_types_ok re (type_of_rawexpr re))
          : @rewrite_with_rule do_again t re rewr = Some v1
            -> rawexpr_interp_related re (rew Ht in v2)
            -> UnderLets_interp_related v1 v2.
        ```

### Tying it all together
- We can now say what it means to rewrite with a decision tree in a given `rawexpr` `re`.  We evaluate the decision tree, and whenever we are asked to try the `k`th rewrite rule, we look for it in our list of rewrite rules, and invoke `rewrite_with_rule`.  By default, if rewriting fails, we will eventually return `expr_of_rawexpr re`.
  ```coq
  Definition eval_rewrite_rules
             (d : decision_tree)
             (rews : rewrite_rulesT)
             (e : rawexpr)
    : UnderLets (expr (type_of_rawexpr e))
    := let defaulte := expr_of_rawexpr e in
       (eval_decision_tree
          (e::nil) d
          (fun k ctx
           => match ctx return option (UnderLets (expr (type_of_rawexpr e))) with
              | e'::nil
                => (pf <- nth_error rews k; rewrite_with_rule e' pf)%option
              | _ => None
              end);;;
          (UnderLets.Base defaulte))%option.
  ```
  - To define the correctness conditions, we must first define what it means for lists of rewrite rules to be good.
    - For `wf`, we need to catch up a bit before getting to lists of rewrite rules.  These say the obvious things:
      ```coq
                Definition wf_with_unif_rewrite_ruleTP_gen
                           (G : list {t : _ & (var1 t * var2 t)%type})
                           {t} {p : pattern t}
                           {rew_should_do_again1 rew_with_opt1 rew_under_lets1}
                           {rew_should_do_again2 rew_with_opt2 rew_under_lets2}
                  : with_unif_rewrite_ruleTP_gen1 p rew_should_do_again1 rew_with_opt1 rew_under_lets1
                    -> with_unif_rewrite_ruleTP_gen2 p rew_should_do_again2 rew_with_opt2 rew_under_lets2
                    -> Prop
                  := fun f g
                     => forall x y,
                         wf_unification_resultT G x y
                         -> option_eq
                              (fun (fx : { evm : _ & deep_rewrite_ruleTP_gen1 rew_should_do_again1 rew_with_opt1 rew_under_lets1 _ })
                                   (gy : { evm : _ & deep_rewrite_ruleTP_gen2 rew_should_do_again2 rew_with_opt2 rew_under_lets2 _ })
                               => related_sigT_by_eq
                                    (fun _ => wf_deep_rewrite_ruleTP_gen G) fx gy)
                              (app_with_unification_resultT_cps f x _ (@Some _))
                              (app_with_unification_resultT_cps g y _ (@Some _)).

                Definition wf_rewrite_rule_data
                           (G : list {t : _ & (var1 t * var2 t)%type})
                           {t} {p : pattern t}
                           (r1 : @rewrite_rule_data1 t p)
                           (r2 : @rewrite_rule_data2 t p)
                  : Prop
                  := wf_with_unif_rewrite_ruleTP_gen G (rew_replacement r1) (rew_replacement r2).

      ```
    - Two lists of rewrite rules are `wf` related if they have the same length, and if any pair of rules in their zipper (`List.combine`) have equal patterns and `wf`-related data:
      ```coq
      Definition rewrite_rules_goodT
                 (rew1 : rewrite_rulesT1) (rew2 : rewrite_rulesT2)
        : Prop
        := length rew1 = length rew2
           /\ (forall p1 r1 p2 r2,
                  List.In (existT _ p1 r1, existT _ p2 r2) (combine rew1 rew2)
                  -> { pf : p1 = p2
                     | forall G,
                         wf_rewrite_rule_data
                           G
                           (rew [fun tp => @rewrite_rule_data1 _ (pattern.pattern_of_anypattern tp)] pf in r1)
                           r2 }).
      ```
    - A list of rewrite rules is good for interpretation if every rewrite rule in that list is good for interpretation:
      ```coq
      Definition rewrite_rules_interp_goodT
                 (rews : rewrite_rulesT)
        : Prop
        := forall p r,
          List.In (existT _ p r) rews
          -> rewrite_rule_data_interp_goodT r.
      ```
    - The `wf`-correctness condition for `eval_rewrite_rules` says the obvious thing: for `wf`-related "rewrite again" functions, `wf`-related lists of rewrite rules, and `wf`-related `rawexpr`s, the output of `eval_rewrite_rules` is `wf`-related:
      ```coq
      Lemma wf_eval_rewrite_rules
            (do_again1 : forall t : base.type, @expr.expr base.type ident (@value var1) t -> @UnderLets var1 (@expr var1 t))
            (do_again2 : forall t : base.type, @expr.expr base.type ident (@value var2) t -> @UnderLets var2 (@expr var2 t))
            (wf_do_again : forall G (t : base.type) e1 e2,
                (exists G', (forall t v1 v2, List.In (existT _ t (v1, v2)) G' -> Compile.wf_value G v1 v2) /\ expr.wf G' e1 e2)
                -> UnderLets.wf (fun G' => expr.wf G') G (@do_again1 t e1) (@do_again2 t e2))
            (d : @decision_tree raw_pident)
            (rew1 : rewrite_rulesT1) (rew2 : rewrite_rulesT2)
            (Hrew : rewrite_rules_goodT rew1 rew2)
            (re1 : @rawexpr var1) (re2 : @rawexpr var2)
            {t} G e1 e2
            (Hwf : @wf_rawexpr G t re1 e1 re2 e2)
        : UnderLets.wf
            (fun G' => expr.wf G')
            G
            (rew [fun t => @UnderLets var1 (expr t)] (proj1 (eq_type_of_rawexpr_of_wf Hwf)) in (eval_rewrite_rules1 do_again1 d rew1 re1))
            (rew [fun t => @UnderLets var2 (expr t)] (proj2 (eq_type_of_rawexpr_of_wf Hwf)) in (eval_rewrite_rules2 do_again2 d rew2 re2)).
      ```
    - The interpretation correctness is also the expected one: for a "rewrite again" function that preserves interp-relatedness, a good-for-interp list of rewrite rules, a `rawexpr` whose types are ok and which is interp-related to a value `v`, the result of `eval_rewrite_rules` is interp-related to `v`:
      ```coq
      Lemma interp_eval_rewrite_rules
            (do_again : forall t : base.type, @expr.expr base.type ident value t -> UnderLets (expr t))
            (d : decision_tree)
            (rew_rules : rewrite_rulesT)
            (re : rawexpr) v
            (Hre : rawexpr_types_ok re (type_of_rawexpr re))
            (res := @eval_rewrite_rules do_again d rew_rules re)
            (Hdo_again : forall t e v,
                expr.interp_related_gen ident_interp (fun t => value_interp_related) e v
                -> UnderLets_interp_related (do_again t e) v)
            (Hr : rawexpr_interp_related re v)
            (Hrew_rules : rewrite_rules_interp_goodT rew_rules)
        : UnderLets_interp_related res v.
      ```
- Only one piece remains (other than defining particular rewrite rules and proving them good).  If you were following carefully, you might note that `eval_rewrite_rules` takes in a `rawexpr` and produces an `UnderLets expr`, while `rewrite_bottomup` expects a function `rewrite_head : forall t (idc : ident t), value_with_lets t`.  From a PHOAST identifier, we must construct a `value_with_lets` which collects all of the `value` arguments to the identifier and performs `eval_rewrite_rules` once the identifier is fully applied.  We call this function `assemble_identifier_rewriters`, and it is built out of a small number of pieces.
  - We define a convenience function that takes a `value` and an `expr` at the same type, and produces a `rawexpr` by using `rExpr` on the expr if the type is a base type, and `rValue` on the `value` otherwise.  Morally, the `expr` and the `value` should be the same term, modulo `reify` and/or `reflect`:
    ```coq
    Definition rValueOrExpr2 {t} : value t -> expr t -> rawexpr
      := match t with
         | type.base _ => fun v e => @rExpr _ e
         | type.arrow _ _ => fun v e => @rValue _ v
         end.
    ```
  - We take in a context variable (eventually autogenerated by python) which eta-iota-expands a function over an identifier by producing a `match` on the identifier.  Its specification is that it is pointwise-equal to function application; it exists entirely so that we can perform rewrite-rule-compilation time reduction on the rewrite rules by writing down the cases for every head identifier separately.  The context variable is `eta_ident_cps : forall {T : type.type base.type -> Type} {t} (idc : ident t) (f : forall t', ident t' -> T t'), T t`, and we require that `forall T t idc f, @eta_ident_cps T t idc f = f t idc`.
  - We can now carefully define the function that turns `eval_rewrite_rules` into a thing that can be plugged into `rewrite_head`.  We take care to preserve thunked computation in `rValue` nodes, while describing the alternative structure via `reify`.  In general, the stored values are only interp-related to the same things that the "unrevealed structure" expressions are interp-related to.  There is no other relation (that we've found) between the values and the expressions, and this caused a great deal of pain when trying to specify the interpretation correctness properties.
    ```coq
    Section with_do_again.
      Context (dtree : decision_tree)
              (rewrite_rules : rewrite_rulesT)
              (default_fuel : nat)
              (do_again : forall t : base.type, @expr.expr base.type ident value t -> UnderLets (expr t)).

      Let dorewrite1 (e : rawexpr) : UnderLets (expr (type_of_rawexpr e))
        := eval_rewrite_rules do_again dtree rewrite_rules e.

      Fixpoint assemble_identifier_rewriters' (t : type) : forall e : rawexpr, (forall P, P (type_of_rawexpr e) -> P t) -> value_with_lets t
        := match t return forall e : rawexpr, (forall P, P (type_of_rawexpr e) -> P t) -> value_with_lets t with
           | type.base _
             => fun e k => k (fun t => UnderLets (expr t)) (dorewrite1 e)
           | type.arrow s d
             => fun f k (x : value' _ _)
                => let x' := reify x in
                   @assemble_identifier_rewriters' d (rApp f (rValueOrExpr2 x x') (k _ (expr_of_rawexpr f) @ x'))%expr (fun _ => id)
           end%under_lets.

      Definition assemble_identifier_rewriters {t} (idc : ident t) : value_with_lets t
        := eta_ident_cps _ _ idc (fun t' idc' => assemble_identifier_rewriters' t' (rIdent true idc' #idc') (fun _ => id)).
    End with_do_again.
    ```
    - The `wf`-correctness condition for `assemble_identifier_rewriters'` says that if two `rawexpr`s are `wf`-related, and both continuations are extensionally/pointwise equal to the identity function transported across the appropriate equality proof, then the results of `assemble_identifier_rewriters'` are `wf`-related, under the assumption that the "rewrite again" functions are appropriately `wf`-related and the list of rewrite rules is good.
      ```coq
      Section with_do_again.
        Context (dtree : @decision_tree raw_pident)
                (rew1 : rewrite_rulesT1)
                (rew2 : rewrite_rulesT2)
                (Hrew : rewrite_rules_goodT rew1 rew2)
                (do_again1 : forall t : base.type, @expr.expr base.type ident (@value var1) t -> @UnderLets var1 (@expr var1 t))
                (do_again2 : forall t : base.type, @expr.expr base.type ident (@value var2) t -> @UnderLets var2 (@expr var2 t))
                (wf_do_again : forall G G' (t : base.type) e1 e2,
                    (forall t v1 v2, List.In (existT _ t (v1, v2)) G' -> Compile.wf_value G v1 v2)
                    -> expr.wf G' e1 e2
                    -> UnderLets.wf (fun G' => expr.wf G') G (@do_again1 t e1) (@do_again2 t e2)).

        Lemma wf_assemble_identifier_rewriters' G t re1 e1 re2 e2
              K1 K2
              (He : @wf_rawexpr G t re1 e1 re2 e2)
              (HK1 : forall P v, K1 P v = rew [P] (proj1 (eq_type_of_rawexpr_of_wf He)) in v)
              (HK2 : forall P v, K2 P v = rew [P] (proj2 (eq_type_of_rawexpr_of_wf He)) in v)
          : wf_value_with_lets
              G
              (@assemble_identifier_rewriters' var1 rew1 do_again1 t re1 K1)
              (@assemble_identifier_rewriters' var2 rew2 do_again2 t re2 K2).
      ```
    - The `wf`-correctness condition for `assemble_identifier_rewriters` merely says that the outputs are always `wf`-related, again under the assumption that the "rewrite again" functions are appropriately `wf`-related and the list of rewrite rules is good.
      ```coq
      Lemma wf_assemble_identifier_rewriters G t (idc : ident t)
        : wf_value_with_lets
            G
            (@assemble_identifier_rewriters var1 rew1 do_again1 t idc)
            (@assemble_identifier_rewriters var2 rew2 do_again2 t idc).
      Proof.
      ```
    - The interpretation correctness condition says that for a good "rewrite again" function, a good-for-interpretation list of rewrite rules, a `rawexpr` `re` whose types are ok and which is interp-related to an interpreted value `v`, the result of `assemble_identifier_rewriters'` is interp-related to `v`.  The actual statement is slightly more obscure, parameterizing over types which are equal to computed things, primarily for ease of induction in the proof.
      ```coq
      Lemma interp_assemble_identifier_rewriters'
            (do_again : forall t : base.type, @expr.expr base.type ident value t -> UnderLets (expr t))
            (dt : decision_tree)
            (rew_rules : rewrite_rulesT)
            t re K
            (res := @assemble_identifier_rewriters' dt rew_rules do_again t re K)
            (Hre : rawexpr_types_ok re (type_of_rawexpr re))
            (Ht : type_of_rawexpr re = t)
            v
            (HK : K = (fun P v => rew [P] Ht in v))
            (Hdo_again : forall t e v,
                expr.interp_related_gen ident_interp (fun t => value_interp_related) e v
                -> UnderLets_interp_related (do_again t e) v)
            (Hrew_rules : rewrite_rules_interp_goodT rew_rules)
            (Hr : rawexpr_interp_related re v)
        : value_interp_related res (rew Ht in v).
      ```
    - The interpretation correctness condition for `assemble_identifier_rewriters` is very similar, where the `rawexpr_interp_related` hypothesis is replaced by an pointwise equality between the interpretation of the identifier and the interpreted value.
      ```coq
      Lemma interp_assemble_identifier_rewriters
            (do_again : forall t : base.type, @expr.expr base.type ident value t -> UnderLets (expr t))
            (d : decision_tree)
            (rew_rules : rewrite_rulesT)
            t idc v
            (res := @assemble_identifier_rewriters d rew_rules do_again t idc)
            (Hdo_again : forall t e v,
                expr.interp_related_gen ident_interp (fun t => value_interp_related) e v
                -> UnderLets_interp_related (do_again t e) v)
            (Hrew_rules : rewrite_rules_interp_goodT rew_rules)
            (Hv : ident_interp t idc == v)
        : value_interp_related res v.
      ```
  - We have not talked about correctness conditions for the functions we looked at in the very beginning, `rewrite_bottomup` and `repeat_rewrite`, but the correctness conditions for these two are straightforward, so we state them without explanation.
    - The `wf` correctness conditions are
      ```coq
      Section with_rewrite_head.
        Context (rewrite_head1 : forall t (idc : ident t), @value_with_lets var1 t)
                (rewrite_head2 : forall t (idc : ident t), @value_with_lets var2 t)
                (wf_rewrite_head : forall G t (idc1 idc2 : ident t),
                    idc1 = idc2 -> wf_value_with_lets G (rewrite_head1 t idc1) (rewrite_head2 t idc2)).

        Local Notation rewrite_bottomup1 := (@rewrite_bottomup var1 rewrite_head1).
        Local Notation rewrite_bottomup2 := (@rewrite_bottomup var2 rewrite_head2).

        Lemma wf_rewrite_bottomup G G' {t} e1 e2 (Hwf : expr.wf G e1 e2)
              (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> wf_value G' v1 v2)
          : wf_value_with_lets G' (@rewrite_bottomup1 t e1) (@rewrite_bottomup2 t e2).
      End with_rewrite_head.

      Local Notation nbe var := (@rewrite_bottomup var (fun t idc => reflect (expr.Ident idc))).

      Lemma wf_nbe G G' {t} e1 e2
            (Hwf : expr.wf G e1 e2)
            (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> wf_value G' v1 v2)
        : wf_value_with_lets G' (@nbe var1 t e1) (@nbe var2 t e2).

      Section with_rewrite_head2.
        Context (rewrite_head1 : forall (do_again : forall t : base.type, @expr (@value var1) (type.base t) -> @UnderLets var1 (@expr var1 (type.base t)))
                                        t (idc : ident t), @value_with_lets var1 t)
                (rewrite_head2 : forall (do_again : forall t : base.type, @expr (@value var2) (type.base t) -> @UnderLets var2 (@expr var2 (type.base t)))
                                        t (idc : ident t), @value_with_lets var2 t)
                (wf_rewrite_head
                 : forall
                    do_again1
                    do_again2
                    (wf_do_again
                     : forall G' G (t : base.type) e1 e2
                              (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> wf_value G' v1 v2),
                        expr.wf G e1 e2
                        -> UnderLets.wf (fun G' => expr.wf G') G' (do_again1 t e1) (do_again2 t e2))
                    G t (idc1 idc2 : ident t),
                    idc1 = idc2 -> wf_value_with_lets G (rewrite_head1 do_again1 t idc1) (rewrite_head2 do_again2 t idc2)).

        Lemma wf_repeat_rewrite fuel
          : forall {t} G G' e1 e2
                   (Hwf : expr.wf G e1 e2)
                   (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> wf_value G' v1 v2),
            wf_value_with_lets G' (@repeat_rewrite var1 rewrite_head1 fuel t e1) (@repeat_rewrite var2 rewrite_head2 fuel t e2).
      ```
    - The interpretation correctness conditions are
      ```coq
      Section with_rewrite_head.
        Context (rewrite_head : forall t (idc : ident t), value_with_lets t)
                (interp_rewrite_head : forall t idc v, ident_interp idc == v -> value_interp_related (rewrite_head t idc) v).

        Lemma interp_rewrite_bottomup {t e v}
              (He : expr.interp_related_gen (@ident_interp) (fun t => value_interp_related) e v)
          : value_interp_related (@rewrite_bottomup var rewrite_head t e) v.
      End with_rewrite_head.

      Local Notation nbe := (@rewrite_bottomup var (fun t idc => reflect (expr.Ident idc))).

      Lemma interp_nbe {t e v}
            (He : expr.interp_related_gen (@ident_interp) (fun t => value_interp_related) e v)
        : value_interp_related (@nbe t e) v.

      Lemma interp_repeat_rewrite
            {rewrite_head fuel t e v}
            (retT := value_interp_related (@repeat_rewrite _ rewrite_head fuel t e) v)
            (Hrewrite_head
             : forall do_again
                      (Hdo_again : forall t e v,
                          expr.interp_related_gen (@ident_interp) (fun t => value_interp_related) e v
                          -> UnderLets.interp_related (@ident_interp) (expr.interp_related (@ident_interp)) (do_again t e) v)
                      t idc v,
                ident_interp idc == v
                -> value_interp_related (@rewrite_head do_again t idc) v)
            (He : expr.interp_related_gen (@ident_interp) (fun t => value_interp_related) e v)
        : retT.
      ```
