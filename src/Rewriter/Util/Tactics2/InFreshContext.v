Require Import Ltac2.Ltac2.
Require Import Rewriter.Util.Tactics2.Constr.Unsafe.MakeAbbreviations.
Require Export Rewriter.Util.FixCoqMistakes.

Module Constr.
  Import Ltac2.Constr.
  (* N.B. tac gets list of binders in reversed order, innermost first *)
  Ltac2 in_fresh_context_avoiding (default : ident) (avoid_goal : bool) (avoid : Fresh.Free.t option) (bs : binder list) (tac : (ident * constr) list -> unit) : constr :=
    let rec aux (avoid : Fresh.Free.t) (bs : binder list) (pending : (ident * constr) list) : constr :=
      match bs with
      | [] => '(ltac2:(tac pending))
      | b :: bs
        => let n := match Binder.name b with
                    | Some n => n
                    | None => default
                    end in
           let n := Fresh.fresh avoid n in
           let t := Binder.type b in
           let t := Unsafe.substnl (List.map (fun (n, _) => mkVar n) pending) 0 t in
           in_context
             n t
             (fun ()
              => match bs with
                 | [] => tac ((n, t) :: pending)
                 | _ :: _
                   => Control.refine
                        (fun ()
                         => aux (Fresh.Free.union avoid (Fresh.Free.of_ids [n])) bs ((n, t) :: pending))
                 end)
      end in
    let avoid := Fresh.Free.union (if avoid_goal then Fresh.Free.of_goal () else Fresh.Free.of_ids [])
                                  (match avoid with | Some avoid => avoid | None => Fresh.Free.of_ids [] end) in
    aux avoid bs [].
  Ltac2 in_fresh_context (default : ident) (bs : binder list) (tac : (ident * constr) list -> unit) : constr :=
    in_fresh_context_avoiding default true None bs tac.
End Constr.
