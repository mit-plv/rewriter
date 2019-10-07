open Ltac_plugin
open Names

let make_definition_by_tactic sigma ~poly (name : Names.Id.t option) (ty : EConstr.t) (tac : unit Proofview.tactic) =
  let env = Global.env () in
  let name = match name with
    | Some name -> name
    | None -> Namegen.next_global_ident_away (Names.Id.of_string "Unnamed_thm") Id.Set.empty in
  let uctx = Evd.evar_universe_context sigma in
  let sign = Environ.val_of_named_context (Environ.named_context env) in
  let (ce, _uses_unsafe_tactic, univs) = Pfedit.build_constant_by_tactic ~name uctx sign ~poly ty tac in
  (* emit global universes *)
  let sigma = Evd.merge_universe_context sigma univs in
  let _ = Evd.univ_entry ~poly sigma in
  let kind = Decls.IsDefinition Decls.Definition in
  let name = Declare.declare_constant ~name ~kind (Declare.DefinitionEntry ce) in
  (sigma, name)

let vernac_make_definition_by_tactic ~poly (name : Names.Id.t option) (ty : Constrexpr.constr_expr) tac =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, ty) = Constrintern.interp_constr_evars env sigma ty in
  ignore(make_definition_by_tactic sigma ~poly name ty (Tacinterp.interp tac))
