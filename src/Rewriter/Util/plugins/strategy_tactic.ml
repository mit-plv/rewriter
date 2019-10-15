open Genarg


let wit_strategy_level : Conv_oracle.level uniform_genarg_type =
  make0 "strategy_level"

let tclSTRATEGY ~local v (q : Names.GlobRef.t list) =
  Proofview.Goal.enter begin
    fun gl ->
      let env = Proofview.Goal.env gl in
      Redexpr.set_strategy local [(Conv_oracle.Level v, List.map (Tacred.evaluable_of_global_reference env) q)];
      Proofview.tclUNIT ()
  end
