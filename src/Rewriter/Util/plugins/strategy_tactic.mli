open Genarg

val wit_strategy_level : Conv_oracle.level uniform_genarg_type

val tclSTRATEGY : local:bool -> int -> Names.GlobRef.t list -> unit Proofview.tactic
