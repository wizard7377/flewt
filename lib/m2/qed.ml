
(* Qed *)
(* Author: Carsten Schuermann *)
module type QED  =
  sig
    module MetaSyn : METASYN
    exception Error of string 
    val subgoal : MetaSyn.__State -> bool
  end;;




(* QED *)
(* Author: Carsten Schuermann *)
module Qed(Qed:sig module Global : GLOBAL module MetaSyn' : METASYN end) :
  QED =
  struct
    module MetaSyn = MetaSyn'
    exception Error of string 
    module M = MetaSyn
    module I = IntSyn
    let rec subgoal (State (name, Prefix (G, M, B), V)) =
      let rec check =
        function
        | I.Null -> true__
        | Decl (M, M.Top) -> check M
        | Decl (M, M.Bot) -> false__ in
      check M
    let subgoal = subgoal
  end ;;
