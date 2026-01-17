
module type QED  =
  sig
    module MetaSyn :
    ((METASYN)(* Qed *)(* Author: Carsten Schuermann *))
    exception Error of string 
    val subgoal : MetaSyn.__State -> bool
  end;;




module Qed(Qed:sig
                 module Global : GLOBAL
                 module MetaSyn' :
                 ((METASYN)(* QED *)(* Author: Carsten Schuermann *))
               end) : QED =
  struct
    module MetaSyn = MetaSyn'
    exception Error of string 
    module M = MetaSyn
    module I = IntSyn
    let rec subgoal (State (name, Prefix (g, M, B), V)) =
      let check =
        function
        | I.Null -> true__
        | Decl (M, M.Top) -> check M
        | Decl (M, M.Bot) -> false__ in
      check M
    let subgoal = subgoal
  end ;;
