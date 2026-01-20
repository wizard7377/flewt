
module type QED  =
  sig
    module MetaSyn : METASYN
    exception Error of string 
    val subgoal : MetaSyn.__State -> bool
  end;;




module Qed(Qed:sig module Global : GLOBAL module MetaSyn' : METASYN end) :
  QED =
  struct
    module MetaSyn = MetaSyn'
    exception Error of string 
    module M = MetaSyn
    module I = IntSyn
    let rec subgoal (State (name, Prefix (__G, __M, __B), __V)) =
      let rec check =
        function
        | I.Null -> true
        | Decl (__M, M.Top) -> check __M
        | Decl (__M, M.Bot) -> false in
      check __M
    let subgoal = subgoal
  end ;;
