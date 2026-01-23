module type QED  =
  sig
    module MetaSyn : METASYN
    exception Error of string 
    val subgoal : MetaSyn.state_ -> bool
  end


module Qed(Qed:sig module Global : GLOBAL module MetaSyn' : METASYN end) :
  QED =
  struct
    module MetaSyn = MetaSyn'
    exception Error of string 
    module M = MetaSyn
    module I = IntSyn
    let rec subgoal (State (name, Prefix (g_, m_, b_), v_)) =
      let rec check =
        begin function
        | I.Null -> true
        | Decl (m_, M.Top) -> check m_
        | Decl (m_, M.Bot) -> false end in
    check m_
    let subgoal = subgoal end 