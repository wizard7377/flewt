
module type FIXEDPOINT  =
  sig
    module State :
    ((STATE)(* Splitting: Version 1.4 *)(* Author: Carsten Schuermann *)
    (*! structure IntSyn : INTSYN !*)(*! structure Tomega : TOMEGA !*))
    exception Error of string 
    type nonrec operator
    val expand : (State.__Focus * Tomega.__TC) -> operator
    val apply : operator -> unit
    val menu : operator -> string
  end;;




module FixedPoint(FixedPoint:sig
                               module State' :
                               ((STATE)(* Fixed Point *)
                               (* Author: Carsten Schuermann *)(*! structure IntSyn' : INTSYN !*)
                               (*! structure Tomega' : TOMEGA !*)
                               (*! sharing Tomega'.IntSyn = IntSyn' !*))
                             end) : FIXEDPOINT =
  struct
    module State =
      ((State')(*! sharing State'.IntSyn = IntSyn' !*)
      (*! sharing State'.Tomega = Tomega' !*)(*! structure IntSyn = IntSyn' !*)
      (*! structure Tomega = Tomega' !*))
    module S = State'
    module T = Tomega
    module I = IntSyn
    exception Error = S.Error
    type nonrec operator = (T.__Prg option ref * T.__Prg)
    let rec expand (Focus (EVar (Psi, r, F, _, TCs, _), W), O) =
      let NDec x = Names.decName ((T.coerceCtx Psi), (I.NDec NONE)) in
      let D = T.PDec (x, F, NONE, NONE) in
      let X = T.newEVar ((I.Decl (Psi, D)), (T.forSub (F, (T.Shift 1)))) in
      (r, (T.Rec (D, X)))
    let rec apply (r, P) = (:=) r SOME P
    let rec menu _ = "Recursion introduction"
    exception Error = Error(* menu O = s

       Invariant:
       s = "Apply universal introduction rules"
    *)
    (* should be trailed -cs Thu Apr 22 11:20:32 2004 *)
    (* apply O = S

       Invariant:
       O = S
    *)(*        val D = T.PDec (SOME "IH" , F, SOME O, SOME O) *)
    (* expand S = S'

       Invariant:
       If   S = (Psi |>  F)
       and  F does not start with an all quantifier
       then S' = (Psi, xx :: F |> F)
    *)
    type nonrec operator = operator
    let expand = expand
    let apply = apply
    let menu = menu
  end ;;
