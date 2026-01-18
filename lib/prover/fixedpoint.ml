
(* Splitting: Version 1.4 *)
(* Author: Carsten Schuermann *)
module type FIXEDPOINT  =
  sig
    (*! structure IntSyn : INTSYN !*)
    (*! structure Tomega : TOMEGA !*)
    module State : STATE
    exception Error of string 
    type nonrec operator
    val expand : (State.__Focus * Tomega.__TC) -> operator
    val apply : operator -> unit
    val menu : operator -> string
  end;;




(* Fixed Point *)
(* Author: Carsten Schuermann *)
module FixedPoint(FixedPoint:sig
                               (*! structure IntSyn' : INTSYN !*)
                               (*! structure Tomega' : TOMEGA !*)
                               (*! sharing Tomega'.IntSyn = IntSyn' !*)
                               module State' : STATE
                             end) : FIXEDPOINT =
  struct
    (*! sharing State'.IntSyn = IntSyn' !*)
    (*! sharing State'.Tomega = Tomega' !*)
    (*! structure IntSyn = IntSyn' !*)
    (*! structure Tomega = Tomega' !*)
    module State = State'
    module S = State'
    module T = Tomega
    module I = IntSyn
    exception Error = S.Error
    type nonrec operator = (T.__Prg option ref * T.__Prg)
    let rec expand (Focus (EVar (Psi, r, F, _, TCs, _), W), O) =
      let NDec x = Names.decName ((T.coerceCtx Psi), (I.NDec None)) in
      let __d = T.PDec (x, F, None, None) in
      let x = T.newEVar ((I.Decl (Psi, __d)), (T.forSub (F, (T.Shift 1)))) in
      (r, (T.Rec (__d, x)))
    let rec apply (r, P) = (:=) r Some P
    let rec menu _ = "Recursion introduction"
    (* expand S = S'

       Invariant:
       If   S = (Psi |>  F)
       and  F does not start with an all quantifier
       then S' = (Psi, xx :: F |> F)
    *)
    (*        val __d = T.PDec (Some "IH" , F, Some O, Some O) *)
    (* apply O = S

       Invariant:
       O = S
    *)
    (* should be trailed -cs Thu Apr 22 11:20:32 2004 *)
    (* menu O = s

       Invariant:
       s = "Apply universal introduction rules"
    *)
    exception Error = Error
    type nonrec operator = operator
    let expand = expand
    let apply = apply
    let menu = menu
  end ;;
