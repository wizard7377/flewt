
(* Introduce: Version 1.4 *)
(* Author: Carsten Schuermann *)
module type INTRODUCE  =
  sig
    (*! structure IntSyn : INTSYN !*)
    (*! structure Tomega : TOMEGA !*)
    module State : STATE
    exception Error of string 
    type nonrec operator
    val expand : State.__Focus -> operator option
    val apply : operator -> unit
    val menu : operator -> string
  end;;




(* Introduce *)
(* Author: Carsten Schuermann *)
module Introduce(Introduce:sig
                             (*! structure IntSyn' : INTSYN !*)
                             (*! structure Tomega' : TOMEGA !*)
                             (*! sharing Tomega'.IntSyn = IntSyn' !*)
                             module State' : STATE
                             module TomegaNames : TOMEGANAMES
                           end) : INTRODUCE =
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
    type nonrec operator = (T.__Prg * T.__Prg)
    let rec stripTC (TC) = TC
    let rec stripTCOpt =
      function | NONE -> NONE | SOME (TC) -> SOME (stripTC TC)
    let rec stripDec =
      function
      | UDec (D) -> T.UDec D
      | PDec (name, F, TC1, TC2) -> T.PDec (name, F, TC1, (stripTCOpt TC2))
    let rec strip =
      function
      | I.Null -> I.Null
      | Decl (Psi, D) -> I.Decl ((strip Psi), (stripDec D))
    let rec expand =
      function
      | Focus ((EVar (Psi, r, All ((D, _), F), NONE, NONE, _) as R), W) ->
          let D' = TomegaNames.decName (Psi, D) in
          SOME (R, (T.Lam (D', (T.newEVar ((I.Decl ((strip Psi), D')), F)))))
      | Focus
          ((EVar (Psi, r, Ex (((Dec (_, V) as D), _), F), NONE, NONE, _) as R),
           W)
          ->
          let X = I.newEVar ((T.coerceCtx Psi), V) in
          let Y = T.newEVar (Psi, (T.forSub (F, (T.Dot ((T.Exp X), T.id))))) in
          SOME (R, (T.PairExp (X, Y)))
      | Focus ((EVar (Psi, r, T.True, NONE, NONE, _) as R), W) ->
          SOME (R, T.Unit)
      | Focus (EVar (Psi, r, FClo (F, s), TC1, TC2, X), W) ->
          expand
            (S.Focus ((T.EVar (Psi, r, (T.forSub (F, s)), TC1, TC2, X)), W))
      | Focus (EVar (Psi, r, _, _, _, _), W) -> NONE
    let rec apply (EVar (_, r, _, _, _, _), P) = (:=) r SOME P
    let rec menu (r, P) = (^) "Intro " TomegaPrint.nameEVar r
    (*    fun stripTC (T.Abs (_, TC)) = TC *)
    (* expand S = S'

       Invariant:
       If   S = (Psi |> all x1:A1 .... xn: An. F)
       and  F does not start with an all quantifier
       then S' = (Psi, x1:A1, ... xn:An |> F)
    *)
    (* apply O = S

       Invariant:
       O = S
    *)
    (* need to trail for back *)
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
