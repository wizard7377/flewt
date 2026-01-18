
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
      function | None -> None | Some (TC) -> Some (stripTC TC)
    let rec stripDec =
      function
      | UDec (__d) -> T.UDec __d
      | PDec (name, F, TC1, TC2) -> T.PDec (name, F, TC1, (stripTCOpt TC2))
    let rec strip =
      function
      | I.Null -> I.Null
      | Decl (Psi, __d) -> I.Decl ((strip Psi), (stripDec __d))
    let rec expand =
      function
      | Focus ((EVar (Psi, r, All ((__d, _), F), None, None, _) as R), W) ->
          let __d' = TomegaNames.decName (Psi, __d) in
          Some (R, (T.Lam (__d', (T.newEVar ((I.Decl ((strip Psi), __d')), F)))))
      | Focus
          ((EVar (Psi, r, Ex (((Dec (_, __v) as __d), _), F), None, None, _) as R),
           W)
          ->
          let x = I.newEVar ((T.coerceCtx Psi), __v) in
          let y = T.newEVar (Psi, (T.forSub (F, (T.Dot ((T.Exp x), T.id))))) in
          Some (R, (T.PairExp (x, y)))
      | Focus ((EVar (Psi, r, T.True, None, None, _) as R), W) ->
          Some (R, T.Unit)
      | Focus (EVar (Psi, r, FClo (F, s), TC1, TC2, x), W) ->
          expand
            (S.Focus ((T.EVar (Psi, r, (T.forSub (F, s)), TC1, TC2, x)), W))
      | Focus (EVar (Psi, r, _, _, _, _), W) -> None
    let rec apply (EVar (_, r, _, _, _, _), P) = (:=) r Some P
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
