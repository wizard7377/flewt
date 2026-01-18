
(* ELIM: Version 1.4 *)
(* Author: Carsten Schuermann *)
module type ELIM  =
  sig
    module State : STATE
    exception Error of string 
    type nonrec operator
    val expand : State.__Focus -> operator list
    val apply : operator -> unit
    val menu : operator -> string
  end;;




(* Elim *)
(* Author: Carsten Schuermann *)
(* Date: Thu Mar 16 13:39:26 2006 *)
module Elim(Elim:sig
                   module Data : DATA
                   module State' : STATE
                   module Abstract : ABSTRACT
                   module TypeCheck : TYPECHECK
                   module Whnf : WHNF
                   (*! structure IntSyn' : INTSYN !*)
                   (*! structure Tomega' : TOMEGA !*)
                   (*! sharing Tomega'.IntSyn = IntSyn' !*)
                   (*! sharing State'.IntSyn = IntSyn' !*)
                   (*! sharing State'.Tomega = Tomega' !*)
                   (*! sharing Abstract.IntSyn = IntSyn' !*)
                   (*! sharing Abstract.Tomega = Tomega' !*)
                   (*! sharing TypeCheck.IntSyn = IntSyn' !*)
                   (*! sharing Whnf.IntSyn = IntSyn' !*)
                   module Unify : UNIFY
                 end) : ELIM =
  struct
    (*! sharing Unify.IntSyn = IntSyn' !*)
    (*! structure IntSyn = IntSyn' !*)
    (*! structure Tomega = Tomega' !*)
    module State = State'
    exception Error of string 
    type __Operator =
      | Local of (Tomega.__Prg * int) 
    type nonrec operator = __Operator
    module S = State
    module T = Tomega
    module I = IntSyn
    exception Success of int 
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
    let rec expand (Focus ((EVar (Psi, r, __g, __v, _, _) as y), W)) =
      let rec matchCtx =
        function
        | (I.Null, _, __Fs) -> __Fs
        | (Decl (__g, PDec (x, F, _, _)), n, __Fs) ->
            matchCtx (__g, (n + 1), ((Local (y, n)) :: __Fs))
        | (Decl (__g, UDec _), n, __Fs) -> matchCtx (__g, (n + 1), __Fs) in
      matchCtx (Psi, 1, nil)
    let rec apply =
      function
      | Local ((EVar (Psi, r, __g, None, None, _) as R), n) ->
          let PDec (_, __F0, _, _) = T.ctxDec (Psi, n) in
          (match __F0 with
           | All ((UDec (Dec (_, __v)), _), F) ->
               let x = I.newEVar ((T.coerceCtx (strip Psi)), __v) in
               let NDec x = Names.decName ((T.coerceCtx Psi), (I.NDec None)) in
               let __d =
                 T.PDec
                   (x, (T.forSub (F, (T.Dot ((T.Exp x), T.id)))), None, None) in
               let Psi' = I.Decl (Psi, __d) in
               let y = T.newEVar ((strip Psi'), (T.forSub (__g, T.shift))) in
               (:=) r Some
                 (T.Let (__d, (T.Redex ((T.Var n), (T.AppExp (x, T.Nil)))), y))
           | Ex ((D1, _), F) ->
               let D1' = Names.decName ((T.coerceCtx Psi), D1) in
               let Psi' = I.Decl (Psi, (T.UDec D1')) in
               let NDec x = Names.decName ((T.coerceCtx Psi'), (I.NDec None)) in
               let D2 = T.PDec (x, F, None, None) in
               let Psi'' = I.Decl (Psi', D2) in
               let y = T.newEVar ((strip Psi''), (T.forSub (__g, (T.Shift 2)))) in
               (:=) r Some (T.LetPairExp (D1', D2, (T.Var n), y))
           | T.True ->
               let y = T.newEVar ((strip Psi), __g) in
               (:=) r Some (T.LetUnit ((T.Var n), y)))
      | Local (EVar (Psi, r, FClo (F, s), TC1, TC2, x), n) ->
          apply
            (Local ((T.EVar (Psi, r, (T.forSub (F, s)), TC1, TC2, x)), n))
    let rec menu (Local ((EVar (Psi, _, _, _, _, _) as x), n)) =
      match I.ctxLookup (Psi, n) with
      | PDec (Some x, _, _, _) ->
          (((^) "Elim " TomegaPrint.nameEVar x) ^ " with variable ") ^ x
    (* These lines need to move *)
    (* fun stripTC (T.Abs (_, TC)) = TC *)
    (* expand' S = op'

       Invariant:
       If   |- S state
       then op' is an operator which performs the filling operation
    *)
    (* y is lowered *)
    (* apply op = B'

       Invariant:
       If op is a filling operator
       then B' holds iff the filling operation was successful
    *)
    (* the None, None may breach an invariant *)
    (* revisit when we add subterm orderings *)
    (* menu op = s'

       Invariant:
       If op is a filling operator
       then s' is a string describing the operation in plain text
    *)
    (* Invariant: Context is named  --cs Fri Mar  3 14:31:08 2006 *)
    let expand = expand
    let apply = apply
    let menu = menu
  end ;;
