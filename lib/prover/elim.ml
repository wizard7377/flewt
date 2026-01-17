
module type ELIM  =
  sig
    module State :
    ((STATE)(* ELIM: Version 1.4 *)(* Author: Carsten Schuermann *))
    exception Error of string 
    type nonrec operator
    val expand : State.__Focus -> operator list
    val apply : operator -> unit
    val menu : operator -> string
  end;;




module Elim(Elim:sig
                   module Data : DATA
                   module State' : STATE
                   module Abstract : ABSTRACT
                   module TypeCheck : TYPECHECK
                   module Whnf : WHNF
                   module Unify :
                   ((UNIFY)(* Elim *)(* Author: Carsten Schuermann *)
                   (* Date: Thu Mar 16 13:39:26 2006 *)
                   (*! structure IntSyn' : INTSYN !*)
                   (*! structure Tomega' : TOMEGA !*)
                   (*! sharing Tomega'.IntSyn = IntSyn' !*)
                   (*! sharing State'.IntSyn = IntSyn' !*)
                   (*! sharing State'.Tomega = Tomega' !*)
                   (*! sharing Abstract.IntSyn = IntSyn' !*)
                   (*! sharing Abstract.Tomega = Tomega' !*)
                   (*! sharing TypeCheck.IntSyn = IntSyn' !*)(*! sharing Whnf.IntSyn = IntSyn' !*))
                 end) : ELIM =
  struct
    module State =
      ((State')(*! sharing Unify.IntSyn = IntSyn' !*)
      (*! structure IntSyn = IntSyn' !*)(*! structure Tomega = Tomega' !*))
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
      function | NONE -> NONE | SOME (TC) -> SOME (stripTC TC)
    let rec stripDec =
      function
      | UDec (D) -> T.UDec D
      | PDec (name, F, TC1, TC2) -> T.PDec (name, F, TC1, (stripTCOpt TC2))
    let rec strip =
      function
      | I.Null -> I.Null
      | Decl (Psi, D) -> I.Decl ((strip Psi), (stripDec D))
    let rec expand (Focus ((EVar (Psi, r, g, V, _, _) as Y), W)) =
      let matchCtx =
        function
        | (I.Null, _, Fs) -> Fs
        | (Decl (g, PDec (x, F, _, _)), n, Fs) ->
            matchCtx (g, (n + 1), ((Local (Y, n)) :: Fs))
        | (Decl (g, UDec _), n, Fs) -> matchCtx (g, (n + 1), Fs) in
      matchCtx (Psi, 1, nil)
    let rec apply =
      function
      | Local ((EVar (Psi, r, g, NONE, NONE, _) as R), n) ->
          let PDec (_, F0, _, _) = T.ctxDec (Psi, n) in
          (match F0 with
           | All ((UDec (Dec (_, V)), _), F) ->
               let X = I.newEVar ((T.coerceCtx (strip Psi)), V) in
               let NDec x = Names.decName ((T.coerceCtx Psi), (I.NDec NONE)) in
               let D =
                 T.PDec
                   (x, (T.forSub (F, (T.Dot ((T.Exp X), T.id)))), NONE, NONE) in
               let Psi' = I.Decl (Psi, D) in
               let Y = T.newEVar ((strip Psi'), (T.forSub (g, T.shift))) in
               (:=) r SOME
                 (T.Let (D, (T.Redex ((T.Var n), (T.AppExp (X, T.Nil)))), Y))
           | Ex ((D1, _), F) ->
               let D1' = Names.decName ((T.coerceCtx Psi), D1) in
               let Psi' = I.Decl (Psi, (T.UDec D1')) in
               let NDec x = Names.decName ((T.coerceCtx Psi'), (I.NDec NONE)) in
               let D2 = T.PDec (x, F, NONE, NONE) in
               let Psi'' = I.Decl (Psi', D2) in
               let Y = T.newEVar ((strip Psi''), (T.forSub (g, (T.Shift 2)))) in
               (:=) r SOME (T.LetPairExp (D1', D2, (T.Var n), Y))
           | T.True ->
               let Y = T.newEVar ((strip Psi), g) in
               (:=) r SOME (T.LetUnit ((T.Var n), Y)))
      | Local (EVar (Psi, r, FClo (F, s), TC1, TC2, X), n) ->
          apply
            (Local ((T.EVar (Psi, r, (T.forSub (F, s)), TC1, TC2, X)), n))
    let rec menu (Local ((EVar (Psi, _, _, _, _, _) as X), n)) =
      match I.ctxLookup (Psi, n) with
      | PDec (SOME x, _, _, _) ->
          (((^) "Elim " TomegaPrint.nameEVar X) ^ " with variable ") ^ x
    let ((expand)(* These lines need to move *)(* fun stripTC (T.Abs (_, TC)) = TC *)
      (* expand' S = op'

       Invariant:
       If   |- S state
       then op' is an operator which performs the filling operation
    *)
      (* Y is lowered *)(* apply op = B'

       Invariant:
       If op is a filling operator
       then B' holds iff the filling operation was successful
    *)
      (* the NONE, NONE may breach an invariant *)(* revisit when we add subterm orderings *)
      (* menu op = s'

       Invariant:
       If op is a filling operator
       then s' is a string describing the operation in plain text
    *)
      (* Invariant: Context is named  --cs Fri Mar  3 14:31:08 2006 *))
      = expand
    let apply = apply
    let menu = menu
  end ;;
