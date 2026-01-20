
module type ELIM  =
  sig
    module State : STATE
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
                   module Unify : UNIFY
                 end) : ELIM =
  struct
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
      function | NONE -> NONE | Some (TC) -> Some (stripTC TC)
    let rec stripDec =
      function
      | UDec (__D) -> T.UDec __D
      | PDec (name, __F, TC1, TC2) ->
          T.PDec (name, __F, TC1, (stripTCOpt TC2))
    let rec strip =
      function
      | I.Null -> I.Null
      | Decl (Psi, __D) -> I.Decl ((strip Psi), (stripDec __D))
    let rec expand (Focus ((EVar (Psi, r, __G, __V, _, _) as Y), __W)) =
      let rec matchCtx __0__ __1__ __2__ =
        match (__0__, __1__, __2__) with
        | (I.Null, _, __Fs) -> __Fs
        | (Decl (__G, PDec (x, __F, _, _)), n, __Fs) ->
            matchCtx (__G, (n + 1), ((Local (__Y, n)) :: __Fs))
        | (Decl (__G, UDec _), n, __Fs) -> matchCtx (__G, (n + 1), __Fs) in
      matchCtx (Psi, 1, nil)(* Y is lowered *)
    let rec apply =
      function
      | Local ((EVar (Psi, r, __G, NONE, NONE, _) as R), n) ->
          let PDec (_, __F0, _, _) = T.ctxDec (Psi, n) in
          (match __F0 with
           | All ((UDec (Dec (_, __V)), _), __F) ->
               let __X = I.newEVar ((T.coerceCtx (strip Psi)), __V) in
               let NDec x = Names.decName ((T.coerceCtx Psi), (I.NDec NONE)) in
               let __D =
                 T.PDec
                   (x, (T.forSub (__F, (T.Dot ((T.Exp __X), T.id)))), NONE,
                     NONE) in
               let Psi' = I.Decl (Psi, __D) in
               let __Y = T.newEVar ((strip Psi'), (T.forSub (__G, T.shift))) in
               (((:=) r Some
                   (T.Let
                      (__D, (T.Redex ((T.Var n), (T.AppExp (__X, T.Nil)))),
                        __Y)))
                 (* the NONE, NONE may breach an invariant *)(* revisit when we add subterm orderings *))
           | Ex ((__D1, _), __F) ->
               let D1' = Names.decName ((T.coerceCtx Psi), __D1) in
               let Psi' = I.Decl (Psi, (T.UDec D1')) in
               let NDec x = Names.decName ((T.coerceCtx Psi'), (I.NDec NONE)) in
               let __D2 = T.PDec (x, __F, NONE, NONE) in
               let Psi'' = I.Decl (Psi', __D2) in
               let __Y =
                 T.newEVar ((strip Psi''), (T.forSub (__G, (T.Shift 2)))) in
               (:=) r Some (T.LetPairExp (D1', __D2, (T.Var n), __Y))
           | T.True ->
               let __Y = T.newEVar ((strip Psi), __G) in
               (:=) r Some (T.LetUnit ((T.Var n), __Y)))
      | Local (EVar (Psi, r, FClo (__F, s), TC1, TC2, __X), n) ->
          apply
            (Local ((T.EVar (Psi, r, (T.forSub (__F, s)), TC1, TC2, __X)), n))
    let rec menu (Local ((EVar (Psi, _, _, _, _, _) as X), n)) =
      match I.ctxLookup (Psi, n) with
      | PDec (Some x, _, _, _) ->
          (((^) "Elim " TomegaPrint.nameEVar __X) ^ " with variable ") ^ x
    let expand = expand
    let apply = apply
    let menu = menu
  end ;;
