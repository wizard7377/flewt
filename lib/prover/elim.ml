module type ELIM  =
  sig
    module State : STATE
    exception Error of string 
    type nonrec operator
    val expand : State.focus_ -> operator list
    val apply : operator -> unit
    val menu : operator -> string
  end


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
    type operator_ =
      | Local of (Tomega.prg_ * int) 
    type nonrec operator = operator_
    module S = State
    module T = Tomega
    module I = IntSyn
    exception Success of int 
    let rec stripTC (TC) = TC
    let rec stripTCOpt =
      begin function | None -> None | Some (TC) -> Some (stripTC TC) end
    let rec stripDec =
      begin function
      | UDec (d_) -> T.UDec d_
      | PDec (name, f_, TC1, TC2) -> T.PDec (name, f_, TC1, (stripTCOpt TC2)) end
  let rec strip =
    begin function
    | I.Null -> I.Null
    | Decl (Psi, d_) -> I.Decl ((strip Psi), (stripDec d_)) end
let rec expand (Focus ((EVar (Psi, r, g_, v_, _, _) as y_), w_)) =
  let rec matchCtx =
    begin function
    | (I.Null, _, fs_) -> fs_
    | (Decl (g_, PDec (x, f_, _, _)), n, fs_) ->
        matchCtx (g_, (n + 1), ((Local (y_, n)) :: fs_))
    | (Decl (g_, UDec _), n, fs_) -> matchCtx (g_, (n + 1), fs_) end in
matchCtx (Psi, 1, [])(* Y is lowered *)
let rec apply =
  begin function
  | Local ((EVar (Psi, r, g_, None, None, _) as r_), n) ->
      let PDec (_, f0_, _, _) = T.ctxDec (Psi, n) in
      (begin match f0_ with
       | All ((UDec (Dec (_, v_)), _), f_) ->
           let x_ = I.newEVar ((T.coerceCtx (strip Psi)), v_) in
           let NDec x = Names.decName ((T.coerceCtx Psi), (I.NDec None)) in
           let d_ =
             T.PDec
               (x, (T.forSub (f_, (T.Dot ((T.Exp x_), T.id)))), None, None) in
           let Psi' = I.Decl (Psi, d_) in
           let y_ = T.newEVar ((strip Psi'), (T.forSub (g_, T.shift))) in
           (((:=) r Some
               (T.Let (d_, (T.Redex ((T.Var n), (T.AppExp (x_, T.Nil)))), y_)))
             (* the NONE, NONE may breach an invariant *)
             (* revisit when we add subterm orderings *))
       | Ex ((d1_, _), f_) ->
           let D1' = Names.decName ((T.coerceCtx Psi), d1_) in
           let Psi' = I.Decl (Psi, (T.UDec D1')) in
           let NDec x = Names.decName ((T.coerceCtx Psi'), (I.NDec None)) in
           let d2_ = T.PDec (x, f_, None, None) in
           let Psi'' = I.Decl (Psi', d2_) in
           let y_ = T.newEVar ((strip Psi''), (T.forSub (g_, (T.Shift 2)))) in
           (:=) r Some (T.LetPairExp (D1', d2_, (T.Var n), y_))
       | T.True ->
           let y_ = T.newEVar ((strip Psi), g_) in
           (:=) r Some (T.LetUnit ((T.Var n), y_)) end)
  | Local (EVar (Psi, r, FClo (f_, s), TC1, TC2, x_), n) ->
      apply (Local ((T.EVar (Psi, r, (T.forSub (f_, s)), TC1, TC2, x_)), n)) end
let rec menu (Local ((EVar (Psi, _, _, _, _, _) as x_), n)) =
  begin match I.ctxLookup (Psi, n) with
  | PDec (Some x, _, _, _) ->
      (((^) "Elim " TomegaPrint.nameEVar x_) ^ " with variable ") ^ x end
let expand = expand
let apply = apply
let menu = menu end
