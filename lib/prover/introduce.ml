module type INTRODUCE  =
  sig
    module State : STATE
    exception Error of string 
    type nonrec operator
    val expand : State.focus_ -> operator option
    val apply : operator -> unit
    val menu : operator -> string
  end


module Introduce(Introduce:sig
                             module State' : STATE
                             module TomegaNames : TOMEGANAMES
                           end) : INTRODUCE =
  struct
    module State = State'
    module S = State'
    module T = Tomega
    module I = IntSyn
    exception Error = S.Error
    type nonrec operator = (T.prg_ * T.prg_)
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
let rec expand =
  begin function
  | Focus ((EVar (Psi, r, All ((d_, _), f_), None, None, _) as r_), w_) ->
      let d'_ = TomegaNames.decName (Psi, d_) in
      Some (r_, (T.Lam (d'_, (T.newEVar ((I.Decl ((strip Psi), d'_)), f_)))))
  | Focus
      ((EVar (Psi, r, Ex (((Dec (_, v_) as d_), _), f_), None, None, _) as r_),
       w_)
      ->
      let x_ = I.newEVar ((T.coerceCtx Psi), v_) in
      let y_ = T.newEVar (Psi, (T.forSub (f_, (T.Dot ((T.Exp x_), T.id))))) in
      Some (r_, (T.PairExp (x_, y_)))
  | Focus ((EVar (Psi, r, T.True, None, None, _) as r_), w_) ->
      Some (r_, T.Unit)
  | Focus (EVar (Psi, r, FClo (f_, s), TC1, TC2, x_), w_) ->
      expand
        (S.Focus ((T.EVar (Psi, r, (T.forSub (f_, s)), TC1, TC2, x_)), w_))
  | Focus (EVar (Psi, r, _, _, _, _), w_) -> None end
let rec apply (EVar (_, r, _, _, _, _), p_) = (:=) r Some p_
let rec menu (r, p_) = (^) "Intro " TomegaPrint.nameEVar r
exception Error = Error
type nonrec operator = operator
let expand = expand
let apply = apply
let menu = menu end
