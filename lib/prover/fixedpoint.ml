module type FIXEDPOINT  =
  sig
    module State : STATE
    exception Error of string 
    type nonrec operator
    val expand : (State.focus_ * Tomega.tC_) -> operator
    val apply : operator -> unit
    val menu : operator -> string
  end


module FixedPoint(FixedPoint:sig module State' : STATE end) : FIXEDPOINT =
  struct
    module State = State'
    module S = State'
    module T = Tomega
    module I = IntSyn
    exception Error = S.Error
    type nonrec operator = (T.prg_ option ref * T.prg_)
    let rec expand (Focus (EVar (Psi, r, f_, _, TCs, _), w_), o_) =
      let NDec x = Names.decName ((T.coerceCtx Psi), (I.NDec None)) in
      let d_ = T.PDec (x, f_, None, None) in
      let x_ = T.newEVar ((I.Decl (Psi, d_)), (T.forSub (f_, (T.Shift 1)))) in
      (((r, (T.Rec (d_, x_))))
        (*        val D = T.PDec (SOME "IH" , F, SOME O, SOME O) *))
    let rec apply (r, p_) = (:=) r Some p_
    let rec menu _ = "Recursion introduction"
    exception Error = Error
    type nonrec operator = operator
    let expand = expand
    let apply = apply
    let menu = menu
  end 