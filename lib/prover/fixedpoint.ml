
module type FIXEDPOINT  =
  sig
    module State : STATE
    exception Error of string 
    type nonrec operator
    val expand : State.__Focus -> Tomega.__TC -> operator
    val apply : operator -> unit
    val menu : operator -> string
  end;;




module FixedPoint(FixedPoint:sig module State' : STATE end) : FIXEDPOINT =
  struct
    module State = State'
    module S = State'
    module T = Tomega
    module I = IntSyn
    exception Error = S.Error
    type nonrec operator = (T.__Prg option ref * T.__Prg)
    let rec expand (Focus (EVar (Psi, r, __F, _, TCs, _), __W)) (__O) =
      let NDec x = Names.decName ((T.coerceCtx Psi), (I.NDec None)) in
      let __D = T.PDec (x, __F, None, None) in
      let __X =
        T.newEVar ((I.Decl (Psi, __D)), (T.forSub (__F, (T.Shift 1)))) in
      (((r, (T.Rec (__D, __X))))
        (*        val D = T.PDec (Some "IH" , F, Some O, Some O) *))
    let rec apply r (__P) = (:=) r Some __P
    let rec menu _ = "Recursion introduction"
    exception Error = Error
    type nonrec operator = operator
    let expand = expand
    let apply = apply
    let menu = menu
  end ;;
