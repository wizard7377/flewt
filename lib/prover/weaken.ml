module type WEAKEN  =
  sig
    val strengthenExp : (IntSyn.exp_ * IntSyn.sub_) -> IntSyn.exp_
    val strengthenSpine : (IntSyn.spine_ * IntSyn.sub_) -> IntSyn.spine_
    val strengthenCtx :
      (IntSyn.dctx * IntSyn.sub_) -> (IntSyn.dctx * IntSyn.sub_)
    val strengthenDec : (IntSyn.dec_ * IntSyn.sub_) -> IntSyn.dec_
    val strengthenSub : (IntSyn.sub_ * IntSyn.sub_) -> IntSyn.sub_
  end


module Weaken(Weaken:sig module Whnf : WHNF end) : WEAKEN =
  struct
    module I = IntSyn
    let rec strengthenExp (u_, s) =
      Whnf.normalize ((Whnf.cloInv (u_, s)), I.id)
    let rec strengthenDec (Dec (name, v_), s) =
      I.Dec (name, (strengthenExp (v_, s)))
    let rec strengthenCtx =
      begin function
      | (I.Null, s) -> (I.Null, s)
      | (Decl (g_, d_), s) ->
          let (g'_, s') = strengthenCtx (g_, s) in
          ((I.Decl (g'_, (strengthenDec (d_, s')))), (I.dot1 s')) end
    let rec strengthenSub (s, t) = Whnf.compInv (s, t)
    let rec strengthenSpine =
      begin function
      | (I.Nil, t) -> I.Nil
      | (App (u_, s_), t) ->
          I.App ((strengthenExp (u_, t)), (strengthenSpine (s_, t))) end
  let strengthenExp = strengthenExp
  let strengthenSpine = strengthenSpine
  let strengthenDec = strengthenDec
  let strengthenCtx = strengthenCtx
  let strengthenSub = strengthenSub end
