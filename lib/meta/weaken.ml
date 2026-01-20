
module type WEAKEN  =
  sig
    val strengthenExp : IntSyn.__Exp -> IntSyn.__Sub -> IntSyn.__Exp
    val strengthenSpine : IntSyn.__Spine -> IntSyn.__Sub -> IntSyn.__Spine
    val strengthenCtx :
      IntSyn.dctx -> IntSyn.__Sub -> (IntSyn.dctx * IntSyn.__Sub)
    val strengthenDec : IntSyn.__Dec -> IntSyn.__Sub -> IntSyn.__Dec
    val strengthenSub : IntSyn.__Sub -> IntSyn.__Sub -> IntSyn.__Sub
  end;;




module Weaken(Weaken:sig module Whnf : WHNF end) : WEAKEN =
  struct
    module I = IntSyn
    let rec strengthenExp (__U) s =
      Whnf.normalize ((Whnf.cloInv (__U, s)), I.id)
    let rec strengthenDec (Dec (name, __V)) s =
      I.Dec (name, (strengthenExp (__V, s)))
    let rec strengthenCtx __0__ __1__ =
      match (__0__, __1__) with
      | (I.Null, s) -> (I.Null, s)
      | (Decl (__G, __D), s) ->
          let (__G', s') = strengthenCtx (__G, s) in
          ((I.Decl (__G', (strengthenDec (__D, s')))), (I.dot1 s'))
    let rec strengthenSub s t = Whnf.compInv (s, t)
    let rec strengthenSpine __2__ __3__ =
      match (__2__, __3__) with
      | (I.Nil, t) -> I.Nil
      | (App (__U, __S), t) ->
          I.App ((strengthenExp (__U, t)), (strengthenSpine (__S, t)))
    let strengthenExp = strengthenExp
    let strengthenSpine = strengthenSpine
    let strengthenDec = strengthenDec
    let strengthenCtx = strengthenCtx
    let strengthenSub = strengthenSub
  end ;;
