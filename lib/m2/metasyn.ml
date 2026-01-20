
module type METASYN  =
  sig
    type __Mode =
      | Bot 
      | Top 
    type __Prefix =
      | Prefix of
      (((IntSyn.dctx * __Mode IntSyn.__Ctx * int IntSyn.__Ctx))(* Mtx modes                  *)
      (* G   declarations           *)) 
    type __State =
      | State of
      (((string * __Prefix * IntSyn.__Exp))(*             G; Mtx; Btx    *)
      (*             [name]         *)) 
    type __Sgn =
      | SgnEmpty 
      | ConDec of (IntSyn.__ConDec * __Sgn) 
    val createAtomConst :
      IntSyn.dctx -> IntSyn.__Head -> (IntSyn.__Exp * IntSyn.eclo)
    val createAtomBVar : IntSyn.dctx -> int -> (IntSyn.__Exp * IntSyn.eclo)
  end;;




module MetaSyn(MetaSyn:sig module Whnf : WHNF end) : METASYN =
  struct
    exception Error of string 
    type nonrec __Var = int
    type __Mode =
      | Bot 
      | Top 
    type __Prefix =
      | Prefix of
      (((IntSyn.dctx * __Mode IntSyn.__Ctx * int IntSyn.__Ctx))(* Mtx modes                  *)
      (* G   declarations           *)) 
    type __State =
      | State of
      (((string * __Prefix * IntSyn.__Exp))(*             G; Mtx; Btx    *)
      (*             [name]         *)) 
    type __Sgn =
      | SgnEmpty 
      | ConDec of (IntSyn.__ConDec * __Sgn) 
    module I = IntSyn
    let rec createEVarSpine (__G) (__Vs) =
      createEVarSpineW (__G, (Whnf.whnf __Vs))
    let rec createEVarSpineW __0__ __1__ =
      match (__0__, __1__) with
      | (__G, ((Uni (I.Type), s) as Vs)) -> (I.Nil, __Vs)
      | (__G, ((Root _, s) as Vs)) -> (I.Nil, __Vs)
      | (__G, (Pi (((Dec (_, __V1) as D), _), __V2), s)) ->
          let __X = I.newEVar (__G, (I.EClo (__V1, s))) in
          let (__S, __Vs) =
            createEVarSpine (__G, (__V2, (I.Dot ((I.Exp __X), s)))) in
          ((I.App (__X, __S)), __Vs)(* s = id *)(* s = id *)
    let rec createAtomConst (__G) (__H) =
      let cid = match __H with | Const cid -> cid | Skonst cid -> cid in
      let __V = I.constType cid in
      let (__S, __Vs) = createEVarSpine (__G, (__V, I.id)) in
      ((I.Root (__H, __S)), __Vs)
    let rec createAtomBVar (__G) k =
      let Dec (_, __V) = I.ctxDec (__G, k) in
      let (__S, __Vs) = createEVarSpine (__G, (__V, I.id)) in
      ((I.Root ((I.BVar k), __S)), __Vs)
    let createAtomConst = createAtomConst
    let createAtomBVar = createAtomBVar
  end ;;
