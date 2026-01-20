
module type NORMALIZE  =
  sig
    module IntSyn : INTSYN
    module Tomega : TOMEGA
    val normalizeFor : Tomega.__For -> Tomega.__Sub -> Tomega.__For
    val normalizePrg : Tomega.__Prg -> Tomega.__Sub -> Tomega.__Prg
    val normalizeSpine : Tomega.__Spine -> Tomega.__Sub -> Tomega.__Spine
    val normalizeSub : Tomega.__Sub -> Tomega.__Sub
  end;;




module Normalize(Normalize:sig
                             module IntSyn' : INTSYN
                             module Tomega' : TOMEGA
                             module Whnf : WHNF
                           end) : NORMALIZE =
  struct
    module IntSyn = IntSyn'
    module Tomega = Tomega'
    exception Error of string 
    module I = IntSyn'
    module T = Tomega'
    let rec normalizeFor __0__ __1__ =
      match (__0__, __1__) with
      | (All (__D, __F), t) ->
          T.All ((T.decSub (__D, t)), (normalizeFor (__F, (T.dot1 t))))
      | (Ex (__D, __F), t) ->
          T.Ex
            ((I.decSub (__D, (T.coerceSub t))),
              (normalizeFor (__F, (T.dot1 t))))
      | (And (__F1, __F2), t) ->
          T.And ((normalizeFor (__F1, t)), (normalizeFor (__F2, t)))
      | (FClo (__F, t1), t2) -> normalizeFor (__F, (T.comp (t1, t2)))
      | (World (__W, __F), t) -> T.World (__W, (normalizeFor (__F, t)))
      | (T.True, _) -> T.True(*      | normalizeFor (T.FVar (G, r))   think about it *)
    let rec normalizePrg __2__ __3__ =
      match (__2__, __3__) with
      | ((Root (Const _, _) as P), t) -> __P
      | ((Root (Var n, _) as P), t) ->
          normalizePrg (__P, (T.Dot ((T.varSub (n, t)), T.id)))
      | (Lam (__D, __P'), t) ->
          T.Lam (__D, (normalizePrg (__P', (T.dot1 t))))
      | (PairExp (__U, __P'), t) ->
          T.PairExp
            ((I.EClo (Whnf.whnf ((__U, (T.coerceSub t)) : I.eclo))),
              (normalizePrg (__P', t)))
      | (PairPrg (__P1, __P2), t) ->
          T.PairPrg ((normalizePrg (__P1, t)), (normalizePrg (__P2, t)))
      | (T.Unit, _) -> T.Unit
      | (Redex (__P, __S), t) ->
          T.Redex ((normalizePrg (__P, t)), (normalizeSpine __S))
      | (Rec (__D, __P), t) -> T.Rec (__D, (normalizePrg (__P, t)))
      | ((Case _ as P), t) -> __P
      | ((EVar (Psi, { contents = Some (__P') }, _) as P), t) ->
          normalizePrg (__P', t)(* Clearly, the redex should be removed here *)
      (*      | normalizePrg (T.PairBlock (B, P'), t) =
          T.PairBlock (B, normalizePrg P') *)
    let rec normalizeSpine =
      function
      | T.Nil -> T.Nil
      | AppExp (__U, __S) -> T.AppExp (__U, (normalizeSpine __S))
      | AppPrg (__P, __S) ->
          T.AppPrg ((normalizePrg (__P, T.id)), (normalizeSpine __S))
      | AppBlock (__B, __S) -> T.AppBlock (__B, (normalizeSpine __S))
    let rec normalizeSub =
      function
      | Shift n as s -> s
      | Dot (Prg (__P), s) ->
          T.Dot ((T.Prg (normalizePrg (__P, T.id))), (normalizeSub s))
      | Dot (__F, s) -> T.Dot (__F, (normalizeSub s))
    let normalizeFor = normalizeFor
    let normalizePrg = normalizePrg
    let normalizeSpine = normalizeSpine
    let normalizeSub = normalizeSub
  end ;;
