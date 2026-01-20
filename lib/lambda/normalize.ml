
module type NORMALIZE  = sig  end;;




module Normalize(Normalize:sig module Whnf : WHNF end) : NORMALIZE =
  struct
    exception Error of string 
    module I = IntSyn
    module T = Tomega
    let rec normalizeFor __0__ __1__ =
      match (__0__, __1__) with
      | (All ((__D, __Q), __F), t) ->
          T.All
            (((T.decSub (__D, t)), __Q), (normalizeFor (__F, (T.dot1 t))))
      | (Ex ((__D, __Q), __F), t) ->
          T.Ex
            (((I.decSub (__D, (T.coerceSub t))), __Q),
              (normalizeFor (__F, (T.dot1 t))))
      | (And (__F1, __F2), t) ->
          T.And ((normalizeFor (__F1, t)), (normalizeFor (__F2, t)))
      | (FClo (__F, t1), t2) -> normalizeFor (__F, (T.comp (t1, t2)))
      | (World (__W, __F), t) -> T.World (__W, (normalizeFor (__F, t)))
      | (T.True, _) -> T.True(*      | normalizeFor (T.FVar (G, r))   think about it *)
    let rec whnfFor __2__ =
      match __2__ with
      | (All (__D, _), t) as Ft -> Ft
      | (Ex (__D, __F), t) as Ft -> Ft
      | (And (__F1, __F2), t) as Ft -> Ft
      | (FClo (__F, t1), t2) -> whnfFor (__F, (T.comp (t1, t2)))
      | (World (__W, __F), t) as Ft -> Ft
      | (T.True, _) as Ft -> Ft
    let rec normalizePrg __3__ __4__ =
      match (__3__, __4__) with
      | (Var n, t) ->
          (match T.varSub (n, t) with
           | Prg (__P) -> __P
           | Idx _ -> raise Domain
           | Exp _ -> raise Domain
           | Block _ -> raise Domain
           | T.Undef -> raise Domain)
      | (PairExp (__U, __P'), t) ->
          T.PairExp
            ((Whnf.normalize (__U, (T.coerceSub t))),
              (normalizePrg (__P', t)))
      | (PairBlock (__B, __P'), t) ->
          T.PairBlock
            ((I.blockSub (__B, (T.coerceSub t))), (normalizePrg (__P', t)))
      | (PairPrg (__P1, __P2), t) ->
          T.PairPrg ((normalizePrg (__P1, t)), (normalizePrg (__P2, t)))
      | (T.Unit, _) -> T.Unit
      | (EVar (_, { contents = Some (__P) }, _), t) -> T.PClo (__P, t)
      | ((EVar _ as P), t) -> T.PClo (__P, t)
      | (PClo (__P, t), t') -> normalizePrg (__P, (T.comp (t, t')))(* ABP *)
      (* ABP -- 1/20/03 *)
    let rec normalizeSpine __5__ __6__ =
      match (__5__, __6__) with
      | (T.Nil, t) -> T.Nil
      | (AppExp (__U, __S), t) ->
          T.AppExp
            ((Whnf.normalize (__U, (T.coerceSub t))),
              (normalizeSpine (__S, t)))
      | (AppPrg (__P, __S), t) ->
          T.AppPrg ((normalizePrg (__P, t)), (normalizeSpine (__S, t)))
      | (AppBlock (__B, __S), t) ->
          T.AppBlock
            ((I.blockSub (__B, (T.coerceSub t))), (normalizeSpine (__S, t)))
      | (SClo (__S, t1), t2) -> normalizeSpine (__S, (T.comp (t1, t2)))
    let rec normalizeSub =
      function
      | Shift n as s -> s
      | Dot (Prg (__P), s) ->
          T.Dot ((T.Prg (normalizePrg (__P, T.id))), (normalizeSub s))
      | Dot (Exp (__E), s) ->
          T.Dot ((T.Exp (Whnf.normalize (__E, I.id))), (normalizeSub s))
      | Dot (Block k, s) -> T.Dot ((T.Block k), (normalizeSub s))
      | Dot (Idx k, s) -> T.Dot ((T.Idx k), (normalizeSub s))
    let normalizeFor = normalizeFor
    let normalizePrg = normalizePrg
    let normalizeSub = normalizeSub
    let whnfFor = whnfFor
  end ;;
