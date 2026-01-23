module type NORMALIZE  = sig  end


module Normalize(Normalize:sig module Whnf : WHNF end) : NORMALIZE =
  struct
    exception Error of string 
    module I = IntSyn
    module T = Tomega
    let rec normalizeFor =
      begin function
      | (All ((d_, q_), f_), t) ->
          T.All (((T.decSub (d_, t)), q_), (normalizeFor (f_, (T.dot1 t))))
      | (Ex ((d_, q_), f_), t) ->
          T.Ex
            (((I.decSub (d_, (T.coerceSub t))), q_),
              (normalizeFor (f_, (T.dot1 t))))
      | (And (f1_, f2_), t) ->
          T.And ((normalizeFor (f1_, t)), (normalizeFor (f2_, t)))
      | (FClo (f_, t1), t2) -> normalizeFor (f_, (T.comp (t1, t2)))
      | (World (w_, f_), t) -> T.World (w_, (normalizeFor (f_, t)))
      | (T.True, _) -> T.True end(*      | normalizeFor (T.FVar (G, r))   think about it *)
    let rec whnfFor =
      begin function
      | (All (d_, _), t) as Ft -> Ft
      | (Ex (d_, f_), t) as Ft -> Ft
      | (And (f1_, f2_), t) as Ft -> Ft
      | (FClo (f_, t1), t2) -> whnfFor (f_, (T.comp (t1, t2)))
      | (World (w_, f_), t) as Ft -> Ft
      | (T.True, _) as Ft -> Ft end
  let rec normalizePrg =
    begin function
    | (Var n, t) ->
        (begin match T.varSub (n, t) with
         | Prg (p_) -> p_
         | Idx _ -> raise Domain
         | Exp _ -> raise Domain
         | Block _ -> raise Domain
         | T.Undef -> raise Domain end)
    | (PairExp (u_, p'_), t) ->
        T.PairExp
          ((Whnf.normalize (u_, (T.coerceSub t))), (normalizePrg (p'_, t)))
    | (PairBlock (b_, p'_), t) ->
        T.PairBlock
          ((I.blockSub (b_, (T.coerceSub t))), (normalizePrg (p'_, t)))
    | (PairPrg (p1_, p2_), t) ->
        T.PairPrg ((normalizePrg (p1_, t)), (normalizePrg (p2_, t)))
    | (T.Unit, _) -> T.Unit
    | (EVar (_, { contents = Some (p_) }, _), t) -> T.PClo (p_, t)
    | ((EVar _ as p_), t) -> T.PClo (p_, t)
    | (PClo (p_, t), t') -> normalizePrg (p_, (T.comp (t, t'))) end(* ABP *)
(* ABP -- 1/20/03 *)
let rec normalizeSpine =
  begin function
  | (T.Nil, t) -> T.Nil
  | (AppExp (u_, s_), t) ->
      T.AppExp
        ((Whnf.normalize (u_, (T.coerceSub t))), (normalizeSpine (s_, t)))
  | (AppPrg (p_, s_), t) ->
      T.AppPrg ((normalizePrg (p_, t)), (normalizeSpine (s_, t)))
  | (AppBlock (b_, s_), t) ->
      T.AppBlock
        ((I.blockSub (b_, (T.coerceSub t))), (normalizeSpine (s_, t)))
  | (SClo (s_, t1), t2) -> normalizeSpine (s_, (T.comp (t1, t2))) end
let rec normalizeSub =
  begin function
  | Shift n as s -> s
  | Dot (Prg (p_), s) ->
      T.Dot ((T.Prg (normalizePrg (p_, T.id))), (normalizeSub s))
  | Dot (Exp (e_), s) ->
      T.Dot ((T.Exp (Whnf.normalize (e_, I.id))), (normalizeSub s))
  | Dot (Block k, s) -> T.Dot ((T.Block k), (normalizeSub s))
  | Dot (Idx k, s) -> T.Dot ((T.Idx k), (normalizeSub s)) end
let normalizeFor = normalizeFor
let normalizePrg = normalizePrg
let normalizeSub = normalizeSub
let whnfFor = whnfFor end
