module type NORMALIZE  =
  sig
    module IntSyn : INTSYN
    module Tomega : TOMEGA
    val normalizeFor : (Tomega.for_ * Tomega.sub_) -> Tomega.for_
    val normalizePrg : (Tomega.prg_ * Tomega.sub_) -> Tomega.prg_
    val normalizeSpine : (Tomega.spine_ * Tomega.sub_) -> Tomega.spine_
    val normalizeSub : Tomega.sub_ -> Tomega.sub_
  end


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
    let rec normalizeFor =
      begin function
      | (All (d_, f_), t) ->
          T.All ((T.decSub (d_, t)), (normalizeFor (f_, (T.dot1 t))))
      | (Ex (d_, f_), t) ->
          T.Ex
            ((I.decSub (d_, (T.coerceSub t))),
              (normalizeFor (f_, (T.dot1 t))))
      | (And (f1_, f2_), t) ->
          T.And ((normalizeFor (f1_, t)), (normalizeFor (f2_, t)))
      | (FClo (f_, t1), t2) -> normalizeFor (f_, (T.comp (t1, t2)))
      | (World (w_, f_), t) -> T.World (w_, (normalizeFor (f_, t)))
      | (T.True, _) -> T.True end(*      | normalizeFor (T.FVar (G, r))   think about it *)
    let rec normalizePrg =
      begin function
      | ((Root (Const _, _) as p_), t) -> p_
      | ((Root (Var n, _) as p_), t) ->
          normalizePrg (p_, (T.Dot ((T.varSub (n, t)), T.id)))
      | (Lam (d_, p'_), t) -> T.Lam (d_, (normalizePrg (p'_, (T.dot1 t))))
      | (PairExp (u_, p'_), t) ->
          T.PairExp
            ((I.EClo (Whnf.whnf ((u_, (T.coerceSub t)) : I.eclo))),
              (normalizePrg (p'_, t)))
      | (PairPrg (p1_, p2_), t) ->
          T.PairPrg ((normalizePrg (p1_, t)), (normalizePrg (p2_, t)))
      | (T.Unit, _) -> T.Unit
      | (Redex (p_, s_), t) ->
          T.Redex ((normalizePrg (p_, t)), (normalizeSpine s_))
      | (Rec (d_, p_), t) -> T.Rec (d_, (normalizePrg (p_, t)))
      | ((Case _ as p_), t) -> p_
      | ((EVar (Psi, { contents = Some (p'_) }, _) as p_), t) ->
          normalizePrg (p'_, t) end(* Clearly, the redex should be removed here *)
    (*      | normalizePrg (T.PairBlock (B, P'), t) =
          T.PairBlock (B, normalizePrg P') *)
  let rec normalizeSpine =
    begin function
    | T.Nil -> T.Nil
    | AppExp (u_, s_) -> T.AppExp (u_, (normalizeSpine s_))
    | AppPrg (p_, s_) ->
        T.AppPrg ((normalizePrg (p_, T.id)), (normalizeSpine s_))
    | AppBlock (b_, s_) -> T.AppBlock (b_, (normalizeSpine s_)) end
let rec normalizeSub =
  begin function
  | Shift n as s -> s
  | Dot (Prg (p_), s) ->
      T.Dot ((T.Prg (normalizePrg (p_, T.id))), (normalizeSub s))
  | Dot (f_, s) -> T.Dot (f_, (normalizeSub s)) end
let normalizeFor = normalizeFor
let normalizePrg = normalizePrg
let normalizeSpine = normalizeSpine
let normalizeSub = normalizeSub end
