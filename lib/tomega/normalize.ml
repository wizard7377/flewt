
(* Normalizer for Delphin meta level *)
(* Author: Carsten Schuermann *)
module type NORMALIZE  =
  sig
    module IntSyn : INTSYN
    module Tomega : TOMEGA
    val normalizeFor : (Tomega.__For * Tomega.__Sub) -> Tomega.__For
    val normalizePrg : (Tomega.__Prg * Tomega.__Sub) -> Tomega.__Prg
    val normalizeSpine : (Tomega.__Spine * Tomega.__Sub) -> Tomega.__Spine
    val normalizeSub : Tomega.__Sub -> Tomega.__Sub
  end;;




(* Internal syntax for functional proof term calculus *)
(* Author: Carsten Schuermann *)
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
      function
      | (All (__d, F), t) ->
          T.All ((T.decSub (__d, t)), (normalizeFor (F, (T.dot1 t))))
      | (Ex (__d, F), t) ->
          T.Ex
            ((I.decSub (__d, (T.coerceSub t))), (normalizeFor (F, (T.dot1 t))))
      | (And (__F1, __F2), t) ->
          T.And ((normalizeFor (__F1, t)), (normalizeFor (__F2, t)))
      | (FClo (F, t1), t2) -> normalizeFor (F, (T.comp (t1, t2)))
      | (World (W, F), t) -> T.World (W, (normalizeFor (F, t)))
      | (T.True, _) -> T.True
    let rec normalizePrg =
      function
      | ((Root (Const _, _) as P), t) -> P
      | ((Root (Var n, _) as P), t) ->
          normalizePrg (P, (T.Dot ((T.varSub (n, t)), T.id)))
      | (Lam (__d, __P'), t) -> T.Lam (__d, (normalizePrg (__P', (T.dot1 t))))
      | (PairExp (__u, __P'), t) ->
          T.PairExp
            ((I.EClo (Whnf.whnf ((__u, (T.coerceSub t)) : I.eclo))),
              (normalizePrg (__P', t)))
      | (PairPrg (__P1, __P2), t) ->
          T.PairPrg ((normalizePrg (__P1, t)), (normalizePrg (__P2, t)))
      | (T.Unit, _) -> T.Unit
      | (Redex (P, S), t) ->
          T.Redex ((normalizePrg (P, t)), (normalizeSpine S))
      | (Rec (__d, P), t) -> T.Rec (__d, (normalizePrg (P, t)))
      | ((Case _ as P), t) -> P
      | ((EVar (Psi, ref (Some (__P')), _) as P), t) -> normalizePrg (__P', t)
    let rec normalizeSpine =
      function
      | T.Nil -> T.Nil
      | AppExp (__u, S) -> T.AppExp (__u, (normalizeSpine S))
      | AppPrg (P, S) ->
          T.AppPrg ((normalizePrg (P, T.id)), (normalizeSpine S))
      | AppBlock (B, S) -> T.AppBlock (B, (normalizeSpine S))
    let rec normalizeSub =
      function
      | Shift n as s -> s
      | Dot (Prg (P), s) ->
          T.Dot ((T.Prg (normalizePrg (P, T.id))), (normalizeSub s))
      | Dot (F, s) -> T.Dot (F, (normalizeSub s))
    (*      | normalizeFor (T.FVar (__g, r))   think about it *)
    (* normalizePrg (P, t) = (__P', t')

       Invariant:
       If   Psi' |- P :: F
       and  Psi  |- t :: Psi'
       and  P doesn't contain free EVars
       then there exists a Psi'', __F'
       s.t. Psi'' |- __F' for
       and  Psi'' |- __P' :: __F'
       and  Psi |- t' : Psi''
       and  Psi |- F [t] == __F' [t']
       and  Psi |- P [t] == __P' [t'] : F [t]
       and  Psi |- __P' [t'] :nf: F [t]
    *)
    (*      | normalizePrg (T.PairBlock (B, __P'), t) =
          T.PairBlock (B, normalizePrg __P') *)
    (* Clearly, the redex should be removed here *)
    (*
    and normalizeDec (T.UDec __d, t) = T.UDec (I.decSub (__d, T.coerceSub t))
      | normalizeDec (T.BDec (k, t1), t2) = *)
    let normalizeFor = normalizeFor
    let normalizePrg = normalizePrg
    let normalizeSpine = normalizeSpine
    let normalizeSub = normalizeSub
  end ;;
