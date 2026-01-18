
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
      | (All (D, F), t) ->
          T.All ((T.decSub (D, t)), (normalizeFor (F, (T.dot1 t))))
      | (Ex (D, F), t) ->
          T.Ex
            ((I.decSub (D, (T.coerceSub t))), (normalizeFor (F, (T.dot1 t))))
      | (And (F1, F2), t) ->
          T.And ((normalizeFor (F1, t)), (normalizeFor (F2, t)))
      | (FClo (F, t1), t2) -> normalizeFor (F, (T.comp (t1, t2)))
      | (World (W, F), t) -> T.World (W, (normalizeFor (F, t)))
      | (T.True, _) -> T.True
    let rec normalizePrg =
      function
      | ((Root (Const _, _) as P), t) -> P
      | ((Root (Var n, _) as P), t) ->
          normalizePrg (P, (T.Dot ((T.varSub (n, t)), T.id)))
      | (Lam (D, P'), t) -> T.Lam (D, (normalizePrg (P', (T.dot1 t))))
      | (PairExp (U, P'), t) ->
          T.PairExp
            ((I.EClo (Whnf.whnf ((U, (T.coerceSub t)) : I.eclo))),
              (normalizePrg (P', t)))
      | (PairPrg (P1, P2), t) ->
          T.PairPrg ((normalizePrg (P1, t)), (normalizePrg (P2, t)))
      | (T.Unit, _) -> T.Unit
      | (Redex (P, S), t) ->
          T.Redex ((normalizePrg (P, t)), (normalizeSpine S))
      | (Rec (D, P), t) -> T.Rec (D, (normalizePrg (P, t)))
      | ((Case _ as P), t) -> P
      | ((EVar (Psi, ref (SOME (P')), _) as P), t) -> normalizePrg (P', t)
    let rec normalizeSpine =
      function
      | T.Nil -> T.Nil
      | AppExp (U, S) -> T.AppExp (U, (normalizeSpine S))
      | AppPrg (P, S) ->
          T.AppPrg ((normalizePrg (P, T.id)), (normalizeSpine S))
      | AppBlock (B, S) -> T.AppBlock (B, (normalizeSpine S))
    let rec normalizeSub =
      function
      | Shift n as s -> s
      | Dot (Prg (P), s) ->
          T.Dot ((T.Prg (normalizePrg (P, T.id))), (normalizeSub s))
      | Dot (F, s) -> T.Dot (F, (normalizeSub s))
    (*      | normalizeFor (T.FVar (G, r))   think about it *)
    (* normalizePrg (P, t) = (P', t')

       Invariant:
       If   Psi' |- P :: F
       and  Psi  |- t :: Psi'
       and  P doesn't contain free EVars
       then there exists a Psi'', F'
       s.t. Psi'' |- F' for
       and  Psi'' |- P' :: F'
       and  Psi |- t' : Psi''
       and  Psi |- F [t] == F' [t']
       and  Psi |- P [t] == P' [t'] : F [t]
       and  Psi |- P' [t'] :nf: F [t]
    *)
    (*      | normalizePrg (T.PairBlock (B, P'), t) =
          T.PairBlock (B, normalizePrg P') *)
    (* Clearly, the redex should be removed here *)
    (*
    and normalizeDec (T.UDec D, t) = T.UDec (I.decSub (D, T.coerceSub t))
      | normalizeDec (T.BDec (k, t1), t2) = *)
    let normalizeFor = normalizeFor
    let normalizePrg = normalizePrg
    let normalizeSpine = normalizeSpine
    let normalizeSub = normalizeSub
  end ;;
