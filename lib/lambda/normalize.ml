
(* Normalizer for Delphin meta level *)
(* Author: Carsten Schuermann *)
module type NORMALIZE  = sig  end;;




(* Internal syntax for functional proof term calculus *)
(* Author: Carsten Schuermann *)
module Normalize(Normalize:sig
                             (*! structure IntSyn' : INTSYN !*)
                             (*! structure Tomega' : TOMEGA !*)
                             (*! sharing Tomega'.IntSyn = IntSyn' !*)
                             module Whnf : WHNF
                           end) : NORMALIZE =
  struct
    (*! sharing Whnf.IntSyn = IntSyn' !*)
    (*! structure IntSyn = IntSyn' !*)
    (*! structure Tomega = Tomega' !*)
    exception Error of string 
    module I = IntSyn
    module T = Tomega
    let rec normalizeFor =
      function
      | (All ((__d, Q), F), t) ->
          T.All (((T.decSub (__d, t)), Q), (normalizeFor (F, (T.dot1 t))))
      | (Ex ((__d, Q), F), t) ->
          T.Ex
            (((I.decSub (__d, (T.coerceSub t))), Q),
              (normalizeFor (F, (T.dot1 t))))
      | (And (__F1, __F2), t) ->
          T.And ((normalizeFor (__F1, t)), (normalizeFor (__F2, t)))
      | (FClo (F, t1), t2) -> normalizeFor (F, (T.comp (t1, t2)))
      | (World (W, F), t) -> T.World (W, (normalizeFor (F, t)))
      | (T.True, _) -> T.True
    let rec whnfFor =
      function
      | (All (__d, _), t) as Ft -> Ft
      | (Ex (__d, F), t) as Ft -> Ft
      | (And (__F1, __F2), t) as Ft -> Ft
      | (FClo (F, t1), t2) -> whnfFor (F, (T.comp (t1, t2)))
      | (World (W, F), t) as Ft -> Ft
      | (T.True, _) as Ft -> Ft
    let rec normalizePrg =
      function
      | (Var n, t) ->
          (match T.varSub (n, t) with
           | Prg (P) -> P
           | Idx _ -> raise Domain
           | Exp _ -> raise Domain
           | Block _ -> raise Domain
           | T.Undef -> raise Domain)
      | (PairExp (__u, __P'), t) ->
          T.PairExp
            ((Whnf.normalize (__u, (T.coerceSub t))), (normalizePrg (__P', t)))
      | (PairBlock (B, __P'), t) ->
          T.PairBlock
            ((I.blockSub (B, (T.coerceSub t))), (normalizePrg (__P', t)))
      | (PairPrg (__P1, __P2), t) ->
          T.PairPrg ((normalizePrg (__P1, t)), (normalizePrg (__P2, t)))
      | (T.Unit, _) -> T.Unit
      | (EVar (_, ref (Some (P)), _), t) -> T.PClo (P, t)
      | ((EVar _ as P), t) -> T.PClo (P, t)
      | (PClo (P, t), t') -> normalizePrg (P, (T.comp (t, t')))
    let rec normalizeSpine =
      function
      | (T.Nil, t) -> T.Nil
      | (AppExp (__u, S), t) ->
          T.AppExp
            ((Whnf.normalize (__u, (T.coerceSub t))), (normalizeSpine (S, t)))
      | (AppPrg (P, S), t) ->
          T.AppPrg ((normalizePrg (P, t)), (normalizeSpine (S, t)))
      | (AppBlock (B, S), t) ->
          T.AppBlock
            ((I.blockSub (B, (T.coerceSub t))), (normalizeSpine (S, t)))
      | (SClo (S, t1), t2) -> normalizeSpine (S, (T.comp (t1, t2)))
    let rec normalizeSub =
      function
      | Shift n as s -> s
      | Dot (Prg (P), s) ->
          T.Dot ((T.Prg (normalizePrg (P, T.id))), (normalizeSub s))
      | Dot (Exp (E), s) ->
          T.Dot ((T.Exp (Whnf.normalize (E, I.id))), (normalizeSub s))
      | Dot (Block k, s) -> T.Dot ((T.Block k), (normalizeSub s))
      | Dot (Idx k, s) -> T.Dot ((T.Idx k), (normalizeSub s))
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
    (* ABP -- 1/20/03 *)
    (* ABP *)
    (*
    and normalizeDec (T.UDec __d, t) = T.UDec (I.decSub (__d, T.coerceSub t))
      | normalizeDec (T.BDec (k, t1), t2) = *)
    let normalizeFor = normalizeFor
    let normalizePrg = normalizePrg
    let normalizeSub = normalizeSub
    let whnfFor = whnfFor
  end ;;
