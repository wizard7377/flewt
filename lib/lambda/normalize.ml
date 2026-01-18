
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
      | (All ((D, Q), F), t) ->
          T.All (((T.decSub (D, t)), Q), (normalizeFor (F, (T.dot1 t))))
      | (Ex ((D, Q), F), t) ->
          T.Ex
            (((I.decSub (D, (T.coerceSub t))), Q),
              (normalizeFor (F, (T.dot1 t))))
      | (And (F1, F2), t) ->
          T.And ((normalizeFor (F1, t)), (normalizeFor (F2, t)))
      | (FClo (F, t1), t2) -> normalizeFor (F, (T.comp (t1, t2)))
      | (World (W, F), t) -> T.World (W, (normalizeFor (F, t)))
      | (T.True, _) -> T.True
    let rec whnfFor =
      function
      | (All (D, _), t) as Ft -> Ft
      | (Ex (D, F), t) as Ft -> Ft
      | (And (F1, F2), t) as Ft -> Ft
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
      | (PairExp (U, P'), t) ->
          T.PairExp
            ((Whnf.normalize (U, (T.coerceSub t))), (normalizePrg (P', t)))
      | (PairBlock (B, P'), t) ->
          T.PairBlock
            ((I.blockSub (B, (T.coerceSub t))), (normalizePrg (P', t)))
      | (PairPrg (P1, P2), t) ->
          T.PairPrg ((normalizePrg (P1, t)), (normalizePrg (P2, t)))
      | (T.Unit, _) -> T.Unit
      | (EVar (_, ref (SOME (P)), _), t) -> T.PClo (P, t)
      | ((EVar _ as P), t) -> T.PClo (P, t)
      | (PClo (P, t), t') -> normalizePrg (P, (T.comp (t, t')))
    let rec normalizeSpine =
      function
      | (T.Nil, t) -> T.Nil
      | (AppExp (U, S), t) ->
          T.AppExp
            ((Whnf.normalize (U, (T.coerceSub t))), (normalizeSpine (S, t)))
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
    (* ABP -- 1/20/03 *)
    (* ABP *)
    (*
    and normalizeDec (T.UDec D, t) = T.UDec (I.decSub (D, T.coerceSub t))
      | normalizeDec (T.BDec (k, t1), t2) = *)
    let normalizeFor = normalizeFor
    let normalizePrg = normalizePrg
    let normalizeSub = normalizeSub
    let whnfFor = whnfFor
  end ;;
