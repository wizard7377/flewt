
(* Abstraction *)
(* Author: Frank Pfenning, Carsten Schuermann *)
module type ABSTRACT  =
  sig
    exception Error of string 
    val piDepend :
      ((IntSyn.__Dec * IntSyn.__Depend) * IntSyn.__Exp) -> IntSyn.__Exp
    val closedDec :
      (IntSyn.__Dec IntSyn.__Ctx * (IntSyn.__Dec * IntSyn.__Sub)) -> bool
    val closedSub : (IntSyn.__Dec IntSyn.__Ctx * IntSyn.__Sub) -> bool
    val closedExp :
      (IntSyn.__Dec IntSyn.__Ctx * (IntSyn.__Exp * IntSyn.__Sub)) -> bool
    val closedCtx : IntSyn.__Dec IntSyn.__Ctx -> bool
    val closedCTX : Tomega.__Dec IntSyn.__Ctx -> bool
    val abstractDecImp : IntSyn.__Exp -> (int * IntSyn.__Exp)
    val abstractDef :
      (IntSyn.__Exp * IntSyn.__Exp) -> (int * (IntSyn.__Exp * IntSyn.__Exp))
    val abstractCtxs :
      IntSyn.__Dec IntSyn.__Ctx list ->
        (IntSyn.__Dec IntSyn.__Ctx * IntSyn.__Dec IntSyn.__Ctx list)
    val abstractTomegaSub :
      Tomega.__Sub -> (Tomega.__Dec IntSyn.__Ctx * Tomega.__Sub)
    val abstractTomegaPrg :
      Tomega.__Prg -> (Tomega.__Dec IntSyn.__Ctx * Tomega.__Prg)
    val abstractSpine :
      (IntSyn.__Spine * IntSyn.__Sub) -> (IntSyn.dctx * IntSyn.__Spine)
    val collectEVars :
      (IntSyn.dctx * IntSyn.eclo * IntSyn.__Exp list) -> IntSyn.__Exp list
    val collectEVarsSpine :
      (IntSyn.dctx * (IntSyn.__Spine * IntSyn.__Sub) * IntSyn.__Exp list) ->
        IntSyn.__Exp list
    val raiseTerm : (IntSyn.dctx * IntSyn.__Exp) -> IntSyn.__Exp
    val raiseType : (IntSyn.dctx * IntSyn.__Exp) -> IntSyn.__Exp
  end;;




(* Abstraction *)
(* Author: Frank Pfenning, Carsten Schuermann *)
(* Modified: Roberto Virga *)
module Abstract(Abstract:sig
                           (*! structure IntSyn' : INTSYN !*)
                           module Whnf : WHNF
                           module Unify : UNIFY
                           (*! sharing Whnf.IntSyn = IntSyn' !*)
                           (*! sharing Unify.IntSyn = IntSyn' !*)
                           module Constraints : CONSTRAINTS
                         end) : ABSTRACT =
  struct
    exception Error of string 
    module I = IntSyn
    module T = Tomega
    module C = Constraints
    module O = Order
    type __EFLVar =
      | EV of I.__Exp 
      | FV of (string * I.__Exp) 
      | LV of I.__Block 
      | PV of T.__Prg 
    let rec collectConstraints =
      function
      | I.Null -> nil
      | Decl (__g, FV _) -> collectConstraints __g
      | Decl (__g, EV (EVar (_, _, _, ref nil))) -> collectConstraints __g
      | Decl (__g, EV (EVar (_, _, _, ref cnstrL))) ->
          (@) (C.simplify cnstrL) collectConstraints __g
      | Decl (__g, LV _) -> collectConstraints __g
    let rec checkConstraints (K) =
      let constraints = collectConstraints K in
      let _ =
        match constraints with | nil -> () | _ -> raise (C.Error constraints) in
      ()
    let rec eqEVar arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (EVar (r1, _, _, _), EV (EVar (r2, _, _, _))) -> r1 = r2
      | (_, _) -> false__
    let rec eqFVar arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (FVar (n1, _, _), FV (n2, _)) -> n1 = n2
      | (_, _) -> false__
    let rec eqLVar arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (LVar (r1, _, _), LV (LVar (r2, _, _))) -> r1 = r2
      | (_, _) -> false__
    let rec exists (P) (K) =
      let rec exists' =
        function | I.Null -> false__ | Decl (K', y) -> (P y) || (exists' K') in
      exists' K
    let rec or__ =
      function
      | (I.Maybe, _) -> I.Maybe
      | (_, I.Maybe) -> I.Maybe
      | (I.Meta, _) -> I.Meta
      | (_, I.Meta) -> I.Meta
      | (I.No, I.No) -> I.No
    let rec occursInExp =
      function
      | (k, Uni _) -> I.No
      | (k, Pi (DP, __v)) ->
          or__ ((occursInDecP (k, DP)), (occursInExp ((k + 1), __v)))
      | (k, Root (H, S)) -> occursInHead (k, H, (occursInSpine (k, S)))
      | (k, Lam (__d, __v)) ->
          or__ ((occursInDec (k, __d)), (occursInExp ((k + 1), __v)))
      | (k, FgnExp csfe) ->
          I.FgnExpStd.fold csfe
            (function
             | (__u, DP) ->
                 or__ (DP, (occursInExp (k, (Whnf.normalize (__u, I.id))))))
            I.No
    let rec occursInHead =
      function
      | (k, BVar k', DP) -> if k = k' then I.Maybe else DP
      | (k, Const _, DP) -> DP
      | (k, Def _, DP) -> DP
      | (k, Proj _, DP) -> DP
      | (k, FgnConst _, DP) -> DP
      | (k, Skonst _, I.No) -> I.No
      | (k, Skonst _, I.Meta) -> I.Meta
      | (k, Skonst _, I.Maybe) -> I.Meta
    let rec occursInSpine =
      function
      | (_, I.Nil) -> I.No
      | (k, App (__u, S)) ->
          or__ ((occursInExp (k, __u)), (occursInSpine (k, S)))
    let rec occursInDec (k, Dec (_, __v)) = occursInExp (k, __v)
    let rec occursInDecP (k, (__d, _)) = occursInDec (k, __d)
    let rec piDepend =
      function
      | ((__d, I.No), __v) as DPV -> I.Pi DPV
      | ((__d, I.Meta), __v) as DPV -> I.Pi DPV
      | ((__d, I.Maybe), __v) -> I.Pi ((__d, (occursInExp (1, __v))), __v)
    let rec raiseType =
      function
      | (I.Null, __v) -> __v
      | (Decl (__g, __d), __v) -> raiseType (__g, (I.Pi ((__d, I.Maybe), __v)))
    let rec raiseTerm =
      function
      | (I.Null, __u) -> __u
      | (Decl (__g, __d), __u) -> raiseTerm (__g, (I.Lam (__d, __u)))
    let rec collectExpW =
      function
      | (__g, (Uni (__l), s), K) -> K
      | (__g, (Pi ((__d, _), __v), s), K) ->
          collectExp
            ((I.Decl (__g, (I.decSub (__d, s)))), (__v, (I.dot1 s)),
              (collectDec (__g, (__d, s), K)))
      | (__g, (Root ((FVar (name, __v, s') as F), S), s), K) ->
          if exists (eqFVar F) K
          then collectSpine (__g, (S, s), K)
          else
            collectSpine
              (__g, (S, s),
                (I.Decl ((collectExp (I.Null, (__v, I.id), K)), (FV (name, __v)))))
      | (__g, (Root (Proj ((LVar (ref (None), sk, (l, t)) as __l), i), S), s), K)
          ->
          collectSpine
            (__g, (S, s), (collectBlock (__g, (I.blockSub (__l, s)), K)))
      | (__g, (Root (_, S), s), K) -> collectSpine (__g, (S, s), K)
      | (__g, (Lam (__d, __u), s), K) ->
          collectExp
            ((I.Decl (__g, (I.decSub (__d, s)))), (__u, (I.dot1 s)),
              (collectDec (__g, (__d, s), K)))
      | (__g, ((EVar (r, GX, __v, cnstrs) as x), s), K) ->
          if exists (eqEVar x) K
          then collectSub (__g, s, K)
          else
            (let __v' = raiseType (GX, __v) in
             let K' = collectExp (I.Null, (__v', I.id), K) in
             collectSub (__g, s, (I.Decl (K', (EV x)))))
      | (__g, (FgnExp csfe, s), K) ->
          I.FgnExpStd.fold csfe
            (function | (__u, K) -> collectExp (__g, (__u, s), K)) K
    let rec collectExp (__g, __Us, K) = collectExpW (__g, (Whnf.whnf __Us), K)
    let rec collectSpine =
      function
      | (__g, (I.Nil, _), K) -> K
      | (__g, (SClo (S, s'), s), K) ->
          collectSpine (__g, (S, (I.comp (s', s))), K)
      | (__g, (App (__u, S), s), K) ->
          collectSpine (__g, (S, s), (collectExp (__g, (__u, s), K)))
    let rec collectDec =
      function
      | (__g, (Dec (_, __v), s), K) -> collectExp (__g, (__v, s), K)
      | (__g, (BDec (_, (_, t)), s), K) -> collectSub (__g, (I.comp (t, s)), K)
      | (__g, (NDec _, s), K) -> K
    let rec collectSub =
      function
      | (__g, Shift _, K) -> K
      | (__g, Dot (Idx _, s), K) -> collectSub (__g, s, K)
      | (__g, Dot (Exp (__u), s), K) ->
          collectSub (__g, s, (collectExp (__g, (__u, I.id), K)))
      | (__g, Dot (Block (B), s), K) ->
          collectSub (__g, s, (collectBlock (__g, B, K)))
    let rec collectBlock =
      function
      | (__g, LVar (ref (Some (B)), sk, _), K) ->
          collectBlock (__g, (I.blockSub (B, sk)), K)
      | (__g, (LVar (_, sk, (l, t)) as __l), K) ->
          if exists (eqLVar __l) K
          then collectSub (__g, (I.comp (t, sk)), K)
          else I.Decl ((collectSub (__g, (I.comp (t, sk)), K)), (LV __l))
    let rec collectCtx =
      function
      | (G0, I.Null, K) -> (G0, K)
      | (G0, Decl (__g, __d), K) ->
          let (G0', K') = collectCtx (G0, __g, K) in
          let K'' = collectDec (G0', (__d, I.id), K') in
          ((I.Decl (G0, __d)), K'')
    let rec collectCtxs =
      function
      | (G0, nil, K) -> K
      | (G0, (__g)::__Gs, K) ->
          let (G0', K') = collectCtx (G0, __g, K) in collectCtxs (G0', __Gs, K')
    let rec abstractEVar =
      function
      | (Decl (K', EV (EVar (r', _, _, _))), depth, (EVar (r, _, _, _) as x))
          ->
          if r = r'
          then I.BVar (depth + 1)
          else abstractEVar (K', (depth + 1), x)
      | (Decl (K', _), depth, x) -> abstractEVar (K', (depth + 1), x)
    let rec abstractFVar =
      function
      | (Decl (K', FV (n', _)), depth, (FVar (n, _, _) as F)) ->
          if n = n'
          then I.BVar (depth + 1)
          else abstractFVar (K', (depth + 1), F)
      | (Decl (K', _), depth, F) -> abstractFVar (K', (depth + 1), F)
    let rec abstractLVar =
      function
      | (Decl (K', LV (LVar (r', _, _))), depth, (LVar (r, _, _) as __l)) ->
          if r = r'
          then I.Bidx (depth + 1)
          else abstractLVar (K', (depth + 1), __l)
      | (Decl (K', _), depth, __l) -> abstractLVar (K', (depth + 1), __l)
    let rec abstractExpW =
      function
      | (K, depth, ((Uni (__l) as __u), s)) -> __u
      | (K, depth, (Pi ((__d, P), __v), s)) ->
          piDepend
            (((abstractDec (K, depth, (__d, s))), P),
              (abstractExp (K, (depth + 1), (__v, (I.dot1 s)))))
      | (K, depth, (Root ((FVar _ as F), S), s)) ->
          I.Root
            ((abstractFVar (K, depth, F)),
              (abstractSpine (K, depth, (S, s))))
      | (K, depth, (Root (Proj ((LVar _ as __l), i), S), s)) ->
          I.Root
            ((I.Proj ((abstractLVar (K, depth, __l)), i)),
              (abstractSpine (K, depth, (S, s))))
      | (K, depth, (Root (H, S), s)) ->
          I.Root (H, (abstractSpine (K, depth, (S, s))))
      | (K, depth, (Lam (__d, __u), s)) ->
          I.Lam
            ((abstractDec (K, depth, (__d, s))),
              (abstractExp (K, (depth + 1), (__u, (I.dot1 s)))))
      | (K, depth, ((EVar _ as x), s)) ->
          I.Root
            ((abstractEVar (K, depth, x)),
              (abstractSub (K, depth, s, I.Nil)))
      | (K, depth, (FgnExp csfe, s)) ->
          I.FgnExpStd.Map.apply csfe
            (function | __u -> abstractExp (K, depth, (__u, s)))
    let rec abstractExp (K, depth, __Us) =
      abstractExpW (K, depth, (Whnf.whnf __Us))
    let rec abstractSub =
      function
      | (K, depth, Shift k, S) ->
          if k < depth
          then
            abstractSub
              (K, depth, (I.Dot ((I.Idx (k + 1)), (I.Shift (k + 1)))), S)
          else S
      | (K, depth, Dot (Idx k, s), S) ->
          abstractSub
            (K, depth, s, (I.App ((I.Root ((I.BVar k), I.Nil)), S)))
      | (K, depth, Dot (Exp (__u), s), S) ->
          abstractSub
            (K, depth, s, (I.App ((abstractExp (K, depth, (__u, I.id))), S)))
    let rec abstractSpine =
      function
      | (K, depth, (I.Nil, _)) -> I.Nil
      | (K, depth, (SClo (S, s'), s)) ->
          abstractSpine (K, depth, (S, (I.comp (s', s))))
      | (K, depth, (App (__u, S), s)) ->
          I.App
            ((abstractExp (K, depth, (__u, s))),
              (abstractSpine (K, depth, (S, s))))
    let rec abstractDec (K, depth, (Dec (x, __v), s)) =
      I.Dec (x, (abstractExp (K, depth, (__v, s))))
    let rec abstractSOME =
      function
      | (K, Shift 0) -> I.Shift (I.ctxLength K)
      | (K, Shift n) -> I.Shift (I.ctxLength K)
      | (K, Dot (Idx k, s)) -> I.Dot ((I.Idx k), (abstractSOME (K, s)))
      | (K, Dot (Exp (__u), s)) ->
          I.Dot
            ((I.Exp (abstractExp (K, 0, (__u, I.id)))), (abstractSOME (K, s)))
      | (K, Dot (Block (LVar _ as __l), s)) ->
          I.Dot ((I.Block (abstractLVar (K, 0, __l))), (abstractSOME (K, s)))
    let rec abstractCtx =
      function
      | (K, depth, I.Null) -> (I.Null, depth)
      | (K, depth, Decl (__g, __d)) ->
          let (__g', depth') = abstractCtx (K, depth, __g) in
          let __d' = abstractDec (K, depth', (__d, I.id)) in
          ((I.Decl (__g', __d')), (depth' + 1))
    let rec abstractCtxlist =
      function
      | (K, depth, nil) -> nil
      | (K, depth, (__g)::__Gs) ->
          let (__g', depth') = abstractCtx (K, depth, __g) in
          let __Gs' = abstractCtxlist (K, depth', __Gs) in __g' :: __Gs'
    let rec abstractKPi =
      function
      | (I.Null, __v) -> __v
      | (Decl (K', EV (EVar (_, GX, VX, _))), __v) ->
          let __v' = raiseType (GX, VX) in
          let __v'' = abstractExp (K', 0, (__v', I.id)) in
          abstractKPi (K', (I.Pi (((I.Dec (None, __v'')), I.Maybe), __v)))
      | (Decl (K', FV (name, __v')), __v) ->
          let __v'' = abstractExp (K', 0, (__v', I.id)) in
          abstractKPi (K', (I.Pi (((I.Dec ((Some name), __v'')), I.Maybe), __v)))
      | (Decl (K', LV (LVar (r, _, (l, t)))), __v) ->
          let t' = abstractSOME (K', t) in
          abstractKPi (K', (I.Pi (((I.BDec (None, (l, t'))), I.Maybe), __v)))
    let rec abstractKLam =
      function
      | (I.Null, __u) -> __u
      | (Decl (K', EV (EVar (_, GX, VX, _))), __u) ->
          let __v' = raiseType (GX, VX) in
          abstractKLam
            (K',
              (I.Lam ((I.Dec (None, (abstractExp (K', 0, (__v', I.id))))), __u)))
      | (Decl (K', FV (name, __v')), __u) ->
          abstractKLam
            (K',
              (I.Lam
                 ((I.Dec ((Some name), (abstractExp (K', 0, (__v', I.id))))),
                   __u)))
    let rec abstractKCtx =
      function
      | I.Null -> I.Null
      | Decl (K', EV (EVar (_, GX, VX, _))) ->
          let __v' = raiseType (GX, VX) in
          let __v'' = abstractExp (K', 0, (__v', I.id)) in
          I.Decl ((abstractKCtx K'), (I.Dec (None, __v'')))
      | Decl (K', FV (name, __v')) ->
          let __v'' = abstractExp (K', 0, (__v', I.id)) in
          I.Decl ((abstractKCtx K'), (I.Dec ((Some name), __v'')))
      | Decl (K', LV (LVar (r, _, (l, t)))) ->
          let t' = abstractSOME (K', t) in
          I.Decl ((abstractKCtx K'), (I.BDec (None, (l, t'))))
    let rec abstractDecImp (__v) =
      let K = collectExp (I.Null, (__v, I.id), I.Null) in
      let _ = checkConstraints K in
      ((I.ctxLength K), (abstractKPi (K, (abstractExp (K, 0, (__v, I.id))))))
    let rec abstractDef (__u, __v) =
      let K =
        collectExp
          (I.Null, (__u, I.id), (collectExp (I.Null, (__v, I.id), I.Null))) in
      let _ = checkConstraints K in
      ((I.ctxLength K),
        ((abstractKLam (K, (abstractExp (K, 0, (__u, I.id))))),
          (abstractKPi (K, (abstractExp (K, 0, (__v, I.id)))))))
    let rec abstractSpineExt (S, s) =
      let K = collectSpine (I.Null, (S, s), I.Null) in
      let _ = checkConstraints K in
      let __g = abstractKCtx K in
      let S = abstractSpine (K, 0, (S, s)) in (__g, S)
    let rec abstractCtxs (__Gs) =
      let K = collectCtxs (I.Null, __Gs, I.Null) in
      let _ = checkConstraints K in
      ((abstractKCtx K), (abstractCtxlist (K, 0, __Gs)))
    let rec closedDec (__g, (Dec (_, __v), s)) =
      match collectExp (__g, (__v, s), I.Null) with
      | I.Null -> true__
      | _ -> false__
    let rec closedSub =
      function
      | (__g, Shift _) -> true__
      | (__g, Dot (Idx _, s)) -> closedSub (__g, s)
      | (__g, Dot (Exp (__u), s)) ->
          (match collectExp (__g, (__u, I.id), I.Null) with
           | I.Null -> closedSub (__g, s)
           | _ -> false__)
    let rec closedExp (__g, (__u, s)) =
      match collectExp (__g, (__u, I.id), I.Null) with
      | I.Null -> true__
      | _ -> false__
    let rec closedCtx =
      function
      | I.Null -> true__
      | Decl (__g, __d) -> (closedCtx __g) && (closedDec (__g, (__d, I.id)))
    let rec closedFor =
      function
      | (Psi, T.True) -> true__
      | (Psi, All ((__d, _), F)) ->
          (closedDEC (Psi, __d)) && (closedFor ((I.Decl (Psi, __d)), F))
      | (Psi, Ex ((__d, _), F)) ->
          (closedDec ((T.coerceCtx Psi), (__d, I.id))) &&
            (closedFor ((I.Decl (Psi, (T.UDec __d))), F))
    let rec closedDEC =
      function
      | (Psi, UDec (__d)) -> closedDec ((T.coerceCtx Psi), (__d, I.id))
      | (Psi, PDec (_, F, _, _)) -> closedFor (Psi, F)
    let rec closedCTX =
      function
      | I.Null -> true__
      | Decl (Psi, __d) -> (closedCTX Psi) && (closedDEC (Psi, __d))
    let rec evarsToK =
      function | nil -> I.Null | (x)::__Xs -> I.Decl ((evarsToK __Xs), (EV x))
    let rec KToEVars =
      function
      | I.Null -> nil
      | Decl (K, EV (x)) -> (::) x KToEVars K
      | Decl (K, _) -> KToEVars K
    let rec collectEVars (__g, __Us, __Xs) =
      KToEVars (collectExp (__g, __Us, (evarsToK __Xs)))
    let rec collectEVarsSpine (__g, (S, s), __Xs) =
      KToEVars (collectSpine (__g, (S, s), (evarsToK __Xs)))
    let rec collectPrg =
      function
      | (_, (EVar (Psi, r, F, _, _, _) as P), K) -> I.Decl (K, (PV P))
      | (Psi, T.Unit, K) -> K
      | (Psi, PairExp (__u, P), K) ->
          collectPrg (Psi, P, (collectExp ((T.coerceCtx Psi), (__u, I.id), K)))
    let rec abstractPVar =
      function
      | (Decl (K', PV (EVar (_, r', _, _, _, _))), depth,
         (EVar (_, r, _, _, _, _) as P)) ->
          if r = r'
          then T.Var (depth + 1)
          else abstractPVar (K', (depth + 1), P)
      | (Decl (K', _), depth, P) -> abstractPVar (K', (depth + 1), P)
    let rec abstractPrg =
      function
      | (K, depth, (EVar _ as x)) -> abstractPVar (K, depth, x)
      | (K, depth, T.Unit) -> T.Unit
      | (K, depth, PairExp (__u, P)) ->
          T.PairExp
            ((abstractExp (K, depth, (__u, I.id))),
              (abstractPrg (K, depth, P)))
    let rec collectTomegaSub =
      function
      | Shift 0 -> I.Null
      | Dot (Exp (__u), t) ->
          collectExp (I.Null, (__u, I.id), (collectTomegaSub t))
      | Dot (Block (B), t) -> collectBlock (I.Null, B, (collectTomegaSub t))
      | Dot (Prg (P), t) -> collectPrg (I.Null, P, (collectTomegaSub t))
    let rec abstractOrder =
      function
      | (K, depth, Arg (us1, us2)) ->
          O.Arg
            (((abstractExp (K, depth, us1)), I.id),
              ((abstractExp (K, depth, us2)), I.id))
      | (K, depth, Simul (__Os)) ->
          O.Simul (map (function | O -> abstractOrder (K, depth, O)) __Os)
      | (K, depth, Lex (__Os)) ->
          O.Lex (map (function | O -> abstractOrder (K, depth, O)) __Os)
    let rec abstractTC =
      function
      | (K, depth, Abs (__d, TC)) ->
          T.Abs
            ((abstractDec (K, depth, (__d, I.id))),
              (abstractTC (K, depth, TC)))
      | (K, depth, Conj (TC1, TC2)) ->
          T.Conj ((abstractTC (K, depth, TC1)), (abstractTC (K, depth, TC2)))
      | (K, depth, Base (O)) -> T.Base (abstractOrder (K, depth, O))
    let rec abstractTCOpt =
      function
      | (K, depth, None) -> None
      | (K, depth, Some (TC)) -> Some (abstractTC (K, depth, TC))
    let rec abstractMetaDec =
      function
      | (K, depth, UDec (__d)) -> T.UDec (abstractDec (K, depth, (__d, I.id)))
      | (K, depth, PDec (xx, F, TC1, TC2)) ->
          T.PDec (xx, (abstractFor (K, depth, F)), TC1, TC2)
    let rec abstractFor =
      function
      | (K, depth, T.True) -> T.True
      | (K, depth, All ((MD, Q), F)) ->
          T.All
            (((abstractMetaDec (K, depth, MD)), Q),
              (abstractFor (K, depth, F)))
      | (K, depth, Ex ((__d, Q), F)) ->
          T.Ex
            (((abstractDec (K, depth, (__d, I.id))), Q),
              (abstractFor (K, depth, F)))
      | (K, depth, And (__F1, __F2)) ->
          T.And ((abstractFor (K, depth, __F1)), (abstractFor (K, depth, __F2)))
      | (K, depth, World (W, F)) -> T.World (W, (abstractFor (K, depth, F)))
    let rec abstractPsi =
      function
      | I.Null -> I.Null
      | Decl (K', EV (EVar (_, GX, VX, _))) ->
          let __v' = raiseType (GX, VX) in
          let __v'' = abstractExp (K', 0, (__v', I.id)) in
          I.Decl ((abstractPsi K'), (T.UDec (I.Dec (None, __v''))))
      | Decl (K', FV (name, __v')) ->
          let __v'' = abstractExp (K', 0, (__v', I.id)) in
          I.Decl ((abstractPsi K'), (T.UDec (I.Dec ((Some name), __v''))))
      | Decl (K', LV (LVar (r, _, (l, t)))) ->
          let t' = abstractSOME (K', t) in
          I.Decl ((abstractPsi K'), (T.UDec (I.BDec (None, (l, t')))))
      | Decl (K', PV (EVar (GX, _, FX, TC1, TC2, _))) ->
          let __F' = abstractFor (K', 0, (T.forSub (FX, T.id))) in
          let TC1' = abstractTCOpt (K', 0, TC1) in
          let TC2' = abstractTCOpt (K', 0, TC2) in
          I.Decl ((abstractPsi K'), (T.PDec (None, __F', TC1, TC2)))
    let rec abstractTomegaSub t =
      let K = collectTomegaSub t in
      let t' = abstractTomegaSub' (K, 0, t) in
      let Psi = abstractPsi K in (Psi, t')
    let rec abstractTomegaSub' =
      function
      | (K, depth, Shift 0) -> T.Shift depth
      | (K, depth, Dot (Exp (__u), t)) ->
          T.Dot
            ((T.Exp (abstractExp (K, depth, (__u, I.id)))),
              (abstractTomegaSub' (K, depth, t)))
      | (K, depth, Dot (Block (B), t)) ->
          T.Dot
            ((T.Block (abstractLVar (K, depth, B))),
              (abstractTomegaSub' (K, depth, t)))
      | (K, depth, Dot (Prg (P), t)) ->
          T.Dot
            ((T.Prg (abstractPrg (K, depth, P))),
              (abstractTomegaSub' (K, depth, t)))
    let rec abstractTomegaPrg (P) =
      let K = collectPrg (I.Null, P, I.Null) in
      let __P' = abstractPrg (K, 0, P) in let Psi = abstractPsi K in (Psi, __P')
    (* Intermediate Data Structure *)
    (* y ::= x         for  GX |- x : VX *)
    (*     | (F, __v)        if . |- F : __v *)
    (*     | __l             if . |- __l in W *)
    (*     | P                            *)
    (*
       We write {{K}} for the context of K, where EVars, FVars, LVars have
       been translated to declarations and their occurrences to BVars.
       We write {{__u}}_K, {{S}}_K for the corresponding translation of an
       expression or spine.

       Just like contexts __g, any K is implicitly assumed to be
       well-formed and in dependency order.

       We write  K ||- __u  if all EVars and FVars in __u are collected in K.
       In particular, . ||- __u means __u contains no EVars or FVars.  Similarly,
       for spines K ||- S and other syntactic categories.

       Collection and abstraction raise Error if there are unresolved
       constraints after simplification.
    *)
    (* collectConstraints K = cnstrs
       where cnstrs collects all constraints attached to EVars in K
    *)
    (* checkConstraints (K) = ()
       Effect: raises Constraints.Error(C) if K contains unresolved constraints
    *)
    (* checkEmpty Cnstr = ()
       raises Error exception if constraints Cnstr cannot be simplified
       to the empty constraint
    *)
    (*
    fun checkEmpty (nil) = ()
      | checkEmpty (Cnstr) =
        (case C.simplify Cnstr
           of nil => ()
            | _ => raise Error "Typing ambiguous -- unresolved constraints")
    *)
    (* eqEVar x y = B
       where B iff x and y represent same variable
    *)
    (* eqFVar F y = B
       where B iff x and y represent same variable
    *)
    (* eqLVar __l y = B
       where B iff x and y represent same variable
    *)
    (* exists P K = B
       where B iff K = K1, y, K2  s.t. P y  holds
    *)
    (* this should be non-strict *)
    (* perhaps the whole repeated traversal are now a performance
       bottleneck in PCC applications where logic programming search
       followed by abstraction creates certificates.  such certificates
       are large, so the quadratic algorithm is not really acceptable.
       possible improvement, collect, abstract, then traverse one more
       time to determine status of all variables.
    *)
    (* Wed Aug  6 16:37:57 2003 -fp *)
    (* !!! *)
    (* occursInExp (k, __u) = DP,

       Invariant:
       If    __u in nf
       then  DP = No      iff k does not occur in __u
             DP = Maybe   iff k occurs in __u some place not as an argument to a Skonst
             DP = Meta    iff k occurs in __u and only as arguments to Skonsts
    *)
    (* no case for Redex, EVar, EClo *)
    (* no case for FVar *)
    (* no case for SClo *)
    (* piDepend ((__d,P), __v) = Pi ((__d,__P'), __v)
       where __P' = Maybe if __d occurs in __v, __P' = No otherwise
    *)
    (* optimize to have fewer traversals? -cs *)
    (* pre-Twelf 1.2 code walk Fri May  8 11:17:10 1998 *)
    (* raiseType (__g, __v) = {{__g}} __v

       Invariant:
       If __g |- __v : __l
       then  . |- {{__g}} __v : __l

       All abstractions are potentially dependent.
    *)
    (* raiseTerm (__g, __u) = [[__g]] __u

       Invariant:
       If __g |- __u : __v
       then  . |- [[__g]] __u : {{__g}} __v

       All abstractions are potentially dependent.
    *)
    (* collectExpW (__g, (__u, s), K) = K'

       Invariant:
       If    __g |- s : G1     G1 |- __u : __v      (__u,s) in whnf
       No circularities in __u
             (enforced by extended occurs-check for FVars in Unify)
       and   K' = K, K''
             where K'' contains all EVars and FVars in (__u,s)
    *)
    (* Possible optimization: Calculate also the normal form of the term *)
    (* s' = ^|__g| *)
    (* BUG : We forget to deref L.  use collectBlock instead
             FPCHECK
             -cs Sat Jul 24 18:48:59 2010
            was:
      | collectExpW (__g, (I.Root (I.Proj (__l as I.LVar (r, sk, (l, t)), i), S), s), K) =
        if exists (eqLVar __l) K
           note: don't collect t again below *)
    (* was: collectSpine (__g, (S, s), collectSub (I.Null, t, K)) *)
    (* Sun Dec 16 10:54:52 2001 -fp !!! *)
    (* -fp Sun Dec  1 21:12:12 2002 *)
    (* collectSpine (__g, (S, s), I.Decl (collectSub (__g, I.comp(t,s), K), LV __l)) *)
    (* was :
         collectSpine (__g, (S, s), collectSub (__g, I.comp(t,s), I.Decl (K, LV __l)))
         July 22, 2010 -fp -cs
         *)
    (* val _ = checkEmpty !cnstrs *)
    (* inefficient *)
    (* No other cases can occur due to whnf invariant *)
    (* collectExp (__g, (__u, s), K) = K'

       same as collectExpW  but  (__u,s) need not to be in whnf
    *)
    (* collectSpine (__g, (S, s), K) = K'

       Invariant:
       If    __g |- s : G1     G1 |- S : __v > P
       then  K' = K, K''
       where K'' contains all EVars and FVars in (S, s)
     *)
    (* collectDec (__g, (x:__v, s), K) = K'

       Invariant:
       If    __g |- s : G1     G1 |- __v : __l
       then  K' = K, K''
       where K'' contains all EVars and FVars in (__v, s)
    *)
    (* . |- t : Gsome, so do not compose with s *)
    (* Sat Dec  8 13:28:15 2001 -fp *)
    (* was: collectSub (I.Null, t, K) *)
    (* collectSub (__g, s, K) = K'

       Invariant:
       If    __g |- s : G1
       then  K' = K, K''
       where K'' contains all EVars and FVars in s
    *)
    (* next case should be impossible *)
    (*
      | collectSub (__g, I.Dot (I.Undef, s), K) =
          collectSub (__g, s, K)
    *)
    (* collectBlock (__g, B, K) where __g |- B block *)
    (* collectBlock (B, K) *)
    (* correct?? -fp Sun Dec  1 21:15:33 2002 *)
    (* was: t in the two lines above, July 22, 2010, -fp -cs *)
    (* | collectBlock (__g, I.Bidx _, K) = K *)
    (* should be impossible: Fronts of substitutions are never Bidx *)
    (* Sat Dec  8 13:30:43 2001 -fp *)
    (* collectCtx (G0, __g, K) = (G0', K')
       Invariant:
       If G0 |- __g ctx,
       then G0' = G0,__g
       and K' = K, K'' where K'' contains all EVars and FVars in __g
    *)
    (* collectCtxs (G0, __Gs, K) = K'
       Invariant: G0 |- G1,...,Gn ctx where __Gs = [G1,...,Gn]
       and K' = K, K'' where K'' contains all EVars and FVars in G1,...,Gn
    *)
    (* abstractEVar (K, depth, x) = C'

       Invariant:
       If   __g |- x : __v
       and  |__g| = depth
       and  x occurs in K  at kth position (starting at 1)
       then C' = BVar (depth + k)
       and  {{K}}, __g |- C' : __v
    *)
    (*      | abstractEVar (I.Decl (K', FV (n', _)), depth, x) =
          abstractEVar (K', depth+1, x) remove later --cs*)
    (* abstractFVar (K, depth, F) = C'

       Invariant:
       If   __g |- F : __v
       and  |__g| = depth
       and  F occurs in K  at kth position (starting at 1)
       then C' = BVar (depth + k)
       and  {{K}}, __g |- C' : __v
    *)
    (*      | abstractFVar (I.Decl(K', EV _), depth, F) =
          abstractFVar (K', depth+1, F) remove later --cs *)
    (* abstractLVar (K, depth, __l) = C'

       Invariant:
       If   __g |- __l : __v
       and  |__g| = depth
       and  __l occurs in K  at kth position (starting at 1)
       then C' = Bidx (depth + k)
       and  {{K}}, __g |- C' : __v
    *)
    (* abstractExpW (K, depth, (__u, s)) = __u'
       __u' = {{__u[s]}}_K

       Invariant:
       If    __g |- s : G1     G1 |- __u : __v    (__u,s) is in whnf
       and   K is internal context in dependency order
       and   |__g| = depth
       and   K ||- __u and K ||- __v
       then  {{K}}, __g |- __u' : __v'
       and   . ||- __u' and . ||- __v'
       and   __u' is in nf
    *)
    (* abstractExp (K, depth, (__u, s)) = __u'

       same as abstractExpW, but (__u,s) need not to be in whnf
    *)
    (* abstractSub (K, depth, s, S) = S'      (implicit raising)
       S' = {{s}}_K @@ S

       Invariant:
       If   __g |- s : G1
       and  |__g| = depth
       and  K ||- s
       then {{K}}, __g |- S' : {G1}.W > W   (for some W)
       and  . ||- S'
    *)
    (* k = depth *)
    (* abstractSpine (K, depth, (S, s)) = S'
       where S' = {{S[s]}}_K

       Invariant:
       If   __g |- s : G1     G1 |- S : __v > P
       and  K ||- S
       and  |__g| = depth

       then {{K}}, __g |- S' : __v' > __P'
       and  . ||- S'
    *)
    (* abstractDec (K, depth, (x:__v, s)) = x:__v'
       where __v = {{__v[s]}}_K

       Invariant:
       If   __g |- s : G1     G1 |- __v : __l
       and  K ||- __v
       and  |__g| = depth

       then {{K}}, __g |- __v' : __l
       and  . ||- __v'
    *)
    (* abstractSOME (K, s) = s'
       s' = {{s}}_K

       Invariant:
       If    . |- s : Gsome
       and   K is internal context in dependency order
       and   K ||- s
       then  {{K}} |- s' : Gsome  --- not changing domain of s'

       Update: modified for globality invariant of . |- t : Gsome
       Sat Dec  8 13:35:55 2001 -fp
       Above is now incorrect
       Sun Dec  1 22:36:50 2002 -fp
    *)
    (* n = 0 by invariant, check for now *)
    (* n > 0 *)
    (* I.Block (I.Bidx _) should be impossible as head of substitutions *)
    (* abstractCtx (K, depth, __g) = (__g', depth')
       where __g' = {{__g}}_K

       Invariants:
       If G0 |- __g ctx
       and K ||- __g
       and |G0| = depth
       then {{K}}, G0 |- __g' ctx
       and . ||- __g'
       and |G0,__g| = depth'
    *)
    (* abstractCtxlist (K, depth, [G1,...,Gn]) = [G1',...,Gn']
       where Gi' = {{Gi}}_K

       Invariants:
       if G0 |- G1,...,Gn ctx
       and K ||- G1,...,Gn
       and |G0| = depth
       then {{K}}, G0 |- G1',...,Gn' ctx
       and . ||- G1',...,Gn'
    *)
    (* dead code under new reconstruction -kw
     getlevel (__v) = __l if __g |- __v : __l

       Invariant: __g |- __v : __l' for some __l'
    *)
    (* checkType (__v) = () if __g |- __v : type

       Invariant: __g |- __v : __l' for some __l'
    *)
    (* abstractKPi (K, __v) = __v'
       where __v' = {{K}} __v

       Invariant:
       If   {{K}} |- __v : __l
       and  . ||- __v

       then __v' = {{K}} __v
       and  . |- __v' : __l
       and  . ||- __v'
    *)
    (* enforced by reconstruction -kw
          val _ = checkType __v'' *)
    (* enforced by reconstruction -kw
          val _ = checkType __v'' *)
    (* abstractKLam (K, __u) = __u'
       where __u' = [[K]] __u

       Invariant:
       If   {{K}} |- __u : __v
       and  . ||- __u
       and  . ||- __v

       then __u' = [[K]] __u
       and  . |- __u' : {{K}} __v
       and  . ||- __u'
    *)
    (* enforced by reconstruction -kw
          val _ = checkType __v'' *)
    (* enforced by reconstruction -kw
          val _ = checkType __v'' *)
    (* abstractDecImp __v = (k', __v')    rename --cs  (see above) *)
    (* abstractDef  (__u, __v) = (k', (__u', __v'))

       Invariant:
       If    . |- __v : __l
       and   . |- __u : __v
       and   K1 ||- __v
       and   K2 ||- __u
       and   K = K1, K2

       then  . |- __v' : __l
       and   __v' = {{K}} __v
       and   . |- __u' : __v'
       and   __u' = [[K]] __u
       and   . ||- __v'
       and   . ||- __u'
       and   k' = |K|
    *)
    (* abstractCtxs [G1,...,Gn] = G0, [G1',...,Gn']
       Invariants:
       If . |- G1,...,Gn ctx
          K ||- G1,...,Gn for some K
       then G0 |- G1',...,Gn' ctx for G0 = {{K}}
       and G1',...,Gn' nf
       and . ||- G1',...,Gn' ctx
    *)
    (* closedDec (__g, __d) = true iff __d contains no EVar or FVar *)
    (* collectEVars (__g, __u[s], __Xs) = __Xs'
       Invariants:
         __g |- __u[s] : __v
         __Xs' extends __Xs by new EVars in __u[s]
    *)
    (* for the theorem prover:
       collect and abstract in subsitutions  including residual lemmas
       pending approval of Frank.
    *)
    (* abstractPVar (K, depth, __l) = C'

       Invariant:
       If   __g |- __l : __v
       and  |__g| = depth
       and  __l occurs in K  at kth position (starting at 1)
       then C' = Bidx (depth + k)
       and  {{K}}, __g |- C' : __v
    *)
    (* TC cannot contain free FVAR's or EVars'
            --cs  Fri Apr 30 13:45:50 2004 *)
    (* Argument must be in normal form *)
    (* enforced by reconstruction -kw
          val _ = checkType __v'' *)
    (* enforced by reconstruction -kw
          val _ = checkType __v'' *)
    (* What's happening with GX? *)
    (* What's happening with TCs? *)
    (* just added to abstract over residual lemmas  -cs *)
    (* Tomorrow: Make collection in program values a priority *)
    (* Then just traverse the Tomega by abstraction to get to the types of those
       variables. *)
    let raiseType = raiseType
    let raiseTerm = raiseTerm
    let piDepend = piDepend
    let closedDec = closedDec
    let closedSub = closedSub
    let closedExp = closedExp
    let abstractDecImp = abstractDecImp
    let abstractDef = abstractDef
    let abstractCtxs = abstractCtxs
    let abstractTomegaSub = abstractTomegaSub
    let abstractTomegaPrg = abstractTomegaPrg
    let abstractSpine = abstractSpineExt
    let collectEVars = collectEVars
    let collectEVarsSpine = collectEVarsSpine
    let closedCtx = closedCtx
    let closedCTX = closedCTX
  end ;;
