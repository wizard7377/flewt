
module type ABSTRACT  =
  sig
    exception Error of
      ((string)(* Author: Frank Pfenning, Carsten Schuermann *)(* Abstraction *))
      
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




module Abstract(Abstract:sig
                           module Whnf : WHNF
                           module Unify : UNIFY
                           module Constraints :
                           ((CONSTRAINTS)(* Abstraction *)
                           (* Author: Frank Pfenning, Carsten Schuermann *)
                           (* Modified: Roberto Virga *)
                           (*! structure IntSyn' : INTSYN !*)(*! sharing Whnf.IntSyn = IntSyn' !*)
                           (*! sharing Unify.IntSyn = IntSyn' !*))
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
      | Decl (g, FV _) -> collectConstraints g
      | Decl (g, EV (EVar (_, _, _, ref nil))) -> collectConstraints g
      | Decl (g, EV (EVar (_, _, _, ref cnstrL))) ->
          (@) (C.simplify cnstrL) collectConstraints g
      | Decl (g, LV _) -> collectConstraints g
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
      let exists' =
        function | I.Null -> false__ | Decl (K', Y) -> (P Y) || (exists' K') in
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
      | (k, Pi (DP, V)) ->
          or__ ((occursInDecP (k, DP)), (occursInExp ((k + 1), V)))
      | (k, Root (H, S)) -> occursInHead (k, H, (occursInSpine (k, S)))
      | (k, Lam (D, V)) ->
          or__ ((occursInDec (k, D)), (occursInExp ((k + 1), V)))
      | (k, FgnExp csfe) ->
          I.FgnExpStd.fold csfe
            (function
             | (U, DP) ->
                 or__ (DP, (occursInExp (k, (Whnf.normalize (U, I.id))))))
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
      | (k, App (U, S)) ->
          or__ ((occursInExp (k, U)), (occursInSpine (k, S)))
    let rec occursInDec (k, Dec (_, V)) = occursInExp (k, V)
    let rec occursInDecP (k, (D, _)) = occursInDec (k, D)
    let rec piDepend =
      function
      | ((D, I.No), V) as DPV -> I.Pi DPV
      | ((D, I.Meta), V) as DPV -> I.Pi DPV
      | ((D, I.Maybe), V) -> I.Pi ((D, (occursInExp (1, V))), V)
    let rec raiseType =
      function
      | (I.Null, V) -> V
      | (Decl (g, D), V) -> raiseType (g, (I.Pi ((D, I.Maybe), V)))
    let rec raiseTerm =
      function
      | (I.Null, U) -> U
      | (Decl (g, D), U) -> raiseTerm (g, (I.Lam (D, U)))
    let rec collectExpW =
      function
      | (g, (Uni (L), s), K) -> K
      | (g, (Pi ((D, _), V), s), K) ->
          collectExp
            ((I.Decl (g, (I.decSub (D, s)))), (V, (I.dot1 s)),
              (collectDec (g, (D, s), K)))
      | (g, (Root ((FVar (name, V, s') as F), S), s), K) ->
          if exists (eqFVar F) K
          then collectSpine (g, (S, s), K)
          else
            collectSpine
              (g, (S, s),
                (I.Decl ((collectExp (I.Null, (V, I.id), K)), (FV (name, V)))))
      | (g, (Root (Proj ((LVar (ref (NONE), sk, (l, t)) as L), i), S), s), K)
          ->
          collectSpine
            (g, (S, s), (collectBlock (g, (I.blockSub (L, s)), K)))
      | (g, (Root (_, S), s), K) -> collectSpine (g, (S, s), K)
      | (g, (Lam (D, U), s), K) ->
          collectExp
            ((I.Decl (g, (I.decSub (D, s)))), (U, (I.dot1 s)),
              (collectDec (g, (D, s), K)))
      | (g, ((EVar (r, GX, V, cnstrs) as X), s), K) ->
          if exists (eqEVar X) K
          then collectSub (g, s, K)
          else
            (let V' = raiseType (GX, V) in
             let K' = collectExp (I.Null, (V', I.id), K) in
             collectSub (g, s, (I.Decl (K', (EV X)))))
      | (g, (FgnExp csfe, s), K) ->
          I.FgnExpStd.fold csfe
            (function | (U, K) -> collectExp (g, (U, s), K)) K
    let rec collectExp (g, Us, K) = collectExpW (g, (Whnf.whnf Us), K)
    let rec collectSpine =
      function
      | (g, (I.Nil, _), K) -> K
      | (g, (SClo (S, s'), s), K) ->
          collectSpine (g, (S, (I.comp (s', s))), K)
      | (g, (App (U, S), s), K) ->
          collectSpine (g, (S, s), (collectExp (g, (U, s), K)))
    let rec collectDec =
      function
      | (g, (Dec (_, V), s), K) -> collectExp (g, (V, s), K)
      | (g, (BDec (_, (_, t)), s), K) -> collectSub (g, (I.comp (t, s)), K)
      | (g, (NDec _, s), K) -> K
    let rec collectSub =
      function
      | (g, Shift _, K) -> K
      | (g, Dot (Idx _, s), K) -> collectSub (g, s, K)
      | (g, Dot (Exp (U), s), K) ->
          collectSub (g, s, (collectExp (g, (U, I.id), K)))
      | (g, Dot (Block (B), s), K) ->
          collectSub (g, s, (collectBlock (g, B, K)))
    let rec collectBlock =
      function
      | (g, LVar (ref (SOME (B)), sk, _), K) ->
          collectBlock (g, (I.blockSub (B, sk)), K)
      | (g, (LVar (_, sk, (l, t)) as L), K) ->
          if exists (eqLVar L) K
          then collectSub (g, (I.comp (t, sk)), K)
          else I.Decl ((collectSub (g, (I.comp (t, sk)), K)), (LV L))
    let rec collectCtx =
      function
      | (G0, I.Null, K) -> (G0, K)
      | (G0, Decl (g, D), K) ->
          let (G0', K') = collectCtx (G0, g, K) in
          let K'' = collectDec (G0', (D, I.id), K') in
          ((I.Decl (G0, D)), K'')
    let rec collectCtxs =
      function
      | (G0, nil, K) -> K
      | (G0, (g)::Gs, K) ->
          let (G0', K') = collectCtx (G0, g, K) in collectCtxs (G0', Gs, K')
    let rec abstractEVar =
      function
      | (Decl (K', EV (EVar (r', _, _, _))), depth, (EVar (r, _, _, _) as X))
          ->
          if r = r'
          then I.BVar (depth + 1)
          else abstractEVar (K', (depth + 1), X)
      | (Decl (K', _), depth, X) -> abstractEVar (K', (depth + 1), X)
    let rec abstractFVar =
      function
      | (Decl (K', FV (n', _)), depth, (FVar (n, _, _) as F)) ->
          if n = n'
          then I.BVar (depth + 1)
          else abstractFVar (K', (depth + 1), F)
      | (Decl (K', _), depth, F) -> abstractFVar (K', (depth + 1), F)
    let rec abstractLVar =
      function
      | (Decl (K', LV (LVar (r', _, _))), depth, (LVar (r, _, _) as L)) ->
          if r = r'
          then I.Bidx (depth + 1)
          else abstractLVar (K', (depth + 1), L)
      | (Decl (K', _), depth, L) -> abstractLVar (K', (depth + 1), L)
    let rec abstractExpW =
      function
      | (K, depth, ((Uni (L) as U), s)) -> U
      | (K, depth, (Pi ((D, P), V), s)) ->
          piDepend
            (((abstractDec (K, depth, (D, s))), P),
              (abstractExp (K, (depth + 1), (V, (I.dot1 s)))))
      | (K, depth, (Root ((FVar _ as F), S), s)) ->
          I.Root
            ((abstractFVar (K, depth, F)),
              (abstractSpine (K, depth, (S, s))))
      | (K, depth, (Root (Proj ((LVar _ as L), i), S), s)) ->
          I.Root
            ((I.Proj ((abstractLVar (K, depth, L)), i)),
              (abstractSpine (K, depth, (S, s))))
      | (K, depth, (Root (H, S), s)) ->
          I.Root (H, (abstractSpine (K, depth, (S, s))))
      | (K, depth, (Lam (D, U), s)) ->
          I.Lam
            ((abstractDec (K, depth, (D, s))),
              (abstractExp (K, (depth + 1), (U, (I.dot1 s)))))
      | (K, depth, ((EVar _ as X), s)) ->
          I.Root
            ((abstractEVar (K, depth, X)),
              (abstractSub (K, depth, s, I.Nil)))
      | (K, depth, (FgnExp csfe, s)) ->
          I.FgnExpStd.Map.apply csfe
            (function | U -> abstractExp (K, depth, (U, s)))
    let rec abstractExp (K, depth, Us) =
      abstractExpW (K, depth, (Whnf.whnf Us))
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
      | (K, depth, Dot (Exp (U), s), S) ->
          abstractSub
            (K, depth, s, (I.App ((abstractExp (K, depth, (U, I.id))), S)))
    let rec abstractSpine =
      function
      | (K, depth, (I.Nil, _)) -> I.Nil
      | (K, depth, (SClo (S, s'), s)) ->
          abstractSpine (K, depth, (S, (I.comp (s', s))))
      | (K, depth, (App (U, S), s)) ->
          I.App
            ((abstractExp (K, depth, (U, s))),
              (abstractSpine (K, depth, (S, s))))
    let rec abstractDec (K, depth, (Dec (x, V), s)) =
      I.Dec (x, (abstractExp (K, depth, (V, s))))
    let rec abstractSOME =
      function
      | (K, Shift 0) -> I.Shift (I.ctxLength K)
      | (K, Shift n) -> I.Shift (I.ctxLength K)
      | (K, Dot (Idx k, s)) -> I.Dot ((I.Idx k), (abstractSOME (K, s)))
      | (K, Dot (Exp (U), s)) ->
          I.Dot
            ((I.Exp (abstractExp (K, 0, (U, I.id)))), (abstractSOME (K, s)))
      | (K, Dot (Block (LVar _ as L), s)) ->
          I.Dot ((I.Block (abstractLVar (K, 0, L))), (abstractSOME (K, s)))
    let rec abstractCtx =
      function
      | (K, depth, I.Null) -> (I.Null, depth)
      | (K, depth, Decl (g, D)) ->
          let (g', depth') = abstractCtx (K, depth, g) in
          let D' = abstractDec (K, depth', (D, I.id)) in
          ((I.Decl (g', D')), (depth' + 1))
    let rec abstractCtxlist =
      function
      | (K, depth, nil) -> nil
      | (K, depth, (g)::Gs) ->
          let (g', depth') = abstractCtx (K, depth, g) in
          let Gs' = abstractCtxlist (K, depth', Gs) in g' :: Gs'
    let rec abstractKPi =
      function
      | (I.Null, V) -> V
      | (Decl (K', EV (EVar (_, GX, VX, _))), V) ->
          let V' = raiseType (GX, VX) in
          let V'' = abstractExp (K', 0, (V', I.id)) in
          abstractKPi (K', (I.Pi (((I.Dec (NONE, V'')), I.Maybe), V)))
      | (Decl (K', FV (name, V')), V) ->
          let V'' = abstractExp (K', 0, (V', I.id)) in
          abstractKPi (K', (I.Pi (((I.Dec ((SOME name), V'')), I.Maybe), V)))
      | (Decl (K', LV (LVar (r, _, (l, t)))), V) ->
          let t' = abstractSOME (K', t) in
          abstractKPi (K', (I.Pi (((I.BDec (NONE, (l, t'))), I.Maybe), V)))
    let rec abstractKLam =
      function
      | (I.Null, U) -> U
      | (Decl (K', EV (EVar (_, GX, VX, _))), U) ->
          let V' = raiseType (GX, VX) in
          abstractKLam
            (K',
              (I.Lam ((I.Dec (NONE, (abstractExp (K', 0, (V', I.id))))), U)))
      | (Decl (K', FV (name, V')), U) ->
          abstractKLam
            (K',
              (I.Lam
                 ((I.Dec ((SOME name), (abstractExp (K', 0, (V', I.id))))),
                   U)))
    let rec abstractKCtx =
      function
      | I.Null -> I.Null
      | Decl (K', EV (EVar (_, GX, VX, _))) ->
          let V' = raiseType (GX, VX) in
          let V'' = abstractExp (K', 0, (V', I.id)) in
          I.Decl ((abstractKCtx K'), (I.Dec (NONE, V'')))
      | Decl (K', FV (name, V')) ->
          let V'' = abstractExp (K', 0, (V', I.id)) in
          I.Decl ((abstractKCtx K'), (I.Dec ((SOME name), V'')))
      | Decl (K', LV (LVar (r, _, (l, t)))) ->
          let t' = abstractSOME (K', t) in
          I.Decl ((abstractKCtx K'), (I.BDec (NONE, (l, t'))))
    let rec abstractDecImp (V) =
      let K = collectExp (I.Null, (V, I.id), I.Null) in
      let _ = checkConstraints K in
      ((I.ctxLength K), (abstractKPi (K, (abstractExp (K, 0, (V, I.id))))))
    let rec abstractDef (U, V) =
      let K =
        collectExp
          (I.Null, (U, I.id), (collectExp (I.Null, (V, I.id), I.Null))) in
      let _ = checkConstraints K in
      ((I.ctxLength K),
        ((abstractKLam (K, (abstractExp (K, 0, (U, I.id))))),
          (abstractKPi (K, (abstractExp (K, 0, (V, I.id)))))))
    let rec abstractSpineExt (S, s) =
      let K = collectSpine (I.Null, (S, s), I.Null) in
      let _ = checkConstraints K in
      let g = abstractKCtx K in
      let S = abstractSpine (K, 0, (S, s)) in (g, S)
    let rec abstractCtxs (Gs) =
      let K = collectCtxs (I.Null, Gs, I.Null) in
      let _ = checkConstraints K in
      ((abstractKCtx K), (abstractCtxlist (K, 0, Gs)))
    let rec closedDec (g, (Dec (_, V), s)) =
      match collectExp (g, (V, s), I.Null) with
      | I.Null -> true__
      | _ -> false__
    let rec closedSub =
      function
      | (g, Shift _) -> true__
      | (g, Dot (Idx _, s)) -> closedSub (g, s)
      | (g, Dot (Exp (U), s)) ->
          (match collectExp (g, (U, I.id), I.Null) with
           | I.Null -> closedSub (g, s)
           | _ -> false__)
    let rec closedExp (g, (U, s)) =
      match collectExp (g, (U, I.id), I.Null) with
      | I.Null -> true__
      | _ -> false__
    let rec closedCtx =
      function
      | I.Null -> true__
      | Decl (g, D) -> (closedCtx g) && (closedDec (g, (D, I.id)))
    let rec closedFor =
      function
      | (Psi, T.True) -> true__
      | (Psi, All ((D, _), F)) ->
          (closedDEC (Psi, D)) && (closedFor ((I.Decl (Psi, D)), F))
      | (Psi, Ex ((D, _), F)) ->
          (closedDec ((T.coerceCtx Psi), (D, I.id))) &&
            (closedFor ((I.Decl (Psi, (T.UDec D))), F))
    let rec closedDEC =
      function
      | (Psi, UDec (D)) -> closedDec ((T.coerceCtx Psi), (D, I.id))
      | (Psi, PDec (_, F, _, _)) -> closedFor (Psi, F)
    let rec closedCTX =
      function
      | I.Null -> true__
      | Decl (Psi, D) -> (closedCTX Psi) && (closedDEC (Psi, D))
    let rec evarsToK =
      function | nil -> I.Null | (X)::Xs -> I.Decl ((evarsToK Xs), (EV X))
    let rec KToEVars =
      function
      | I.Null -> nil
      | Decl (K, EV (X)) -> (::) X KToEVars K
      | Decl (K, _) -> KToEVars K
    let rec collectEVars (g, Us, Xs) =
      KToEVars (collectExp (g, Us, (evarsToK Xs)))
    let rec collectEVarsSpine (g, (S, s), Xs) =
      KToEVars (collectSpine (g, (S, s), (evarsToK Xs)))
    let rec collectPrg =
      function
      | (_, (EVar (Psi, r, F, _, _, _) as P), K) -> I.Decl (K, (PV P))
      | (Psi, T.Unit, K) -> K
      | (Psi, PairExp (U, P), K) ->
          collectPrg (Psi, P, (collectExp ((T.coerceCtx Psi), (U, I.id), K)))
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
      | (K, depth, (EVar _ as X)) -> abstractPVar (K, depth, X)
      | (K, depth, T.Unit) -> T.Unit
      | (K, depth, PairExp (U, P)) ->
          T.PairExp
            ((abstractExp (K, depth, (U, I.id))),
              (abstractPrg (K, depth, P)))
    let rec collectTomegaSub =
      function
      | Shift 0 -> I.Null
      | Dot (Exp (U), t) ->
          collectExp (I.Null, (U, I.id), (collectTomegaSub t))
      | Dot (Block (B), t) -> collectBlock (I.Null, B, (collectTomegaSub t))
      | Dot (Prg (P), t) -> collectPrg (I.Null, P, (collectTomegaSub t))
    let rec abstractOrder =
      function
      | (K, depth, Arg (us1, us2)) ->
          O.Arg
            (((abstractExp (K, depth, us1)), I.id),
              ((abstractExp (K, depth, us2)), I.id))
      | (K, depth, Simul (Os)) ->
          O.Simul (map (function | O -> abstractOrder (K, depth, O)) Os)
      | (K, depth, Lex (Os)) ->
          O.Lex (map (function | O -> abstractOrder (K, depth, O)) Os)
    let rec abstractTC =
      function
      | (K, depth, Abs (D, TC)) ->
          T.Abs
            ((abstractDec (K, depth, (D, I.id))),
              (abstractTC (K, depth, TC)))
      | (K, depth, Conj (TC1, TC2)) ->
          T.Conj ((abstractTC (K, depth, TC1)), (abstractTC (K, depth, TC2)))
      | (K, depth, Base (O)) -> T.Base (abstractOrder (K, depth, O))
    let rec abstractTCOpt =
      function
      | (K, depth, NONE) -> NONE
      | (K, depth, SOME (TC)) -> SOME (abstractTC (K, depth, TC))
    let rec abstractMetaDec =
      function
      | (K, depth, UDec (D)) -> T.UDec (abstractDec (K, depth, (D, I.id)))
      | (K, depth, PDec (xx, F, TC1, TC2)) ->
          T.PDec (xx, (abstractFor (K, depth, F)), TC1, TC2)
    let rec abstractFor =
      function
      | (K, depth, T.True) -> T.True
      | (K, depth, All ((MD, Q), F)) ->
          T.All
            (((abstractMetaDec (K, depth, MD)), Q),
              (abstractFor (K, depth, F)))
      | (K, depth, Ex ((D, Q), F)) ->
          T.Ex
            (((abstractDec (K, depth, (D, I.id))), Q),
              (abstractFor (K, depth, F)))
      | (K, depth, And (F1, F2)) ->
          T.And ((abstractFor (K, depth, F1)), (abstractFor (K, depth, F2)))
      | (K, depth, World (W, F)) -> T.World (W, (abstractFor (K, depth, F)))
    let rec abstractPsi =
      function
      | I.Null -> I.Null
      | Decl (K', EV (EVar (_, GX, VX, _))) ->
          let V' = raiseType (GX, VX) in
          let V'' = abstractExp (K', 0, (V', I.id)) in
          I.Decl ((abstractPsi K'), (T.UDec (I.Dec (NONE, V''))))
      | Decl (K', FV (name, V')) ->
          let V'' = abstractExp (K', 0, (V', I.id)) in
          I.Decl ((abstractPsi K'), (T.UDec (I.Dec ((SOME name), V''))))
      | Decl (K', LV (LVar (r, _, (l, t)))) ->
          let t' = abstractSOME (K', t) in
          I.Decl ((abstractPsi K'), (T.UDec (I.BDec (NONE, (l, t')))))
      | Decl (K', PV (EVar (GX, _, FX, TC1, TC2, _))) ->
          let F' = abstractFor (K', 0, (T.forSub (FX, T.id))) in
          let TC1' = abstractTCOpt (K', 0, TC1) in
          let TC2' = abstractTCOpt (K', 0, TC2) in
          I.Decl ((abstractPsi K'), (T.PDec (NONE, F', TC1, TC2)))
    let rec abstractTomegaSub t =
      let K = collectTomegaSub t in
      let t' = abstractTomegaSub' (K, 0, t) in
      let Psi = abstractPsi K in (Psi, t')
    let rec abstractTomegaSub' =
      function
      | (K, depth, Shift 0) -> T.Shift depth
      | (K, depth, Dot (Exp (U), t)) ->
          T.Dot
            ((T.Exp (abstractExp (K, depth, (U, I.id)))),
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
      let P' = abstractPrg (K, 0, P) in let Psi = abstractPsi K in (Psi, P')
    let ((raiseType)(* Intermediate Data Structure *)
      (* Y ::= X         for  GX |- X : VX *)(*     | (F, V)        if . |- F : V *)
      (*     | L             if . |- L in W *)(*     | P                            *)
      (*
       We write {{K}} for the context of K, where EVars, FVars, LVars have
       been translated to declarations and their occurrences to BVars.
       We write {{U}}_K, {{S}}_K for the corresponding translation of an
       expression or spine.

       Just like contexts g, any K is implicitly assumed to be
       well-formed and in dependency order.

       We write  K ||- U  if all EVars and FVars in U are collected in K.
       In particular, . ||- U means U contains no EVars or FVars.  Similarly,
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
      (* eqEVar X Y = B
       where B iff X and Y represent same variable
    *)
      (* eqFVar F Y = B
       where B iff X and Y represent same variable
    *)
      (* eqLVar L Y = B
       where B iff X and Y represent same variable
    *)
      (* exists P K = B
       where B iff K = K1, Y, K2  s.t. P Y  holds
    *)
      (* this should be non-strict *)(* perhaps the whole repeated traversal are now a performance
       bottleneck in PCC applications where logic programming search
       followed by abstraction creates certificates.  such certificates
       are large, so the quadratic algorithm is not really acceptable.
       possible improvement, collect, abstract, then traverse one more
       time to determine status of all variables.
    *)
      (* Wed Aug  6 16:37:57 2003 -fp *)(* !!! *)
      (* occursInExp (k, U) = DP,

       Invariant:
       If    U in nf
       then  DP = No      iff k does not occur in U
             DP = Maybe   iff k occurs in U some place not as an argument to a Skonst
             DP = Meta    iff k occurs in U and only as arguments to Skonsts
    *)
      (* no case for Redex, EVar, EClo *)(* no case for FVar *)
      (* no case for SClo *)(* piDepend ((D,P), V) = Pi ((D,P'), V)
       where P' = Maybe if D occurs in V, P' = No otherwise
    *)
      (* optimize to have fewer traversals? -cs *)(* pre-Twelf 1.2 code walk Fri May  8 11:17:10 1998 *)
      (* raiseType (g, V) = {{g}} V

       Invariant:
       If g |- V : L
       then  . |- {{g}} V : L

       All abstractions are potentially dependent.
    *)
      (* raiseTerm (g, U) = [[g]] U

       Invariant:
       If g |- U : V
       then  . |- [[g]] U : {{g}} V

       All abstractions are potentially dependent.
    *)
      (* collectExpW (g, (U, s), K) = K'

       Invariant:
       If    g |- s : G1     G1 |- U : V      (U,s) in whnf
       No circularities in U
             (enforced by extended occurs-check for FVars in Unify)
       and   K' = K, K''
             where K'' contains all EVars and FVars in (U,s)
    *)
      (* Possible optimization: Calculate also the normal form of the term *)
      (* s' = ^|g| *)(* BUG : We forget to deref L.  use collectBlock instead
             FPCHECK
             -cs Sat Jul 24 18:48:59 2010
            was:
      | collectExpW (g, (I.Root (I.Proj (L as I.LVar (r, sk, (l, t)), i), S), s), K) =
        if exists (eqLVar L) K
           note: don't collect t again below *)
      (* was: collectSpine (g, (S, s), collectSub (I.Null, t, K)) *)
      (* Sun Dec 16 10:54:52 2001 -fp !!! *)(* -fp Sun Dec  1 21:12:12 2002 *)
      (* collectSpine (g, (S, s), I.Decl (collectSub (g, I.comp(t,s), K), LV L)) *)
      (* was :
         collectSpine (g, (S, s), collectSub (g, I.comp(t,s), I.Decl (K, LV L)))
         July 22, 2010 -fp -cs
         *)
      (* val _ = checkEmpty !cnstrs *)(* inefficient *)
      (* No other cases can occur due to whnf invariant *)
      (* collectExp (g, (U, s), K) = K'

       same as collectExpW  but  (U,s) need not to be in whnf
    *)
      (* collectSpine (g, (S, s), K) = K'

       Invariant:
       If    g |- s : G1     G1 |- S : V > P
       then  K' = K, K''
       where K'' contains all EVars and FVars in (S, s)
     *)
      (* collectDec (g, (x:V, s), K) = K'

       Invariant:
       If    g |- s : G1     G1 |- V : L
       then  K' = K, K''
       where K'' contains all EVars and FVars in (V, s)
    *)
      (* . |- t : Gsome, so do not compose with s *)
      (* Sat Dec  8 13:28:15 2001 -fp *)(* was: collectSub (I.Null, t, K) *)
      (* collectSub (g, s, K) = K'

       Invariant:
       If    g |- s : G1
       then  K' = K, K''
       where K'' contains all EVars and FVars in s
    *)
      (* next case should be impossible *)(*
      | collectSub (g, I.Dot (I.Undef, s), K) =
          collectSub (g, s, K)
    *)
      (* collectBlock (g, B, K) where g |- B block *)
      (* collectBlock (B, K) *)(* correct?? -fp Sun Dec  1 21:15:33 2002 *)
      (* was: t in the two lines above, July 22, 2010, -fp -cs *)
      (* | collectBlock (g, I.Bidx _, K) = K *)(* should be impossible: Fronts of substitutions are never Bidx *)
      (* Sat Dec  8 13:30:43 2001 -fp *)(* collectCtx (G0, g, K) = (G0', K')
       Invariant:
       If G0 |- g ctx,
       then G0' = G0,g
       and K' = K, K'' where K'' contains all EVars and FVars in g
    *)
      (* collectCtxs (G0, Gs, K) = K'
       Invariant: G0 |- G1,...,Gn ctx where Gs = [G1,...,Gn]
       and K' = K, K'' where K'' contains all EVars and FVars in G1,...,Gn
    *)
      (* abstractEVar (K, depth, X) = C'

       Invariant:
       If   g |- X : V
       and  |g| = depth
       and  X occurs in K  at kth position (starting at 1)
       then C' = BVar (depth + k)
       and  {{K}}, g |- C' : V
    *)
      (*      | abstractEVar (I.Decl (K', FV (n', _)), depth, X) =
          abstractEVar (K', depth+1, X) remove later --cs*)
      (* abstractFVar (K, depth, F) = C'

       Invariant:
       If   g |- F : V
       and  |g| = depth
       and  F occurs in K  at kth position (starting at 1)
       then C' = BVar (depth + k)
       and  {{K}}, g |- C' : V
    *)
      (*      | abstractFVar (I.Decl(K', EV _), depth, F) =
          abstractFVar (K', depth+1, F) remove later --cs *)
      (* abstractLVar (K, depth, L) = C'

       Invariant:
       If   g |- L : V
       and  |g| = depth
       and  L occurs in K  at kth position (starting at 1)
       then C' = Bidx (depth + k)
       and  {{K}}, g |- C' : V
    *)
      (* abstractExpW (K, depth, (U, s)) = U'
       U' = {{U[s]}}_K

       Invariant:
       If    g |- s : G1     G1 |- U : V    (U,s) is in whnf
       and   K is internal context in dependency order
       and   |g| = depth
       and   K ||- U and K ||- V
       then  {{K}}, g |- U' : V'
       and   . ||- U' and . ||- V'
       and   U' is in nf
    *)
      (* abstractExp (K, depth, (U, s)) = U'

       same as abstractExpW, but (U,s) need not to be in whnf
    *)
      (* abstractSub (K, depth, s, S) = S'      (implicit raising)
       S' = {{s}}_K @@ S

       Invariant:
       If   g |- s : G1
       and  |g| = depth
       and  K ||- s
       then {{K}}, g |- S' : {G1}.W > W   (for some W)
       and  . ||- S'
    *)
      (* k = depth *)(* abstractSpine (K, depth, (S, s)) = S'
       where S' = {{S[s]}}_K

       Invariant:
       If   g |- s : G1     G1 |- S : V > P
       and  K ||- S
       and  |g| = depth

       then {{K}}, g |- S' : V' > P'
       and  . ||- S'
    *)
      (* abstractDec (K, depth, (x:V, s)) = x:V'
       where V = {{V[s]}}_K

       Invariant:
       If   g |- s : G1     G1 |- V : L
       and  K ||- V
       and  |g| = depth

       then {{K}}, g |- V' : L
       and  . ||- V'
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
      (* n = 0 by invariant, check for now *)(* n > 0 *)
      (* I.Block (I.Bidx _) should be impossible as head of substitutions *)
      (* abstractCtx (K, depth, g) = (g', depth')
       where g' = {{g}}_K

       Invariants:
       If G0 |- g ctx
       and K ||- g
       and |G0| = depth
       then {{K}}, G0 |- g' ctx
       and . ||- g'
       and |G0,g| = depth'
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
     getlevel (V) = L if g |- V : L

       Invariant: g |- V : L' for some L'
    *)
      (* checkType (V) = () if g |- V : type

       Invariant: g |- V : L' for some L'
    *)
      (* abstractKPi (K, V) = V'
       where V' = {{K}} V

       Invariant:
       If   {{K}} |- V : L
       and  . ||- V

       then V' = {{K}} V
       and  . |- V' : L
       and  . ||- V'
    *)
      (* enforced by reconstruction -kw
          val _ = checkType V'' *)
      (* enforced by reconstruction -kw
          val _ = checkType V'' *)
      (* abstractKLam (K, U) = U'
       where U' = [[K]] U

       Invariant:
       If   {{K}} |- U : V
       and  . ||- U
       and  . ||- V

       then U' = [[K]] U
       and  . |- U' : {{K}} V
       and  . ||- U'
    *)
      (* enforced by reconstruction -kw
          val _ = checkType V'' *)
      (* enforced by reconstruction -kw
          val _ = checkType V'' *)
      (* abstractDecImp V = (k', V')    rename --cs  (see above) *)
      (* abstractDef  (U, V) = (k', (U', V'))

       Invariant:
       If    . |- V : L
       and   . |- U : V
       and   K1 ||- V
       and   K2 ||- U
       and   K = K1, K2

       then  . |- V' : L
       and   V' = {{K}} V
       and   . |- U' : V'
       and   U' = [[K]] U
       and   . ||- V'
       and   . ||- U'
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
      (* closedDec (g, D) = true iff D contains no EVar or FVar *)
      (* collectEVars (g, U[s], Xs) = Xs'
       Invariants:
         g |- U[s] : V
         Xs' extends Xs by new EVars in U[s]
    *)
      (* for the theorem prover:
       collect and abstract in subsitutions  including residual lemmas
       pending approval of Frank.
    *)
      (* abstractPVar (K, depth, L) = C'

       Invariant:
       If   g |- L : V
       and  |g| = depth
       and  L occurs in K  at kth position (starting at 1)
       then C' = Bidx (depth + k)
       and  {{K}}, g |- C' : V
    *)
      (* TC cannot contain free FVAR's or EVars'
            --cs  Fri Apr 30 13:45:50 2004 *)
      (* Argument must be in normal form *)(* enforced by reconstruction -kw
          val _ = checkType V'' *)
      (* enforced by reconstruction -kw
          val _ = checkType V'' *)
      (* What's happening with GX? *)(* What's happening with TCs? *)
      (* just added to abstract over residual lemmas  -cs *)
      (* Tomorrow: Make collection in program values a priority *)
      (* Then just traverse the Tomega by abstraction to get to the types of those
       variables. *))
      = raiseType
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
