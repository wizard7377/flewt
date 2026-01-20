
module type ABSTRACT  =
  sig
    exception Error of string 
    val piDepend :
      (IntSyn.__Dec * IntSyn.__Depend) -> IntSyn.__Exp -> IntSyn.__Exp
    val closedDec :
      IntSyn.__Dec IntSyn.__Ctx -> (IntSyn.__Dec * IntSyn.__Sub) -> bool
    val closedSub : IntSyn.__Dec IntSyn.__Ctx -> IntSyn.__Sub -> bool
    val closedExp :
      IntSyn.__Dec IntSyn.__Ctx -> (IntSyn.__Exp * IntSyn.__Sub) -> bool
    val closedCtx : IntSyn.__Dec IntSyn.__Ctx -> bool
    val closedCTX : Tomega.__Dec IntSyn.__Ctx -> bool
    val abstractDecImp : IntSyn.__Exp -> (int * IntSyn.__Exp)
    val abstractDef :
      IntSyn.__Exp -> IntSyn.__Exp -> (int * (IntSyn.__Exp * IntSyn.__Exp))
    val abstractCtxs :
      IntSyn.__Dec IntSyn.__Ctx list ->
        (IntSyn.__Dec IntSyn.__Ctx * IntSyn.__Dec IntSyn.__Ctx list)
    val abstractTomegaSub :
      Tomega.__Sub -> (Tomega.__Dec IntSyn.__Ctx * Tomega.__Sub)
    val abstractTomegaPrg :
      Tomega.__Prg -> (Tomega.__Dec IntSyn.__Ctx * Tomega.__Prg)
    val abstractSpine :
      IntSyn.__Spine -> IntSyn.__Sub -> (IntSyn.dctx * IntSyn.__Spine)
    val collectEVars :
      IntSyn.dctx -> IntSyn.eclo -> IntSyn.__Exp list -> IntSyn.__Exp list
    val collectEVarsSpine :
      IntSyn.dctx ->
        (IntSyn.__Spine * IntSyn.__Sub) ->
          IntSyn.__Exp list -> IntSyn.__Exp list
    val raiseTerm : IntSyn.dctx -> IntSyn.__Exp -> IntSyn.__Exp
    val raiseType : IntSyn.dctx -> IntSyn.__Exp -> IntSyn.__Exp
  end;;




module Abstract(Abstract:sig
                           module Whnf : WHNF
                           module Unify : UNIFY
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
      | Decl (__G, FV _) -> collectConstraints __G
      | Decl (__G, EV (EVar (_, _, _, { contents = nil }))) ->
          collectConstraints __G
      | Decl (__G, EV (EVar (_, _, _, { contents = cnstrL }))) ->
          (@) (C.simplify cnstrL) collectConstraints __G
      | Decl (__G, LV _) -> collectConstraints __G
    let rec checkConstraints (__K) =
      let constraints = collectConstraints __K in
      let _ =
        match constraints with | nil -> () | _ -> raise (C.Error constraints) in
      ()
    let rec eqEVar __0__ __1__ =
      match (__0__, __1__) with
      | (EVar (r1, _, _, _), EV (EVar (r2, _, _, _))) -> r1 = r2
      | (_, _) -> false__
    let rec eqFVar __2__ __3__ =
      match (__2__, __3__) with
      | (FVar (n1, _, _), FV (n2, _)) -> n1 = n2
      | (_, _) -> false__
    let rec eqLVar __4__ __5__ =
      match (__4__, __5__) with
      | (LVar (r1, _, _), LV (LVar (r2, _, _))) -> r1 = r2
      | (_, _) -> false__
    let rec exists (__P) (__K) =
      let rec exists' =
        function
        | I.Null -> false__
        | Decl (__K', __Y) -> (__P __Y) || (exists' __K') in
      exists' __K
    let rec or__ __6__ __7__ =
      match (__6__, __7__) with
      | (I.Maybe, _) -> I.Maybe
      | (_, I.Maybe) -> I.Maybe
      | (I.Meta, _) -> I.Meta
      | (_, I.Meta) -> I.Meta
      | (I.No, I.No) -> I.No
    let rec occursInExp __8__ __9__ =
      match (__8__, __9__) with
      | (k, Uni _) -> I.No
      | (k, Pi (DP, __V)) ->
          or__ ((occursInDecP (k, DP)), (occursInExp ((k + 1), __V)))
      | (k, Root (__H, __S)) ->
          occursInHead (k, __H, (occursInSpine (k, __S)))
      | (k, Lam (__D, __V)) ->
          or__ ((occursInDec (k, __D)), (occursInExp ((k + 1), __V)))
      | (k, FgnExp csfe) ->
          I.FgnExpStd.fold csfe
            (fun (__U) ->
               fun (DP) ->
                 or__ (DP, (occursInExp (k, (Whnf.normalize (__U, I.id))))))
            I.No
    let rec occursInHead __10__ __11__ __12__ =
      match (__10__, __11__, __12__) with
      | (k, BVar k', DP) -> if k = k' then I.Maybe else DP
      | (k, Const _, DP) -> DP
      | (k, Def _, DP) -> DP
      | (k, Proj _, DP) -> DP
      | (k, FgnConst _, DP) -> DP
      | (k, Skonst _, I.No) -> I.No
      | (k, Skonst _, I.Meta) -> I.Meta
      | (k, Skonst _, I.Maybe) -> I.Meta
    let rec occursInSpine __13__ __14__ =
      match (__13__, __14__) with
      | (_, I.Nil) -> I.No
      | (k, App (__U, __S)) ->
          or__ ((occursInExp (k, __U)), (occursInSpine (k, __S)))
    let rec occursInDec k (Dec (_, __V)) = occursInExp (k, __V)
    let rec occursInDecP k (__D, _) = occursInDec (k, __D)
    let rec piDepend __15__ =
      match __15__ with
      | ((__D, I.No), __V) as DPV -> I.Pi DPV
      | ((__D, I.Meta), __V) as DPV -> I.Pi DPV
      | ((__D, I.Maybe), __V) -> I.Pi ((__D, (occursInExp (1, __V))), __V)
    let rec raiseType __16__ __17__ =
      match (__16__, __17__) with
      | (I.Null, __V) -> __V
      | (Decl (__G, __D), __V) ->
          raiseType (__G, (I.Pi ((__D, I.Maybe), __V)))
    let rec raiseTerm __18__ __19__ =
      match (__18__, __19__) with
      | (I.Null, __U) -> __U
      | (Decl (__G, __D), __U) -> raiseTerm (__G, (I.Lam (__D, __U)))
    let rec collectExpW __20__ __21__ __22__ =
      match (__20__, __21__, __22__) with
      | (__G, (Uni (__L), s), __K) -> __K
      | (__G, (Pi ((__D, _), __V), s), __K) ->
          collectExp
            ((I.Decl (__G, (I.decSub (__D, s)))), (__V, (I.dot1 s)),
              (collectDec (__G, (__D, s), __K)))
      | (__G, (Root ((FVar (name, __V, s') as F), __S), s), __K) ->
          ((if exists (eqFVar __F) __K
            then collectSpine (__G, (__S, s), __K)
            else
              collectSpine
                (__G, (__S, s),
                  (I.Decl
                     ((collectExp (I.Null, (__V, I.id), __K)),
                       (FV (name, __V))))))
          (* s' = ^|G| *))
      | (__G,
         (Root
          (Proj ((LVar ({ contents = NONE }, sk, (l, t)) as L), i), __S), s),
         __K) ->
          collectSpine
            (__G, (__S, s), (collectBlock (__G, (I.blockSub (__L, s)), __K)))
      | (__G, (Root (_, __S), s), __K) -> collectSpine (__G, (__S, s), __K)
      | (__G, (Lam (__D, __U), s), __K) ->
          collectExp
            ((I.Decl (__G, (I.decSub (__D, s)))), (__U, (I.dot1 s)),
              (collectDec (__G, (__D, s), __K)))
      | (__G, ((EVar (r, GX, __V, cnstrs) as X), s), __K) ->
          if exists (eqEVar __X) __K
          then collectSub (__G, s, __K)
          else
            (let __V' = raiseType (GX, __V) in
             let __K' = collectExp (I.Null, (__V', I.id), __K) in
             ((collectSub (__G, s, (I.Decl (__K', (EV __X)))))
               (* val _ = checkEmpty !cnstrs *)(* inefficient *)))
      | (__G, (FgnExp csfe, s), __K) ->
          I.FgnExpStd.fold csfe
            (fun (__U) -> fun (__K) -> collectExp (__G, (__U, s), __K)) __K
      (* was :
         collectSpine (G, (S, s), collectSub (G, I.comp(t,s), I.Decl (K, LV L)))
         July 22, 2010 -fp -cs
         *)
      (* collectSpine (G, (S, s), I.Decl (collectSub (G, I.comp(t,s), K), LV L)) *)
      (* -fp Sun Dec  1 21:12:12 2002 *)(* Sun Dec 16 10:54:52 2001 -fp !!! *)
      (* was: collectSpine (G, (S, s), collectSub (I.Null, t, K)) *)
      (* BUG : We forget to deref L.  use collectBlock instead
             FPCHECK
             -cs Sat Jul 24 18:48:59 2010
            was:
      | collectExpW (G, (I.Root (I.Proj (L as I.LVar (r, sk, (l, t)), i), S), s), K) =
        if exists (eqLVar L) K
           note: don't collect t again below *)
    let rec collectExp (__G) (__Us) (__K) =
      collectExpW (__G, (Whnf.whnf __Us), __K)
    let rec collectSpine __23__ __24__ __25__ =
      match (__23__, __24__, __25__) with
      | (__G, (I.Nil, _), __K) -> __K
      | (__G, (SClo (__S, s'), s), __K) ->
          collectSpine (__G, (__S, (I.comp (s', s))), __K)
      | (__G, (App (__U, __S), s), __K) ->
          collectSpine (__G, (__S, s), (collectExp (__G, (__U, s), __K)))
    let rec collectDec __26__ __27__ __28__ =
      match (__26__, __27__, __28__) with
      | (__G, (Dec (_, __V), s), __K) -> collectExp (__G, (__V, s), __K)
      | (__G, (BDec (_, (_, t)), s), __K) ->
          collectSub (__G, (I.comp (t, s)), __K)
      | (__G, (NDec _, s), __K) -> __K(* was: collectSub (I.Null, t, K) *)
      (* Sat Dec  8 13:28:15 2001 -fp *)(* . |- t : Gsome, so do not compose with s *)
    let rec collectSub __29__ __30__ __31__ =
      match (__29__, __30__, __31__) with
      | (__G, Shift _, __K) -> __K
      | (__G, Dot (Idx _, s), __K) -> collectSub (__G, s, __K)
      | (__G, Dot (Exp (__U), s), __K) ->
          collectSub (__G, s, (collectExp (__G, (__U, I.id), __K)))
      | (__G, Dot (Block (__B), s), __K) ->
          collectSub (__G, s, (collectBlock (__G, __B, __K)))
    let rec collectBlock __32__ __33__ __34__ =
      match (__32__, __33__, __34__) with
      | (__G, LVar ({ contents = Some (__B) }, sk, _), __K) ->
          collectBlock (__G, (I.blockSub (__B, sk)), __K)
      | (__G, (LVar (_, sk, (l, t)) as L), __K) ->
          if exists (eqLVar __L) __K
          then collectSub (__G, (I.comp (t, sk)), __K)
          else I.Decl ((collectSub (__G, (I.comp (t, sk)), __K)), (LV __L))
      (* correct?? -fp Sun Dec  1 21:15:33 2002 *)(* collectBlock (B, K) *)
    let rec collectCtx __35__ __36__ __37__ =
      match (__35__, __36__, __37__) with
      | (__G0, I.Null, __K) -> (__G0, __K)
      | (__G0, Decl (__G, __D), __K) ->
          let (G0', __K') = collectCtx (__G0, __G, __K) in
          let K'' = collectDec (G0', (__D, I.id), __K') in
          ((I.Decl (__G0, __D)), K'')
    let rec collectCtxs __38__ __39__ __40__ =
      match (__38__, __39__, __40__) with
      | (__G0, nil, __K) -> __K
      | (__G0, (__G)::__Gs, __K) ->
          let (G0', __K') = collectCtx (__G0, __G, __K) in
          collectCtxs (G0', __Gs, __K')
    let rec abstractEVar __41__ __42__ __43__ =
      match (__41__, __42__, __43__) with
      | (Decl (__K', EV (EVar (r', _, _, _))), depth,
         (EVar (r, _, _, _) as X)) ->
          if r = r'
          then I.BVar (depth + 1)
          else abstractEVar (__K', (depth + 1), __X)
      | (Decl (__K', _), depth, __X) -> abstractEVar (__K', (depth + 1), __X)
      (*      | abstractEVar (I.Decl (K', FV (n', _)), depth, X) =
          abstractEVar (K', depth+1, X) remove later --cs*)
    let rec abstractFVar __44__ __45__ __46__ =
      match (__44__, __45__, __46__) with
      | (Decl (__K', FV (n', _)), depth, (FVar (n, _, _) as F)) ->
          if n = n'
          then I.BVar (depth + 1)
          else abstractFVar (__K', (depth + 1), __F)
      | (Decl (__K', _), depth, __F) -> abstractFVar (__K', (depth + 1), __F)
      (*      | abstractFVar (I.Decl(K', EV _), depth, F) =
          abstractFVar (K', depth+1, F) remove later --cs *)
    let rec abstractLVar __47__ __48__ __49__ =
      match (__47__, __48__, __49__) with
      | (Decl (__K', LV (LVar (r', _, _))), depth, (LVar (r, _, _) as L)) ->
          if r = r'
          then I.Bidx (depth + 1)
          else abstractLVar (__K', (depth + 1), __L)
      | (Decl (__K', _), depth, __L) -> abstractLVar (__K', (depth + 1), __L)
    let rec abstractExpW __50__ __51__ __52__ =
      match (__50__, __51__, __52__) with
      | (__K, depth, ((Uni (__L) as U), s)) -> __U
      | (__K, depth, (Pi ((__D, __P), __V), s)) ->
          piDepend
            (((abstractDec (__K, depth, (__D, s))), __P),
              (abstractExp (__K, (depth + 1), (__V, (I.dot1 s)))))
      | (__K, depth, (Root ((FVar _ as F), __S), s)) ->
          I.Root
            ((abstractFVar (__K, depth, __F)),
              (abstractSpine (__K, depth, (__S, s))))
      | (__K, depth, (Root (Proj ((LVar _ as L), i), __S), s)) ->
          I.Root
            ((I.Proj ((abstractLVar (__K, depth, __L)), i)),
              (abstractSpine (__K, depth, (__S, s))))
      | (__K, depth, (Root (__H, __S), s)) ->
          I.Root (__H, (abstractSpine (__K, depth, (__S, s))))
      | (__K, depth, (Lam (__D, __U), s)) ->
          I.Lam
            ((abstractDec (__K, depth, (__D, s))),
              (abstractExp (__K, (depth + 1), (__U, (I.dot1 s)))))
      | (__K, depth, ((EVar _ as X), s)) ->
          I.Root
            ((abstractEVar (__K, depth, __X)),
              (abstractSub (__K, depth, s, I.Nil)))
      | (__K, depth, (FgnExp csfe, s)) ->
          I.FgnExpStd.Map.apply csfe
            (fun (__U) -> abstractExp (__K, depth, (__U, s)))
    let rec abstractExp (__K) depth (__Us) =
      abstractExpW (__K, depth, (Whnf.whnf __Us))
    let rec abstractSub __53__ __54__ __55__ __56__ =
      match (__53__, __54__, __55__, __56__) with
      | (__K, depth, Shift k, __S) ->
          ((if k < depth
            then
              abstractSub
                (__K, depth, (I.Dot ((I.Idx (k + 1)), (I.Shift (k + 1)))),
                  __S)
            else __S)
          (* k = depth *))
      | (__K, depth, Dot (Idx k, s), __S) ->
          abstractSub
            (__K, depth, s, (I.App ((I.Root ((I.BVar k), I.Nil)), __S)))
      | (__K, depth, Dot (Exp (__U), s), __S) ->
          abstractSub
            (__K, depth, s,
              (I.App ((abstractExp (__K, depth, (__U, I.id))), __S)))
    let rec abstractSpine __57__ __58__ __59__ =
      match (__57__, __58__, __59__) with
      | (__K, depth, (I.Nil, _)) -> I.Nil
      | (__K, depth, (SClo (__S, s'), s)) ->
          abstractSpine (__K, depth, (__S, (I.comp (s', s))))
      | (__K, depth, (App (__U, __S), s)) ->
          I.App
            ((abstractExp (__K, depth, (__U, s))),
              (abstractSpine (__K, depth, (__S, s))))
    let rec abstractDec (__K) depth (Dec (x, __V), s) =
      I.Dec (x, (abstractExp (__K, depth, (__V, s))))
    let rec abstractSOME __60__ __61__ =
      match (__60__, __61__) with
      | (__K, Shift 0) -> I.Shift (I.ctxLength __K)
      | (__K, Shift n) -> I.Shift (I.ctxLength __K)
      | (__K, Dot (Idx k, s)) -> I.Dot ((I.Idx k), (abstractSOME (__K, s)))
      | (__K, Dot (Exp (__U), s)) ->
          I.Dot
            ((I.Exp (abstractExp (__K, 0, (__U, I.id)))),
              (abstractSOME (__K, s)))
      | (__K, Dot (Block (LVar _ as L), s)) ->
          I.Dot
            ((I.Block (abstractLVar (__K, 0, __L))), (abstractSOME (__K, s)))
      (* n > 0 *)(* n = 0 by invariant, check for now *)
    let rec abstractCtx __62__ __63__ __64__ =
      match (__62__, __63__, __64__) with
      | (__K, depth, I.Null) -> (I.Null, depth)
      | (__K, depth, Decl (__G, __D)) ->
          let (__G', depth') = abstractCtx (__K, depth, __G) in
          let __D' = abstractDec (__K, depth', (__D, I.id)) in
          ((I.Decl (__G', __D')), (depth' + 1))
    let rec abstractCtxlist __65__ __66__ __67__ =
      match (__65__, __66__, __67__) with
      | (__K, depth, nil) -> nil
      | (__K, depth, (__G)::__Gs) ->
          let (__G', depth') = abstractCtx (__K, depth, __G) in
          let __Gs' = abstractCtxlist (__K, depth', __Gs) in __G' :: __Gs'
    let rec abstractKPi __68__ __69__ =
      match (__68__, __69__) with
      | (I.Null, __V) -> __V
      | (Decl (__K', EV (EVar (_, GX, VX, _))), __V) ->
          let __V' = raiseType (GX, VX) in
          let V'' = abstractExp (__K', 0, (__V', I.id)) in
          ((abstractKPi (__K', (I.Pi (((I.Dec (NONE, V'')), I.Maybe), __V))))
            (* enforced by reconstruction -kw
          val _ = checkType V'' *))
      | (Decl (__K', FV (name, __V')), __V) ->
          let V'' = abstractExp (__K', 0, (__V', I.id)) in
          ((abstractKPi
              (__K', (I.Pi (((I.Dec ((Some name), V'')), I.Maybe), __V))))
            (* enforced by reconstruction -kw
          val _ = checkType V'' *))
      | (Decl (__K', LV (LVar (r, _, (l, t)))), __V) ->
          let t' = abstractSOME (__K', t) in
          abstractKPi
            (__K', (I.Pi (((I.BDec (NONE, (l, t'))), I.Maybe), __V)))
    let rec abstractKLam __70__ __71__ =
      match (__70__, __71__) with
      | (I.Null, __U) -> __U
      | (Decl (__K', EV (EVar (_, GX, VX, _))), __U) ->
          let __V' = raiseType (GX, VX) in
          abstractKLam
            (__K',
              (I.Lam
                 ((I.Dec (NONE, (abstractExp (__K', 0, (__V', I.id))))), __U)))
      | (Decl (__K', FV (name, __V')), __U) ->
          abstractKLam
            (__K',
              (I.Lam
                 ((I.Dec ((Some name), (abstractExp (__K', 0, (__V', I.id))))),
                   __U)))
    let rec abstractKCtx =
      function
      | I.Null -> I.Null
      | Decl (__K', EV (EVar (_, GX, VX, _))) ->
          let __V' = raiseType (GX, VX) in
          let V'' = abstractExp (__K', 0, (__V', I.id)) in
          ((I.Decl ((abstractKCtx __K'), (I.Dec (NONE, V''))))
            (* enforced by reconstruction -kw
          val _ = checkType V'' *))
      | Decl (__K', FV (name, __V')) ->
          let V'' = abstractExp (__K', 0, (__V', I.id)) in
          ((I.Decl ((abstractKCtx __K'), (I.Dec ((Some name), V''))))
            (* enforced by reconstruction -kw
          val _ = checkType V'' *))
      | Decl (__K', LV (LVar (r, _, (l, t)))) ->
          let t' = abstractSOME (__K', t) in
          I.Decl ((abstractKCtx __K'), (I.BDec (NONE, (l, t'))))
    let rec abstractDecImp (__V) =
      let __K = collectExp (I.Null, (__V, I.id), I.Null) in
      let _ = checkConstraints __K in
      ((I.ctxLength __K),
        (abstractKPi (__K, (abstractExp (__K, 0, (__V, I.id))))))
    let rec abstractDef (__U) (__V) =
      let __K =
        collectExp
          (I.Null, (__U, I.id), (collectExp (I.Null, (__V, I.id), I.Null))) in
      let _ = checkConstraints __K in
      ((I.ctxLength __K),
        ((abstractKLam (__K, (abstractExp (__K, 0, (__U, I.id))))),
          (abstractKPi (__K, (abstractExp (__K, 0, (__V, I.id)))))))
    let rec abstractSpineExt (__S) s =
      let __K = collectSpine (I.Null, (__S, s), I.Null) in
      let _ = checkConstraints __K in
      let __G = abstractKCtx __K in
      let __S = abstractSpine (__K, 0, (__S, s)) in (__G, __S)
    let rec abstractCtxs (__Gs) =
      let __K = collectCtxs (I.Null, __Gs, I.Null) in
      let _ = checkConstraints __K in
      ((abstractKCtx __K), (abstractCtxlist (__K, 0, __Gs)))
    let rec closedDec (__G) (Dec (_, __V), s) =
      match collectExp (__G, (__V, s), I.Null) with
      | I.Null -> true__
      | _ -> false__
    let rec closedSub __72__ __73__ =
      match (__72__, __73__) with
      | (__G, Shift _) -> true__
      | (__G, Dot (Idx _, s)) -> closedSub (__G, s)
      | (__G, Dot (Exp (__U), s)) ->
          (match collectExp (__G, (__U, I.id), I.Null) with
           | I.Null -> closedSub (__G, s)
           | _ -> false__)
    let rec closedExp (__G) (__U, s) =
      match collectExp (__G, (__U, I.id), I.Null) with
      | I.Null -> true__
      | _ -> false__
    let rec closedCtx =
      function
      | I.Null -> true__
      | Decl (__G, __D) -> (closedCtx __G) && (closedDec (__G, (__D, I.id)))
    let rec closedFor __74__ __75__ =
      match (__74__, __75__) with
      | (Psi, T.True) -> true__
      | (Psi, All ((__D, _), __F)) ->
          (closedDEC (Psi, __D)) && (closedFor ((I.Decl (Psi, __D)), __F))
      | (Psi, Ex ((__D, _), __F)) ->
          (closedDec ((T.coerceCtx Psi), (__D, I.id))) &&
            (closedFor ((I.Decl (Psi, (T.UDec __D))), __F))
    let rec closedDEC __76__ __77__ =
      match (__76__, __77__) with
      | (Psi, UDec (__D)) -> closedDec ((T.coerceCtx Psi), (__D, I.id))
      | (Psi, PDec (_, __F, _, _)) -> closedFor (Psi, __F)
    let rec closedCTX =
      function
      | I.Null -> true__
      | Decl (Psi, __D) -> (closedCTX Psi) && (closedDEC (Psi, __D))
    let rec evarsToK =
      function
      | nil -> I.Null
      | (__X)::__Xs -> I.Decl ((evarsToK __Xs), (EV __X))
    let rec KToEVars =
      function
      | I.Null -> nil
      | Decl (__K, EV (__X)) -> (::) __X KToEVars __K
      | Decl (__K, _) -> KToEVars __K
    let rec collectEVars (__G) (__Us) (__Xs) =
      KToEVars (collectExp (__G, __Us, (evarsToK __Xs)))
    let rec collectEVarsSpine (__G) (__S, s) (__Xs) =
      KToEVars (collectSpine (__G, (__S, s), (evarsToK __Xs)))
    let rec collectPrg __78__ __79__ __80__ =
      match (__78__, __79__, __80__) with
      | (_, (EVar (Psi, r, __F, _, _, _) as P), __K) ->
          I.Decl (__K, (PV __P))
      | (Psi, T.Unit, __K) -> __K
      | (Psi, PairExp (__U, __P), __K) ->
          collectPrg
            (Psi, __P, (collectExp ((T.coerceCtx Psi), (__U, I.id), __K)))
    let rec abstractPVar __81__ __82__ __83__ =
      match (__81__, __82__, __83__) with
      | (Decl (__K', PV (EVar (_, r', _, _, _, _))), depth,
         (EVar (_, r, _, _, _, _) as P)) ->
          if r = r'
          then T.Var (depth + 1)
          else abstractPVar (__K', (depth + 1), __P)
      | (Decl (__K', _), depth, __P) -> abstractPVar (__K', (depth + 1), __P)
    let rec abstractPrg __84__ __85__ __86__ =
      match (__84__, __85__, __86__) with
      | (__K, depth, (EVar _ as X)) -> abstractPVar (__K, depth, __X)
      | (__K, depth, T.Unit) -> T.Unit
      | (__K, depth, PairExp (__U, __P)) ->
          T.PairExp
            ((abstractExp (__K, depth, (__U, I.id))),
              (abstractPrg (__K, depth, __P)))
    let rec collectTomegaSub =
      function
      | Shift 0 -> I.Null
      | Dot (Exp (__U), t) ->
          collectExp (I.Null, (__U, I.id), (collectTomegaSub t))
      | Dot (Block (__B), t) ->
          collectBlock (I.Null, __B, (collectTomegaSub t))
      | Dot (Prg (__P), t) -> collectPrg (I.Null, __P, (collectTomegaSub t))
    let rec abstractOrder __87__ __88__ __89__ =
      match (__87__, __88__, __89__) with
      | (__K, depth, Arg (__Us1, __Us2)) ->
          O.Arg
            (((abstractExp (__K, depth, __Us1)), I.id),
              ((abstractExp (__K, depth, __Us2)), I.id))
      | (__K, depth, Simul (__Os)) ->
          O.Simul (map (fun (__O) -> abstractOrder (__K, depth, __O)) __Os)
      | (__K, depth, Lex (__Os)) ->
          O.Lex (map (fun (__O) -> abstractOrder (__K, depth, __O)) __Os)
    let rec abstractTC __90__ __91__ __92__ =
      match (__90__, __91__, __92__) with
      | (__K, depth, Abs (__D, TC)) ->
          T.Abs
            ((abstractDec (__K, depth, (__D, I.id))),
              (abstractTC (__K, depth, TC)))
      | (__K, depth, Conj (TC1, TC2)) ->
          T.Conj
            ((abstractTC (__K, depth, TC1)), (abstractTC (__K, depth, TC2)))
      | (__K, depth, Base (__O)) -> T.Base (abstractOrder (__K, depth, __O))
    let rec abstractTCOpt __93__ __94__ __95__ =
      match (__93__, __94__, __95__) with
      | (__K, depth, NONE) -> NONE
      | (__K, depth, Some (TC)) -> Some (abstractTC (__K, depth, TC))
    let rec abstractMetaDec __96__ __97__ __98__ =
      match (__96__, __97__, __98__) with
      | (__K, depth, UDec (__D)) ->
          T.UDec (abstractDec (__K, depth, (__D, I.id)))
      | (__K, depth, PDec (xx, __F, TC1, TC2)) ->
          T.PDec (xx, (abstractFor (__K, depth, __F)), TC1, TC2)
    let rec abstractFor __99__ __100__ __101__ =
      match (__99__, __100__, __101__) with
      | (__K, depth, T.True) -> T.True
      | (__K, depth, All ((MD, __Q), __F)) ->
          T.All
            (((abstractMetaDec (__K, depth, MD)), __Q),
              (abstractFor (__K, depth, __F)))
      | (__K, depth, Ex ((__D, __Q), __F)) ->
          T.Ex
            (((abstractDec (__K, depth, (__D, I.id))), __Q),
              (abstractFor (__K, depth, __F)))
      | (__K, depth, And (__F1, __F2)) ->
          T.And
            ((abstractFor (__K, depth, __F1)),
              (abstractFor (__K, depth, __F2)))
      | (__K, depth, World (__W, __F)) ->
          T.World (__W, (abstractFor (__K, depth, __F)))
    let rec abstractPsi =
      function
      | I.Null -> I.Null
      | Decl (__K', EV (EVar (_, GX, VX, _))) ->
          let __V' = raiseType (GX, VX) in
          let V'' = abstractExp (__K', 0, (__V', I.id)) in
          ((I.Decl ((abstractPsi __K'), (T.UDec (I.Dec (NONE, V'')))))
            (* enforced by reconstruction -kw
          val _ = checkType V'' *))
      | Decl (__K', FV (name, __V')) ->
          let V'' = abstractExp (__K', 0, (__V', I.id)) in
          ((I.Decl ((abstractPsi __K'), (T.UDec (I.Dec ((Some name), V'')))))
            (* enforced by reconstruction -kw
          val _ = checkType V'' *))
      | Decl (__K', LV (LVar (r, _, (l, t)))) ->
          let t' = abstractSOME (__K', t) in
          I.Decl ((abstractPsi __K'), (T.UDec (I.BDec (NONE, (l, t')))))
      | Decl (__K', PV (EVar (GX, _, FX, TC1, TC2, _))) ->
          let __F' = abstractFor (__K', 0, (T.forSub (FX, T.id))) in
          let TC1' = abstractTCOpt (__K', 0, TC1) in
          let TC2' = abstractTCOpt (__K', 0, TC2) in
          I.Decl ((abstractPsi __K'), (T.PDec (NONE, __F', TC1, TC2)))
      (* What's happening with TCs? *)(* What's happening with GX? *)
    let rec abstractTomegaSub t =
      let __K = collectTomegaSub t in
      let t' = abstractTomegaSub' (__K, 0, t) in
      let Psi = abstractPsi __K in (Psi, t')
    let rec abstractTomegaSub' __102__ __103__ __104__ =
      match (__102__, __103__, __104__) with
      | (__K, depth, Shift 0) -> T.Shift depth
      | (__K, depth, Dot (Exp (__U), t)) ->
          T.Dot
            ((T.Exp (abstractExp (__K, depth, (__U, I.id)))),
              (abstractTomegaSub' (__K, depth, t)))
      | (__K, depth, Dot (Block (__B), t)) ->
          T.Dot
            ((T.Block (abstractLVar (__K, depth, __B))),
              (abstractTomegaSub' (__K, depth, t)))
      | (__K, depth, Dot (Prg (__P), t)) ->
          T.Dot
            ((T.Prg (abstractPrg (__K, depth, __P))),
              (abstractTomegaSub' (__K, depth, t)))
    let rec abstractTomegaPrg (__P) =
      let __K = collectPrg (I.Null, __P, I.Null) in
      let __P' = abstractPrg (__K, 0, __P) in
      let Psi = abstractPsi __K in (Psi, __P')
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
