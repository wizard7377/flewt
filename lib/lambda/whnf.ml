
module type WHNF  =
  sig
    val isPatSub : IntSyn.__Sub -> bool
    val makePatSub : IntSyn.__Sub -> IntSyn.__Sub option
    val dotEta : IntSyn.__Front -> IntSyn.__Sub -> IntSyn.__Sub
    exception Eta 
    val etaContract : IntSyn.__Exp -> int
    val whnf : IntSyn.eclo -> IntSyn.eclo
    val expandDef : IntSyn.eclo -> IntSyn.eclo
    val whnfExpandDef : IntSyn.eclo -> IntSyn.eclo
    val etaExpandRoot : IntSyn.__Exp -> IntSyn.__Exp
    val whnfEta : IntSyn.eclo -> IntSyn.eclo -> (IntSyn.eclo * IntSyn.eclo)
    val lowerEVar : IntSyn.__Exp -> IntSyn.__Exp
    val newLoweredEVar : IntSyn.dctx -> IntSyn.eclo -> IntSyn.__Exp
    val newSpineVar : IntSyn.dctx -> IntSyn.eclo -> IntSyn.__Spine
    val spineToSub : IntSyn.__Spine -> IntSyn.__Sub -> IntSyn.__Sub
    val normalize : IntSyn.eclo -> IntSyn.__Exp
    val normalizeDec : IntSyn.__Dec -> IntSyn.__Sub -> IntSyn.__Dec
    val normalizeCtx : IntSyn.dctx -> IntSyn.dctx
    val invert : IntSyn.__Sub -> IntSyn.__Sub
    val strengthen : IntSyn.__Sub -> IntSyn.dctx -> IntSyn.dctx
    val isId : IntSyn.__Sub -> bool
    val cloInv : IntSyn.__Exp -> IntSyn.__Sub -> IntSyn.__Exp
    val compInv : IntSyn.__Sub -> IntSyn.__Sub -> IntSyn.__Sub
  end;;




module Whnf() : WHNF =
  struct
    open IntSyn
    exception Eta 
    let rec etaContract __0__ __1__ __2__ =
      match (__0__, __1__, __2__) with
      | (Root (BVar k, __S), s, n) ->
          (match bvarSub (k, s) with
           | Idx k' ->
               if k' > n
               then (etaContract' (__S, s, n); k' - n)
               else raise Eta
           | _ -> raise Eta)
      | (Lam (__D, __U), s, n) -> etaContract (__U, (dot1 s), (n + 1))
      | (EClo (__U, s'), s, n) -> etaContract (__U, (comp (s', s)), n)
      | (EVar ({ contents = Some (__U) }, _, _, _), s, n) ->
          etaContract (__U, s, n)
      | (AVar { contents = Some (__U) }, s, n) -> etaContract (__U, s, n)
      | _ -> raise Eta
    let rec etaContract' __3__ __4__ __5__ =
      match (__3__, __4__, __5__) with
      | (Nil, s, 0) -> ()
      | (App (__U, __S), s, n) ->
          if (etaContract (__U, s, 0)) = n
          then etaContract' (__S, s, (n - 1))
          else raise Eta
      | (SClo (__S, s'), s, n) -> etaContract' (__S, (comp (s', s)), n)
      | _ -> raise Eta
    let rec dotEta __6__ __7__ =
      match (__6__, __7__) with
      | ((Idx _ as Ft), s) -> Dot (Ft, s)
      | ((Exp (__U) as Ft), s) ->
          let Ft' = try Idx (etaContract (__U, id, 0)) with | Eta -> Ft in
          Dot (Ft', s)
      | ((Undef as Ft), s) -> Dot (Ft, s)
    let rec appendSpine __8__ __9__ =
      match (__8__, __9__) with
      | ((Nil, s1), __Ss2) -> SClo __Ss2
      | ((App (__U1, __S1), s1), __Ss2) ->
          App ((EClo (__U1, s1)), (appendSpine ((__S1, s1), __Ss2)))
      | ((SClo (__S1, s1'), s1), __Ss2) ->
          appendSpine ((__S1, (comp (s1', s1))), __Ss2)
    let rec whnfRedex __10__ __11__ =
      match (__10__, __11__) with
      | (__Us, (SClo (__S, s2'), s2)) ->
          whnfRedex (__Us, (__S, (comp (s2', s2))))
      | (((Root (__R), s1) as Us), (Nil, s2)) -> __Us
      | ((Root (__H1, __S1), s1), (__S2, s2)) ->
          ((Root (__H1, (appendSpine ((__S1, s1), (__S2, s2))))), id)
      | ((Lam (_, __U1), s1), (App (__U2, __S), s2)) ->
          whnfRedex
            ((whnf (__U1, (dotEta ((frontSub ((Exp __U2), s2)), s1)))),
              (__S, s2))
      | (((Lam _, s1) as Us), _) -> __Us
      | (((EVar _, s1) as Us), (Nil, s2)) -> __Us
      | ((((EVar _ as X), s1) as Us), __Ss2) ->
          (lowerEVar __X; whnfRedex ((whnf __Us), __Ss2))
      | (((AVar { contents = Some (__U) }, s1) as Us), __Ss2) ->
          whnfRedex ((__U, s1), __Ss2)
      | (((AVar { contents = NONE }, s1) as Us), __Ss2) -> __Us
      | (((FgnExp _, _) as Us), _) -> __Us
      | (((Uni _, s1) as Us), _) -> __Us
      | (((Pi _, s1) as Us), _) -> __Us(* S2[s2] = Nil *)
      (* Uni and Pi can arise after instantiation of EVar X : K *)
      (* lowerEVar X results in redex, optimize by unfolding call to whnfRedex *)
      (* Ss2 must be App, since prior cases do not apply *)
      (* S2[s2] = Nil *)(* S2 = App _, only possible if term is not eta-expanded *)
    let rec lowerEVar' __12__ __13__ =
      match (__12__, __13__) with
      | (__G, (Pi ((__D', _), __V'), s')) ->
          let D'' = decSub (__D', s') in
          let (__X', __U) =
            lowerEVar' ((Decl (__G, D'')), (whnfExpandDef (__V', (dot1 s')))) in
          (__X', (Lam (D'', __U)))
      | (__G, __Vs') ->
          let __X' = newEVar (__G, (EClo __Vs')) in (__X', __X')
    let rec lowerEVar1 __14__ __15__ =
      match (__14__, __15__) with
      | (EVar (r, __G, _, _), ((Pi _, _) as Vs)) ->
          let (__X', __U) = lowerEVar' (__G, __Vs) in
          let _ = (:=) r Some __U in __X'
      | (__X, _) -> __X
    let rec lowerEVar =
      function
      | EVar (r, __G, __V, { contents = nil }) as X ->
          lowerEVar1 (__X, (whnfExpandDef (__V, id)))
      | EVar _ ->
          raise
            (Error
               "Typing ambiguous -- constraint of functional type cannot be simplified")
      (* pre-Twelf 1.2 code walk, Fri May  8 11:05:08 1998 *)(* It is not clear if this case can happen *)
    let rec whnfRoot __16__ __17__ =
      match (__16__, __17__) with
      | ((BVar k, __S), s) ->
          (match bvarSub (k, s) with
           | Idx k -> ((Root ((BVar k), (SClo (__S, s)))), id)
           | Exp (__U) -> whnfRedex ((whnf (__U, id)), (__S, s)))
      | ((Proj ((Bidx _ as B), i), __S), s) ->
          (match blockSub (__B, s) with
           | Bidx k as B' -> ((Root ((Proj (__B', i)), (SClo (__S, s)))), id)
           | LVar _ as B' ->
               whnfRoot (((Proj (__B', i)), (SClo (__S, s))), id)
           | Inst (__L) ->
               whnfRedex ((whnf ((List.nth (__L, (i - 1))), id)), (__S, s)))
      | ((Proj (LVar ({ contents = Some (__B) }, sk, (l, t)), i), __S), s) ->
          whnfRoot
            (((Proj ((blockSub (__B, (comp (sk, s)))), i)), (SClo (__S, s))),
              id)
      | ((Proj ((LVar (r, sk, (l, t)) as L), i), __S), s) ->
          ((Root
              ((Proj ((LVar (r, (comp (sk, s)), (l, t))), i)),
                (SClo (__S, s)))), id)
      | ((FVar (name, __V, s'), __S), s) ->
          ((Root ((FVar (name, __V, (comp (s', s)))), (SClo (__S, s)))), id)
      | ((NSDef d, __S), s) ->
          whnfRedex ((whnf ((IntSyn.constDef d), id)), (__S, s))
      | ((__H, __S), s) -> ((Root (__H, (SClo (__S, s)))), id)(* Undef and Exp should be impossible by definition of substitution -cs *)
      (* no longer satisfied Wed Nov 27 09:49:58 2002 -fp *)(* going back to first version, because globality invariant *)
      (* was: (Root (Proj (L, i), SClo (S, s)), id) *)
      (* Thu Dec  6 20:34:30 2001 -fp !!! *)(* do not compose with t due to globality invariant *)
      (* was:
         (Root (Proj (LVar (r, comp (sk, s), (l, comp(t, s))), i), SClo (S, s)), id)
         Jul 22, 2010 -fp -cs
         *)
      (* scary: why is comp(sk, s) = ^n ?? -fp July 22, 2010, -fp -cs *)
      (* r = ref NONE *)(* was: (Root (Proj (blockSub (B, s), i), SClo (S, s)), id) *)
      (* yes Thu Dec 13 21:48:10 2001 -fp !!! *)(* Sat Dec  8 13:43:17 2001 -fp !!! *)
      (* could blockSub (B, s) return instantiated LVar ? *)(* Undef should be impossible *)
    let rec whnf __18__ __19__ =
      match (__18__, __19__) with
      | ((Uni _ as U), s) -> (__U, s)
      | ((Pi _ as U), s) -> (__U, s)
      | (Root (__R), s) -> whnfRoot (__R, s)
      | (Redex (__U, __S), s) -> whnfRedex ((whnf (__U, s)), (__S, s))
      | (Lam _, s) as Us -> __Us
      | (AVar { contents = Some (__U) }, s) -> whnf (__U, s)
      | (AVar _, s) as Us -> __Us
      | (EVar ({ contents = Some (__U) }, _, _, _), s) -> whnf (__U, s)
      | (EVar (r, _, Root _, _), s) as Us -> __Us
      | (EVar (r, _, Uni _, _), s) as Us -> __Us
      | ((EVar (r, _, __V, _) as X), s) as Us ->
          (((match whnf (__V, id) with
             | (Pi _, _) -> (lowerEVar __X; whnf __Us)
             | _ -> __Us))
          (* possible opt: call lowerEVar1 *))
      | (EClo (__U, s'), s) -> whnf (__U, (comp (s', s)))
      | (FgnExp _, Shift 0) as Us -> __Us
      | (FgnExp csfe, s) as Us ->
          ((FgnExpStd.Map.apply csfe (fun (__U) -> EClo (__U, s))), id)
      (* next two avoid calls to whnf (V, id), where V is type of X *)
      (* | whnf (Us as (EVar _, s)) = Us *)(* commented out, because non-strict definitions slip
         Mon May 24 09:50:22 EDT 1999 -cs  *)
      (*      | whnf (Us as (Root _, Shift (0))) = Us*)
      (* Sat Feb 14 20:53:08 1998 -fp *)(* applied in Twelf 1.1 *)
      (* simple optimization (C@S)[id] = C@S[id] *)
    let rec expandDef (Root (Def d, __S)) s =
      whnfRedex ((whnf ((constDef d), id)), (__S, s))(* why the call to whnf?  isn't constDef (d) in nf? -kw *)
    let rec whnfExpandDefW =
      function
      | (Root (Def _, _), _) as Us -> whnfExpandDefW (expandDef __Us)
      | __Us -> __Us
    let rec whnfExpandDef (__Us) = whnfExpandDefW (whnf __Us)
    let rec newLoweredEVarW __20__ __21__ =
      match (__20__, __21__) with
      | (__G, (Pi ((__D, _), __V), s)) ->
          let __D' = decSub (__D, s) in
          Lam (__D', (newLoweredEVar ((Decl (__G, __D')), (__V, (dot1 s)))))
      | (__G, __Vs) -> newEVar (__G, (EClo __Vs))
    let rec newLoweredEVar (__G) (__Vs) =
      newLoweredEVarW (__G, (whnfExpandDef __Vs))
    let rec newSpineVarW __22__ __23__ =
      match (__22__, __23__) with
      | (__G, (Pi ((Dec (_, Va), _), Vr), s)) ->
          let __X = newLoweredEVar (__G, (Va, s)) in
          App (__X, (newSpineVar (__G, (Vr, (dotEta ((Exp __X), s))))))
      | (__G, _) -> Nil
    let rec newSpineVar (__G) (__Vs) =
      newSpineVarW (__G, (whnfExpandDef __Vs))
    let rec spineToSub __24__ __25__ =
      match (__24__, __25__) with
      | (Nil, s) -> s
      | (App (__U, __S), s) -> spineToSub (__S, (dotEta ((Exp __U), s)))
    let rec inferSpine __26__ __27__ =
      match (__26__, __27__) with
      | ((Nil, _), __Vs) -> __Vs
      | ((SClo (__S, s'), s), __Vs) ->
          inferSpine ((__S, (comp (s', s))), __Vs)
      | ((App (__U, __S), s1), (Pi (_, __V2), s2)) ->
          inferSpine
            ((__S, s1),
              (whnfExpandDef (__V2, (Dot ((Exp (EClo (__U, s1))), s2)))))
    let rec inferCon =
      function
      | Const cid -> constType cid
      | Skonst cid -> constType cid
      | Def cid -> constType cid
    let rec etaExpand' __28__ __29__ =
      match (__28__, __29__) with
      | (__U, (Root _, s)) -> __U
      | (__U, (Pi ((__D, _), __V), s)) ->
          Lam
            ((decSub (__D, s)),
              (etaExpand'
                 ((Redex
                     ((EClo (__U, shift)),
                       (App ((Root ((BVar 1), Nil)), Nil)))),
                   (whnfExpandDef (__V, (dot1 s))))))
    let rec etaExpandRoot (Root (__H, __S) as U) =
      etaExpand' (__U, (inferSpine ((__S, id), ((inferCon __H), id))))
    let rec whnfEta (__Us) (__Vs) = whnfEtaW ((whnf __Us), (whnf __Vs))
    let rec whnfEtaW __30__ =
      match __30__ with
      | (_, (Root _, _)) as UsVs -> UsVs
      | ((Lam _, _), (Pi _, _)) as UsVs -> UsVs
      | ((__U, s1), ((Pi ((__D, __P), __V), s2) as Vs2)) ->
          (((Lam
               ((decSub (__D, s2)),
                 (Redex
                    ((EClo (__U, (comp (s1, shift)))),
                      (App ((Root ((BVar 1), Nil)), Nil)))))), id), __Vs2)
    let rec normalizeExp (__Us) = normalizeExpW (whnf __Us)
    let rec normalizeExpW __31__ __32__ =
      match (__31__, __32__) with
      | ((Uni (__L) as U), s) -> __U
      | (Pi (DP, __U), s) ->
          Pi ((normalizeDecP (DP, s)), (normalizeExp (__U, (dot1 s))))
      | ((Root (__H, __S) as U), s) -> Root (__H, (normalizeSpine (__S, s)))
      | (Lam (__D, __U), s) ->
          Lam ((normalizeDec (__D, s)), (normalizeExp (__U, (dot1 s))))
      | (EVar _, s) as Us -> EClo __Us
      | (FgnExp csfe, s) ->
          FgnExpStd.Map.apply csfe (fun (__U) -> normalizeExp (__U, s))
      | (AVar { contents = Some (__U) }, s) as Us -> normalizeExpW (__U, s)
      | (AVar _, s) as Us -> (print "Normalize  AVAR\n"; raise (Error ""))
      (* s = id *)
    let rec normalizeSpine __33__ __34__ =
      match (__33__, __34__) with
      | (Nil, s) -> Nil
      | (App (__U, __S), s) ->
          App ((normalizeExp (__U, s)), (normalizeSpine (__S, s)))
      | (SClo (__S, s'), s) -> normalizeSpine (__S, (comp (s', s)))
    let rec normalizeDec __35__ __36__ =
      match (__35__, __36__) with
      | (Dec (xOpt, __V), s) -> Dec (xOpt, (normalizeExp (__V, s)))
      | (BDec (xOpt, (c, t)), s) ->
          BDec (xOpt, (c, (normalizeSub (comp (t, s)))))
    let rec normalizeDecP (__D, __P) s = ((normalizeDec (__D, s)), __P)
    let rec normalizeSub =
      function
      | Shift _ as s -> s
      | Dot ((Idx _ as Ft), s) -> Dot (Ft, (normalizeSub s))
      | Dot (Exp (__U), s) ->
          dotEta ((Exp (normalizeExp (__U, id))), (normalizeSub s))(* Dot (Exp (normalizeExp (U, id)), normalizeSub s) *)
      (* Sat Dec  7 16:58:09 2002 -fp *)(* changed to obtain pattern substitution if possible *)
    let rec normalizeCtx =
      function
      | Null -> Null
      | Decl (__G, __D) ->
          Decl ((normalizeCtx __G), (normalizeDec (__D, id)))
    let rec invert s =
      let rec lookup __37__ __38__ __39__ =
        match (__37__, __38__, __39__) with
        | (n, Shift _, p) -> NONE
        | (n, Dot (Undef, s'), p) -> lookup ((n + 1), s', p)
        | (n, Dot (Idx k, s'), p) ->
            if k = p then Some n else lookup ((n + 1), s', p) in
      let rec invert'' __40__ __41__ =
        match (__40__, __41__) with
        | (0, si) -> si
        | (p, si) ->
            (match lookup (1, s, p) with
             | Some k -> invert'' ((p - 1), (Dot ((Idx k), si)))
             | NONE -> invert'' ((p - 1), (Dot (Undef, si)))) in
      let rec invert' __42__ __43__ =
        match (__42__, __43__) with
        | (n, Shift p) -> invert'' (p, (Shift n))
        | (n, Dot (_, s')) -> invert' ((n + 1), s') in
      invert' (0, s)
    let rec strengthen __44__ __45__ =
      match (__44__, __45__) with
      | (Shift n, Null) -> Null
      | (Dot (((Idx k, t))(* k = 1 *)), Decl (__G, __D)) ->
          let t' = comp (t, invShift) in
          ((Decl ((strengthen (t', __G)), (decSub (__D, t'))))
            (* G |- D dec *)(* G' |- t' : G *)(* G' |- D[t'] dec *))
      | (Dot (Undef, t), Decl (__G, __D)) -> strengthen (t, __G)
      | (Shift n, __G) ->
          strengthen ((Dot ((Idx (n + 1)), (Shift (n + 1)))), __G)(* = 0 *)
    let rec isId' __46__ __47__ =
      match (__46__, __47__) with
      | (Shift k, k') -> k = k'
      | (Dot (Idx n, s'), k') -> (n = k') && (isId' (s', (k' + 1)))
      | _ -> false__
    let rec isId s = isId' (s, 0)
    let rec cloInv (__U) w = EClo (__U, (invert w))
    let rec compInv s w = comp (s, (invert w))
    let rec isPatSub =
      function
      | Shift k -> true__
      | Dot (Idx n, s) ->
          let rec checkBVar =
            function
            | Shift k -> n <= k
            | Dot (Idx n', s) -> (n <> n') && (checkBVar s)
            | Dot (Undef, s) -> checkBVar s
            | _ -> false__ in
          (checkBVar s) && (isPatSub s)
      | Dot (Undef, s) -> isPatSub s
      | _ -> false__
    let rec mkPatSub =
      function
      | Shift k as s -> s
      | Dot (Idx n, s) ->
          let s' = mkPatSub s in
          let rec checkBVar =
            function
            | Shift k -> n <= k
            | Dot (Idx n', s') -> (n <> n') && (checkBVar s')
            | Dot (Undef, s') -> checkBVar s' in
          let _ = checkBVar s' in Dot ((Idx n), s')
      | Dot (Undef, s) -> Dot (Undef, (mkPatSub s))
      | Dot (Exp (__U), s) ->
          let (__U', t') = whnf (__U, id) in
          let k = etaContract (__U', t', 0) in ((Dot ((Idx k), (mkPatSub s)))
            (* may raise Eta *))
      | _ -> raise Eta
    let rec makePatSub s = try Some (mkPatSub s) with | Eta -> NONE
    let isPatSub = isPatSub
    let makePatSub = makePatSub
    let dotEta = dotEta
    exception Eta = Eta
    let etaContract (__U) = etaContract (__U, id, 0)
    let whnf = whnf
    let expandDef = expandDef
    let whnfExpandDef = whnfExpandDef
    let etaExpandRoot = etaExpandRoot
    let whnfEta = whnfEta
    let lowerEVar = lowerEVar
    let newLoweredEVar = newLoweredEVar
    let newSpineVar = newSpineVar
    let spineToSub = spineToSub
    let normalize = normalizeExp
    let normalizeDec = normalizeDec
    let normalizeCtx = normalizeCtx
    let invert = invert
    let strengthen = strengthen
    let isId = isId
    let cloInv = cloInv
    let compInv = compInv
  end ;;
