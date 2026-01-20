
module type MTPABSTRACT  =
  sig
    module StateSyn : STATESYN
    exception Error of string 
    type __ApproxFor =
      | Head of (IntSyn.dctx * (FunSyn.__For * IntSyn.__Sub) * int) 
      | Block of ((IntSyn.dctx * IntSyn.__Sub * int * IntSyn.__Dec list) *
      __ApproxFor) 
    val weaken : IntSyn.dctx -> IntSyn.cid -> IntSyn.__Sub
    val raiseType : IntSyn.dctx -> IntSyn.__Exp -> IntSyn.__Exp
    val abstractSub :
      IntSyn.__Sub ->
        StateSyn.__Tag IntSyn.__Ctx ->
          (IntSyn.dctx * StateSyn.__Tag IntSyn.__Ctx) ->
            IntSyn.__Sub ->
              StateSyn.__Tag IntSyn.__Ctx ->
                ((IntSyn.dctx * StateSyn.__Tag IntSyn.__Ctx) * IntSyn.__Sub)
    val abstractSub' :
      (IntSyn.dctx * StateSyn.__Tag IntSyn.__Ctx) ->
        IntSyn.__Sub ->
          StateSyn.__Tag IntSyn.__Ctx ->
            ((IntSyn.dctx * StateSyn.__Tag IntSyn.__Ctx) * IntSyn.__Sub)
    val abstractApproxFor : __ApproxFor -> FunSyn.__For
  end;;




module MTPAbstract(MTPAbstract:sig
                                 module StateSyn' : STATESYN
                                 module Whnf : WHNF
                                 module Constraints : CONSTRAINTS
                                 module Unify : UNIFY
                                 module Subordinate : SUBORDINATE
                                 module TypeCheck : TYPECHECK
                                 module FunTypeCheck : FUNTYPECHECK
                                 module Abstract : ABSTRACT
                               end) : MTPABSTRACT =
  struct
    module StateSyn = StateSyn'
    exception Error of string 
    type __ApproxFor =
      | Head of (IntSyn.dctx * (FunSyn.__For * IntSyn.__Sub) * int) 
      | Block of ((IntSyn.dctx * IntSyn.__Sub * int * IntSyn.__Dec list) *
      __ApproxFor) 
    module I = IntSyn
    module F = FunSyn
    module S = StateSyn
    module C = Constraints
    type __EBVar =
      | EV of (I.__Exp option ref * I.__Exp * S.__Tag * int) 
      | BV of (I.__Dec * S.__Tag) 
    let rec checkEmpty =
      function
      | nil -> ()
      | cnstrL ->
          (match C.simplify cnstrL with
           | nil -> ()
           | _ -> raise (Error "Typing ambiguous -- unresolved constraints"))
    let rec eqEVar __0__ __1__ =
      match (__0__, __1__) with
      | (EVar (r1, _, _, _), EV (r2, _, _, _)) -> r1 = r2
      | (_, _) -> false
    let rec exists (__P) (__K) =
      let rec exists' =
        function
        | I.Null -> false
        | Decl (__K', __Y) -> (__P __Y) || (exists' __K') in
      exists' __K
    let rec or__ __2__ __3__ =
      match (__2__, __3__) with
      | (I.Maybe, _) -> I.Maybe
      | (_, I.Maybe) -> I.Maybe
      | (I.Meta, _) -> I.Meta
      | (_, I.Meta) -> I.Meta
      | (I.No, I.No) -> I.No
    let rec occursInExp __4__ __5__ =
      match (__4__, __5__) with
      | (k, Uni _) -> I.No
      | (k, Pi (DP, __V)) ->
          or__ ((occursInDecP (k, DP)), (occursInExp ((k + 1), __V)))
      | (k, Root (__H, __S)) ->
          occursInHead (k, __H, (occursInSpine (k, __S)))
      | (k, Lam (__D, __V)) ->
          or__ ((occursInDec (k, __D)), (occursInExp ((k + 1), __V)))
    let rec occursInHead __6__ __7__ __8__ =
      match (__6__, __7__, __8__) with
      | (k, BVar k', DP) -> if k = k' then I.Maybe else DP
      | (k, Const _, DP) -> DP
      | (k, Def _, DP) -> DP
      | (k, Skonst _, I.No) -> I.No
      | (k, Skonst _, I.Meta) -> I.Meta
      | (k, Skonst _, I.Maybe) -> I.Meta
    let rec occursInSpine __9__ __10__ =
      match (__9__, __10__) with
      | (_, I.Nil) -> I.No
      | (k, App (__U, __S)) ->
          or__ ((occursInExp (k, __U)), (occursInSpine (k, __S)))
    let rec occursInDec k (Dec (_, __V)) = occursInExp (k, __V)
    let rec occursInDecP k (__D, _) = occursInDec (k, __D)
    let rec piDepend __11__ =
      match __11__ with
      | ((__D, I.No), __V) as DPV -> I.Pi DPV
      | ((__D, I.Meta), __V) as DPV -> I.Pi DPV
      | ((__D, I.Maybe), __V) -> I.Pi ((__D, (occursInExp (1, __V))), __V)
    let rec weaken __12__ __13__ =
      match (__12__, __13__) with
      | (I.Null, a) -> I.id
      | (Decl (__G', (Dec (name, __V) as D)), a) ->
          let w' = weaken (__G', a) in
          if Subordinate.belowEq ((I.targetFam __V), a)
          then I.dot1 w'
          else I.comp (w', I.shift)
    let rec raiseType __14__ __15__ =
      match (__14__, __15__) with
      | (I.Null, __V) -> __V
      | (Decl (__G, __D), __V) ->
          raiseType (__G, (I.Pi ((__D, I.Maybe), __V)))
    let rec restore __16__ __17__ =
      match (__16__, __17__) with
      | (0, Gp) -> (Gp, I.Null)
      | (n, Decl (__G, __D)) ->
          let (Gp', GX') = restore ((n - 1), __G) in
          (Gp', (I.Decl (GX', __D)))
    let rec concat __18__ __19__ =
      match (__18__, __19__) with
      | (Gp, I.Null) -> Gp
      | (Gp, Decl (__G, __D)) -> I.Decl ((concat (Gp, __G)), __D)
    let rec collectExpW __20__ __21__ __22__ __23__ __24__ =
      match (__20__, __21__, __22__, __23__, __24__) with
      | (__T, d, __G, (Uni (__L), s), __K) -> __K
      | (__T, d, __G, (Pi ((__D, _), __V), s), __K) ->
          collectExp
            (__T, d, (I.Decl (__G, (I.decSub (__D, s)))), (__V, (I.dot1 s)),
              (collectDec (__T, d, __G, (__D, s), __K)))
      | (__T, d, __G, (Root (_, __S), s), __K) ->
          collectSpine ((S.decrease __T), d, __G, (__S, s), __K)
      | (__T, d, __G, (Lam (__D, __U), s), __K) ->
          collectExp
            (__T, d, (I.Decl (__G, (I.decSub (__D, s)))), (__U, (I.dot1 s)),
              (collectDec (__T, d, __G, (__D, s), __K)))
      | (__T, d, __G, ((EVar (r, GdX, __V, cnstrs) as X), s), __K) ->
          if exists (eqEVar __X) __K
          then collectSub (__T, d, __G, s, __K)
          else
            (let (Gp, GX) = restore (((I.ctxLength GdX) - d), GdX) in
             let _ = checkEmpty (!cnstrs) in
             let w = weaken (GX, (I.targetFam __V)) in
             let iw = Whnf.invert w in
             let GX' = Whnf.strengthen (iw, GX) in
             let EVar (r', _, _, _) as X' =
               I.newEVar ((concat (Gp, GX')), (I.EClo (__V, iw))) in
             let _ = Unify.instantiateEVar (r, (I.EClo (__X', w)), nil) in
             let __V' = raiseType (GX', (I.EClo (__V, iw))) in
             ((collectSub
                 (__T, d, __G, (I.comp (w, s)),
                   (I.Decl
                      ((collectExp (__T, d, Gp, (__V', I.id), __K)),
                        (EV (r', __V', __T, d))))))
               (* optimization possible for d = 0 *)))
      | (__T, d, __G, (FgnExp csfe, s), __K) ->
          I.FgnExpStd.fold csfe
            (fun (__U) ->
               fun (__K') -> collectExp (__T, d, __G, (__U, s), __K')) __K
    let rec collectExp (__T) d (__G) (__Us) (__K) =
      collectExpW (__T, d, __G, (Whnf.whnf __Us), __K)
    let rec collectSpine __25__ __26__ __27__ __28__ __29__ =
      match (__25__, __26__, __27__, __28__, __29__) with
      | (__T, d, __G, (I.Nil, _), __K) -> __K
      | (__T, d, __G, (SClo (__S, s'), s), __K) ->
          collectSpine (__T, d, __G, (__S, (I.comp (s', s))), __K)
      | (__T, d, __G, (App (__U, __S), s), __K) ->
          collectSpine
            (__T, d, __G, (__S, s),
              (collectExp (__T, d, __G, (__U, s), __K)))
    let rec collectDec (__T) d (__G) (Dec (_, __V), s) (__K) =
      collectExp (__T, d, __G, (__V, s), __K)
    let rec collectSub __30__ __31__ __32__ __33__ __34__ =
      match (__30__, __31__, __32__, __33__, __34__) with
      | (__T, d, __G, Shift _, __K) -> __K
      | (__T, d, __G, Dot (Idx _, s), __K) ->
          collectSub (__T, d, __G, s, __K)
      | (__T, d, __G, Dot (Exp (__U), s), __K) ->
          collectSub
            (__T, d, __G, s, (collectExp (__T, d, __G, (__U, I.id), __K)))
    let rec abstractEVar __35__ __36__ __37__ =
      match (__35__, __36__, __37__) with
      | (Decl (__K', EV (r', _, _, d)), depth, (EVar (r, _, _, _) as X)) ->
          if r = r'
          then ((I.BVar (depth + 1)), d)
          else abstractEVar (__K', (depth + 1), __X)
      | (Decl (__K', BV _), depth, __X) ->
          abstractEVar (__K', (depth + 1), __X)
    let rec lookupBV (__K) i =
      let rec lookupBV' __38__ __39__ __40__ =
        match (__38__, __39__, __40__) with
        | (Decl (__K, EV (r, __V, _, _)), i, k) ->
            lookupBV' (__K, i, (k + 1))
        | (Decl (__K, BV _), 1, k) -> k
        | (Decl (__K, BV _), i, k) -> lookupBV' (__K, (i - 1), (k + 1)) in
      ((lookupBV' (__K, i, 1))
        (* lookupBV' I.Null cannot occur by invariant *))
    let rec abstractExpW __41__ __42__ __43__ =
      match (__41__, __42__, __43__) with
      | (__K, depth, ((Uni (__L) as U), s)) -> __U
      | (__K, depth, (Pi ((__D, __P), __V), s)) ->
          piDepend
            (((abstractDec (__K, depth, (__D, s))), __P),
              (abstractExp (__K, (depth + 1), (__V, (I.dot1 s)))))
      | (__K, depth, (Root ((BVar k as H), __S), s)) ->
          if k > depth
          then
            let k' = lookupBV (__K, (k - depth)) in
            I.Root
              ((I.BVar (k' + depth)), (abstractSpine (__K, depth, (__S, s))))
          else I.Root (__H, (abstractSpine (__K, depth, (__S, s))))
      | (__K, depth, (Root (__H, __S), s)) ->
          I.Root (__H, (abstractSpine (__K, depth, (__S, s))))
      | (__K, depth, (Lam (__D, __U), s)) ->
          I.Lam
            ((abstractDec (__K, depth, (__D, s))),
              (abstractExp (__K, (depth + 1), (__U, (I.dot1 s)))))
      | (__K, depth, ((EVar (_, __G, _, _) as X), s)) ->
          let (__H, d) = abstractEVar (__K, depth, __X) in
          I.Root
            (__H,
              (abstractSub (((I.ctxLength __G) - d), __K, depth, s, I.Nil)))
      | (__K, depth, (FgnExp csfe, s)) ->
          I.FgnExpStd.Map.apply csfe
            (fun (__U) -> abstractExp (__K, depth, (__U, s)))(* s = id *)
    let rec abstractExp (__K) depth (__Us) =
      abstractExpW (__K, depth, (Whnf.whnf __Us))
    let rec abstractSub __44__ __45__ __46__ __47__ __48__ =
      match (__44__, __45__, __46__, __47__, __48__) with
      | (n, __K, depth, Shift k, __S) ->
          ((if n > 0
            then
              abstractSub
                (n, __K, depth, (I.Dot ((I.Idx (k + 1)), (I.Shift (k + 1)))),
                  __S)
            else __S)
          (* n = 0 *))
      | (n, __K, depth, Dot (Idx k, s), __S) ->
          let __H =
            if k > depth
            then let k' = lookupBV (__K, (k - depth)) in I.BVar (k' + depth)
            else I.BVar k in
          abstractSub
            ((n - 1), __K, depth, s, (I.App ((I.Root (__H, I.Nil)), __S)))
      | (n, __K, depth, Dot (Exp (__U), s), __S) ->
          abstractSub
            ((n - 1), __K, depth, s,
              (I.App ((abstractExp (__K, depth, (__U, I.id))), __S)))
    let rec abstractSpine __49__ __50__ __51__ =
      match (__49__, __50__, __51__) with
      | (__K, depth, (I.Nil, _)) -> I.Nil
      | (__K, depth, (SClo (__S, s'), s)) ->
          abstractSpine (__K, depth, (__S, (I.comp (s', s))))
      | (__K, depth, (App (__U, __S), s)) ->
          I.App
            ((abstractExp (__K, depth, (__U, s))),
              (abstractSpine (__K, depth, (__S, s))))
    let rec abstractDec (__K) depth (Dec (x, __V), s) =
      I.Dec (x, (abstractExp (__K, depth, (__V, s))))
    let rec getLevel =
      function
      | Uni _ -> I.Kind
      | Pi (_, __U) -> getLevel __U
      | Root _ -> I.Type
      | Redex (__U, _) -> getLevel __U
      | Lam (_, __U) -> getLevel __U
      | EClo (__U, _) -> getLevel __U
    let rec checkType (__V) =
      match getLevel __V with
      | I.Type -> ()
      | _ -> raise (Error "Typing ambiguous -- free type variable")
    let rec abstractCtx =
      function
      | I.Null -> (I.Null, I.Null)
      | Decl (__K', EV (_, __V', (Lemma b as T), _)) ->
          let V'' = abstractExp (__K', 0, (__V', I.id)) in
          let _ = checkType V'' in
          let (__G', __B') = abstractCtx __K' in
          let __D' = I.Dec (None, V'') in
          ((I.Decl (__G', __D')), (I.Decl (__B', __T)))
      | Decl (__K', EV (_, __V', (S.None as T), _)) ->
          let V'' = abstractExp (__K', 0, (__V', I.id)) in
          let _ = checkType V'' in
          let (__G', __B') = abstractCtx __K' in
          let __D' = I.Dec (None, V'') in
          ((I.Decl (__G', __D')), (I.Decl (__B', S.None)))
      | Decl (__K', BV (__D, __T)) ->
          let __D' = abstractDec (__K', 0, (__D, I.id)) in
          let (__G', __B') = abstractCtx __K' in
          ((I.Decl (__G', __D')), (I.Decl (__B', __T)))
    let rec abstractGlobalSub __52__ __53__ __54__ =
      match (__52__, __53__, __54__) with
      | (__K, Shift _, I.Null) -> I.Shift (I.ctxLength __K)
      | (__K, Shift n, (Decl _ as B)) ->
          abstractGlobalSub
            (__K, (I.Dot ((I.Idx (n + 1)), (I.Shift (n + 1)))), __B)
      | (__K, Dot (Idx k, s'), Decl (__B, (Parameter _ as T))) ->
          I.Dot
            ((I.Idx (lookupBV (__K, k))), (abstractGlobalSub (__K, s', __B)))
      | (__K, Dot (Exp (__U), s'), Decl (__B, (Lemma _ as T))) ->
          I.Dot
            ((I.Exp (abstractExp (__K, 0, (__U, I.id)))),
              (abstractGlobalSub (__K, s', __B)))
    let rec collectGlobalSub __55__ __56__ __57__ __58__ =
      match (__55__, __56__, __57__, __58__) with
      | (__G0, Shift _, I.Null, collect) -> collect
      | (__G0, s, (Decl (_, Parameter (Some l)) as B), collect) ->
          let LabelDec (name, _, __G2) = F.labelLookup l in
          skip (__G0, (List.length __G2), s, __B, collect)
      | (__G0, Dot (Exp (__U), s), Decl (__B, __T), collect) ->
          collectGlobalSub
            (__G0, s, __B,
              (fun d ->
                 fun (__K) ->
                   collect (d, (collectExp (__T, d, __G0, (__U, I.id), __K)))))
    let rec skip __59__ __60__ __61__ __62__ __63__ =
      match (__59__, __60__, __61__, __62__, __63__) with
      | (__G0, 0, s, __B, collect) ->
          collectGlobalSub (__G0, s, __B, collect)
      | (Decl (__G0, __D), n, s, Decl (__B, (Parameter _ as T)), collect) ->
          skip
            (__G0, (n - 1), (I.invDot1 s), __B,
              (fun d ->
                 fun (__K) ->
                   collect ((d + 1), (I.Decl (__K, (BV (__D, __T)))))))
    let rec abstractNew (__G0, __B0) s (__B) =
      let cf = collectGlobalSub (__G0, s, __B, (fun _ -> fun (__K') -> __K')) in
      let __K = cf (0, I.Null) in
      ((abstractCtx __K), (abstractGlobalSub (__K, s, __B)))
    let rec abstractSubAll t (__B1) (__G0, __B0) s (__B) =
      let rec skip'' __64__ __65__ =
        match (__64__, __65__) with
        | (__K, (I.Null, I.Null)) -> __K
        | (__K, (Decl (__G0, __D), Decl (__B0, __T))) ->
            I.Decl ((skip'' (__K, (__G0, __B0))), (BV (__D, __T))) in
      let collect2 =
        collectGlobalSub (__G0, s, __B, (fun _ -> fun (__K') -> __K')) in
      let collect0 =
        collectGlobalSub (I.Null, t, __B1, (fun _ -> fun (__K') -> __K')) in
      let __K0 = collect0 (0, I.Null) in
      let __K1 = skip'' (__K0, (__G0, __B0)) in
      let d = I.ctxLength __G0 in
      let __K = collect2 (d, __K1) in
      ((((abstractCtx __K), (abstractGlobalSub (__K, s, __B))))
        (* skip'' (K, (G, B)) = K'

             Invariant:
             If   G = x1:V1 .. xn:Vn
             and  G |- B = <param> ... <param> tags
             then  K' = K, BV (x1) .. BV (xn)
          *))
    let rec abstractFor __66__ __67__ __68__ =
      match (__66__, __67__, __68__) with
      | (__K, depth, (All (Prim (__D), __F), s)) ->
          F.All
            ((F.Prim (abstractDec (__K, depth, (__D, s)))),
              (abstractFor (__K, (depth + 1), (__F, (I.dot1 s)))))
      | (__K, depth, (Ex (__D, __F), s)) ->
          F.Ex
            ((abstractDec (__K, depth, (__D, s))),
              (abstractFor (__K, (depth + 1), (__F, (I.dot1 s)))))
      | (__K, depth, (F.True, s)) -> F.True
      | (__K, depth, (And (__F1, __F2), s)) ->
          F.And
            ((abstractFor (__K, depth, (__F1, s))),
              (abstractFor (__K, depth, (__F2, s))))
    let rec allClo __69__ __70__ =
      match (__69__, __70__) with
      | (I.Null, __F) -> __F
      | (Decl (Gx, __D), __F) -> allClo (Gx, (F.All ((F.Prim __D), __F)))
    let rec convert =
      function
      | I.Null -> I.Null
      | Decl (__G, __D) ->
          I.Decl ((convert __G), (BV (__D, (S.Parameter None))))
    let rec createEmptyB =
      function | 0 -> I.Null | n -> I.Decl ((createEmptyB (n - 1)), S.None)
    let rec lower __71__ __72__ =
      match (__71__, __72__) with
      | (_, 0) -> I.Null
      | (Decl (__G, __D), n) -> I.Decl ((lower (__G, (n - 1))), __D)
    let rec split __73__ __74__ =
      match (__73__, __74__) with
      | (__G, 0) -> (__G, I.Null)
      | (Decl (__G, __D), n) ->
          let (__G1, __G2) = split (__G, (n - 1)) in
          (__G1, (I.Decl (__G2, __D)))
    let rec shift =
      function | I.Null -> I.shift | Decl (__G, _) -> I.dot1 (shift __G)
    let rec ctxSub __75__ __76__ =
      match (__75__, __76__) with
      | (nil, s) -> nil
      | ((__D)::__G, s) -> (::) (I.decSub (__D, s)) ctxSub (__G, (I.dot1 s))
    let rec weaken2 __77__ __78__ __79__ =
      match (__77__, __78__, __79__) with
      | (I.Null, a, i) -> (I.id, ((fun (__S) -> __S)))
      | (Decl (__G', (Dec (name, __V) as D)), a, i) ->
          let (w', __S') = weaken2 (__G', a, (i + 1)) in
          if Subordinate.belowEq ((I.targetFam __V), a)
          then
            ((I.dot1 w'),
              ((fun (__S) -> I.App ((I.Root ((I.BVar i), I.Nil)), __S))))
          else ((I.comp (w', I.shift)), __S')
    let rec raiseType __80__ __81__ =
      match (__80__, __81__) with
      | (I.Null, __V) -> __V
      | (Decl (__G, __D), __V) ->
          raiseType
            (__G,
              (Abstract.piDepend
                 (((Whnf.normalizeDec (__D, I.id)), I.Maybe), __V)))
    let rec raiseFor __82__ __83__ __84__ __85__ __86__ =
      match (__82__, __83__, __84__, __85__, __86__) with
      | (k, Gorig, (F.True as F), w, sc) -> __F
      | (k, Gorig, Ex (Dec (name, __V), __F), w, sc) ->
          let __G = F.listToCtx (ctxSub ((F.ctxToList Gorig), w)) in
          let g = I.ctxLength __G in
          let s = sc (w, k) in
          let __V' = I.EClo (__V, s) in
          let (nw, __S) = weaken2 (__G, (I.targetFam __V), 1) in
          let iw = Whnf.invert nw in
          let Gw = Whnf.strengthen (iw, __G) in
          let V'' = Whnf.normalize (__V', iw) in
          let V''' = Whnf.normalize ((raiseType (Gw, V'')), I.id) in
          let S''' = __S I.Nil in
          let sc' w' k' =
            let s' = sc (w', k') in
            ((I.Dot ((I.Exp (I.Root ((I.BVar ((g + k') - k)), S'''))), s'))
              (* G0, GA |- w' : G0 *)(* G0, GA, G[..] |- s' : G0, G, GF *)
              (* G0, GA, G[..] |- (g+k'-k). S', s' : G0, G, GF, V *)) in
          let __F' =
            raiseFor ((k + 1), Gorig, __F, (I.comp (w, I.shift)), sc') in
          ((F.Ex ((I.Dec (name, V''')), __F'))
            (* G0, {G}GF[..], G |- s : G0, G, GF *)(* G0, {G}GF[..], G |- V' : type *)
            (* G0, {G}GF[..], G |- nw : G0, {G}GF[..], Gw
                                         Gw < G *)
            (* G0, {G}GF[..], Gw |- iw : G0, {G}GF[..], G *)
            (* Generalize the invariant for Whnf.strengthen --cs *)
            (* G0, {G}GF[..], Gw |- V'' = V'[iw] : type*)
            (* G0, {G}GF[..] |- V''' = {Gw} V'' : type*)
            (* G0, {G}GF[..], G[..] |- S''' : {Gw} V''[..] > V''[..] *)
            (* G0, {G}GF[..], G |- s : G0, G, GF *))
      | (k, Gorig, All (Prim (Dec (name, __V)), __F), w, sc) ->
          let __G = F.listToCtx (ctxSub ((F.ctxToList Gorig), w)) in
          let g = I.ctxLength __G in
          let s = sc (w, k) in
          let __V' = I.EClo (__V, s) in
          let (nw, __S) = weaken2 (__G, (I.targetFam __V), 1) in
          let iw = Whnf.invert nw in
          let Gw = Whnf.strengthen (iw, __G) in
          let V'' = Whnf.normalize (__V', iw) in
          let V''' = Whnf.normalize ((raiseType (Gw, V'')), I.id) in
          let S''' = __S I.Nil in
          let sc' w' k' =
            let s' = sc (w', k') in
            ((I.Dot ((I.Exp (I.Root ((I.BVar ((g + k') - k)), S'''))), s'))
              (* G0, GA |- w' : G0 *)(* G0, GA, G[..] |- s' : G0, G, GF *)
              (* G0, GA, G[..] |- (g+k'-k). S', s' : G0, G, GF, V *)) in
          let __F' =
            raiseFor ((k + 1), Gorig, __F, (I.comp (w, I.shift)), sc') in
          ((F.All ((F.Prim (I.Dec (name, V'''))), __F'))
            (*                val G = F.listToCtx (ctxSub (F.ctxToList Gorig, w))
                  val g = I.ctxLength G
                  val s = sc (w, k)
                                         G0, {G}GF[..], G |- s : G0, G, GF *)
            (* G0, {G}GF[..] |- V' = {G}(V[s]) : type *)
            (* G0, {G}GF[..] |- S' > {G}(V[s]) > V[s] *)
            (* G0, GA |- w' : G0 *)(* G0, GA, G[..] |- s' : G0, G, GF *)
            (* G0, GA, G[..] |- g+k'-k. S', s' : G0, G, GF, V *)
            (* G0, {G}GF[..], G |- s : G0, G, GF *)(* G0, {G}GF[..], G |- V' : type *)
            (* G0, {G}GF[..], G |- nw : G0, {G}GF[..], Gw
                                         Gw < G *)
            (* G0, {G}GF[..], Gw |- iw : G0, {G}GF[..], G *)
            (* Generalize the invariant for Whnf.strengthen --cs *)
            (* G0, {G}GF[..], Gw |- V'' = V'[iw] : type*)
            (* G0, {G}GF[..] |- V''' = {Gw} V'' : type*)
            (* G0, {G}GF[..], G[..] |- S''' : {Gw} V''[..] > V''[..] *)
            (* G0, {G}GF[..], G |- s : G0, G, GF *))
    let rec extend __87__ __88__ =
      match (__87__, __88__) with
      | (__K, nil) -> __K
      | (__K, (__D)::__L) -> extend ((I.Decl (__K, (BV (__D, S.None)))), __L)
    let rec makeFor __89__ __90__ __91__ =
      match (__89__, __90__, __91__) with
      | (__K, w, Head (__G, (__F, s), d)) ->
          let cf =
            collectGlobalSub
              (__G, s, (createEmptyB d), (fun _ -> fun (__K') -> __K')) in
          let k = I.ctxLength __K in
          let __K' = cf ((I.ctxLength __G), __K) in
          let k' = I.ctxLength __K' in
          let (GK, BK) = abstractCtx __K' in
          let _ =
            if !Global.doubleCheck then TypeCheck.typeCheckCtx GK else () in
          let w' = I.comp (w, (I.Shift (k' - k))) in
          let FK = abstractFor (__K', 0, (__F, s)) in
          let _ =
            if !Global.doubleCheck then FunTypeCheck.isFor (GK, FK) else () in
          let (GK1, GK2) = split (GK, (k' - k)) in
          (((GK1, (allClo (GK2, FK))))
            (*        val _ = if !Global.doubleCheck then checkTags (GK, BK) else () *))
      | (__K, w, Block ((__G, t, d, __G2), AF)) ->
          let k = I.ctxLength __K in
          let collect =
            collectGlobalSub
              (__G, t, (createEmptyB d), (fun _ -> fun (__K') -> __K')) in
          let __K' = collect ((I.ctxLength __G), __K) in
          let k' = I.ctxLength __K' in
          let K'' = extend (__K', __G2) in
          let w' =
            F.dot1n ((F.listToCtx __G2), (I.comp (w, (I.Shift (k' - k))))) in
          let (GK, __F') = makeFor (K'', w', AF) in
          let _ =
            if !Global.doubleCheck then FunTypeCheck.isFor (GK, __F') else () in
          let (GK1, GK2) = split (GK, (List.length __G2)) in
          let F'' =
            raiseFor
              (0, GK2, __F', I.id, (fun w -> fun _ -> F.dot1n (GK2, w))) in
          let _ =
            if !Global.doubleCheck then FunTypeCheck.isFor (GK1, F'') else () in
          let (GK11, GK12) = split (GK1, (k' - k)) in
          let F''' = allClo (GK12, F'') in
          let _ =
            if !Global.doubleCheck
            then FunTypeCheck.isFor (GK11, F''')
            else () in
          (((GK11, F'''))(* BUG *))
    let rec abstractApproxFor =
      function
      | Head (__G, _, _) as AF ->
          let (_, __F) = makeFor ((convert __G), I.id, AF) in __F
      | Block ((__G, _, _, _), _) as AF ->
          let (_, __F) = makeFor ((convert __G), I.id, AF) in __F
    let weaken = weaken
    let raiseType = raiseType
    let abstractSub = abstractSubAll
    let abstractSub' = abstractNew
    let abstractApproxFor = abstractApproxFor
  end ;;
