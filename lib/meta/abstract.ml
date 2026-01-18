
(* Meta Theorem Prover abstraction : Version 1.3 *)
(* Author: Frank Pfenning, Carsten Schuermann *)
module type MTPABSTRACT  =
  sig
    (*! structure IntSyn : INTSYN !*)
    (*! structure FunSyn : FUNSYN !*)
    module StateSyn : STATESYN
    exception Error of string 
    type __ApproxFor =
      | Head of (IntSyn.dctx * (FunSyn.__For * IntSyn.__Sub) * int) 
      | Block of ((IntSyn.dctx * IntSyn.__Sub * int * IntSyn.__Dec list) *
      __ApproxFor) 
    (*  | (t, G2), AF *)
    val weaken : (IntSyn.dctx * IntSyn.cid) -> IntSyn.__Sub
    val raiseType : (IntSyn.dctx * IntSyn.__Exp) -> IntSyn.__Exp
    val abstractSub :
      (IntSyn.__Sub * StateSyn.__Tag IntSyn.__Ctx * (IntSyn.dctx *
        StateSyn.__Tag IntSyn.__Ctx) * IntSyn.__Sub * StateSyn.__Tag
        IntSyn.__Ctx) ->
        ((IntSyn.dctx * StateSyn.__Tag IntSyn.__Ctx) * IntSyn.__Sub)
    val abstractSub' :
      ((IntSyn.dctx * StateSyn.__Tag IntSyn.__Ctx) * IntSyn.__Sub *
        StateSyn.__Tag IntSyn.__Ctx) ->
        ((IntSyn.dctx * StateSyn.__Tag IntSyn.__Ctx) * IntSyn.__Sub)
    val abstractApproxFor : __ApproxFor -> FunSyn.__For
  end;;




(* Meta Theorem Prover abstraction : Version 1.3 *)
(* Author: Frank Pfenning, Carsten Schuermann *)
module MTPAbstract(MTPAbstract:sig
                                 (*! structure IntSyn' : INTSYN !*)
                                 (*! structure FunSyn' : FUNSYN !*)
                                 (*! sharing FunSyn'.IntSyn = IntSyn' !*)
                                 module StateSyn' : STATESYN
                                 module Whnf : WHNF
                                 module Constraints : CONSTRAINTS
                                 module Unify : UNIFY
                                 module Subordinate : SUBORDINATE
                                 module TypeCheck : TYPECHECK
                                 module FunTypeCheck : FUNTYPECHECK
                                 (*! sharing StateSyn'.FunSyn = FunSyn' !*)
                                 (*! sharing Whnf.IntSyn = IntSyn' !*)
                                 (*! sharing Constraints.IntSyn = IntSyn' !*)
                                 (*! sharing Unify.IntSyn = IntSyn' !*)
                                 (*! sharing Subordinate.IntSyn = IntSyn' !*)
                                 (*! sharing TypeCheck.IntSyn = IntSyn' !*)
                                 (*! sharing FunTypeCheck.FunSyn = FunSyn' !*)
                                 module Abstract : ABSTRACT
                               end) : MTPABSTRACT =
  struct
    (*! sharing Abstract.IntSyn = IntSyn' !*)
    (*! structure IntSyn = IntSyn' !*)
    (*! structure FunSyn = FunSyn' !*)
    module StateSyn = StateSyn'
    exception Error of string 
    type __ApproxFor =
      | Head of (IntSyn.dctx * (FunSyn.__For * IntSyn.__Sub) * int) 
      | Block of ((IntSyn.dctx * IntSyn.__Sub * int * IntSyn.__Dec list) *
      __ApproxFor) 
    (*      | (t, G2), AF *)
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
    let rec eqEVar arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (EVar (r1, _, _, _), EV (r2, _, _, _)) -> r1 = r2
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
    let rec occursInHead =
      function
      | (k, BVar k', DP) -> if k = k' then I.Maybe else DP
      | (k, Const _, DP) -> DP
      | (k, Def _, DP) -> DP
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
    let rec weaken =
      function
      | (I.Null, a) -> I.id
      | (Decl (__g', (Dec (name, __v) as __d)), a) ->
          let w' = weaken (__g', a) in
          if Subordinate.belowEq ((I.targetFam __v), a)
          then I.dot1 w'
          else I.comp (w', I.shift)
    let rec raiseType =
      function
      | (I.Null, __v) -> __v
      | (Decl (__g, __d), __v) -> raiseType (__g, (I.Pi ((__d, I.Maybe), __v)))
    let rec restore =
      function
      | (0, Gp) -> (Gp, I.Null)
      | (n, Decl (__g, __d)) ->
          let (Gp', GX') = restore ((n - 1), __g) in (Gp', (I.Decl (GX', __d)))
    let rec concat =
      function
      | (Gp, I.Null) -> Gp
      | (Gp, Decl (__g, __d)) -> I.Decl ((concat (Gp, __g)), __d)
    let rec collectExpW =
      function
      | (T, d, __g, (Uni (__l), s), K) -> K
      | (T, d, __g, (Pi ((__d, _), __v), s), K) ->
          collectExp
            (T, d, (I.Decl (__g, (I.decSub (__d, s)))), (__v, (I.dot1 s)),
              (collectDec (T, d, __g, (__d, s), K)))
      | (T, d, __g, (Root (_, S), s), K) ->
          collectSpine ((S.decrease T), d, __g, (S, s), K)
      | (T, d, __g, (Lam (__d, __u), s), K) ->
          collectExp
            (T, d, (I.Decl (__g, (I.decSub (__d, s)))), (__u, (I.dot1 s)),
              (collectDec (T, d, __g, (__d, s), K)))
      | (T, d, __g, ((EVar (r, GdX, __v, cnstrs) as x), s), K) ->
          if exists (eqEVar x) K
          then collectSub (T, d, __g, s, K)
          else
            (let (Gp, GX) = restore (((I.ctxLength GdX) - d), GdX) in
             let _ = checkEmpty (!cnstrs) in
             let w = weaken (GX, (I.targetFam __v)) in
             let iw = Whnf.invert w in
             let GX' = Whnf.strengthen (iw, GX) in
             let EVar (r', _, _, _) as x' =
               I.newEVar ((concat (Gp, GX')), (I.EClo (__v, iw))) in
             let _ = Unify.instantiateEVar (r, (I.EClo (x', w)), nil) in
             let __v' = raiseType (GX', (I.EClo (__v, iw))) in
             collectSub
               (T, d, __g, (I.comp (w, s)),
                 (I.Decl
                    ((collectExp (T, d, Gp, (__v', I.id), K)),
                      (EV (r', __v', T, d))))))
      | (T, d, __g, (FgnExp csfe, s), K) ->
          I.FgnExpStd.fold csfe
            (function | (__u, K') -> collectExp (T, d, __g, (__u, s), K')) K
    let rec collectExp (T, d, __g, __Us, K) =
      collectExpW (T, d, __g, (Whnf.whnf __Us), K)
    let rec collectSpine =
      function
      | (T, d, __g, (I.Nil, _), K) -> K
      | (T, d, __g, (SClo (S, s'), s), K) ->
          collectSpine (T, d, __g, (S, (I.comp (s', s))), K)
      | (T, d, __g, (App (__u, S), s), K) ->
          collectSpine (T, d, __g, (S, s), (collectExp (T, d, __g, (__u, s), K)))
    let rec collectDec (T, d, __g, (Dec (_, __v), s), K) =
      collectExp (T, d, __g, (__v, s), K)
    let rec collectSub =
      function
      | (T, d, __g, Shift _, K) -> K
      | (T, d, __g, Dot (Idx _, s), K) -> collectSub (T, d, __g, s, K)
      | (T, d, __g, Dot (Exp (__u), s), K) ->
          collectSub (T, d, __g, s, (collectExp (T, d, __g, (__u, I.id), K)))
    let rec abstractEVar =
      function
      | (Decl (K', EV (r', _, _, d)), depth, (EVar (r, _, _, _) as x)) ->
          if r = r'
          then ((I.BVar (depth + 1)), d)
          else abstractEVar (K', (depth + 1), x)
      | (Decl (K', BV _), depth, x) -> abstractEVar (K', (depth + 1), x)
    let rec lookupBV (K, i) =
      let rec lookupBV' =
        function
        | (Decl (K, EV (r, __v, _, _)), i, k) -> lookupBV' (K, i, (k + 1))
        | (Decl (K, BV _), 1, k) -> k
        | (Decl (K, BV _), i, k) -> lookupBV' (K, (i - 1), (k + 1)) in
      lookupBV' (K, i, 1)
    let rec abstractExpW =
      function
      | (K, depth, ((Uni (__l) as __u), s)) -> __u
      | (K, depth, (Pi ((__d, P), __v), s)) ->
          piDepend
            (((abstractDec (K, depth, (__d, s))), P),
              (abstractExp (K, (depth + 1), (__v, (I.dot1 s)))))
      | (K, depth, (Root ((BVar k as H), S), s)) ->
          if k > depth
          then
            let k' = lookupBV (K, (k - depth)) in
            I.Root
              ((I.BVar (k' + depth)), (abstractSpine (K, depth, (S, s))))
          else I.Root (H, (abstractSpine (K, depth, (S, s))))
      | (K, depth, (Root (H, S), s)) ->
          I.Root (H, (abstractSpine (K, depth, (S, s))))
      | (K, depth, (Lam (__d, __u), s)) ->
          I.Lam
            ((abstractDec (K, depth, (__d, s))),
              (abstractExp (K, (depth + 1), (__u, (I.dot1 s)))))
      | (K, depth, ((EVar (_, __g, _, _) as x), s)) ->
          let (H, d) = abstractEVar (K, depth, x) in
          I.Root
            (H, (abstractSub (((I.ctxLength __g) - d), K, depth, s, I.Nil)))
      | (K, depth, (FgnExp csfe, s)) ->
          I.FgnExpStd.Map.apply csfe
            (function | __u -> abstractExp (K, depth, (__u, s)))
    let rec abstractExp (K, depth, __Us) =
      abstractExpW (K, depth, (Whnf.whnf __Us))
    let rec abstractSub =
      function
      | (n, K, depth, Shift k, S) ->
          if n > 0
          then
            abstractSub
              (n, K, depth, (I.Dot ((I.Idx (k + 1)), (I.Shift (k + 1)))), S)
          else S
      | (n, K, depth, Dot (Idx k, s), S) ->
          let H =
            if k > depth
            then let k' = lookupBV (K, (k - depth)) in I.BVar (k' + depth)
            else I.BVar k in
          abstractSub
            ((n - 1), K, depth, s, (I.App ((I.Root (H, I.Nil)), S)))
      | (n, K, depth, Dot (Exp (__u), s), S) ->
          abstractSub
            ((n - 1), K, depth, s,
              (I.App ((abstractExp (K, depth, (__u, I.id))), S)))
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
    let rec getLevel =
      function
      | Uni _ -> I.Kind
      | Pi (_, __u) -> getLevel __u
      | Root _ -> I.Type
      | Redex (__u, _) -> getLevel __u
      | Lam (_, __u) -> getLevel __u
      | EClo (__u, _) -> getLevel __u
    let rec checkType (__v) =
      match getLevel __v with
      | I.Type -> ()
      | _ -> raise (Error "Typing ambiguous -- free type variable")
    let rec abstractCtx =
      function
      | I.Null -> (I.Null, I.Null)
      | Decl (K', EV (_, __v', (Lemma b as T), _)) ->
          let __v'' = abstractExp (K', 0, (__v', I.id)) in
          let _ = checkType __v'' in
          let (__g', B') = abstractCtx K' in
          let __d' = I.Dec (None, __v'') in ((I.Decl (__g', __d')), (I.Decl (B', T)))
      | Decl (K', EV (_, __v', (S.None as T), _)) ->
          let __v'' = abstractExp (K', 0, (__v', I.id)) in
          let _ = checkType __v'' in
          let (__g', B') = abstractCtx K' in
          let __d' = I.Dec (None, __v'') in
          ((I.Decl (__g', __d')), (I.Decl (B', S.None)))
      | Decl (K', BV (__d, T)) ->
          let __d' = abstractDec (K', 0, (__d, I.id)) in
          let (__g', B') = abstractCtx K' in
          ((I.Decl (__g', __d')), (I.Decl (B', T)))
    let rec abstractGlobalSub =
      function
      | (K, Shift _, I.Null) -> I.Shift (I.ctxLength K)
      | (K, Shift n, (Decl _ as B)) ->
          abstractGlobalSub
            (K, (I.Dot ((I.Idx (n + 1)), (I.Shift (n + 1)))), B)
      | (K, Dot (Idx k, s'), Decl (B, (Parameter _ as T))) ->
          I.Dot ((I.Idx (lookupBV (K, k))), (abstractGlobalSub (K, s', B)))
      | (K, Dot (Exp (__u), s'), Decl (B, (Lemma _ as T))) ->
          I.Dot
            ((I.Exp (abstractExp (K, 0, (__u, I.id)))),
              (abstractGlobalSub (K, s', B)))
    let rec collectGlobalSub =
      function
      | (G0, Shift _, I.Null, collect) -> collect
      | (G0, s, (Decl (_, Parameter (Some l)) as B), collect) ->
          let LabelDec (name, _, G2) = F.labelLookup l in
          skip (G0, (List.length G2), s, B, collect)
      | (G0, Dot (Exp (__u), s), Decl (B, T), collect) ->
          collectGlobalSub
            (G0, s, B,
              (function
               | (d, K) -> collect (d, (collectExp (T, d, G0, (__u, I.id), K)))))
    let rec skip =
      function
      | (G0, 0, s, B, collect) -> collectGlobalSub (G0, s, B, collect)
      | (Decl (G0, __d), n, s, Decl (B, (Parameter _ as T)), collect) ->
          skip
            (G0, (n - 1), (I.invDot1 s), B,
              (function
               | (d, K) -> collect ((d + 1), (I.Decl (K, (BV (__d, T)))))))
    let rec abstractNew ((G0, B0), s, B) =
      let cf = collectGlobalSub (G0, s, B, (function | (_, K') -> K')) in
      let K = cf (0, I.Null) in
      ((abstractCtx K), (abstractGlobalSub (K, s, B)))
    let rec abstractSubAll (t, B1, (G0, B0), s, B) =
      let rec skip'' =
        function
        | (K, (I.Null, I.Null)) -> K
        | (K, (Decl (G0, __d), Decl (B0, T))) ->
            I.Decl ((skip'' (K, (G0, B0))), (BV (__d, T))) in
      let collect2 = collectGlobalSub (G0, s, B, (function | (_, K') -> K')) in
      let collect0 =
        collectGlobalSub (I.Null, t, B1, (function | (_, K') -> K')) in
      let K0 = collect0 (0, I.Null) in
      let K1 = skip'' (K0, (G0, B0)) in
      let d = I.ctxLength G0 in
      let K = collect2 (d, K1) in
      ((abstractCtx K), (abstractGlobalSub (K, s, B)))
    let rec abstractFor =
      function
      | (K, depth, (All (Prim (__d), F), s)) ->
          F.All
            ((F.Prim (abstractDec (K, depth, (__d, s)))),
              (abstractFor (K, (depth + 1), (F, (I.dot1 s)))))
      | (K, depth, (Ex (__d, F), s)) ->
          F.Ex
            ((abstractDec (K, depth, (__d, s))),
              (abstractFor (K, (depth + 1), (F, (I.dot1 s)))))
      | (K, depth, (F.True, s)) -> F.True
      | (K, depth, (And (__F1, __F2), s)) ->
          F.And
            ((abstractFor (K, depth, (__F1, s))),
              (abstractFor (K, depth, (__F2, s))))
    let rec allClo =
      function
      | (I.Null, F) -> F
      | (Decl (Gx, __d), F) -> allClo (Gx, (F.All ((F.Prim __d), F)))
    let rec convert =
      function
      | I.Null -> I.Null
      | Decl (__g, __d) -> I.Decl ((convert __g), (BV (__d, (S.Parameter None))))
    let rec createEmptyB =
      function | 0 -> I.Null | n -> I.Decl ((createEmptyB (n - 1)), S.None)
    let rec lower =
      function
      | (_, 0) -> I.Null
      | (Decl (__g, __d), n) -> I.Decl ((lower (__g, (n - 1))), __d)
    let rec split =
      function
      | (__g, 0) -> (__g, I.Null)
      | (Decl (__g, __d), n) ->
          let (G1, G2) = split (__g, (n - 1)) in (G1, (I.Decl (G2, __d)))
    let rec shift =
      function | I.Null -> I.shift | Decl (__g, _) -> I.dot1 (shift __g)
    let rec ctxSub =
      function
      | (nil, s) -> nil
      | ((__d)::__g, s) -> (::) (I.decSub (__d, s)) ctxSub (__g, (I.dot1 s))
    let rec weaken2 =
      function
      | (I.Null, a, i) -> (I.id, ((function | S -> S)))
      | (Decl (__g', (Dec (name, __v) as __d)), a, i) ->
          let (w', S') = weaken2 (__g', a, (i + 1)) in
          if Subordinate.belowEq ((I.targetFam __v), a)
          then
            ((I.dot1 w'),
              ((function | S -> I.App ((I.Root ((I.BVar i), I.Nil)), S))))
          else ((I.comp (w', I.shift)), S')
    let rec raiseType =
      function
      | (I.Null, __v) -> __v
      | (Decl (__g, __d), __v) ->
          raiseType
            (__g,
              (Abstract.piDepend
                 (((Whnf.normalizeDec (__d, I.id)), I.Maybe), __v)))
    let rec raiseFor =
      function
      | (k, Gorig, (F.True as F), w, sc) -> F
      | (k, Gorig, Ex (Dec (name, __v), F), w, sc) ->
          let __g = F.listToCtx (ctxSub ((F.ctxToList Gorig), w)) in
          let g = I.ctxLength __g in
          let s = sc (w, k) in
          let __v' = I.EClo (__v, s) in
          let (nw, S) = weaken2 (__g, (I.targetFam __v), 1) in
          let iw = Whnf.invert nw in
          let Gw = Whnf.strengthen (iw, __g) in
          let __v'' = Whnf.normalize (__v', iw) in
          let __v''' = Whnf.normalize ((raiseType (Gw, __v'')), I.id) in
          let S''' = S I.Nil in
          let sc' =
            function
            | (w', k') ->
                let s' = sc (w', k') in
                I.Dot ((I.Exp (I.Root ((I.BVar ((g + k') - k)), S'''))), s') in
          let __F' = raiseFor ((k + 1), Gorig, F, (I.comp (w, I.shift)), sc') in
          F.Ex ((I.Dec (name, __v''')), __F')
      | (k, Gorig, All (Prim (Dec (name, __v)), F), w, sc) ->
          let __g = F.listToCtx (ctxSub ((F.ctxToList Gorig), w)) in
          let g = I.ctxLength __g in
          let s = sc (w, k) in
          let __v' = I.EClo (__v, s) in
          let (nw, S) = weaken2 (__g, (I.targetFam __v), 1) in
          let iw = Whnf.invert nw in
          let Gw = Whnf.strengthen (iw, __g) in
          let __v'' = Whnf.normalize (__v', iw) in
          let __v''' = Whnf.normalize ((raiseType (Gw, __v'')), I.id) in
          let S''' = S I.Nil in
          let sc' =
            function
            | (w', k') ->
                let s' = sc (w', k') in
                I.Dot ((I.Exp (I.Root ((I.BVar ((g + k') - k)), S'''))), s') in
          let __F' = raiseFor ((k + 1), Gorig, F, (I.comp (w, I.shift)), sc') in
          F.All ((F.Prim (I.Dec (name, __v'''))), __F')
    let rec extend =
      function
      | (K, nil) -> K
      | (K, (__d)::__l) -> extend ((I.Decl (K, (BV (__d, S.None)))), __l)
    let rec makeFor =
      function
      | (K, w, Head (__g, (F, s), d)) ->
          let cf =
            collectGlobalSub
              (__g, s, (createEmptyB d), (function | (_, K') -> K')) in
          let k = I.ctxLength K in
          let K' = cf ((I.ctxLength __g), K) in
          let k' = I.ctxLength K' in
          let (GK, BK) = abstractCtx K' in
          let _ =
            if !Global.doubleCheck then TypeCheck.typeCheckCtx GK else () in
          let w' = I.comp (w, (I.Shift (k' - k))) in
          let FK = abstractFor (K', 0, (F, s)) in
          let _ =
            if !Global.doubleCheck then FunTypeCheck.isFor (GK, FK) else () in
          let (GK1, GK2) = split (GK, (k' - k)) in (GK1, (allClo (GK2, FK)))
      | (K, w, Block ((__g, t, d, G2), AF)) ->
          let k = I.ctxLength K in
          let collect =
            collectGlobalSub
              (__g, t, (createEmptyB d), (function | (_, K') -> K')) in
          let K' = collect ((I.ctxLength __g), K) in
          let k' = I.ctxLength K' in
          let K'' = extend (K', G2) in
          let w' =
            F.dot1n ((F.listToCtx G2), (I.comp (w, (I.Shift (k' - k))))) in
          let (GK, __F') = makeFor (K'', w', AF) in
          let _ =
            if !Global.doubleCheck then FunTypeCheck.isFor (GK, __F') else () in
          let (GK1, GK2) = split (GK, (List.length G2)) in
          let __F'' =
            raiseFor
              (0, GK2, __F', I.id, (function | (w, _) -> F.dot1n (GK2, w))) in
          let _ =
            if !Global.doubleCheck then FunTypeCheck.isFor (GK1, __F'') else () in
          let (GK11, GK12) = split (GK1, (k' - k)) in
          let __F''' = allClo (GK12, __F'') in
          let _ =
            if !Global.doubleCheck
            then FunTypeCheck.isFor (GK11, __F''')
            else () in
          (GK11, __F''')
    let rec abstractApproxFor =
      function
      | Head (__g, _, _) as AF ->
          let (_, F) = makeFor ((convert __g), I.id, AF) in F
      | Block ((__g, _, _, _), _) as AF ->
          let (_, F) = makeFor ((convert __g), I.id, AF) in F
    (* Intermediate Data Structure *)
    (* y ::= (x , {G2} __v)  if {G1, G2 |- x : __v
                                          |G1| = d *)
    (*
       We write {{K}} for the context of K, where EVars and BVars have
       been translated to declarations and their occurrences to BVars.
       We write {{__u}}_K, {{S}}_K for the corresponding translation of an
       expression or spine.

       Just like contexts __g, any K is implicitly assumed to be
       well-formed and in dependency order.

       We write  K ||- __u  if all EVars and BVars in __u are collected in K.
       In particular, . ||- __u means __u contains no EVars or BVars.  Similarly,
       for spines K ||- S and other syntactic categories.

       Collection and abstraction raise Error if there are unresolved
       constraints after simplification.
    *)
    (* checkEmpty Cnstr = ()
       raises Error exception if constraints Cnstr cannot be simplified
       to the empty constraint
    *)
    (* eqEVar x y = B
       where B iff x and y represent same variable
    *)
    (* exists P K = B
       where B iff K = K1, y, K2  s.t. P y  holds
    *)
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
    (* weaken (depth,  __g, a) = (w')
    *)
    (* raiseType (__g, __v) = {{__g}} __v

       Invariant:
       If __g |- __v : __l
       then  . |- {{__g}} __v : __l

       All abstractions are potentially dependent.
    *)
    (* collectExpW (T, d, __g, (__u, s), K) = K'

       Invariant:
       If    __g |- s : G1     G1 |- __u : __v      (__u,s) in whnf
       No circularities in __u
             (enforced by extended occurs-check for BVars in Unify)
       and   K' = K, K''
             where K'' contains all EVars and BVars in (__u,s)
    *)
    (* Possible optimization: Calculate also the normal form of the term *)
    (* optimization possible for d = 0 *)
    (* hack - should consult cs    -rv *)
    (* No other cases can occur due to whnf invariant *)
    (* collectExp (T, d, __g, (__u, s), K) = K'

       same as collectExpW  but  (__u,s) need not to be in whnf
    *)
    (* collectSpine (T, d, __g, (S, s), K) = K'

       Invariant:
       If    __g |- s : G1     G1 |- S : __v > P
       then  K' = K, K''
       where K'' contains all EVars and BVars in (S, s)
     *)
    (* collectDec (T, d, __g, (x:__v, s), K) = K'

       Invariant:
       If    __g |- s : G1     G1 |- __v : __l
       then  K' = K, K''
       where K'' contains all EVars and BVars in (__v, s)
    *)
    (* collectSub (T, d, __g, s, K) = K'

       Invariant:
       If    __g |- s : G1
       then  K' = K, K''
       where K'' contains all EVars and BVars in s
    *)
    (* abstractEVar (K, depth, x) = C'

       Invariant:
       If   __g |- x : __v
       and  |__g| = depth
       and  x occurs in K  at kth position (starting at 1)
       then C' = BVar (depth + k)
       and  {{K}}, __g |- C' : __v
    *)
    (* lookupBV (A, i) = k'

       Invariant:

       If   A ||- __v
       and  __g |- __v type
       and  __g [x] A |- i : __v'
       then ex a substititution  __g x A |- s : __g [x] A
       and  __g x A |- k' : __v''
       and  __g x A |- __v' [s] = __v'' : type
    *)
    (* lookupBV' I.Null cannot occur by invariant *)
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
    (* s = id *)
    (* hack - should consult cs   -rv *)
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
    (* n = 0 *)
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
    (* getlevel (__v) = __l if __g |- __v : __l

       Invariant: __g |- __v : __l' for some __l'
    *)
    (* checkType (__v) = () if __g |- __v : type

       Invariant: __g |- __v : __l' for some __l'
    *)
    (* abstractCtx (K, __v) = __v'
       where __v' = {{K}} __v

       Invariant:
       If   {{K}} |- __v : __l
       and  . ||- __v

       then __v' = {{K}} __v
       and  . |- __v' : __l
       and  . ||- __v'
    *)
    (* abstractGlobalSub (K, s, B) = s'

       Invariant:
       If   K > __g   aux context
       and  __g |- s : __g'
       then K |- s' : __g'
    *)
    (* collectGlobalSub (G0, s, B, collect) = collect'

       Invariant:
       If   |- G0 ctx
       and  |- __g ctx
       and  __g |- B tags
       and  G0 |- s : __g
       and  collect is a function which maps
               (d, K)  (d expresses the number of parameters in K, |- K aux ctx)
            to K'      (|- K' aux ctx, which collects all EVars in K)
    *)
    (* no cases for (G0, s, B as I.Decl (_, S.Parameter None), collect) *)
    (* abstractNew ((G0, B0), s, B) = ((__g', B'), s')

       Invariant:
       If   . |- G0 ctx
       and  G0 |- B0 tags
       and  G0 |- s : __g
       and  __g |- B tags
       then . |- __g' = G1, Gp, G2
       and  __g' |- B' tags
       and  __g' |- s' : __g
    *)
    (* abstractSub (t, B1, (G0, B0), s, B) = ((__g', B'), s')

       Invariant:
       If   . |- t : G1
       and  G1 |- B1 tags

       and  G0 |- B0 tags
       and  G0 |- s : __g
       and  __g |- B tags
       then . |- __g' = G1, G0, G2
       and  B' |- __g' tags
       and  __g' |- s' : __g
    *)
    (* skip'' (K, (__g, B)) = K'

             Invariant:
             If   __g = x1:V1 .. xn:Vn
             and  __g |- B = <param> ... <param> tags
             then  K' = K, BV (x1) .. BV (xn)
          *)
    (* abstractFor (K, depth, (F, s)) = __F'
       __F' = {{F[s]}}_K

       Invariant:
       If    __g |- s : G1     G1 |- __u : __v    (__u,s) is in whnf
       and   K is internal context in dependency order
       and   |__g| = depth
       and   K ||- __u and K ||- __v
       then  {{K}}, __g |- __u' : __v'
       and   . ||- __u' and . ||- __v'
       and   __u' is in nf
    *)
    (* abstract (Gx, F) = __F'

       Invariant:
       If   __g, Gx |- F formula
       then __g |- __F' = {{Gx}} F formula
    *)
    (* shift __g = s'

       Invariant:
       Forall contexts G0:
       If   |- G0, __g ctx
       then G0, __v, __g |- s' : G0, __g
    *)
    (* ctxSub (__g, s) = __g'

       Invariant:
       If   G2 |- s : G1
       and  G1 |- __g ctx
       then G2 |- __g' = __g[s] ctx
    *)
    (* weaken2 (__g, a, i, S) = w'

       Invariant:
       __g |- w' : Gw
       Gw < __g
       __g |- S : {Gw} __v > __v
    *)
    (* raiseType (__g, __v) = {{__g}} __v

       Invariant:
       If __g |- __v : __l
       then  . |- {{__g}} __v : __l

       All abstractions are potentially dependent.
    *)
    (* raiseFor (__g, F, w, sc) = __F'

       Invariant:
       If   G0 |- __g ctx
       and  G0, __g, GF |- F for
       and  G0, {__g} GF [...] |- w : G0
       and  sc maps  (G0, GA |- w : G0, |GA|)  to   (G0, GA, __g[..] |- s : G0, __g, GF)
       then G0, {__g} GF |- __F' for
    *)
    (* G0, {__g}GF[..], __g |- s : G0, __g, GF *)
    (* G0, {__g}GF[..], __g |- __v' : type *)
    (* G0, {__g}GF[..], __g |- nw : G0, {__g}GF[..], Gw
                                         Gw < __g *)
    (* G0, {__g}GF[..], Gw |- iw : G0, {__g}GF[..], __g *)
    (* Generalize the invariant for Whnf.strengthen --cs *)
    (* G0, {__g}GF[..], Gw |- __v'' = __v'[iw] : type*)
    (* G0, {__g}GF[..] |- __v''' = {Gw} __v'' : type*)
    (* G0, {__g}GF[..], __g[..] |- S''' : {Gw} __v''[..] > __v''[..] *)
    (* G0, {__g}GF[..], __g |- s : G0, __g, GF *)
    (* G0, GA |- w' : G0 *)
    (* G0, GA, __g[..] |- s' : G0, __g, GF *)
    (* G0, GA, __g[..] |- (g+k'-k). S', s' : G0, __g, GF, __v *)
    (*                val __g = F.listToCtx (ctxSub (F.ctxToList Gorig, w))
                  val g = I.ctxLength __g
                  val s = sc (w, k)
                                         G0, {__g}GF[..], __g |- s : G0, __g, GF *)
    (* G0, {__g}GF[..] |- __v' = {__g}(__v[s]) : type *)
    (* G0, {__g}GF[..] |- S' > {__g}(__v[s]) > __v[s] *)
    (* G0, GA |- w' : G0 *)
    (* G0, GA, __g[..] |- s' : G0, __g, GF *)
    (* G0, GA, __g[..] |- g+k'-k. S', s' : G0, __g, GF, __v *)
    (* G0, {__g}GF[..], __g |- s : G0, __g, GF *)
    (* G0, {__g}GF[..], __g |- __v' : type *)
    (* G0, {__g}GF[..], __g |- nw : G0, {__g}GF[..], Gw
                                         Gw < __g *)
    (* G0, {__g}GF[..], Gw |- iw : G0, {__g}GF[..], __g *)
    (* Generalize the invariant for Whnf.strengthen --cs *)
    (* G0, {__g}GF[..], Gw |- __v'' = __v'[iw] : type*)
    (* G0, {__g}GF[..] |- __v''' = {Gw} __v'' : type*)
    (* G0, {__g}GF[..], __g[..] |- S''' : {Gw} __v''[..] > __v''[..] *)
    (* G0, {__g}GF[..], __g |- s : G0, __g, GF *)
    (* G0, GA |- w' : G0 *)
    (* G0, GA, __g[..] |- s' : G0, __g, GF *)
    (* G0, GA, __g[..] |- (g+k'-k). S', s' : G0, __g, GF, __v *)
    (* the other case of F.All (F.Block _, _) is not yet covered *)
    (* makeFor (__g, w, AF) = __F'

       Invariant :
       If   |- __g ctx
       and  __g |- w : __g'
       and  __g' |- AF approx for
       then __g'; . |- __F' = {EVARS} AF  for
    *)
    (*        val _ = if !Global.doubleCheck then checkTags (GK, BK) else () *)
    (* BUG *)
    let weaken = weaken
    let raiseType = raiseType
    let abstractSub = abstractSubAll
    let abstractSub' = abstractNew
    let abstractApproxFor = abstractApproxFor
  end ;;
