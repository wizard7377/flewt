
module type MTPABSTRACT  =
  sig
    module StateSyn :
    ((STATESYN)(* Meta Theorem Prover abstraction : Version 1.3 *)
    (* Author: Frank Pfenning, Carsten Schuermann *)
    (*! structure IntSyn : INTSYN !*)(*! structure FunSyn : FUNSYN !*))
    exception Error of string 
    type __ApproxFor =
      | Head of (((IntSyn.dctx)(* Approximat formula *)) *
      (FunSyn.__For * IntSyn.__Sub) * int) 
      | Block of ((((IntSyn.dctx)(* AF ::= F [s] *)) *
      IntSyn.__Sub * int * IntSyn.__Dec list) * __ApproxFor) 
    val weaken :
      (IntSyn.dctx * IntSyn.cid) ->
        ((IntSyn.__Sub)(*  | (t, G2), AF *))
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




module MTPAbstract(MTPAbstract:sig
                                 module StateSyn' : STATESYN
                                 module Whnf : WHNF
                                 module Constraints : CONSTRAINTS
                                 module Unify : UNIFY
                                 module Subordinate : SUBORDINATE
                                 module TypeCheck : TYPECHECK
                                 module FunTypeCheck : FUNTYPECHECK
                                 module Abstract :
                                 ((ABSTRACT)(* Meta Theorem Prover abstraction : Version 1.3 *)
                                 (* Author: Frank Pfenning, Carsten Schuermann *)
                                 (*! structure IntSyn' : INTSYN !*)
                                 (*! structure FunSyn' : FUNSYN !*)
                                 (*! sharing FunSyn'.IntSyn = IntSyn' !*)
                                 (*! sharing StateSyn'.FunSyn = FunSyn' !*)
                                 (*! sharing Whnf.IntSyn = IntSyn' !*)
                                 (*! sharing Constraints.IntSyn = IntSyn' !*)
                                 (*! sharing Unify.IntSyn = IntSyn' !*)
                                 (*! sharing Subordinate.IntSyn = IntSyn' !*)
                                 (*! sharing TypeCheck.IntSyn = IntSyn' !*)
                                 (*! sharing FunTypeCheck.FunSyn = FunSyn' !*))
                               end) : MTPABSTRACT =
  struct
    module StateSyn =
      ((StateSyn')(*! sharing Abstract.IntSyn = IntSyn' !*)
      (*! structure IntSyn = IntSyn' !*)(*! structure FunSyn = FunSyn' !*))
    exception Error of string 
    type __ApproxFor =
      | Head of (((IntSyn.dctx)(* Approximat formula *)) *
      (FunSyn.__For * IntSyn.__Sub) * int) 
      | Block of ((((IntSyn.dctx)(* AF ::= F [s] *)) *
      IntSyn.__Sub * int * IntSyn.__Dec list) * __ApproxFor) 
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
      | (k, App (U, S)) ->
          or__ ((occursInExp (k, U)), (occursInSpine (k, S)))
    let rec occursInDec (k, Dec (_, V)) = occursInExp (k, V)
    let rec occursInDecP (k, (D, _)) = occursInDec (k, D)
    let rec piDepend =
      function
      | ((D, I.No), V) as DPV -> I.Pi DPV
      | ((D, I.Meta), V) as DPV -> I.Pi DPV
      | ((D, I.Maybe), V) -> I.Pi ((D, (occursInExp (1, V))), V)
    let rec weaken =
      function
      | (I.Null, a) -> I.id
      | (Decl (g', (Dec (name, V) as D)), a) ->
          let w' = weaken (g', a) in
          if Subordinate.belowEq ((I.targetFam V), a)
          then I.dot1 w'
          else I.comp (w', I.shift)
    let rec raiseType =
      function
      | (I.Null, V) -> V
      | (Decl (g, D), V) -> raiseType (g, (I.Pi ((D, I.Maybe), V)))
    let rec restore =
      function
      | (0, Gp) -> (Gp, I.Null)
      | (n, Decl (g, D)) ->
          let (Gp', GX') = restore ((n - 1), g) in (Gp', (I.Decl (GX', D)))
    let rec concat =
      function
      | (Gp, I.Null) -> Gp
      | (Gp, Decl (g, D)) -> I.Decl ((concat (Gp, g)), D)
    let rec collectExpW =
      function
      | (T, d, g, (Uni (L), s), K) -> K
      | (T, d, g, (Pi ((D, _), V), s), K) ->
          collectExp
            (T, d, (I.Decl (g, (I.decSub (D, s)))), (V, (I.dot1 s)),
              (collectDec (T, d, g, (D, s), K)))
      | (T, d, g, (Root (_, S), s), K) ->
          collectSpine ((S.decrease T), d, g, (S, s), K)
      | (T, d, g, (Lam (D, U), s), K) ->
          collectExp
            (T, d, (I.Decl (g, (I.decSub (D, s)))), (U, (I.dot1 s)),
              (collectDec (T, d, g, (D, s), K)))
      | (T, d, g, ((EVar (r, GdX, V, cnstrs) as X), s), K) ->
          if exists (eqEVar X) K
          then collectSub (T, d, g, s, K)
          else
            (let (Gp, GX) = restore (((I.ctxLength GdX) - d), GdX) in
             let _ = checkEmpty (!cnstrs) in
             let w = weaken (GX, (I.targetFam V)) in
             let iw = Whnf.invert w in
             let GX' = Whnf.strengthen (iw, GX) in
             let EVar (r', _, _, _) as X' =
               I.newEVar ((concat (Gp, GX')), (I.EClo (V, iw))) in
             let _ = Unify.instantiateEVar (r, (I.EClo (X', w)), nil) in
             let V' = raiseType (GX', (I.EClo (V, iw))) in
             collectSub
               (T, d, g, (I.comp (w, s)),
                 (I.Decl
                    ((collectExp (T, d, Gp, (V', I.id), K)),
                      (EV (r', V', T, d))))))
      | (T, d, g, (FgnExp csfe, s), K) ->
          I.FgnExpStd.fold csfe
            (function | (U, K') -> collectExp (T, d, g, (U, s), K')) K
    let rec collectExp (T, d, g, Us, K) =
      collectExpW (T, d, g, (Whnf.whnf Us), K)
    let rec collectSpine =
      function
      | (T, d, g, (I.Nil, _), K) -> K
      | (T, d, g, (SClo (S, s'), s), K) ->
          collectSpine (T, d, g, (S, (I.comp (s', s))), K)
      | (T, d, g, (App (U, S), s), K) ->
          collectSpine (T, d, g, (S, s), (collectExp (T, d, g, (U, s), K)))
    let rec collectDec (T, d, g, (Dec (_, V), s), K) =
      collectExp (T, d, g, (V, s), K)
    let rec collectSub =
      function
      | (T, d, g, Shift _, K) -> K
      | (T, d, g, Dot (Idx _, s), K) -> collectSub (T, d, g, s, K)
      | (T, d, g, Dot (Exp (U), s), K) ->
          collectSub (T, d, g, s, (collectExp (T, d, g, (U, I.id), K)))
    let rec abstractEVar =
      function
      | (Decl (K', EV (r', _, _, d)), depth, (EVar (r, _, _, _) as X)) ->
          if r = r'
          then ((I.BVar (depth + 1)), d)
          else abstractEVar (K', (depth + 1), X)
      | (Decl (K', BV _), depth, X) -> abstractEVar (K', (depth + 1), X)
    let rec lookupBV (K, i) =
      let lookupBV' =
        function
        | (Decl (K, EV (r, V, _, _)), i, k) -> lookupBV' (K, i, (k + 1))
        | (Decl (K, BV _), 1, k) -> k
        | (Decl (K, BV _), i, k) -> lookupBV' (K, (i - 1), (k + 1)) in
      lookupBV' (K, i, 1)
    let rec abstractExpW =
      function
      | (K, depth, ((Uni (L) as U), s)) -> U
      | (K, depth, (Pi ((D, P), V), s)) ->
          piDepend
            (((abstractDec (K, depth, (D, s))), P),
              (abstractExp (K, (depth + 1), (V, (I.dot1 s)))))
      | (K, depth, (Root ((BVar k as H), S), s)) ->
          if k > depth
          then
            let k' = lookupBV (K, (k - depth)) in
            I.Root
              ((I.BVar (k' + depth)), (abstractSpine (K, depth, (S, s))))
          else I.Root (H, (abstractSpine (K, depth, (S, s))))
      | (K, depth, (Root (H, S), s)) ->
          I.Root (H, (abstractSpine (K, depth, (S, s))))
      | (K, depth, (Lam (D, U), s)) ->
          I.Lam
            ((abstractDec (K, depth, (D, s))),
              (abstractExp (K, (depth + 1), (U, (I.dot1 s)))))
      | (K, depth, ((EVar (_, g, _, _) as X), s)) ->
          let (H, d) = abstractEVar (K, depth, X) in
          I.Root
            (H, (abstractSub (((I.ctxLength g) - d), K, depth, s, I.Nil)))
      | (K, depth, (FgnExp csfe, s)) ->
          I.FgnExpStd.Map.apply csfe
            (function | U -> abstractExp (K, depth, (U, s)))
    let rec abstractExp (K, depth, Us) =
      abstractExpW (K, depth, (Whnf.whnf Us))
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
      | (n, K, depth, Dot (Exp (U), s), S) ->
          abstractSub
            ((n - 1), K, depth, s,
              (I.App ((abstractExp (K, depth, (U, I.id))), S)))
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
    let rec getLevel =
      function
      | Uni _ -> I.Kind
      | Pi (_, U) -> getLevel U
      | Root _ -> I.Type
      | Redex (U, _) -> getLevel U
      | Lam (_, U) -> getLevel U
      | EClo (U, _) -> getLevel U
    let rec checkType (V) =
      match getLevel V with
      | I.Type -> ()
      | _ -> raise (Error "Typing ambiguous -- free type variable")
    let rec abstractCtx =
      function
      | I.Null -> (I.Null, I.Null)
      | Decl (K', EV (_, V', (Lemma b as T), _)) ->
          let V'' = abstractExp (K', 0, (V', I.id)) in
          let _ = checkType V'' in
          let (g', B') = abstractCtx K' in
          let D' = I.Dec (NONE, V'') in ((I.Decl (g', D')), (I.Decl (B', T)))
      | Decl (K', EV (_, V', (S.None as T), _)) ->
          let V'' = abstractExp (K', 0, (V', I.id)) in
          let _ = checkType V'' in
          let (g', B') = abstractCtx K' in
          let D' = I.Dec (NONE, V'') in
          ((I.Decl (g', D')), (I.Decl (B', S.None)))
      | Decl (K', BV (D, T)) ->
          let D' = abstractDec (K', 0, (D, I.id)) in
          let (g', B') = abstractCtx K' in
          ((I.Decl (g', D')), (I.Decl (B', T)))
    let rec abstractGlobalSub =
      function
      | (K, Shift _, I.Null) -> I.Shift (I.ctxLength K)
      | (K, Shift n, (Decl _ as B)) ->
          abstractGlobalSub
            (K, (I.Dot ((I.Idx (n + 1)), (I.Shift (n + 1)))), B)
      | (K, Dot (Idx k, s'), Decl (B, (Parameter _ as T))) ->
          I.Dot ((I.Idx (lookupBV (K, k))), (abstractGlobalSub (K, s', B)))
      | (K, Dot (Exp (U), s'), Decl (B, (Lemma _ as T))) ->
          I.Dot
            ((I.Exp (abstractExp (K, 0, (U, I.id)))),
              (abstractGlobalSub (K, s', B)))
    let rec collectGlobalSub =
      function
      | (G0, Shift _, I.Null, collect) -> collect
      | (G0, s, (Decl (_, Parameter (SOME l)) as B), collect) ->
          let LabelDec (name, _, G2) = F.labelLookup l in
          skip (G0, (List.length G2), s, B, collect)
      | (G0, Dot (Exp (U), s), Decl (B, T), collect) ->
          collectGlobalSub
            (G0, s, B,
              (function
               | (d, K) -> collect (d, (collectExp (T, d, G0, (U, I.id), K)))))
    let rec skip =
      function
      | (G0, 0, s, B, collect) -> collectGlobalSub (G0, s, B, collect)
      | (Decl (G0, D), n, s, Decl (B, (Parameter _ as T)), collect) ->
          skip
            (G0, (n - 1), (I.invDot1 s), B,
              (function
               | (d, K) -> collect ((d + 1), (I.Decl (K, (BV (D, T)))))))
    let rec abstractNew ((G0, B0), s, B) =
      let cf = collectGlobalSub (G0, s, B, (function | (_, K') -> K')) in
      let K = cf (0, I.Null) in
      ((abstractCtx K), (abstractGlobalSub (K, s, B)))
    let rec abstractSubAll (t, B1, (G0, B0), s, B) =
      let skip'' =
        function
        | (K, (I.Null, I.Null)) -> K
        | (K, (Decl (G0, D), Decl (B0, T))) ->
            I.Decl ((skip'' (K, (G0, B0))), (BV (D, T))) in
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
      | (K, depth, (All (Prim (D), F), s)) ->
          F.All
            ((F.Prim (abstractDec (K, depth, (D, s)))),
              (abstractFor (K, (depth + 1), (F, (I.dot1 s)))))
      | (K, depth, (Ex (D, F), s)) ->
          F.Ex
            ((abstractDec (K, depth, (D, s))),
              (abstractFor (K, (depth + 1), (F, (I.dot1 s)))))
      | (K, depth, (F.True, s)) -> F.True
      | (K, depth, (And (F1, F2), s)) ->
          F.And
            ((abstractFor (K, depth, (F1, s))),
              (abstractFor (K, depth, (F2, s))))
    let rec allClo =
      function
      | (I.Null, F) -> F
      | (Decl (Gx, D), F) -> allClo (Gx, (F.All ((F.Prim D), F)))
    let rec convert =
      function
      | I.Null -> I.Null
      | Decl (g, D) -> I.Decl ((convert g), (BV (D, (S.Parameter NONE))))
    let rec createEmptyB =
      function | 0 -> I.Null | n -> I.Decl ((createEmptyB (n - 1)), S.None)
    let rec lower =
      function
      | (_, 0) -> I.Null
      | (Decl (g, D), n) -> I.Decl ((lower (g, (n - 1))), D)
    let rec split =
      function
      | (g, 0) -> (g, I.Null)
      | (Decl (g, D), n) ->
          let (G1, G2) = split (g, (n - 1)) in (G1, (I.Decl (G2, D)))
    let rec shift =
      function | I.Null -> I.shift | Decl (g, _) -> I.dot1 (shift g)
    let rec ctxSub =
      function
      | (nil, s) -> nil
      | ((D)::g, s) -> (::) (I.decSub (D, s)) ctxSub (g, (I.dot1 s))
    let rec weaken2 =
      function
      | (I.Null, a, i) -> (I.id, ((function | S -> S)))
      | (Decl (g', (Dec (name, V) as D)), a, i) ->
          let (w', S') = weaken2 (g', a, (i + 1)) in
          if Subordinate.belowEq ((I.targetFam V), a)
          then
            ((I.dot1 w'),
              ((function | S -> I.App ((I.Root ((I.BVar i), I.Nil)), S))))
          else ((I.comp (w', I.shift)), S')
    let rec raiseType =
      function
      | (I.Null, V) -> V
      | (Decl (g, D), V) ->
          raiseType
            (g,
              (Abstract.piDepend
                 (((Whnf.normalizeDec (D, I.id)), I.Maybe), V)))
    let rec raiseFor =
      function
      | (k, Gorig, (F.True as F), w, sc) -> F
      | (k, Gorig, Ex (Dec (name, V), F), w, sc) ->
          let g = F.listToCtx (ctxSub ((F.ctxToList Gorig), w)) in
          let g = I.ctxLength g in
          let s = sc (w, k) in
          let V' = I.EClo (V, s) in
          let (nw, S) = weaken2 (g, (I.targetFam V), 1) in
          let iw = Whnf.invert nw in
          let Gw = Whnf.strengthen (iw, g) in
          let V'' = Whnf.normalize (V', iw) in
          let V''' = Whnf.normalize ((raiseType (Gw, V'')), I.id) in
          let S''' = S I.Nil in
          let sc' =
            function
            | (w', k') ->
                let s' = sc (w', k') in
                I.Dot ((I.Exp (I.Root ((I.BVar ((g + k') - k)), S'''))), s') in
          let F' = raiseFor ((k + 1), Gorig, F, (I.comp (w, I.shift)), sc') in
          F.Ex ((I.Dec (name, V''')), F')
      | (k, Gorig, All (Prim (Dec (name, V)), F), w, sc) ->
          let g = F.listToCtx (ctxSub ((F.ctxToList Gorig), w)) in
          let g = I.ctxLength g in
          let s = sc (w, k) in
          let V' = I.EClo (V, s) in
          let (nw, S) = weaken2 (g, (I.targetFam V), 1) in
          let iw = Whnf.invert nw in
          let Gw = Whnf.strengthen (iw, g) in
          let V'' = Whnf.normalize (V', iw) in
          let V''' = Whnf.normalize ((raiseType (Gw, V'')), I.id) in
          let S''' = S I.Nil in
          let sc' =
            function
            | (w', k') ->
                let s' = sc (w', k') in
                I.Dot ((I.Exp (I.Root ((I.BVar ((g + k') - k)), S'''))), s') in
          let F' = raiseFor ((k + 1), Gorig, F, (I.comp (w, I.shift)), sc') in
          F.All ((F.Prim (I.Dec (name, V'''))), F')
    let rec extend =
      function
      | (K, nil) -> K
      | (K, (D)::L) -> extend ((I.Decl (K, (BV (D, S.None)))), L)
    let rec makeFor =
      function
      | (K, w, Head (g, (F, s), d)) ->
          let cf =
            collectGlobalSub
              (g, s, (createEmptyB d), (function | (_, K') -> K')) in
          let k = I.ctxLength K in
          let K' = cf ((I.ctxLength g), K) in
          let k' = I.ctxLength K' in
          let (GK, BK) = abstractCtx K' in
          let _ =
            if !Global.doubleCheck then TypeCheck.typeCheckCtx GK else () in
          let w' = I.comp (w, (I.Shift (k' - k))) in
          let FK = abstractFor (K', 0, (F, s)) in
          let _ =
            if !Global.doubleCheck then FunTypeCheck.isFor (GK, FK) else () in
          let (GK1, GK2) = split (GK, (k' - k)) in (GK1, (allClo (GK2, FK)))
      | (K, w, Block ((g, t, d, G2), AF)) ->
          let k = I.ctxLength K in
          let collect =
            collectGlobalSub
              (g, t, (createEmptyB d), (function | (_, K') -> K')) in
          let K' = collect ((I.ctxLength g), K) in
          let k' = I.ctxLength K' in
          let K'' = extend (K', G2) in
          let w' =
            F.dot1n ((F.listToCtx G2), (I.comp (w, (I.Shift (k' - k))))) in
          let (GK, F') = makeFor (K'', w', AF) in
          let _ =
            if !Global.doubleCheck then FunTypeCheck.isFor (GK, F') else () in
          let (GK1, GK2) = split (GK, (List.length G2)) in
          let F'' =
            raiseFor
              (0, GK2, F', I.id, (function | (w, _) -> F.dot1n (GK2, w))) in
          let _ =
            if !Global.doubleCheck then FunTypeCheck.isFor (GK1, F'') else () in
          let (GK11, GK12) = split (GK1, (k' - k)) in
          let F''' = allClo (GK12, F'') in
          let _ =
            if !Global.doubleCheck
            then FunTypeCheck.isFor (GK11, F''')
            else () in
          (GK11, F''')
    let rec abstractApproxFor =
      function
      | Head (g, _, _) as AF ->
          let (_, F) = makeFor ((convert g), I.id, AF) in F
      | Block ((g, _, _, _), _) as AF ->
          let (_, F) = makeFor ((convert g), I.id, AF) in F
    let ((weaken)(*      | (t, G2), AF *)(* Intermediate Data Structure *)
      (* y ::= (X , {G2} V)  if {G1, G2 |- X : V
                                          |G1| = d *)
      (*
       We write {{K}} for the context of K, where EVars and BVars have
       been translated to declarations and their occurrences to BVars.
       We write {{U}}_K, {{S}}_K for the corresponding translation of an
       expression or spine.

       Just like contexts g, any K is implicitly assumed to be
       well-formed and in dependency order.

       We write  K ||- U  if all EVars and BVars in U are collected in K.
       In particular, . ||- U means U contains no EVars or BVars.  Similarly,
       for spines K ||- S and other syntactic categories.

       Collection and abstraction raise Error if there are unresolved
       constraints after simplification.
    *)
      (* checkEmpty Cnstr = ()
       raises Error exception if constraints Cnstr cannot be simplified
       to the empty constraint
    *)
      (* eqEVar X Y = B
       where B iff X and Y represent same variable
    *)
      (* exists P K = B
       where B iff K = K1, Y, K2  s.t. P Y  holds
    *)
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
      (* weaken (depth,  g, a) = (w')
    *)(* raiseType (g, V) = {{g}} V

       Invariant:
       If g |- V : L
       then  . |- {{g}} V : L

       All abstractions are potentially dependent.
    *)
      (* collectExpW (T, d, g, (U, s), K) = K'

       Invariant:
       If    g |- s : G1     G1 |- U : V      (U,s) in whnf
       No circularities in U
             (enforced by extended occurs-check for BVars in Unify)
       and   K' = K, K''
             where K'' contains all EVars and BVars in (U,s)
    *)
      (* Possible optimization: Calculate also the normal form of the term *)
      (* optimization possible for d = 0 *)(* hack - should consult cs    -rv *)
      (* No other cases can occur due to whnf invariant *)
      (* collectExp (T, d, g, (U, s), K) = K'

       same as collectExpW  but  (U,s) need not to be in whnf
    *)
      (* collectSpine (T, d, g, (S, s), K) = K'

       Invariant:
       If    g |- s : G1     G1 |- S : V > P
       then  K' = K, K''
       where K'' contains all EVars and BVars in (S, s)
     *)
      (* collectDec (T, d, g, (x:V, s), K) = K'

       Invariant:
       If    g |- s : G1     G1 |- V : L
       then  K' = K, K''
       where K'' contains all EVars and BVars in (V, s)
    *)
      (* collectSub (T, d, g, s, K) = K'

       Invariant:
       If    g |- s : G1
       then  K' = K, K''
       where K'' contains all EVars and BVars in s
    *)
      (* abstractEVar (K, depth, X) = C'

       Invariant:
       If   g |- X : V
       and  |g| = depth
       and  X occurs in K  at kth position (starting at 1)
       then C' = BVar (depth + k)
       and  {{K}}, g |- C' : V
    *)
      (* lookupBV (A, i) = k'

       Invariant:

       If   A ||- V
       and  g |- V type
       and  g [x] A |- i : V'
       then ex a substititution  g x A |- s : g [x] A
       and  g x A |- k' : V''
       and  g x A |- V' [s] = V'' : type
    *)
      (* lookupBV' I.Null cannot occur by invariant *)
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
      (* s = id *)(* hack - should consult cs   -rv *)
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
      (* n = 0 *)(* abstractSpine (K, depth, (S, s)) = S'
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
      (* getlevel (V) = L if g |- V : L

       Invariant: g |- V : L' for some L'
    *)
      (* checkType (V) = () if g |- V : type

       Invariant: g |- V : L' for some L'
    *)
      (* abstractCtx (K, V) = V'
       where V' = {{K}} V

       Invariant:
       If   {{K}} |- V : L
       and  . ||- V

       then V' = {{K}} V
       and  . |- V' : L
       and  . ||- V'
    *)
      (* abstractGlobalSub (K, s, B) = s'

       Invariant:
       If   K > g   aux context
       and  g |- s : g'
       then K |- s' : g'
    *)
      (* collectGlobalSub (G0, s, B, collect) = collect'

       Invariant:
       If   |- G0 ctx
       and  |- g ctx
       and  g |- B tags
       and  G0 |- s : g
       and  collect is a function which maps
               (d, K)  (d expresses the number of parameters in K, |- K aux ctx)
            to K'      (|- K' aux ctx, which collects all EVars in K)
    *)
      (* no cases for (G0, s, B as I.Decl (_, S.Parameter NONE), collect) *)
      (* abstractNew ((G0, B0), s, B) = ((g', B'), s')

       Invariant:
       If   . |- G0 ctx
       and  G0 |- B0 tags
       and  G0 |- s : g
       and  g |- B tags
       then . |- g' = G1, Gp, G2
       and  g' |- B' tags
       and  g' |- s' : g
    *)
      (* abstractSub (t, B1, (G0, B0), s, B) = ((g', B'), s')

       Invariant:
       If   . |- t : G1
       and  G1 |- B1 tags

       and  G0 |- B0 tags
       and  G0 |- s : g
       and  g |- B tags
       then . |- g' = G1, G0, G2
       and  B' |- g' tags
       and  g' |- s' : g
    *)
      (* skip'' (K, (g, B)) = K'

             Invariant:
             If   g = x1:V1 .. xn:Vn
             and  g |- B = <param> ... <param> tags
             then  K' = K, BV (x1) .. BV (xn)
          *)
      (* abstractFor (K, depth, (F, s)) = F'
       F' = {{F[s]}}_K

       Invariant:
       If    g |- s : G1     G1 |- U : V    (U,s) is in whnf
       and   K is internal context in dependency order
       and   |g| = depth
       and   K ||- U and K ||- V
       then  {{K}}, g |- U' : V'
       and   . ||- U' and . ||- V'
       and   U' is in nf
    *)
      (* abstract (Gx, F) = F'

       Invariant:
       If   g, Gx |- F formula
       then g |- F' = {{Gx}} F formula
    *)
      (* shift g = s'

       Invariant:
       Forall contexts G0:
       If   |- G0, g ctx
       then G0, V, g |- s' : G0, g
    *)
      (* ctxSub (g, s) = g'

       Invariant:
       If   G2 |- s : G1
       and  G1 |- g ctx
       then G2 |- g' = g[s] ctx
    *)
      (* weaken2 (g, a, i, S) = w'

       Invariant:
       g |- w' : Gw
       Gw < g
       g |- S : {Gw} V > V
    *)
      (* raiseType (g, V) = {{g}} V

       Invariant:
       If g |- V : L
       then  . |- {{g}} V : L

       All abstractions are potentially dependent.
    *)
      (* raiseFor (g, F, w, sc) = F'

       Invariant:
       If   G0 |- g ctx
       and  G0, g, GF |- F for
       and  G0, {g} GF [...] |- w : G0
       and  sc maps  (G0, GA |- w : G0, |GA|)  to   (G0, GA, g[..] |- s : G0, g, GF)
       then G0, {g} GF |- F' for
    *)
      (* G0, {g}GF[..], g |- s : G0, g, GF *)(* G0, {g}GF[..], g |- V' : type *)
      (* G0, {g}GF[..], g |- nw : G0, {g}GF[..], Gw
                                         Gw < g *)
      (* G0, {g}GF[..], Gw |- iw : G0, {g}GF[..], g *)
      (* Generalize the invariant for Whnf.strengthen --cs *)(* G0, {g}GF[..], Gw |- V'' = V'[iw] : type*)
      (* G0, {g}GF[..] |- V''' = {Gw} V'' : type*)(* G0, {g}GF[..], g[..] |- S''' : {Gw} V''[..] > V''[..] *)
      (* G0, {g}GF[..], g |- s : G0, g, GF *)(* G0, GA |- w' : G0 *)
      (* G0, GA, g[..] |- s' : G0, g, GF *)(* G0, GA, g[..] |- (g+k'-k). S', s' : G0, g, GF, V *)
      (*                val g = F.listToCtx (ctxSub (F.ctxToList Gorig, w))
                  val g = I.ctxLength g
                  val s = sc (w, k)
                                         G0, {g}GF[..], g |- s : G0, g, GF *)
      (* G0, {g}GF[..] |- V' = {g}(V[s]) : type *)(* G0, {g}GF[..] |- S' > {g}(V[s]) > V[s] *)
      (* G0, GA |- w' : G0 *)(* G0, GA, g[..] |- s' : G0, g, GF *)
      (* G0, GA, g[..] |- g+k'-k. S', s' : G0, g, GF, V *)
      (* G0, {g}GF[..], g |- s : G0, g, GF *)(* G0, {g}GF[..], g |- V' : type *)
      (* G0, {g}GF[..], g |- nw : G0, {g}GF[..], Gw
                                         Gw < g *)
      (* G0, {g}GF[..], Gw |- iw : G0, {g}GF[..], g *)
      (* Generalize the invariant for Whnf.strengthen --cs *)(* G0, {g}GF[..], Gw |- V'' = V'[iw] : type*)
      (* G0, {g}GF[..] |- V''' = {Gw} V'' : type*)(* G0, {g}GF[..], g[..] |- S''' : {Gw} V''[..] > V''[..] *)
      (* G0, {g}GF[..], g |- s : G0, g, GF *)(* G0, GA |- w' : G0 *)
      (* G0, GA, g[..] |- s' : G0, g, GF *)(* G0, GA, g[..] |- (g+k'-k). S', s' : G0, g, GF, V *)
      (* the other case of F.All (F.Block _, _) is not yet covered *)
      (* makeFor (g, w, AF) = F'

       Invariant :
       If   |- g ctx
       and  g |- w : g'
       and  g' |- AF approx for
       then g'; . |- F' = {EVARS} AF  for
    *)
      (*        val _ = if !Global.doubleCheck then checkTags (GK, BK) else () *)
      (* BUG *)) = weaken
    let raiseType = raiseType
    let abstractSub = abstractSubAll
    let abstractSub' = abstractNew
    let abstractApproxFor = abstractApproxFor
  end ;;
