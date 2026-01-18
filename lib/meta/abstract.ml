
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
      | (Decl (G', (Dec (name, V) as D)), a) ->
          let w' = weaken (G', a) in
          if Subordinate.belowEq ((I.targetFam V), a)
          then I.dot1 w'
          else I.comp (w', I.shift)
    let rec raiseType =
      function
      | (I.Null, V) -> V
      | (Decl (G, D), V) -> raiseType (G, (I.Pi ((D, I.Maybe), V)))
    let rec restore =
      function
      | (0, Gp) -> (Gp, I.Null)
      | (n, Decl (G, D)) ->
          let (Gp', GX') = restore ((n - 1), G) in (Gp', (I.Decl (GX', D)))
    let rec concat =
      function
      | (Gp, I.Null) -> Gp
      | (Gp, Decl (G, D)) -> I.Decl ((concat (Gp, G)), D)
    let rec collectExpW =
      function
      | (T, d, G, (Uni (L), s), K) -> K
      | (T, d, G, (Pi ((D, _), V), s), K) ->
          collectExp
            (T, d, (I.Decl (G, (I.decSub (D, s)))), (V, (I.dot1 s)),
              (collectDec (T, d, G, (D, s), K)))
      | (T, d, G, (Root (_, S), s), K) ->
          collectSpine ((S.decrease T), d, G, (S, s), K)
      | (T, d, G, (Lam (D, U), s), K) ->
          collectExp
            (T, d, (I.Decl (G, (I.decSub (D, s)))), (U, (I.dot1 s)),
              (collectDec (T, d, G, (D, s), K)))
      | (T, d, G, ((EVar (r, GdX, V, cnstrs) as X), s), K) ->
          if exists (eqEVar X) K
          then collectSub (T, d, G, s, K)
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
               (T, d, G, (I.comp (w, s)),
                 (I.Decl
                    ((collectExp (T, d, Gp, (V', I.id), K)),
                      (EV (r', V', T, d))))))
      | (T, d, G, (FgnExp csfe, s), K) ->
          I.FgnExpStd.fold csfe
            (function | (U, K') -> collectExp (T, d, G, (U, s), K')) K
    let rec collectExp (T, d, G, Us, K) =
      collectExpW (T, d, G, (Whnf.whnf Us), K)
    let rec collectSpine =
      function
      | (T, d, G, (I.Nil, _), K) -> K
      | (T, d, G, (SClo (S, s'), s), K) ->
          collectSpine (T, d, G, (S, (I.comp (s', s))), K)
      | (T, d, G, (App (U, S), s), K) ->
          collectSpine (T, d, G, (S, s), (collectExp (T, d, G, (U, s), K)))
    let rec collectDec (T, d, G, (Dec (_, V), s), K) =
      collectExp (T, d, G, (V, s), K)
    let rec collectSub =
      function
      | (T, d, G, Shift _, K) -> K
      | (T, d, G, Dot (Idx _, s), K) -> collectSub (T, d, G, s, K)
      | (T, d, G, Dot (Exp (U), s), K) ->
          collectSub (T, d, G, s, (collectExp (T, d, G, (U, I.id), K)))
    let rec abstractEVar =
      function
      | (Decl (K', EV (r', _, _, d)), depth, (EVar (r, _, _, _) as X)) ->
          if r = r'
          then ((I.BVar (depth + 1)), d)
          else abstractEVar (K', (depth + 1), X)
      | (Decl (K', BV _), depth, X) -> abstractEVar (K', (depth + 1), X)
    let rec lookupBV (K, i) =
      let rec lookupBV' =
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
      | (K, depth, ((EVar (_, G, _, _) as X), s)) ->
          let (H, d) = abstractEVar (K, depth, X) in
          I.Root
            (H, (abstractSub (((I.ctxLength G) - d), K, depth, s, I.Nil)))
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
          let (G', B') = abstractCtx K' in
          let D' = I.Dec (NONE, V'') in ((I.Decl (G', D')), (I.Decl (B', T)))
      | Decl (K', EV (_, V', (S.None as T), _)) ->
          let V'' = abstractExp (K', 0, (V', I.id)) in
          let _ = checkType V'' in
          let (G', B') = abstractCtx K' in
          let D' = I.Dec (NONE, V'') in
          ((I.Decl (G', D')), (I.Decl (B', S.None)))
      | Decl (K', BV (D, T)) ->
          let D' = abstractDec (K', 0, (D, I.id)) in
          let (G', B') = abstractCtx K' in
          ((I.Decl (G', D')), (I.Decl (B', T)))
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
      let rec skip'' =
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
      | Decl (G, D) -> I.Decl ((convert G), (BV (D, (S.Parameter NONE))))
    let rec createEmptyB =
      function | 0 -> I.Null | n -> I.Decl ((createEmptyB (n - 1)), S.None)
    let rec lower =
      function
      | (_, 0) -> I.Null
      | (Decl (G, D), n) -> I.Decl ((lower (G, (n - 1))), D)
    let rec split =
      function
      | (G, 0) -> (G, I.Null)
      | (Decl (G, D), n) ->
          let (G1, G2) = split (G, (n - 1)) in (G1, (I.Decl (G2, D)))
    let rec shift =
      function | I.Null -> I.shift | Decl (G, _) -> I.dot1 (shift G)
    let rec ctxSub =
      function
      | (nil, s) -> nil
      | ((D)::G, s) -> (::) (I.decSub (D, s)) ctxSub (G, (I.dot1 s))
    let rec weaken2 =
      function
      | (I.Null, a, i) -> (I.id, ((function | S -> S)))
      | (Decl (G', (Dec (name, V) as D)), a, i) ->
          let (w', S') = weaken2 (G', a, (i + 1)) in
          if Subordinate.belowEq ((I.targetFam V), a)
          then
            ((I.dot1 w'),
              ((function | S -> I.App ((I.Root ((I.BVar i), I.Nil)), S))))
          else ((I.comp (w', I.shift)), S')
    let rec raiseType =
      function
      | (I.Null, V) -> V
      | (Decl (G, D), V) ->
          raiseType
            (G,
              (Abstract.piDepend
                 (((Whnf.normalizeDec (D, I.id)), I.Maybe), V)))
    let rec raiseFor =
      function
      | (k, Gorig, (F.True as F), w, sc) -> F
      | (k, Gorig, Ex (Dec (name, V), F), w, sc) ->
          let G = F.listToCtx (ctxSub ((F.ctxToList Gorig), w)) in
          let g = I.ctxLength G in
          let s = sc (w, k) in
          let V' = I.EClo (V, s) in
          let (nw, S) = weaken2 (G, (I.targetFam V), 1) in
          let iw = Whnf.invert nw in
          let Gw = Whnf.strengthen (iw, G) in
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
          let G = F.listToCtx (ctxSub ((F.ctxToList Gorig), w)) in
          let g = I.ctxLength G in
          let s = sc (w, k) in
          let V' = I.EClo (V, s) in
          let (nw, S) = weaken2 (G, (I.targetFam V), 1) in
          let iw = Whnf.invert nw in
          let Gw = Whnf.strengthen (iw, G) in
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
      | (K, w, Head (G, (F, s), d)) ->
          let cf =
            collectGlobalSub
              (G, s, (createEmptyB d), (function | (_, K') -> K')) in
          let k = I.ctxLength K in
          let K' = cf ((I.ctxLength G), K) in
          let k' = I.ctxLength K' in
          let (GK, BK) = abstractCtx K' in
          let _ =
            if !Global.doubleCheck then TypeCheck.typeCheckCtx GK else () in
          let w' = I.comp (w, (I.Shift (k' - k))) in
          let FK = abstractFor (K', 0, (F, s)) in
          let _ =
            if !Global.doubleCheck then FunTypeCheck.isFor (GK, FK) else () in
          let (GK1, GK2) = split (GK, (k' - k)) in (GK1, (allClo (GK2, FK)))
      | (K, w, Block ((G, t, d, G2), AF)) ->
          let k = I.ctxLength K in
          let collect =
            collectGlobalSub
              (G, t, (createEmptyB d), (function | (_, K') -> K')) in
          let K' = collect ((I.ctxLength G), K) in
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
      | Head (G, _, _) as AF ->
          let (_, F) = makeFor ((convert G), I.id, AF) in F
      | Block ((G, _, _, _), _) as AF ->
          let (_, F) = makeFor ((convert G), I.id, AF) in F
    (* Intermediate Data Structure *)
    (* y ::= (X , {G2} V)  if {G1, G2 |- X : V
                                          |G1| = d *)
    (*
       We write {{K}} for the context of K, where EVars and BVars have
       been translated to declarations and their occurrences to BVars.
       We write {{U}}_K, {{S}}_K for the corresponding translation of an
       expression or spine.

       Just like contexts G, any K is implicitly assumed to be
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
    (* no case for Redex, EVar, EClo *)
    (* no case for FVar *)
    (* no case for SClo *)
    (* piDepend ((D,P), V) = Pi ((D,P'), V)
       where P' = Maybe if D occurs in V, P' = No otherwise
    *)
    (* optimize to have fewer traversals? -cs *)
    (* pre-Twelf 1.2 code walk Fri May  8 11:17:10 1998 *)
    (* weaken (depth,  G, a) = (w')
    *)
    (* raiseType (G, V) = {{G}} V

       Invariant:
       If G |- V : L
       then  . |- {{G}} V : L

       All abstractions are potentially dependent.
    *)
    (* collectExpW (T, d, G, (U, s), K) = K'

       Invariant:
       If    G |- s : G1     G1 |- U : V      (U,s) in whnf
       No circularities in U
             (enforced by extended occurs-check for BVars in Unify)
       and   K' = K, K''
             where K'' contains all EVars and BVars in (U,s)
    *)
    (* Possible optimization: Calculate also the normal form of the term *)
    (* optimization possible for d = 0 *)
    (* hack - should consult cs    -rv *)
    (* No other cases can occur due to whnf invariant *)
    (* collectExp (T, d, G, (U, s), K) = K'

       same as collectExpW  but  (U,s) need not to be in whnf
    *)
    (* collectSpine (T, d, G, (S, s), K) = K'

       Invariant:
       If    G |- s : G1     G1 |- S : V > P
       then  K' = K, K''
       where K'' contains all EVars and BVars in (S, s)
     *)
    (* collectDec (T, d, G, (x:V, s), K) = K'

       Invariant:
       If    G |- s : G1     G1 |- V : L
       then  K' = K, K''
       where K'' contains all EVars and BVars in (V, s)
    *)
    (* collectSub (T, d, G, s, K) = K'

       Invariant:
       If    G |- s : G1
       then  K' = K, K''
       where K'' contains all EVars and BVars in s
    *)
    (* abstractEVar (K, depth, X) = C'

       Invariant:
       If   G |- X : V
       and  |G| = depth
       and  X occurs in K  at kth position (starting at 1)
       then C' = BVar (depth + k)
       and  {{K}}, G |- C' : V
    *)
    (* lookupBV (A, i) = k'

       Invariant:

       If   A ||- V
       and  G |- V type
       and  G [x] A |- i : V'
       then ex a substititution  G x A |- s : G [x] A
       and  G x A |- k' : V''
       and  G x A |- V' [s] = V'' : type
    *)
    (* lookupBV' I.Null cannot occur by invariant *)
    (* abstractExpW (K, depth, (U, s)) = U'
       U' = {{U[s]}}_K

       Invariant:
       If    G |- s : G1     G1 |- U : V    (U,s) is in whnf
       and   K is internal context in dependency order
       and   |G| = depth
       and   K ||- U and K ||- V
       then  {{K}}, G |- U' : V'
       and   . ||- U' and . ||- V'
       and   U' is in nf
    *)
    (* s = id *)
    (* hack - should consult cs   -rv *)
    (* abstractExp (K, depth, (U, s)) = U'

       same as abstractExpW, but (U,s) need not to be in whnf
    *)
    (* abstractSub (K, depth, s, S) = S'      (implicit raising)
       S' = {{s}}_K @@ S

       Invariant:
       If   G |- s : G1
       and  |G| = depth
       and  K ||- s
       then {{K}}, G |- S' : {G1}.W > W   (for some W)
       and  . ||- S'
    *)
    (* n = 0 *)
    (* abstractSpine (K, depth, (S, s)) = S'
       where S' = {{S[s]}}_K

       Invariant:
       If   G |- s : G1     G1 |- S : V > P
       and  K ||- S
       and  |G| = depth

       then {{K}}, G |- S' : V' > P'
       and  . ||- S'
    *)
    (* abstractDec (K, depth, (x:V, s)) = x:V'
       where V = {{V[s]}}_K

       Invariant:
       If   G |- s : G1     G1 |- V : L
       and  K ||- V
       and  |G| = depth

       then {{K}}, G |- V' : L
       and  . ||- V'
    *)
    (* getlevel (V) = L if G |- V : L

       Invariant: G |- V : L' for some L'
    *)
    (* checkType (V) = () if G |- V : type

       Invariant: G |- V : L' for some L'
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
       If   K > G   aux context
       and  G |- s : G'
       then K |- s' : G'
    *)
    (* collectGlobalSub (G0, s, B, collect) = collect'

       Invariant:
       If   |- G0 ctx
       and  |- G ctx
       and  G |- B tags
       and  G0 |- s : G
       and  collect is a function which maps
               (d, K)  (d expresses the number of parameters in K, |- K aux ctx)
            to K'      (|- K' aux ctx, which collects all EVars in K)
    *)
    (* no cases for (G0, s, B as I.Decl (_, S.Parameter NONE), collect) *)
    (* abstractNew ((G0, B0), s, B) = ((G', B'), s')

       Invariant:
       If   . |- G0 ctx
       and  G0 |- B0 tags
       and  G0 |- s : G
       and  G |- B tags
       then . |- G' = G1, Gp, G2
       and  G' |- B' tags
       and  G' |- s' : G
    *)
    (* abstractSub (t, B1, (G0, B0), s, B) = ((G', B'), s')

       Invariant:
       If   . |- t : G1
       and  G1 |- B1 tags

       and  G0 |- B0 tags
       and  G0 |- s : G
       and  G |- B tags
       then . |- G' = G1, G0, G2
       and  B' |- G' tags
       and  G' |- s' : G
    *)
    (* skip'' (K, (G, B)) = K'

             Invariant:
             If   G = x1:V1 .. xn:Vn
             and  G |- B = <param> ... <param> tags
             then  K' = K, BV (x1) .. BV (xn)
          *)
    (* abstractFor (K, depth, (F, s)) = F'
       F' = {{F[s]}}_K

       Invariant:
       If    G |- s : G1     G1 |- U : V    (U,s) is in whnf
       and   K is internal context in dependency order
       and   |G| = depth
       and   K ||- U and K ||- V
       then  {{K}}, G |- U' : V'
       and   . ||- U' and . ||- V'
       and   U' is in nf
    *)
    (* abstract (Gx, F) = F'

       Invariant:
       If   G, Gx |- F formula
       then G |- F' = {{Gx}} F formula
    *)
    (* shift G = s'

       Invariant:
       Forall contexts G0:
       If   |- G0, G ctx
       then G0, V, G |- s' : G0, G
    *)
    (* ctxSub (G, s) = G'

       Invariant:
       If   G2 |- s : G1
       and  G1 |- G ctx
       then G2 |- G' = G[s] ctx
    *)
    (* weaken2 (G, a, i, S) = w'

       Invariant:
       G |- w' : Gw
       Gw < G
       G |- S : {Gw} V > V
    *)
    (* raiseType (G, V) = {{G}} V

       Invariant:
       If G |- V : L
       then  . |- {{G}} V : L

       All abstractions are potentially dependent.
    *)
    (* raiseFor (G, F, w, sc) = F'

       Invariant:
       If   G0 |- G ctx
       and  G0, G, GF |- F for
       and  G0, {G} GF [...] |- w : G0
       and  sc maps  (G0, GA |- w : G0, |GA|)  to   (G0, GA, G[..] |- s : G0, G, GF)
       then G0, {G} GF |- F' for
    *)
    (* G0, {G}GF[..], G |- s : G0, G, GF *)
    (* G0, {G}GF[..], G |- V' : type *)
    (* G0, {G}GF[..], G |- nw : G0, {G}GF[..], Gw
                                         Gw < G *)
    (* G0, {G}GF[..], Gw |- iw : G0, {G}GF[..], G *)
    (* Generalize the invariant for Whnf.strengthen --cs *)
    (* G0, {G}GF[..], Gw |- V'' = V'[iw] : type*)
    (* G0, {G}GF[..] |- V''' = {Gw} V'' : type*)
    (* G0, {G}GF[..], G[..] |- S''' : {Gw} V''[..] > V''[..] *)
    (* G0, {G}GF[..], G |- s : G0, G, GF *)
    (* G0, GA |- w' : G0 *)
    (* G0, GA, G[..] |- s' : G0, G, GF *)
    (* G0, GA, G[..] |- (g+k'-k). S', s' : G0, G, GF, V *)
    (*                val G = F.listToCtx (ctxSub (F.ctxToList Gorig, w))
                  val g = I.ctxLength G
                  val s = sc (w, k)
                                         G0, {G}GF[..], G |- s : G0, G, GF *)
    (* G0, {G}GF[..] |- V' = {G}(V[s]) : type *)
    (* G0, {G}GF[..] |- S' > {G}(V[s]) > V[s] *)
    (* G0, GA |- w' : G0 *)
    (* G0, GA, G[..] |- s' : G0, G, GF *)
    (* G0, GA, G[..] |- g+k'-k. S', s' : G0, G, GF, V *)
    (* G0, {G}GF[..], G |- s : G0, G, GF *)
    (* G0, {G}GF[..], G |- V' : type *)
    (* G0, {G}GF[..], G |- nw : G0, {G}GF[..], Gw
                                         Gw < G *)
    (* G0, {G}GF[..], Gw |- iw : G0, {G}GF[..], G *)
    (* Generalize the invariant for Whnf.strengthen --cs *)
    (* G0, {G}GF[..], Gw |- V'' = V'[iw] : type*)
    (* G0, {G}GF[..] |- V''' = {Gw} V'' : type*)
    (* G0, {G}GF[..], G[..] |- S''' : {Gw} V''[..] > V''[..] *)
    (* G0, {G}GF[..], G |- s : G0, G, GF *)
    (* G0, GA |- w' : G0 *)
    (* G0, GA, G[..] |- s' : G0, G, GF *)
    (* G0, GA, G[..] |- (g+k'-k). S', s' : G0, G, GF, V *)
    (* the other case of F.All (F.Block _, _) is not yet covered *)
    (* makeFor (G, w, AF) = F'

       Invariant :
       If   |- G ctx
       and  G |- w : G'
       and  G' |- AF approx for
       then G'; . |- F' = {EVARS} AF  for
    *)
    (*        val _ = if !Global.doubleCheck then checkTags (GK, BK) else () *)
    (* BUG *)
    let weaken = weaken
    let raiseType = raiseType
    let abstractSub = abstractSubAll
    let abstractSub' = abstractNew
    let abstractApproxFor = abstractApproxFor
  end ;;
