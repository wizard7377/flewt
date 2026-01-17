
module type RELFUN  =
  sig
    exception Error of
      ((string)(*! structure FunSyn : FUNSYN !*)(* Author: Carsten Schuermann *)
      (* Converter from relational representation to a functional
   representation of proof terms *))
      
    val convertFor : IntSyn.cid list -> FunSyn.__For
    val convertPro : IntSyn.cid list -> FunSyn.__Pro
  end;;




module RelFun(RelFun:sig
                       module Global : GLOBAL
                       module ModeTable : MODETABLE
                       module Names : NAMES
                       module Unify : UNIFY
                       module Whnf : WHNF
                       module Weaken : WEAKEN
                       module TypeCheck : TYPECHECK
                       module FunWeaken : FUNWEAKEN
                       module FunNames :
                       ((FUNNAMES)(* Converter from relational representation to a functional
   representation of proof terms *)
                       (* Author: Carsten Schuermann *)
                       (*! structure FunSyn' : FUNSYN !*)
                       (*! sharing ModeSyn.IntSyn = FunSyn'.IntSyn !*)
                       (*! sharing Names.IntSyn = FunSyn'.IntSyn !*)
                       (*! sharing Unify.IntSyn = FunSyn'.IntSyn !*)
                       (*! sharing Whnf.IntSyn = FunSyn'.IntSyn !*)
                       (*! sharing Weaken.IntSyn = FunSyn'.IntSyn !*)
                       (*! sharing TypeCheck.IntSyn = FunSyn'.IntSyn !*)
                       (*! sharing FunWeaken.FunSyn = FunSyn' !*))
                     end) : RELFUN =
  struct
    exception Error of
      ((string)(*! structure FunSyn = FunSyn' !*)(*! sharing FunNames.FunSyn = FunSyn' !*))
      
    module F = FunSyn
    module I = IntSyn
    module M = ModeSyn
    let rec ctxSub =
      function
      | (I.Null, s) -> (I.Null, s)
      | (Decl (g, D), s) ->
          let (g', s') = ctxSub (g, s) in
          ((I.Decl (g', (I.decSub (D, s')))), (I.dot1 s))
    let rec convertOneFor cid =
      let V =
        match I.sgnLookup cid with
        | ConDec (name, _, _, _, V, I.Kind) -> V
        | _ -> raise (Error "Type Constant declaration expected") in
      let mS =
        match ModeTable.modeLookup cid with
        | NONE -> raise (Error "Mode declaration expected")
        | SOME mS -> mS in
      let convertFor' =
        function
        | (Pi ((D, _), V), Mapp (Marg (M.Plus, _), mS), w1, w2, n) ->
            let (F', F'') =
              convertFor'
                (V, mS, (I.dot1 w1), (I.Dot ((I.Idx n), w2)), (n - 1)) in
            (((function
               | F -> F.All ((F.Prim (Weaken.strengthenDec (D, w1))), (F' F)))),
              F'')
        | (Pi ((D, _), V), Mapp (Marg (M.Minus, _), mS), w1, w2, n) ->
            let (F', F'') =
              convertFor'
                (V, mS, (I.comp (w1, I.shift)), (I.dot1 w2), (n + 1)) in
            (F', (F.Ex ((I.decSub (D, w2)), F'')))
        | (Uni (I.Type), M.Mnil, _, _, _) -> (((function | F -> F)), F.True)
        | _ -> raise (Error "type family must be +/- moded") in
      let shiftPlus mS =
        let shiftPlus' =
          function
          | (M.Mnil, n) -> n
          | (Mapp (Marg (M.Plus, _), mS'), n) -> shiftPlus' (mS', (n + 1))
          | (Mapp (Marg (M.Minus, _), mS'), n) -> shiftPlus' (mS', n) in
        shiftPlus' (mS, 0) in
      let n = shiftPlus mS in
      let (F, F') = convertFor' (V, mS, I.id, (I.Shift n), n) in F F'
    let rec convertFor =
      function
      | nil -> raise (Error "Empty theorem")
      | a::[] -> convertOneFor a
      | a::L -> F.And ((convertOneFor a), (convertFor L))
    let rec occursInExpN =
      function
      | (k, Uni _) -> false__
      | (k, Pi (DP, V)) ->
          (occursInDecP (k, DP)) || (occursInExpN ((k + 1), V))
      | (k, Root (H, S)) -> (occursInHead (k, H)) || (occursInSpine (k, S))
      | (k, Lam (D, V)) ->
          (occursInDec (k, D)) || (occursInExpN ((k + 1), V))
      | (k, FgnExp csfe) ->
          I.FgnExpStd.fold csfe
            (function
             | (U, B) -> B || (occursInExpN (k, (Whnf.normalize (U, I.id)))))
            false__
    let rec occursInHead =
      function
      | (k, BVar k') -> k = k'
      | (k, Const _) -> false__
      | (k, Def _) -> false__
      | (k, FgnConst _) -> false__
    let rec occursInSpine =
      function
      | (_, I.Nil) -> false__
      | (k, App (U, S)) -> (occursInExpN (k, U)) || (occursInSpine (k, S))
    let rec occursInDec (k, Dec (_, V)) = occursInExpN (k, V)
    let rec occursInDecP (k, (D, _)) = occursInDec (k, D)
    let rec occursInExp (k, U) = occursInExpN (k, (Whnf.normalize (U, I.id)))
    let rec dot1inv w = Weaken.strengthenSub ((I.comp (I.shift, w)), I.shift)
    let rec shiftinv w = Weaken.strengthenSub (w, I.shift)
    let rec eqIdx = function | (Idx n, Idx k) -> n = k | _ -> false__
    let rec peel w =
      if eqIdx ((I.bvarSub (1, w)), (I.Idx 1)) then dot1inv w else shiftinv w
    let rec peeln =
      function | (0, w) -> w | (n, w) -> peeln ((n - 1), (peel w))
    let rec domain =
      function
      | (g, Dot (Idx _, s)) -> (domain (g, s)) + 1
      | (I.Null, Shift 0) -> 0
      | ((Decl _ as g), Shift 0) ->
          domain (g, (I.Dot ((I.Idx 1), (I.Shift 1))))
      | (Decl (g, _), Shift n) -> domain (g, (I.Shift (n - 1)))
    let rec strengthen (Psi, (a, S), w, m) =
      let mS =
        match ModeTable.modeLookup a with
        | NONE -> raise (Error "Mode declaration expected")
        | SOME mS -> mS in
      let args =
        function
        | (I.Nil, M.Mnil) -> nil
        | (App (U, S'), Mapp (Marg (m', _), mS)) ->
            let L = args (S', mS) in
            (match M.modeEqual (m, m') with | true__ -> U :: L | false__ -> L) in
      let strengthenArgs =
        function
        | (nil, s) -> nil
        | ((U)::L, s) ->
            (::) (Weaken.strengthenExp (U, s)) strengthenArgs (L, s) in
      let occursInArgs =
        function
        | (n, nil) -> false__
        | (n, (U)::L) -> (occursInExp (n, U)) || (occursInArgs (n, L)) in
      let occursInPsi =
        function
        | (n, (nil, L)) -> occursInArgs (n, L)
        | (n, ((Prim (Dec (_, V)))::Psi1, L)) ->
            (occursInExp (n, V)) || (occursInPsi ((n + 1), (Psi1, L)))
        | (n, ((Block (CtxBlock (l, g)))::Psi1, L)) ->
            occursInG (n, g, (function | n' -> occursInPsi (n', (Psi1, L))))
      and occursInG =
        function
        | (n, I.Null, k) -> k n
        | (n, Decl (g, Dec (_, V)), k) ->
            occursInG
              (n, g,
                (function | n' -> (occursInExp (n', V)) || (k (n' + 1)))) in
      let occursBlock (g, (Psi2, L)) =
        let occursBlock =
          function
          | (I.Null, n) -> false__
          | (Decl (g, D), n) ->
              (occursInPsi (n, (Psi2, L))) || (occursBlock (g, (n + 1))) in
        occursBlock (g, 1) in
      let inBlock =
        function
        | (I.Null, (bw, w1)) -> (bw, w1)
        | (Decl (g, D), (bw, w1)) ->
            if eqIdx ((I.bvarSub (1, w1)), (I.Idx 1))
            then inBlock (g, (true__, (dot1inv w1)))
            else inBlock (g, (bw, (Weaken.strengthenSub (w1, I.shift)))) in
      let blockSub =
        function
        | (I.Null, w) -> (I.Null, w)
        | (Decl (g, Dec (name, V)), w) ->
            let (g', w') = blockSub (g, w) in
            let V' = Weaken.strengthenExp (V, w') in
            ((I.Decl (g', (I.Dec (name, V')))), (I.dot1 w')) in
      let strengthen' =
        function
        | (I.Null, Psi2, L, w1) -> (I.Null, I.id)
        | (Decl (Psi1, (Prim (Dec (name, V)) as LD)), Psi2, L, w1) ->
            let (bw, w1') =
              if eqIdx ((I.bvarSub (1, w1)), (I.Idx 1))
              then (true__, (dot1inv w1))
              else (false__, (Weaken.strengthenSub (w1, I.shift))) in
            if bw || (occursInPsi (1, (Psi2, L)))
            then
              let (Psi1', w') = strengthen' (Psi1, (LD :: Psi2), L, w1') in
              let V' = Weaken.strengthenExp (V, w') in
              ((I.Decl (Psi1', (F.Prim (I.Dec (name, V'))))), (I.dot1 w'))
            else
              (let w2 = I.shift in
               let (Psi2', w2') = FunWeaken.strengthenPsi' (Psi2, w2) in
               let L' = strengthenArgs (L, w2') in
               let (Psi1'', w') = strengthen' (Psi1, Psi2', L', w1') in
               (Psi1'', (I.comp (w', I.shift))))
        | (Decl (Psi1, (Block (CtxBlock (name, g)) as LD)), Psi2, L, w1) ->
            let (bw, w1') = inBlock (g, (false__, w1)) in
            if bw || (occursBlock (g, (Psi2, L)))
            then
              let (Psi1', w') = strengthen' (Psi1, (LD :: Psi2), L, w1') in
              let (g'', w'') = blockSub (g, w') in
              ((I.Decl (Psi1', (F.Block (F.CtxBlock (name, g''))))), w'')
            else
              (let w2 = I.Shift (I.ctxLength g) in
               let (Psi2', w2') = FunWeaken.strengthenPsi' (Psi2, w2) in
               let L' = strengthenArgs (L, w2') in
               strengthen' (Psi1, Psi2', L', w1')) in
      strengthen' (Psi, nil, (args (S, mS)), w)
    let rec recursion (L) =
      let F = convertFor L in
      let name =
        function
        | a::[] -> I.conDecName (I.sgnLookup a)
        | a::L -> ((I.conDecName (I.sgnLookup a)) ^ "/") ^ (name L) in
      function | p -> F.Rec ((F.MDec ((SOME (name L)), F)), p)
    let rec abstract a =
      let mS =
        match ModeTable.modeLookup a with
        | NONE -> raise (Error "Mode declaration expected")
        | SOME mS -> mS in
      let V =
        match I.sgnLookup a with
        | ConDec (name, _, _, _, V, I.Kind) -> V
        | _ -> raise (Error "Type Constant declaration expected") in
      let abstract' =
        function
        | ((_, M.Mnil), w) -> (function | p -> p)
        | ((Pi ((D, _), V2), Mapp (Marg (M.Plus, _), mS)), w) ->
            let D' = Weaken.strengthenDec (D, w) in
            let P = abstract' ((V2, mS), (I.dot1 w)) in
            (function | p -> F.Lam ((F.Prim D'), (P p)))
        | ((Pi (_, V2), Mapp (Marg (M.Minus, _), mS)), w) ->
            abstract' ((V2, mS), (I.comp (w, I.shift))) in
      abstract' ((V, mS), I.id)
    let rec transformInit (Psi, (a, S), w1) =
      let mS =
        match ModeTable.modeLookup a with
        | NONE -> raise (Error "Mode declaration expected")
        | SOME mS -> mS in
      let V =
        match I.sgnLookup a with
        | ConDec (name, _, _, _, V, I.Kind) -> V
        | _ -> raise (Error "Type Constant declaration expected") in
      let transformInit' =
        function
        | ((I.Nil, M.Mnil), Uni (I.Type), (w, s)) -> (w, s)
        | ((App (U, S), Mapp (Marg (M.Minus, _), mS)), Pi (_, V2), (w, s)) ->
            let w' = I.comp (w, I.shift) in
            let s' = s in transformInit' ((S, mS), V2, (w', s'))
        | ((App (U, S), Mapp (Marg (M.Plus, _), mS)), Pi
           ((Dec (name, V1), _), V2), (w, s)) ->
            let V1' = Weaken.strengthenExp (V1, w) in
            let w' = I.dot1 w in
            let U' = Weaken.strengthenExp (U, w1) in
            let s' = Whnf.dotEta ((I.Exp U'), s) in
            transformInit' ((S, mS), V2, (w', s')) in
      transformInit' ((S, mS), V, (I.id, (I.Shift (F.lfctxLength Psi))))
    let rec transformDec (Ts, (Psi, G0), d, (a, S), w1, w2, t0) =
      let mS =
        match ModeTable.modeLookup a with
        | NONE -> raise (Error "Mode declaration expected")
        | SOME mS -> mS in
      let V =
        match I.sgnLookup a with
        | ConDec (name, _, _, _, V, I.Kind) -> V
        | _ -> raise (Error "Type Constant declaration expected") in
      let raiseExp (g, U, a) =
        let raiseExp' =
          function
          | I.Null -> (I.id, ((function | x -> x)))
          | Decl (g, (Dec (_, V) as D)) ->
              let (w, k) = raiseExp' g in
              if Subordinate.belowEq ((I.targetFam V), a)
              then
                ((I.dot1 w),
                  ((function
                    | x -> k (I.Lam ((Weaken.strengthenDec (D, w)), x)))))
              else ((I.comp (w, I.shift)), k) in
        let (w, k) = raiseExp' g in k (Weaken.strengthenExp (U, w)) in
      let raiseType (g, U, a) =
        let raiseType' =
          function
          | (I.Null, n) ->
              (I.id, ((function | x -> x)), ((function | S -> S)))
          | (Decl (g, (Dec (_, V) as D)), n) ->
              let (w, k, k') = raiseType' (g, (n + 1)) in
              if Subordinate.belowEq ((I.targetFam V), a)
              then
                ((I.dot1 w),
                  ((function
                    | x ->
                        k
                          (I.Pi (((Weaken.strengthenDec (D, w)), I.Maybe), x)))),
                  ((function | S -> I.App ((I.Root ((I.BVar n), I.Nil)), S))))
              else ((I.comp (w, I.shift)), k, k') in
        let (w, k, k') = raiseType' (g, 2) in
        ((k (Weaken.strengthenExp (U, w))),
          (I.Root ((I.BVar 1), (k' I.Nil)))) in
      let exchangeSub (G0) =
        let g0 = I.ctxLength G0 in
        let exchangeSub' =
          function
          | (0, s) -> s
          | (k, s) -> exchangeSub' ((k - 1), (I.Dot ((I.Idx k), s))) in
        I.Dot ((I.Idx (g0 + 1)), (exchangeSub' (g0, (I.Shift (g0 + 1))))) in
      let transformDec' =
        function
        | (d, (I.Nil, M.Mnil), Uni (I.Type), (z1, z2), (w, t)) ->
            (w, t,
              (d, ((function | (k, Ds) -> Ds k)),
                ((function | _ -> F.Empty))))
        | (d, (App (U, S), Mapp (Marg (M.Minus, _), mS)), Pi
           ((Dec (_, V1), DP), V2), (z1, z2), (w, t)) ->
            let g = I.ctxLength G0 in
            let w1' = peeln (g, w1) in
            let (G1, _) = Weaken.strengthenCtx (G0, w1') in
            let (G2, _) = ctxSub (G1, z1) in
            let (V1'', Ur) =
              raiseType (G2, (I.EClo (V1, z2)), (I.targetFam V1)) in
            let w' =
              match DP with
              | I.Maybe -> I.dot1 w
              | I.No -> I.comp (w, I.shift) in
            let u0 = raiseExp (G0, U, (I.targetFam V1'')) in
            let U' = Weaken.strengthenExp (u0, w2) in
            let t' = Whnf.dotEta ((I.Exp U'), t) in
            let z1' = I.comp (z1, I.shift) in
            let xc = exchangeSub G0 in
            let z2n = I.comp (z2, (I.comp (I.shift, xc))) in
            let Ur' = I.EClo (Ur, xc) in
            let z2' = Whnf.dotEta ((I.Exp Ur'), z2n) in
            let (w'', t'', (d', Dplus, Dminus)) =
              transformDec' ((d + 1), (S, mS), V2, (z1', z2'), (w', t')) in
            (w'', t'',
              (d', Dplus, ((function | k -> F.Split (k, (Dminus 1))))))
        | (d, (App (U, S), Mapp (Marg (M.Plus, _), mS)), Pi
           ((Dec (name, V1), _), V2), (z1, z2), (w, t)) ->
            let V1' = Weaken.strengthenExp (V1, w) in
            let w' = I.dot1 w in
            let U' = Weaken.strengthenExp (U, w1) in
            let t' = t in
            let z1' = F.dot1n (G0, z1) in
            let z2' = I.Dot ((I.Exp (I.EClo (U', z1'))), z2) in
            let (w'', t'', (d', Dplus, Dminus)) =
              transformDec' ((d + 1), (S, mS), V2, (z1, z2'), (w', t')) in
            (w'', t'',
              (d',
                ((function | (k, Ds) -> F.App ((k, U'), (Dplus (1, Ds))))),
                Dminus)) in
      let (w'', t'', (d', Dplus, Dminus)) =
        transformDec'
          (d, (S, mS), V,
            (I.id, (I.Shift ((+) (domain (Psi, t0)) I.ctxLength G0))),
            (I.id, t0)) in
      let varHead (Ts) (w'', t'', (d', Dplus, Dminus)) =
        let head' =
          function
          | (a'::[], d1, k1) -> (d1, k1)
          | (a'::Ts', d1, k1) ->
              if a = a'
              then ((d1 + 1), ((function | xx -> F.Left (xx, (k1 1)))))
              else
                (let (d2, k2) = head' (Ts', (d1 + 1), k1) in
                 (d2, (function | xx -> F.Right (xx, (k2 1))))) in
        let (d2, k2) = head' (Ts, d', (function | xx -> Dplus (xx, Dminus))) in
        (d2, w'', t'', (k2 d)) in
      let lemmaHead (w'', t'', (d', Dplus, Dminus)) =
        let name = I.conDecName (I.sgnLookup a) in
        let l =
          match FunNames.nameLookup name with
          | NONE -> raise (Error (("Lemma " ^ name) ^ " not defined"))
          | SOME lemma -> lemma in
        ((d' + 1), w'', t'', (F.Lemma (l, (Dplus (1, Dminus))))) in
      if List.exists (function | x -> x = a) Ts
      then varHead Ts (w'', t'', (d', Dplus, Dminus))
      else lemmaHead (w'', t'', (d', Dplus, Dminus))
    let rec transformConc ((a, S), w) =
      let mS =
        match ModeTable.modeLookup a with
        | NONE -> raise (Error "Mode declaration expected")
        | SOME mS -> mS in
      let transformConc' =
        function
        | (I.Nil, M.Mnil) -> F.Unit
        | (App (U, S'), Mapp (Marg (M.Plus, _), mS')) ->
            transformConc' (S', mS')
        | (App (U, S'), Mapp (Marg (M.Minus, _), mS')) ->
            F.Inx ((Weaken.strengthenExp (U, w)), (transformConc' (S', mS'))) in
      transformConc' (S, mS)
    let rec traverse (Ts, c) =
      let traverseNeg =
        function
        | (c'', Psi, (Pi (((Dec (_, V1) as D), I.Maybe), V2), v), L) ->
            (match traverseNeg
                     (c'',
                       (I.Decl (Psi, (F.Prim (Weaken.strengthenDec (D, v))))),
                       (V2, (I.dot1 v)), L)
             with
             | (SOME (w', d', PQ'), L') -> ((SOME ((peel w'), d', PQ')), L')
             | (NONE, L') -> (NONE, L'))
        | (c'', Psi, (Pi (((Dec (_, V1) as D), I.No), V2), v), L) ->
            (match traverseNeg (c'', Psi, (V2, (I.comp (v, I.shift))), L)
             with
             | (SOME (w', d', PQ'), L') ->
                 traversePos
                   (c'', Psi, I.Null, ((Weaken.strengthenExp (V1, v)), I.id),
                     (SOME (w', d', PQ')), L')
             | (NONE, L') ->
                 traversePos
                   (c'', Psi, I.Null, ((Weaken.strengthenExp (V1, v)), I.id),
                     NONE, L'))
        | (c'', Psi, ((Root (Const c', S) as V), v), L) ->
            if c = c'
            then
              let S' = Weaken.strengthenSpine (S, v) in
              let (Psi', w') =
                strengthen
                  (Psi, (c', S'), (I.Shift (F.lfctxLength Psi)), M.Plus) in
              let (w'', s'') = transformInit (Psi', (c', S'), w') in
              ((SOME
                  (w', 1,
                    ((function | p -> (Psi', s'', p)),
                      (function | wf -> transformConc ((c', S'), wf))))), L)
            else (NONE, L)
      and traversePos =
        function
        | (c'', Psi, g, (Pi (((Dec (_, V1) as D), I.Maybe), V2), v), SOME
           (w, d, PQ), L) ->
            (match traversePos
                     (c'', Psi, (I.Decl (g, (Weaken.strengthenDec (D, v)))),
                       (V2, (I.dot1 v)), (SOME ((I.dot1 w), d, PQ)), L)
             with
             | (SOME (w', d', PQ'), L') -> ((SOME (w', d', PQ')), L'))
        | (c'', Psi, g, (Pi (((Dec (_, V1) as D), I.No), V2), v), SOME
           (w, d, PQ), L) ->
            (match traversePos
                     (c'', Psi, g, (V2, (I.comp (v, I.shift))),
                       (SOME (w, d, PQ)), L)
             with
             | (SOME (w', d', PQ'), L') ->
                 (match traverseNeg
                          (c'',
                            (I.Decl (Psi, (F.Block (F.CtxBlock (NONE, g))))),
                            (V1, v), L')
                  with
                  | (SOME (w'', d'', (P'', Q'')), L'') ->
                      ((SOME (w', d', PQ')), ((P'' (Q'' w'')) :: L''))
                  | (NONE, L'') -> ((SOME (w', d', PQ')), L'')))
        | (c'', Psi, I.Null, (V, v), SOME (w1, d, (P, Q)), L) ->
            let Root (Const a', S) =
              Whnf.normalize ((Weaken.strengthenExp (V, v)), I.id) in
            let (Psi', w2) = strengthen (Psi, (a', S), w1, M.Minus) in
            let _ =
              if !Global.doubleCheck
              then
                TypeCheck.typeCheck
                  ((F.makectx Psi'), ((I.Uni I.Type), (I.Uni I.Kind)))
              else () in
            let w3 = Weaken.strengthenSub (w1, w2) in
            let (d4, w4, t4, Ds) =
              transformDec (Ts, (Psi', I.Null), d, (a', S), w1, w2, w3) in
            ((SOME
                (w2, d4,
                  ((function
                    | p -> P (F.Let (Ds, (F.Case (F.Opts [(Psi', t4, p)]))))),
                    Q))), L)
        | (c'', Psi, g, (V, v), SOME (w1, d, (P, Q)), L) ->
            let Root (Const a', S) = Weaken.strengthenExp (V, v) in
            let ((Decl (Psi', Block (CtxBlock (name, G2))) as dummy), w2) =
              strengthen
                ((I.Decl (Psi, (F.Block (F.CtxBlock (NONE, g))))), (a', S),
                  w1, M.Minus) in
            let _ =
              if !Global.doubleCheck
              then
                TypeCheck.typeCheck
                  ((F.makectx dummy), ((I.Uni I.Type), (I.Uni I.Kind)))
              else () in
            let g = I.ctxLength g in
            let w1' = peeln (g, w1) in
            let w2' = peeln (g, w2) in
            let (G1, _) = Weaken.strengthenCtx (g, w1') in
            let w3 = Weaken.strengthenSub (w1', w2') in
            let (d4, w4, t4, Ds) =
              transformDec (Ts, (Psi', g), d, (a', S), w1, w2', w3) in
            ((SOME
                (w2', d4,
                  ((function
                    | p ->
                        P
                          (F.Let
                             ((F.New ((F.CtxBlock (NONE, G1)), Ds)),
                               (F.Case (F.Opts [(Psi', t4, p)]))))), Q))), L)
        | (c'', Psi, g, (Pi (((Dec (_, V1) as D), I.Maybe), V2), v), NONE, L)
            ->
            traversePos
              (c'', Psi, (I.Decl (g, (Weaken.strengthenDec (D, v)))),
                (V2, (I.dot1 v)), NONE, L)
        | (c'', Psi, g, (Pi (((Dec (_, V1) as D), I.No), V2), v), NONE, L) ->
            (match traversePos
                     (c'', Psi, g, (V2, (I.comp (v, I.shift))), NONE, L)
             with
             | (NONE, L') ->
                 (match traverseNeg
                          (c'',
                            (I.Decl (Psi, (F.Block (F.CtxBlock (NONE, g))))),
                            (V1, v), L')
                  with
                  | (SOME (w'', d'', (P'', Q'')), L'') ->
                      (NONE, ((P'' (Q'' w'')) :: L''))
                  | (NONE, L'') -> (NONE, L'')))
        | (c'', Psi, g, (V, v), NONE, L) -> (NONE, L) in
      let traverseSig' (c'', L) =
        if (=) c'' (fun r -> r.1) (I.sgnSize ())
        then L
        else
          (match I.sgnLookup c'' with
           | ConDec (name, _, _, _, V, I.Type) ->
               (match traverseNeg (c'', I.Null, (V, I.id), L) with
                | (SOME (wf, d', (P', Q')), L') ->
                    traverseSig' ((c'' + 1), ((P' (Q' wf)) :: L'))
                | (NONE, L') -> traverseSig' ((c'' + 1), L'))
           | _ -> traverseSig' ((c'' + 1), L)) in
      traverseSig' (0, nil)
    let rec convertPro (Ts) =
      let convertOnePro a =
        let V =
          match I.sgnLookup a with
          | ConDec (name, _, _, _, V, I.Kind) -> V
          | _ -> raise (Error "Type Constant declaration expected") in
        let mS =
          match ModeTable.modeLookup a with
          | NONE -> raise (Error "Mode declaration expected")
          | SOME mS -> mS in
        let P = abstract a in P (F.Case (F.Opts (traverse (Ts, a)))) in
      let convertPro' =
        function
        | nil -> raise (Error "Cannot convert Empty program")
        | a::[] -> convertOnePro a
        | a::Ts' -> F.Pair ((convertOnePro a), (convertPro' Ts')) in
      let R = recursion Ts in R (convertPro' Ts)
    let ((convertFor)(* ctxSub (g, s) = (g', s')

       Invariant:
       if   Psi |- g ctx
       and  Psi' |- s : Psi
       then Psi' |- g' ctx
       and  Psi', g' |- s' : g
       and  g' = g [s],  declarationwise defined
    *)
      (* convertFor' (V, mS, w1, w2, n) = (F', F'')

           Invariant:
           If   g |- V = {{g'}} type :kind
           and  g |- w1 : g+
           and  g+, g'+, g- |- w2 : g
           and  g+, g'+, g- |- ^n : g+
           and  mS is a spine for g'
           then F'  is a formula excepting a another formula as argument s.t.
                If g+, g'+ |- F formula,
                then . |- F' F formula
           and  g+, g'+ |- F'' formula
        *)
      (* shiftPlus (mS) = s'

         Invariant:
         s' = ^(# of +'s in mS)
         *)
      (* convertFor L = F'

       Invariant:
       If   L is a list of type families
       then F' is the conjunction of the logical interpretation of each
            type family
     *)
      (* occursInExpN (k, U) = B,

       Invariant:
       If    U in nf
       then  B iff k occurs in U
    *)
      (* no case for Redex, EVar, EClo *)(* no case for FVar *)
      (* no case for SClo *)(* dot1inv w = w'

       Invariant:
       If   g, A |- w : g', A
       then g |- w' : g'
       and  w = 1.w' o ^
    *)
      (* shiftinv (w) = w'

       Invariant:
       If   g, A |- w : g'
       and  1 does not occur in w
       then w  = w' o ^
    *)
      (* domain (G2, w) = n'

       Invariant:
       If   G2 |- w: G1   and w weakening substitution
       then n' = |G1|
    *)
      (* strenghten (Psi, (a, S), w, m) = (Psi', w')

       Invariant:
       If   |- Psi ctx
       and  |- Psi1 ctx      where Psi1 is a subcontext of Psi
       and  |- Psi2 ctx
       and  Sigma (a) = {x1:A1} .. {xn:An} type
       and  Psi |- S : m1{x1:A1} .. mn{xn:An} > type
       and  Psi |- w : Psi1
       and  m mode
       then |- Psi' ctx
       and  Psi |- w' : Psi'
       where Psi' extends Psi1
    *)
      (* testBlock (g, (bw, w1)) = (bw', w')

           Invariant:
           If   |- g ctx
           and  |- G1 ctx
           and  |- G2 ctx
           and  G1 |- w1 : G2, g
           and  bw is a boolean value
           then there ex. a G1'
           s.t. |- G1' ctx
           and  G1' |- w' : G2
           and  bw' = bw or (G1 =/= G1')
         *)
      (* strengthen' (Psi1, Psi2, S, w1) =  (Psi', w')

           Invariant:
           If   |- Psi1 ctx
           and  Psi1 |- Psi2 ctx      (Psi2 is a list to maintain order)
           and  |- Psi3 ctx
           and  Psi1 |- w1 : Psi3     where w1 is a weakening substitution
           and  Psi1, Psi2 |- S : V1 > V2
           then |- Psi' ctx
           and  Psi1 |- w' : Psi'     where w' is a weakening substitution
           where Psi3 < Psi' < Psi1   (Psi' contains all variables of Psi3
                                       and all variables occuring in m
                                       position in S)
        *)
      (* =  I.id *)(* abstract a = P'

       Invariant:
       If   a is a type family
       and  Sigma (a) = {x1:A1}..{xn:An} type
       then for all P s.t.
            +x1:A1, .., +xn:An; . |- P in [[-x1:A1]] .. [[-xn:An]] true
            . ;. |- (P' P) in [[+x1:A1]] .. [[+xn:An]] [[-x1:A1]] .. [[-xn:An]] true
    *)
      (* abstract' ((V, mS), w) = P'

           Invariant:
           If  Sigma (a) = {x1:A1} .. {xn:An} type
           and  Psi |- S : m1{x1:A1} .. mn{xn:An} type > type
           and  Gamma= x1:A1, .. x(j-1):A(j-1)
           and  Gamma |- w : Gamma+
           then P' is a Lam abstraction
        *)
      (* transformInit (Psi, (a, S), w1) = (w', s')

       Invariant:
       If   |- Psi ctx
       and  Sigma (a) = {x1:A1} .. {xn:An} type
       and  Psi |- S : m1{x1:A1} .. mn{xn:An} type > type
       and  Psi |- w1 : Psi+
       then |- Gamma+ ctx
       and  Gamma+ = +x(k1):A(k1), ... +x(km):A(km)
       and  Psi+ |- s' : Gamma+
       and  x1:A1 .. xn:An |- w: Gamma+    (w weakening substitution)
    *)
      (* transformInit' ((S, mS), V, (w, s)) = (w', s')

           Invariant:
           If   Psi |- S : V > type
           and  x1:A1...x(j-1):A(j-1) |- V = mj{xj:Aj} .. mn{xn:An} type : kind
           and  x1:A1...x(j-1):A(j-1) |- w : +x1:A1... +x(j-1):A(j-1)
           and  Psi |- w1 : Psi+
           and  Psi+ |- s : +x1:A1... +x(j-1):A(j-1)
           then x1:A1...xn:An |- w' : +x1:A1... +xn:An
           and  Psi+ |- s' : +x1:A1 .. +xn:An
        *)
      (* transformDec (c'', (Psi+-, G0), d, (a, S), w1, w2, t) = (d', w', s', t', Ds)

       Invariant:
       If   |- Psi ctx
       and  Psi |- G0 ctx
       and  d = |Delta|
       and  Sigma (a) = {x1:A1} .. {xn:An} type
       and  Psi, G0 |- S : m1{x1:A1} .. mn{xn:An} type > type
       and  Psi, G0 |- w1 : Psi+, G0[w1^-1]
       and  Psi |- w2 : Psi+-
       and  Psi+- |- t0 : Psi+
       then |- Gamma+ ctx
       and  Gamma+ = +x(k1):A(k1), ... +x(km):A(km)
       and  Psi |- s' : Gamma+
       and  x1:A1 .. xn:An |- w': Gamma+    (w weakening substitution)
       and  Psi+- |- t' : Psi+, -x(k1):{G0} A(k1), ... -x(km):{G0} A(km)
       and  d' = |Delta'|
    *)
      (* raiseExp (g, U, a) = U'

           Invariant:
           If   |- Psi ctx         (for some given Psi)
           and  Psi |- g ctx
           and  Psi, g |- U : V    (for some V)
           then Psi, g |- [[g]] U : {{g}} V     (wrt subordination)
        *)
      (* raiseExp g = (w', k)

               Invariant:
               If   |-  Psi ctx
               and  Psi |- g ctx
               and  Psi |- g' ctx   which ARE subordinate to a
               then Psi, g |- w : Psi, g'
               and  k is a continuation calculuting the right exprssion:
                    for all U, s.t. Psi, g |- U : V
                    Psi |- [[g']] U : {{g'}} V
            *)
      (* raiseType (g, U, a) = U'

           Invariant:
           If   |- Psi ctx         (for some given Psi)
           and  Psi |- g ctx
           and  Psi, g |- U : V    (for some V)
           then Psi, g |- [[g]] U : {{g}} V     (wrt subordination)
           and  Psi, g, x:{{g}} V |- x g : V
        *)
      (* raiseType (g, n) = (w', k, S')

              Invariant:
              If   |-  Psi ctx
              and  Psi |- g, Gv ctx
              and  Psi |- g' ctx   which ARE subordinate to a
              and  n = |Gv| + 1
              then Psi, g |- w : Psi, g'
              and  k is a continuation calculating the right exprssion:
                   for all U, s.t. Psi, g |- U : V
                   Psi |- [[g']] U : {{g'}} V
              and  k' is a continuation calculating the corresponding spine:
                   for all S, s.t. Psi, g, G0,|- ... refine
            *)
      (* exchangeSub (G0) = s'

           Invariant:
           For some Psi, some g, some V:
           Psi, V, G0 |- s' : Psi, G0, V
        *)
      (* transformDec' (d, (S, mS), V, (z1, z2), (w, t)) = (d', w', t', (Ds+, Ds-))

           Invariant:
           If   Psi, G0 |- S : V > type
           and  S doesn't contain Skolem constants
           and  d = |Delta|
           and  x1:A1...x(j-1):A(j-1) |- V = mj{xj:Aj} .. mn{xn:An} type : kind
           and  x1:A1...x(j-1):A(j-1) |- w : +x1:A1... +x(j-1):A(j-1)
           and  Psi, G0 |- w1 : Psi+, G0[w1^-1]
           and  Psi |- w2 : Psi+-
           and  Psi+- |- t : Psi+, -x1:{{G0}} A1... -xj:{{G0}} Aj
           and  Psi+, -x1:{{G0}} A1...-x(j-1):{{G0}} A(j-1) |- z1: Psi+
           and  Psi+, -x1:{{G0}} A1...-x(j-1):{{G0}} A(j-1), G0 |- z2: x1:A1...x(j-1):A(j-1)
           then x1:A1...xn:An |- w' : +x1:A1... +xn:An
           and  Psi+- |- s' : +x1:A1 .. +xn:An
           and  Psi+- |- t' : Psi+, -x1:{{G0}} A1... -xn:{{G0}} An
           and  d' = |Delta'|
        *)
      (* head Ts (w, t, (d, Dplus, Dminus)) = (d', w', t', P')

             Invariant:
             If   a not in Ts  then d'= d+1,  P' makes a lemma call
             If   Ts = [a]     then d'= d     P' used directly the ih.
             If   Ts = a1 .. ai ... and ai = a
             then d' = d+i   and P' select ih, and then decomposes is, using
                  (i-1) Rights and 1 Left
          *)
      (* transformConc ((a, S), w) = P

       Invariant:
       If   Sigma (a) = {x1:A1} .. {xn:An} type
       and  Psi |- S : m1{x1:A1} .. mn{xn:An} type > type
       and  Psi |- w : PsiAll
       then P is proof term consisting of all - objects of S,
            defined in PsiAll
    *)
      (* traverse (Ts, c) = L'

       Invariant:
       If   Ts is a list of type families
       and  c is a type family which entries are currently traversed
       then L' is a list of cases
    *)
      (* traverseNeg (c'', Psi, (V, v), L) = ([w', d', PQ'], L')    [] means optional

           Invariant:
           If   Psi0 |- V : type
           and  Psi0 |- v : Psi
           and  V[v^-1] does not contain Skolem constants
           and  c'' is the name of the object constant currently considered
           and  L is a list of cases
           then L' list of cases and CL' extends CL
           and  Psi |- w' : Psi'   (Psi' is the context of all variables considered so far)
           and  d' is the length of Delta
           and  PQ'  is a pair, generating the proof term
        *)
      (*                                   (Names.decName (F.makectx Psi, Weaken.strengthenDec (D, v)))),
*)
      (* Clause head found *)(* traversePos (c, Psi, g, (V, v), [w', d', PQ'], L) =  ([w'', d'', PQ''], L'')

           Invariant:
           If   Psi, g |- V : type
           and  Psi, g |- v : Psi'       (s.t.  Psi' |- V[v^-1] : type exists)
           and V[v^-1] does not contain Skolem constants
           [ and Psi', g |- w' : Psi''
             and |Delta'| = d'    for a Delta'
             and PQ' can generate the proof term so far in Delta'; Psi''
           ]
           and  c is the name of the constant currently considered
           and  L is a list of cases
           then L'' list of cases and L'' extends L
           and  Psi |- w'' : Psi2
           and  |Delta''| = d''  for a Delta'
           and  PQ'' can genreate the proof term so far in Delta''; Psi2
        *)
      (* Lemma calls (no context block) *)(* provide typeCheckCtx from typecheck *)
      (* Lemma calls (under a context block) *)(* provide typeCheckCtx from typecheck *)
      (* change w1 to w1' and w2 to w2' below *)(* convertPro Ts = P'

       Invariant:
       If   Ts is a list of type families
       then P' is a conjunction of all programs resulting from converting
            the relational encoding of the function expressed by each type
            family in Ts into functional form
    *))
      = convertFor
    let convertPro = convertPro
    let traverse = traverse
  end ;;
