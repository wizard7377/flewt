
(* Converter from relational representation to a functional
   representation of proof terms *)
(* Author: Carsten Schuermann *)
module type RELFUN  =
  sig
    (*! structure FunSyn : FUNSYN !*)
    exception Error of string 
    val convertFor : IntSyn.cid list -> FunSyn.__For
    val convertPro : IntSyn.cid list -> FunSyn.__Pro
  end;;




(* Converter from relational representation to a functional
   representation of proof terms *)
(* Author: Carsten Schuermann *)
module RelFun(RelFun:sig
                       module Global : GLOBAL
                       module ModeTable : MODETABLE
                       module Names : NAMES
                       module Unify : UNIFY
                       module Whnf : WHNF
                       module Weaken : WEAKEN
                       module TypeCheck : TYPECHECK
                       module FunWeaken : FUNWEAKEN
                       (*! structure FunSyn' : FUNSYN !*)
                       (*! sharing ModeSyn.IntSyn = FunSyn'.IntSyn !*)
                       (*! sharing Names.IntSyn = FunSyn'.IntSyn !*)
                       (*! sharing Unify.IntSyn = FunSyn'.IntSyn !*)
                       (*! sharing Whnf.IntSyn = FunSyn'.IntSyn !*)
                       (*! sharing Weaken.IntSyn = FunSyn'.IntSyn !*)
                       (*! sharing TypeCheck.IntSyn = FunSyn'.IntSyn !*)
                       (*! sharing FunWeaken.FunSyn = FunSyn' !*)
                       module FunNames : FUNNAMES
                     end) : RELFUN =
  struct
    (*! sharing FunNames.FunSyn = FunSyn' !*)
    (*! structure FunSyn = FunSyn' !*)
    exception Error of string 
    module F = FunSyn
    module I = IntSyn
    module M = ModeSyn
    let rec ctxSub =
      function
      | (I.Null, s) -> (I.Null, s)
      | (Decl (__g, __d), s) ->
          let (__g', s') = ctxSub (__g, s) in
          ((I.Decl (__g', (I.decSub (__d, s')))), (I.dot1 s))
    let rec convertOneFor cid =
      let __v =
        match I.sgnLookup cid with
        | ConDec (name, _, _, _, __v, I.Kind) -> __v
        | _ -> raise (Error "Type Constant declaration expected") in
      let mS =
        match ModeTable.modeLookup cid with
        | None -> raise (Error "Mode declaration expected")
        | Some mS -> mS in
      let rec convertFor' =
        function
        | (Pi ((__d, _), __v), Mapp (Marg (M.Plus, _), mS), w1, w2, n) ->
            let (__F', __F'') =
              convertFor'
                (__v, mS, (I.dot1 w1), (I.Dot ((I.Idx n), w2)), (n - 1)) in
            (((function
               | F -> F.All ((F.Prim (Weaken.strengthenDec (__d, w1))), (__F' F)))),
              __F'')
        | (Pi ((__d, _), __v), Mapp (Marg (M.Minus, _), mS), w1, w2, n) ->
            let (__F', __F'') =
              convertFor'
                (__v, mS, (I.comp (w1, I.shift)), (I.dot1 w2), (n + 1)) in
            (__F', (F.Ex ((I.decSub (__d, w2)), __F'')))
        | (Uni (I.Type), M.Mnil, _, _, _) -> (((function | F -> F)), F.True)
        | _ -> raise (Error "type family must be +/- moded") in
      let rec shiftPlus mS =
        let rec shiftPlus' =
          function
          | (M.Mnil, n) -> n
          | (Mapp (Marg (M.Plus, _), mS'), n) -> shiftPlus' (mS', (n + 1))
          | (Mapp (Marg (M.Minus, _), mS'), n) -> shiftPlus' (mS', n) in
        shiftPlus' (mS, 0) in
      let n = shiftPlus mS in
      let (F, __F') = convertFor' (__v, mS, I.id, (I.Shift n), n) in F __F'
    let rec convertFor =
      function
      | nil -> raise (Error "Empty theorem")
      | a::[] -> convertOneFor a
      | a::__l -> F.And ((convertOneFor a), (convertFor __l))
    let rec occursInExpN =
      function
      | (k, Uni _) -> false__
      | (k, Pi (DP, __v)) ->
          (occursInDecP (k, DP)) || (occursInExpN ((k + 1), __v))
      | (k, Root (H, S)) -> (occursInHead (k, H)) || (occursInSpine (k, S))
      | (k, Lam (__d, __v)) ->
          (occursInDec (k, __d)) || (occursInExpN ((k + 1), __v))
      | (k, FgnExp csfe) ->
          I.FgnExpStd.fold csfe
            (function
             | (__u, B) -> B || (occursInExpN (k, (Whnf.normalize (__u, I.id)))))
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
      | (k, App (__u, S)) -> (occursInExpN (k, __u)) || (occursInSpine (k, S))
    let rec occursInDec (k, Dec (_, __v)) = occursInExpN (k, __v)
    let rec occursInDecP (k, (__d, _)) = occursInDec (k, __d)
    let rec occursInExp (k, __u) = occursInExpN (k, (Whnf.normalize (__u, I.id)))
    let rec dot1inv w = Weaken.strengthenSub ((I.comp (I.shift, w)), I.shift)
    let rec shiftinv w = Weaken.strengthenSub (w, I.shift)
    let rec eqIdx = function | (Idx n, Idx k) -> n = k | _ -> false__
    let rec peel w =
      if eqIdx ((I.bvarSub (1, w)), (I.Idx 1)) then dot1inv w else shiftinv w
    let rec peeln =
      function | (0, w) -> w | (n, w) -> peeln ((n - 1), (peel w))
    let rec domain =
      function
      | (__g, Dot (Idx _, s)) -> (domain (__g, s)) + 1
      | (I.Null, Shift 0) -> 0
      | ((Decl _ as __g), Shift 0) ->
          domain (__g, (I.Dot ((I.Idx 1), (I.Shift 1))))
      | (Decl (__g, _), Shift n) -> domain (__g, (I.Shift (n - 1)))
    let rec strengthen (Psi, (a, S), w, m) =
      let mS =
        match ModeTable.modeLookup a with
        | None -> raise (Error "Mode declaration expected")
        | Some mS -> mS in
      let rec args =
        function
        | (I.Nil, M.Mnil) -> nil
        | (App (__u, S'), Mapp (Marg (m', _), mS)) ->
            let __l = args (S', mS) in
            (match M.modeEqual (m, m') with | true__ -> __u :: __l | false__ -> __l) in
      let rec strengthenArgs =
        function
        | (nil, s) -> nil
        | ((__u)::__l, s) ->
            (::) (Weaken.strengthenExp (__u, s)) strengthenArgs (__l, s) in
      let rec occursInArgs =
        function
        | (n, nil) -> false__
        | (n, (__u)::__l) -> (occursInExp (n, __u)) || (occursInArgs (n, __l)) in
      let rec occursInPsi =
        function
        | (n, (nil, __l)) -> occursInArgs (n, __l)
        | (n, ((Prim (Dec (_, __v)))::Psi1, __l)) ->
            (occursInExp (n, __v)) || (occursInPsi ((n + 1), (Psi1, __l)))
        | (n, ((Block (CtxBlock (l, __g)))::Psi1, __l)) ->
            occursInG (n, __g, (function | n' -> occursInPsi (n', (Psi1, __l))))
      and occursInG =
        function
        | (n, I.Null, k) -> k n
        | (n, Decl (__g, Dec (_, __v)), k) ->
            occursInG
              (n, __g,
                (function | n' -> (occursInExp (n', __v)) || (k (n' + 1)))) in
      let rec occursBlock (__g, (Psi2, __l)) =
        let rec occursBlock =
          function
          | (I.Null, n) -> false__
          | (Decl (__g, __d), n) ->
              (occursInPsi (n, (Psi2, __l))) || (occursBlock (__g, (n + 1))) in
        occursBlock (__g, 1) in
      let rec inBlock =
        function
        | (I.Null, (bw, w1)) -> (bw, w1)
        | (Decl (__g, __d), (bw, w1)) ->
            if eqIdx ((I.bvarSub (1, w1)), (I.Idx 1))
            then inBlock (__g, (true__, (dot1inv w1)))
            else inBlock (__g, (bw, (Weaken.strengthenSub (w1, I.shift)))) in
      let rec blockSub =
        function
        | (I.Null, w) -> (I.Null, w)
        | (Decl (__g, Dec (name, __v)), w) ->
            let (__g', w') = blockSub (__g, w) in
            let __v' = Weaken.strengthenExp (__v, w') in
            ((I.Decl (__g', (I.Dec (name, __v')))), (I.dot1 w')) in
      let rec strengthen' =
        function
        | (I.Null, Psi2, __l, w1) -> (I.Null, I.id)
        | (Decl (Psi1, (Prim (Dec (name, __v)) as LD)), Psi2, __l, w1) ->
            let (bw, w1') =
              if eqIdx ((I.bvarSub (1, w1)), (I.Idx 1))
              then (true__, (dot1inv w1))
              else (false__, (Weaken.strengthenSub (w1, I.shift))) in
            if bw || (occursInPsi (1, (Psi2, __l)))
            then
              let (Psi1', w') = strengthen' (Psi1, (LD :: Psi2), __l, w1') in
              let __v' = Weaken.strengthenExp (__v, w') in
              ((I.Decl (Psi1', (F.Prim (I.Dec (name, __v'))))), (I.dot1 w'))
            else
              (let w2 = I.shift in
               let (Psi2', w2') = FunWeaken.strengthenPsi' (Psi2, w2) in
               let __l' = strengthenArgs (__l, w2') in
               let (Psi1'', w') = strengthen' (Psi1, Psi2', __l', w1') in
               (Psi1'', (I.comp (w', I.shift))))
        | (Decl (Psi1, (Block (CtxBlock (name, __g)) as LD)), Psi2, __l, w1) ->
            let (bw, w1') = inBlock (__g, (false__, w1)) in
            if bw || (occursBlock (__g, (Psi2, __l)))
            then
              let (Psi1', w') = strengthen' (Psi1, (LD :: Psi2), __l, w1') in
              let (__g'', w'') = blockSub (__g, w') in
              ((I.Decl (Psi1', (F.Block (F.CtxBlock (name, __g''))))), w'')
            else
              (let w2 = I.Shift (I.ctxLength __g) in
               let (Psi2', w2') = FunWeaken.strengthenPsi' (Psi2, w2) in
               let __l' = strengthenArgs (__l, w2') in
               strengthen' (Psi1, Psi2', __l', w1')) in
      strengthen' (Psi, nil, (args (S, mS)), w)
    let rec recursion (__l) =
      let F = convertFor __l in
      let rec name =
        function
        | a::[] -> I.conDecName (I.sgnLookup a)
        | a::__l -> ((I.conDecName (I.sgnLookup a)) ^ "/") ^ (name __l) in
      function | p -> F.Rec ((F.MDec ((Some (name __l)), F)), p)
    let rec abstract a =
      let mS =
        match ModeTable.modeLookup a with
        | None -> raise (Error "Mode declaration expected")
        | Some mS -> mS in
      let __v =
        match I.sgnLookup a with
        | ConDec (name, _, _, _, __v, I.Kind) -> __v
        | _ -> raise (Error "Type Constant declaration expected") in
      let rec abstract' =
        function
        | ((_, M.Mnil), w) -> (function | p -> p)
        | ((Pi ((__d, _), V2), Mapp (Marg (M.Plus, _), mS)), w) ->
            let __d' = Weaken.strengthenDec (__d, w) in
            let P = abstract' ((V2, mS), (I.dot1 w)) in
            (function | p -> F.Lam ((F.Prim __d'), (P p)))
        | ((Pi (_, V2), Mapp (Marg (M.Minus, _), mS)), w) ->
            abstract' ((V2, mS), (I.comp (w, I.shift))) in
      abstract' ((__v, mS), I.id)
    let rec transformInit (Psi, (a, S), w1) =
      let mS =
        match ModeTable.modeLookup a with
        | None -> raise (Error "Mode declaration expected")
        | Some mS -> mS in
      let __v =
        match I.sgnLookup a with
        | ConDec (name, _, _, _, __v, I.Kind) -> __v
        | _ -> raise (Error "Type Constant declaration expected") in
      let rec transformInit' =
        function
        | ((I.Nil, M.Mnil), Uni (I.Type), (w, s)) -> (w, s)
        | ((App (__u, S), Mapp (Marg (M.Minus, _), mS)), Pi (_, V2), (w, s)) ->
            let w' = I.comp (w, I.shift) in
            let s' = s in transformInit' ((S, mS), V2, (w', s'))
        | ((App (__u, S), Mapp (Marg (M.Plus, _), mS)), Pi
           ((Dec (name, V1), _), V2), (w, s)) ->
            let V1' = Weaken.strengthenExp (V1, w) in
            let w' = I.dot1 w in
            let __u' = Weaken.strengthenExp (__u, w1) in
            let s' = Whnf.dotEta ((I.Exp __u'), s) in
            transformInit' ((S, mS), V2, (w', s')) in
      transformInit' ((S, mS), __v, (I.id, (I.Shift (F.lfctxLength Psi))))
    let rec transformDec (__Ts, (Psi, G0), d, (a, S), w1, w2, t0) =
      let mS =
        match ModeTable.modeLookup a with
        | None -> raise (Error "Mode declaration expected")
        | Some mS -> mS in
      let __v =
        match I.sgnLookup a with
        | ConDec (name, _, _, _, __v, I.Kind) -> __v
        | _ -> raise (Error "Type Constant declaration expected") in
      let rec raiseExp (__g, __u, a) =
        let rec raiseExp' =
          function
          | I.Null -> (I.id, ((function | x -> x)))
          | Decl (__g, (Dec (_, __v) as __d)) ->
              let (w, k) = raiseExp' __g in
              if Subordinate.belowEq ((I.targetFam __v), a)
              then
                ((I.dot1 w),
                  ((function
                    | x -> k (I.Lam ((Weaken.strengthenDec (__d, w)), x)))))
              else ((I.comp (w, I.shift)), k) in
        let (w, k) = raiseExp' __g in k (Weaken.strengthenExp (__u, w)) in
      let rec raiseType (__g, __u, a) =
        let rec raiseType' =
          function
          | (I.Null, n) ->
              (I.id, ((function | x -> x)), ((function | S -> S)))
          | (Decl (__g, (Dec (_, __v) as __d)), n) ->
              let (w, k, k') = raiseType' (__g, (n + 1)) in
              if Subordinate.belowEq ((I.targetFam __v), a)
              then
                ((I.dot1 w),
                  ((function
                    | x ->
                        k
                          (I.Pi (((Weaken.strengthenDec (__d, w)), I.Maybe), x)))),
                  ((function | S -> I.App ((I.Root ((I.BVar n), I.Nil)), S))))
              else ((I.comp (w, I.shift)), k, k') in
        let (w, k, k') = raiseType' (__g, 2) in
        ((k (Weaken.strengthenExp (__u, w))),
          (I.Root ((I.BVar 1), (k' I.Nil)))) in
      let rec exchangeSub (G0) =
        let g0 = I.ctxLength G0 in
        let rec exchangeSub' =
          function
          | (0, s) -> s
          | (k, s) -> exchangeSub' ((k - 1), (I.Dot ((I.Idx k), s))) in
        I.Dot ((I.Idx (g0 + 1)), (exchangeSub' (g0, (I.Shift (g0 + 1))))) in
      let rec transformDec' =
        function
        | (d, (I.Nil, M.Mnil), Uni (I.Type), (z1, z2), (w, t)) ->
            (w, t,
              (d, ((function | (k, __Ds) -> __Ds k)),
                ((function | _ -> F.Empty))))
        | (d, (App (__u, S), Mapp (Marg (M.Minus, _), mS)), Pi
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
            let __U0 = raiseExp (G0, __u, (I.targetFam V1'')) in
            let __u' = Weaken.strengthenExp (__U0, w2) in
            let t' = Whnf.dotEta ((I.Exp __u'), t) in
            let z1' = I.comp (z1, I.shift) in
            let xc = exchangeSub G0 in
            let z2n = I.comp (z2, (I.comp (I.shift, xc))) in
            let Ur' = I.EClo (Ur, xc) in
            let z2' = Whnf.dotEta ((I.Exp Ur'), z2n) in
            let (w'', t'', (d', Dplus, Dminus)) =
              transformDec' ((d + 1), (S, mS), V2, (z1', z2'), (w', t')) in
            (w'', t'',
              (d', Dplus, ((function | k -> F.Split (k, (Dminus 1))))))
        | (d, (App (__u, S), Mapp (Marg (M.Plus, _), mS)), Pi
           ((Dec (name, V1), _), V2), (z1, z2), (w, t)) ->
            let V1' = Weaken.strengthenExp (V1, w) in
            let w' = I.dot1 w in
            let __u' = Weaken.strengthenExp (__u, w1) in
            let t' = t in
            let z1' = F.dot1n (G0, z1) in
            let z2' = I.Dot ((I.Exp (I.EClo (__u', z1'))), z2) in
            let (w'', t'', (d', Dplus, Dminus)) =
              transformDec' ((d + 1), (S, mS), V2, (z1, z2'), (w', t')) in
            (w'', t'',
              (d',
                ((function | (k, __Ds) -> F.App ((k, __u'), (Dplus (1, __Ds))))),
                Dminus)) in
      let (w'', t'', (d', Dplus, Dminus)) =
        transformDec'
          (d, (S, mS), __v,
            (I.id, (I.Shift ((+) (domain (Psi, t0)) I.ctxLength G0))),
            (I.id, t0)) in
      let rec varHead (__Ts) (w'', t'', (d', Dplus, Dminus)) =
        let rec head' =
          function
          | (a'::[], d1, k1) -> (d1, k1)
          | (a'::__Ts', d1, k1) ->
              if a = a'
              then ((d1 + 1), ((function | xx -> F.Left (xx, (k1 1)))))
              else
                (let (d2, k2) = head' (__Ts', (d1 + 1), k1) in
                 (d2, (function | xx -> F.Right (xx, (k2 1))))) in
        let (d2, k2) = head' (__Ts, d', (function | xx -> Dplus (xx, Dminus))) in
        (d2, w'', t'', (k2 d)) in
      let rec lemmaHead (w'', t'', (d', Dplus, Dminus)) =
        let name = I.conDecName (I.sgnLookup a) in
        let l =
          match FunNames.nameLookup name with
          | None -> raise (Error (("Lemma " ^ name) ^ " not defined"))
          | Some lemma -> lemma in
        ((d' + 1), w'', t'', (F.Lemma (l, (Dplus (1, Dminus))))) in
      if List.exists (function | x -> x = a) __Ts
      then varHead __Ts (w'', t'', (d', Dplus, Dminus))
      else lemmaHead (w'', t'', (d', Dplus, Dminus))
    let rec transformConc ((a, S), w) =
      let mS =
        match ModeTable.modeLookup a with
        | None -> raise (Error "Mode declaration expected")
        | Some mS -> mS in
      let rec transformConc' =
        function
        | (I.Nil, M.Mnil) -> F.Unit
        | (App (__u, S'), Mapp (Marg (M.Plus, _), mS')) ->
            transformConc' (S', mS')
        | (App (__u, S'), Mapp (Marg (M.Minus, _), mS')) ->
            F.Inx ((Weaken.strengthenExp (__u, w)), (transformConc' (S', mS'))) in
      transformConc' (S, mS)
    let rec traverse (__Ts, c) =
      let rec traverseNeg =
        function
        | (c'', Psi, (Pi (((Dec (_, V1) as __d), I.Maybe), V2), v), __l) ->
            (match traverseNeg
                     (c'',
                       (I.Decl (Psi, (F.Prim (Weaken.strengthenDec (__d, v))))),
                       (V2, (I.dot1 v)), __l)
             with
             | (Some (w', d', PQ'), __l') -> ((Some ((peel w'), d', PQ')), __l')
             | (None, __l') -> (None, __l'))
        | (c'', Psi, (Pi (((Dec (_, V1) as __d), I.No), V2), v), __l) ->
            (match traverseNeg (c'', Psi, (V2, (I.comp (v, I.shift))), __l)
             with
             | (Some (w', d', PQ'), __l') ->
                 traversePos
                   (c'', Psi, I.Null, ((Weaken.strengthenExp (V1, v)), I.id),
                     (Some (w', d', PQ')), __l')
             | (None, __l') ->
                 traversePos
                   (c'', Psi, I.Null, ((Weaken.strengthenExp (V1, v)), I.id),
                     None, __l'))
        | (c'', Psi, ((Root (Const c', S) as __v), v), __l) ->
            if c = c'
            then
              let S' = Weaken.strengthenSpine (S, v) in
              let (Psi', w') =
                strengthen
                  (Psi, (c', S'), (I.Shift (F.lfctxLength Psi)), M.Plus) in
              let (w'', s'') = transformInit (Psi', (c', S'), w') in
              ((Some
                  (w', 1,
                    ((function | p -> (Psi', s'', p)),
                      (function | wf -> transformConc ((c', S'), wf))))), __l)
            else (None, __l)
      and traversePos =
        function
        | (c'', Psi, __g, (Pi (((Dec (_, V1) as __d), I.Maybe), V2), v), Some
           (w, d, PQ), __l) ->
            (match traversePos
                     (c'', Psi, (I.Decl (__g, (Weaken.strengthenDec (__d, v)))),
                       (V2, (I.dot1 v)), (Some ((I.dot1 w), d, PQ)), __l)
             with
             | (Some (w', d', PQ'), __l') -> ((Some (w', d', PQ')), __l'))
        | (c'', Psi, __g, (Pi (((Dec (_, V1) as __d), I.No), V2), v), Some
           (w, d, PQ), __l) ->
            (match traversePos
                     (c'', Psi, __g, (V2, (I.comp (v, I.shift))),
                       (Some (w, d, PQ)), __l)
             with
             | (Some (w', d', PQ'), __l') ->
                 (match traverseNeg
                          (c'',
                            (I.Decl (Psi, (F.Block (F.CtxBlock (None, __g))))),
                            (V1, v), __l')
                  with
                  | (Some (w'', d'', (__P'', Q'')), __l'') ->
                      ((Some (w', d', PQ')), ((__P'' (Q'' w'')) :: __l''))
                  | (None, __l'') -> ((Some (w', d', PQ')), __l'')))
        | (c'', Psi, I.Null, (__v, v), Some (w1, d, (P, Q)), __l) ->
            let Root (Const a', S) =
              Whnf.normalize ((Weaken.strengthenExp (__v, v)), I.id) in
            let (Psi', w2) = strengthen (Psi, (a', S), w1, M.Minus) in
            let _ =
              if !Global.doubleCheck
              then
                TypeCheck.typeCheck
                  ((F.makectx Psi'), ((I.Uni I.Type), (I.Uni I.Kind)))
              else () in
            let w3 = Weaken.strengthenSub (w1, w2) in
            let (d4, w4, t4, __Ds) =
              transformDec (__Ts, (Psi', I.Null), d, (a', S), w1, w2, w3) in
            ((Some
                (w2, d4,
                  ((function
                    | p -> P (F.Let (__Ds, (F.Case (F.Opts [(Psi', t4, p)]))))),
                    Q))), __l)
        | (c'', Psi, __g, (__v, v), Some (w1, d, (P, Q)), __l) ->
            let Root (Const a', S) = Weaken.strengthenExp (__v, v) in
            let ((Decl (Psi', Block (CtxBlock (name, G2))) as dummy), w2) =
              strengthen
                ((I.Decl (Psi, (F.Block (F.CtxBlock (None, __g))))), (a', S),
                  w1, M.Minus) in
            let _ =
              if !Global.doubleCheck
              then
                TypeCheck.typeCheck
                  ((F.makectx dummy), ((I.Uni I.Type), (I.Uni I.Kind)))
              else () in
            let g = I.ctxLength __g in
            let w1' = peeln (g, w1) in
            let w2' = peeln (g, w2) in
            let (G1, _) = Weaken.strengthenCtx (__g, w1') in
            let w3 = Weaken.strengthenSub (w1', w2') in
            let (d4, w4, t4, __Ds) =
              transformDec (__Ts, (Psi', __g), d, (a', S), w1, w2', w3) in
            ((Some
                (w2', d4,
                  ((function
                    | p ->
                        P
                          (F.Let
                             ((F.New ((F.CtxBlock (None, G1)), __Ds)),
                               (F.Case (F.Opts [(Psi', t4, p)]))))), Q))), __l)
        | (c'', Psi, __g, (Pi (((Dec (_, V1) as __d), I.Maybe), V2), v), None, __l)
            ->
            traversePos
              (c'', Psi, (I.Decl (__g, (Weaken.strengthenDec (__d, v)))),
                (V2, (I.dot1 v)), None, __l)
        | (c'', Psi, __g, (Pi (((Dec (_, V1) as __d), I.No), V2), v), None, __l) ->
            (match traversePos
                     (c'', Psi, __g, (V2, (I.comp (v, I.shift))), None, __l)
             with
             | (None, __l') ->
                 (match traverseNeg
                          (c'',
                            (I.Decl (Psi, (F.Block (F.CtxBlock (None, __g))))),
                            (V1, v), __l')
                  with
                  | (Some (w'', d'', (__P'', Q'')), __l'') ->
                      (None, ((__P'' (Q'' w'')) :: __l''))
                  | (None, __l'') -> (None, __l'')))
        | (c'', Psi, __g, (__v, v), None, __l) -> (None, __l) in
      let rec traverseSig' (c'', __l) =
        if (=) c'' (fun (r, _) -> r) (I.sgnSize ())
        then __l
        else
          (match I.sgnLookup c'' with
           | ConDec (name, _, _, _, __v, I.Type) ->
               (match traverseNeg (c'', I.Null, (__v, I.id), __l) with
                | (Some (wf, d', (__P', Q')), __l') ->
                    traverseSig' ((c'' + 1), ((__P' (Q' wf)) :: __l'))
                | (None, __l') -> traverseSig' ((c'' + 1), __l'))
           | _ -> traverseSig' ((c'' + 1), __l)) in
      traverseSig' (0, nil)
    let rec convertPro (__Ts) =
      let rec convertOnePro a =
        let __v =
          match I.sgnLookup a with
          | ConDec (name, _, _, _, __v, I.Kind) -> __v
          | _ -> raise (Error "Type Constant declaration expected") in
        let mS =
          match ModeTable.modeLookup a with
          | None -> raise (Error "Mode declaration expected")
          | Some mS -> mS in
        let P = abstract a in P (F.Case (F.Opts (traverse (__Ts, a)))) in
      let rec convertPro' =
        function
        | nil -> raise (Error "Cannot convert Empty program")
        | a::[] -> convertOnePro a
        | a::__Ts' -> F.Pair ((convertOnePro a), (convertPro' __Ts')) in
      let R = recursion __Ts in R (convertPro' __Ts)
    (* ctxSub (__g, s) = (__g', s')

       Invariant:
       if   Psi |- __g ctx
       and  Psi' |- s : Psi
       then Psi' |- __g' ctx
       and  Psi', __g' |- s' : __g
       and  __g' = __g [s],  declarationwise defined
    *)
    (* convertFor' (__v, mS, w1, w2, n) = (__F', __F'')

           Invariant:
           If   __g |- __v = {{__g'}} type :kind
           and  __g |- w1 : __g+
           and  __g+, __g'+, __g- |- w2 : __g
           and  __g+, __g'+, __g- |- ^n : __g+
           and  mS is a spine for __g'
           then __F'  is a formula excepting a another formula as argument s.t.
                If __g+, __g'+ |- F formula,
                then . |- __F' F formula
           and  __g+, __g'+ |- __F'' formula
        *)
    (* shiftPlus (mS) = s'

         Invariant:
         s' = ^(# of +'s in mS)
         *)
    (* convertFor __l = __F'

       Invariant:
       If   __l is a list of type families
       then __F' is the conjunction of the logical interpretation of each
            type family
     *)
    (* occursInExpN (k, __u) = B,

       Invariant:
       If    __u in nf
       then  B iff k occurs in __u
    *)
    (* no case for Redex, EVar, EClo *)
    (* no case for FVar *)
    (* no case for SClo *)
    (* dot1inv w = w'

       Invariant:
       If   __g, A |- w : __g', A
       then __g |- w' : __g'
       and  w = 1.w' o ^
    *)
    (* shiftinv (w) = w'

       Invariant:
       If   __g, A |- w : __g'
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
    (* testBlock (__g, (bw, w1)) = (bw', w')

           Invariant:
           If   |- __g ctx
           and  |- G1 ctx
           and  |- G2 ctx
           and  G1 |- w1 : G2, __g
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
    (* =  I.id *)
    (* abstract a = __P'

       Invariant:
       If   a is a type family
       and  Sigma (a) = {x1:A1}..{xn:An} type
       then for all P s.t.
            +x1:A1, .., +xn:An; . |- P in [[-x1:A1]] .. [[-xn:An]] true
            . ;. |- (__P' P) in [[+x1:A1]] .. [[+xn:An]] [[-x1:A1]] .. [[-xn:An]] true
    *)
    (* abstract' ((__v, mS), w) = __P'

           Invariant:
           If  Sigma (a) = {x1:A1} .. {xn:An} type
           and  Psi |- S : m1{x1:A1} .. mn{xn:An} type > type
           and  Gamma= x1:A1, .. x(j-1):A(j-1)
           and  Gamma |- w : Gamma+
           then __P' is a Lam abstraction
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
    (* transformInit' ((S, mS), __v, (w, s)) = (w', s')

           Invariant:
           If   Psi |- S : __v > type
           and  x1:A1...x(j-1):A(j-1) |- __v = mj{xj:Aj} .. mn{xn:An} type : kind
           and  x1:A1...x(j-1):A(j-1) |- w : +x1:A1... +x(j-1):A(j-1)
           and  Psi |- w1 : Psi+
           and  Psi+ |- s : +x1:A1... +x(j-1):A(j-1)
           then x1:A1...xn:An |- w' : +x1:A1... +xn:An
           and  Psi+ |- s' : +x1:A1 .. +xn:An
        *)
    (* transformDec (c'', (Psi+-, G0), d, (a, S), w1, w2, t) = (d', w', s', t', __Ds)

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
    (* raiseExp (__g, __u, a) = __u'

           Invariant:
           If   |- Psi ctx         (for some given Psi)
           and  Psi |- __g ctx
           and  Psi, __g |- __u : __v    (for some __v)
           then Psi, __g |- [[__g]] __u : {{__g}} __v     (wrt subordination)
        *)
    (* raiseExp __g = (w', k)

               Invariant:
               If   |-  Psi ctx
               and  Psi |- __g ctx
               and  Psi |- __g' ctx   which ARE subordinate to a
               then Psi, __g |- w : Psi, __g'
               and  k is a continuation calculuting the right exprssion:
                    for all __u, s.t. Psi, __g |- __u : __v
                    Psi |- [[__g']] __u : {{__g'}} __v
            *)
    (* raiseType (__g, __u, a) = __u'

           Invariant:
           If   |- Psi ctx         (for some given Psi)
           and  Psi |- __g ctx
           and  Psi, __g |- __u : __v    (for some __v)
           then Psi, __g |- [[__g]] __u : {{__g}} __v     (wrt subordination)
           and  Psi, __g, x:{{__g}} __v |- x __g : __v
        *)
    (* raiseType (__g, n) = (w', k, S')

              Invariant:
              If   |-  Psi ctx
              and  Psi |- __g, Gv ctx
              and  Psi |- __g' ctx   which ARE subordinate to a
              and  n = |Gv| + 1
              then Psi, __g |- w : Psi, __g'
              and  k is a continuation calculating the right exprssion:
                   for all __u, s.t. Psi, __g |- __u : __v
                   Psi |- [[__g']] __u : {{__g'}} __v
              and  k' is a continuation calculating the corresponding spine:
                   for all S, s.t. Psi, __g, G0,|- ... refine
            *)
    (* exchangeSub (G0) = s'

           Invariant:
           For some Psi, some __g, some __v:
           Psi, __v, G0 |- s' : Psi, G0, __v
        *)
    (* transformDec' (d, (S, mS), __v, (z1, z2), (w, t)) = (d', w', t', (__Ds+, __Ds-))

           Invariant:
           If   Psi, G0 |- S : __v > type
           and  S doesn't contain Skolem constants
           and  d = |Delta|
           and  x1:A1...x(j-1):A(j-1) |- __v = mj{xj:Aj} .. mn{xn:An} type : kind
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
    (* head __Ts (w, t, (d, Dplus, Dminus)) = (d', w', t', __P')

             Invariant:
             If   a not in __Ts  then d'= d+1,  __P' makes a lemma call
             If   __Ts = [a]     then d'= d     __P' used directly the ih.
             If   __Ts = a1 .. ai ... and ai = a
             then d' = d+i   and __P' select ih, and then decomposes is, using
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
    (* traverse (__Ts, c) = __l'

       Invariant:
       If   __Ts is a list of type families
       and  c is a type family which entries are currently traversed
       then __l' is a list of cases
    *)
    (* traverseNeg (c'', Psi, (__v, v), __l) = ([w', d', PQ'], __l')    [] means optional

           Invariant:
           If   Psi0 |- __v : type
           and  Psi0 |- v : Psi
           and  __v[v^-1] does not contain Skolem constants
           and  c'' is the name of the object constant currently considered
           and  __l is a list of cases
           then __l' list of cases and CL' extends CL
           and  Psi |- w' : Psi'   (Psi' is the context of all variables considered so far)
           and  d' is the length of Delta
           and  PQ'  is a pair, generating the proof term
        *)
    (*                                   (Names.decName (F.makectx Psi, Weaken.strengthenDec (__d, v)))),
*)
    (* Clause head found *)
    (* traversePos (c, Psi, __g, (__v, v), [w', d', PQ'], __l) =  ([w'', d'', PQ''], __l'')

           Invariant:
           If   Psi, __g |- __v : type
           and  Psi, __g |- v : Psi'       (s.t.  Psi' |- __v[v^-1] : type exists)
           and __v[v^-1] does not contain Skolem constants
           [ and Psi', __g |- w' : Psi''
             and |Delta'| = d'    for a Delta'
             and PQ' can generate the proof term so far in Delta'; Psi''
           ]
           and  c is the name of the constant currently considered
           and  __l is a list of cases
           then __l'' list of cases and __l'' extends __l
           and  Psi |- w'' : Psi2
           and  |Delta''| = d''  for a Delta'
           and  PQ'' can genreate the proof term so far in Delta''; Psi2
        *)
    (* Lemma calls (no context block) *)
    (* provide typeCheckCtx from typecheck *)
    (* Lemma calls (under a context block) *)
    (* provide typeCheckCtx from typecheck *)
    (* change w1 to w1' and w2 to w2' below *)
    (* convertPro __Ts = __P'

       Invariant:
       If   __Ts is a list of type families
       then __P' is a conjunction of all programs resulting from converting
            the relational encoding of the function expressed by each type
            family in __Ts into functional form
    *)
    let convertFor = convertFor
    let convertPro = convertPro
    let traverse = traverse
  end ;;
