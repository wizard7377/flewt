
(* Converter from relational representation to a functional
   representation of proof terms *)
(* Author: Carsten Schuermann *)
module type CONVERTER  =
  sig
    (*! structure IntSyn : INTSYN !*)
    (*! structure Tomega : TOMEGA !*)
    exception Error of string 
    exception Error' of Tomega.__Sub 
    val convertFor : IntSyn.cid list -> Tomega.__For
    val convertPrg : IntSyn.cid list -> Tomega.__Prg
    val installPrg :
      IntSyn.cid list -> (IntSyn.cid * Tomega.lemma list * Tomega.lemma list)
    (* projections *)
    (* selections *)
    val convertGoal :
      (Tomega.__Dec IntSyn.__Ctx * IntSyn.__Exp) -> Tomega.__Prg
  end;;




(* Converter from relational representation to a functional
   representation of proof terms *)
(* Author: Carsten Schuermann *)
module Converter(Converter:sig
                             module Global : GLOBAL
                             module Abstract : ABSTRACT
                             module ModeTable : MODETABLE
                             module Names : NAMES
                             module Unify : UNIFY
                             module Whnf : WHNF
                             module Print : PRINT
                             module TomegaPrint : TOMEGAPRINT
                             module WorldSyn : WORLDSYN
                             module Worldify : WORLDIFY
                             module TomegaTypeCheck : TOMEGATYPECHECK
                             module Subordinate : SUBORDINATE
                             module TypeCheck : TYPECHECK
                             module Redundant : REDUNDANT
                             (*! structure IntSyn' : INTSYN !*)
                             (*! structure Tomega' : TOMEGA !*)
                             (*! sharing Tomega'.IntSyn = IntSyn' !*)
                             (*! sharing Abstract.IntSyn = IntSyn' !*)
                             (*! sharing ModeSyn.IntSyn = IntSyn' !*)
                             (*! sharing Names.IntSyn = IntSyn' !*)
                             (*! sharing Unify.IntSyn = IntSyn' !*)
                             (*! sharing Whnf.IntSyn = IntSyn' !*)
                             (*! sharing Print.IntSyn = IntSyn' !*)
                             (*! sharing TomegaPrint.IntSyn = IntSyn' !*)
                             (*! sharing TomegaPrint.Tomega = Tomega' !*)
                             (*! sharing WorldSyn.IntSyn = IntSyn' !*)
                             (*! sharing WorldSyn.Tomega = Tomega' !*)
                             (*! sharing Worldify.IntSyn = IntSyn' !*)
                             (*! sharing Worldify.Tomega = Tomega' !*)
                             (*! sharing TomegaTypeCheck.IntSyn = IntSyn' !*)
                             (*! sharing TomegaTypeCheck.Tomega = Tomega' !*)
                             (*! sharing Subordinate.IntSyn = IntSyn' !*)
                             (*! sharing TypeCheck.IntSyn = IntSyn' !*)
                             module TomegaAbstract : TOMEGAABSTRACT
                           end) : CONVERTER =
  struct
    (*! structure IntSyn = IntSyn' !*)
    (*! structure Tomega = Tomega' !*)
    exception Error of string 
    exception Error' of Tomega.__Sub 
    module T = Tomega
    module I = IntSyn
    module M = ModeSyn
    module S = Subordinate
    module A = Abstract
    module TA = TomegaAbstract
    let rec isIdx1 = function | Idx 1 -> true__ | _ -> false__
    let rec modeSpine a =
      match ModeTable.modeLookup a with
      | NONE -> raise (Error "Mode declaration expected")
      | SOME mS -> mS
    let rec typeOf a =
      match I.sgnLookup a with
      | ConDec (name, _, _, _, V, I.Kind) -> V
      | _ -> raise (Error "Type Constant declaration expected")
    let rec nameOf a =
      match I.sgnLookup a with
      | ConDec (name, _, _, _, V, I.Kind) -> name
      | _ -> raise (Error "Type Constant declaration expected")
    let rec chatter chlev f =
      if (!Global.chatter) >= chlev then print ((^) "[tomega] " f ()) else ()
    let rec strengthenExp (U, s) =
      Whnf.normalize ((Whnf.cloInv (U, s)), I.id)
    let rec strengthenSub (s, t) = Whnf.compInv (s, t)
    let rec strengthenDec =
      function
      | (Dec (name, V), s) -> I.Dec (name, (strengthenExp (V, s)))
      | (BDec (name, (L, t)), s) ->
          I.BDec (name, (L, (strengthenSub (t, s))))
    let rec strengthenCtx =
      function
      | (I.Null, s) -> (I.Null, s)
      | (Decl (G, D), s) ->
          let (G', s') = strengthenCtx (G, s) in
          ((I.Decl (G', (strengthenDec (D, s')))), (I.dot1 s'))
    let rec strengthenFor =
      function
      | (T.True, s) -> T.True
      | (And (F1, F2), s) ->
          T.And ((strengthenFor (F1, s)), (strengthenFor (F2, s)))
      | (All ((UDec (D), Q), F), s) ->
          T.All
            (((T.UDec (strengthenDec (D, s))), Q),
              (strengthenFor (F, (I.dot1 s))))
      | (Ex ((D, Q), F), s) ->
          T.Ex (((strengthenDec (D, s)), Q), (strengthenFor (F, (I.dot1 s))))
    let rec strengthenOrder =
      function
      | (Arg ((U, s1), (V, s2)), s) ->
          Order.Arg
            ((U, (strengthenSub (s1, s))), (V, (strengthenSub (s2, s))))
      | (Simul (Os), s) ->
          Order.Simul (map (function | O -> strengthenOrder (O, s)) Os)
      | (Lex (Os), s) ->
          Order.Lex (map (function | O -> strengthenOrder (O, s)) Os)
    let rec strengthenTC =
      function
      | (Base (O), s) -> T.Base (strengthenOrder (O, s))
      | (Conj (TC1, TC2), s) ->
          T.Conj ((strengthenTC (TC1, s)), (strengthenTC (TC2, s)))
      | (Abs (D, TC), s) ->
          T.Abs ((strengthenDec (D, s)), (strengthenTC (TC, (I.dot1 s))))
    let rec strengthenSpine =
      function
      | (I.Nil, t) -> I.Nil
      | (App (U, S), t) ->
          I.App ((strengthenExp (U, t)), (strengthenSpine (S, t)))
    let rec strengthenPsi =
      function
      | (I.Null, s) -> (I.Null, s)
      | (Decl (Psi, UDec (D)), s) ->
          let (Psi', s') = strengthenPsi (Psi, s) in
          ((I.Decl (Psi', (T.UDec (strengthenDec (D, s'))))), (I.dot1 s'))
      | (Decl (Psi, PDec (name, F, NONE, NONE)), s) ->
          let (Psi', s') = strengthenPsi (Psi, s) in
          ((I.Decl
              (Psi', (T.PDec (name, (strengthenFor (F, s')), NONE, NONE)))),
            (I.dot1 s'))
    let rec strengthenPsi' =
      function
      | (nil, s) -> (nil, s)
      | ((UDec (D))::Psi, s) ->
          let D' = strengthenDec (D, s) in
          let s' = I.dot1 s in
          let (Psi'', s'') = strengthenPsi' (Psi, s') in
          (((T.UDec D') :: Psi''), s'')
    let rec ctxSub =
      function
      | (I.Null, s) -> (I.Null, s)
      | (Decl (G, D), s) ->
          let (G', s') = ctxSub (G, s) in
          ((I.Decl (G', (I.decSub (D, s')))), (I.dot1 s))
    let rec validMode =
      function
      | M.Mnil -> ()
      | Mapp (Marg (M.Plus, _), mS) -> validMode mS
      | Mapp (Marg (M.Minus, _), mS) -> validMode mS
      | Mapp (Marg (M.Star, _), mS) ->
          raise (Error "+ or - mode expected, * found")
    let rec validSig =
      function
      | (Psi0, nil) -> ()
      | (Psi0, (G, V)::Sig) ->
          let rec append =
            function
            | (G, I.Null) -> G
            | (G, Decl (G', D)) -> I.Decl ((append (G, G')), D) in
          (TypeCheck.typeCheck
             ((T.coerceCtx (append (Psi0, (T.embedCtx G)))),
               (V, (I.Uni I.Type)));
           validSig (Psi0, Sig))
    let rec convertOneFor cid =
      let V =
        match I.sgnLookup cid with
        | ConDec (name, _, _, _, V, I.Kind) -> V
        | _ -> raise (Error "Type Constant declaration expected") in
      let mS =
        match ModeTable.modeLookup cid with
        | NONE -> raise (Error "Mode declaration expected")
        | SOME mS -> mS in
      let _ = validMode mS in
      let rec convertFor' =
        function
        | (Pi ((D, _), V), Mapp (Marg (M.Plus, _), mS), w1, w2, n) ->
            let (F', F'') =
              convertFor'
                (V, mS, (I.dot1 w1), (I.Dot ((I.Idx n), w2)), (n - 1)) in
            (((function
               | F ->
                   T.All
                     (((T.UDec (strengthenDec (D, w1))), T.Explicit), (F' F)))),
              F'')
        | (Pi ((D, _), V), Mapp (Marg (M.Minus, _), mS), w1, w2, n) ->
            let (F', F'') =
              convertFor'
                (V, mS, (I.comp (w1, I.shift)), (I.dot1 w2), (n + 1)) in
            (F', (T.Ex (((I.decSub (D, w2)), T.Explicit), F'')))
        | (Uni (I.Type), M.Mnil, _, _, _) -> (((function | F -> F)), T.True)
        | _ -> raise (Error "type family must be +/- moded") in
      let rec shiftPlus mS =
        let rec shiftPlus' =
          function
          | (M.Mnil, n) -> n
          | (Mapp (Marg (M.Plus, _), mS'), n) -> shiftPlus' (mS', (n + 1))
          | (Mapp (Marg (M.Minus, _), mS'), n) -> shiftPlus' (mS', n) in
        shiftPlus' (mS, 0) in
      let n = shiftPlus mS in
      let (F, F') = convertFor' (V, mS, I.id, (I.Shift n), n) in F F'
    let rec createIH =
      function
      | nil -> raise (Error "Empty theorem")
      | a::[] ->
          let name = I.conDecName (I.sgnLookup a) in
          let F = convertOneFor a in (name, F)
      | a::L ->
          let name = I.conDecName (I.sgnLookup a) in
          let F = convertOneFor a in
          let (name', F') = createIH L in
          (((name ^ "/") ^ name'), (T.And (F, F')))
    let rec convertFor (L) = let (_, F') = createIH L in F'
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
             | (U, DP) -> DP || (occursInExp (k, (Whnf.normalize (U, I.id)))))
            false__
    let rec occursInHead =
      function
      | (k, BVar k') -> k = k'
      | (k, Const _) -> false__
      | (k, Def _) -> false__
      | (k, FgnConst _) -> false__
      | (k, Proj _) -> false__
    let rec occursInSpine =
      function
      | (_, I.Nil) -> false__
      | (k, App (U, S)) -> (occursInExpN (k, U)) || (occursInSpine (k, S))
    let rec occursInDec (k, Dec (_, V)) = occursInExpN (k, V)
    let rec occursInDecP (k, (D, _)) = occursInDec (k, D)
    let rec occursInExp (k, U) = occursInExpN (k, (Whnf.normalize (U, I.id)))
    let rec dot1inv w = strengthenSub ((I.comp (I.shift, w)), I.shift)
    let rec shiftinv w = strengthenSub (w, I.shift)
    let rec peel w =
      if isIdx1 (I.bvarSub (1, w)) then dot1inv w else shiftinv w
    let rec peeln =
      function | (0, w) -> w | (n, w) -> peeln ((n - 1), (peel w))
    let rec popn =
      function
      | (0, Psi) -> (Psi, I.Null)
      | (n, Decl (Psi, UDec (D))) ->
          let (Psi', G') = popn ((n - 1), Psi) in (Psi', (I.Decl (G', D)))
    let rec domain =
      function
      | (G, Dot (Idx _, s)) -> (domain (G, s)) + 1
      | (I.Null, Shift 0) -> 0
      | ((Decl _ as G), Shift 0) ->
          domain (G, (I.Dot ((I.Idx 1), (I.Shift 1))))
      | (Decl (G, _), Shift n) -> domain (G, (I.Shift (n - 1)))
    let rec strengthen (Psi, (a, S), w, m) =
      let mS = modeSpine a in
      let rec args =
        function
        | (I.Nil, M.Mnil) -> nil
        | (App (U, S'), Mapp (Marg (m', _), mS)) ->
            let L = args (S', mS) in
            (match M.modeEqual (m, m') with | true__ -> U :: L | false__ -> L) in
      let rec strengthenArgs =
        function
        | (nil, s) -> nil
        | ((U)::L, s) -> (::) (strengthenExp (U, s)) strengthenArgs (L, s) in
      let rec occursInArgs =
        function
        | (n, nil) -> false__
        | (n, (U)::L) -> (occursInExp (n, U)) || (occursInArgs (n, L)) in
      let rec occursInPsi =
        function
        | (n, (nil, L)) -> occursInArgs (n, L)
        | (n, ((UDec (Dec (_, V)))::Psi1, L)) ->
            (occursInExp (n, V)) || (occursInPsi ((n + 1), (Psi1, L)))
        | (n, ((UDec (BDec (_, (cid, s))))::Psi1, L)) ->
            let BlockDec (_, _, G, _) = I.sgnLookup cid in
            (occursInSub (n, s, G)) || (occursInPsi ((n + 1), (Psi1, L)))
      and occursInSub =
        function
        | (_, _, I.Null) -> false__
        | (n, Shift k, G) ->
            occursInSub (n, (I.Dot ((I.Idx (k + 1)), (I.Shift (k + 1)))), G)
        | (n, Dot (Idx k, s), Decl (G, _)) ->
            (n = k) || (occursInSub (n, s, G))
        | (n, Dot (Exp (U), s), Decl (G, _)) ->
            (occursInExp (n, U)) || (occursInSub (n, s, G))
        | (n, Dot (Block _, s), Decl (G, _)) -> occursInSub (n, s, G)
      and occursInG =
        function
        | (n, I.Null, k) -> k n
        | (n, Decl (G, Dec (_, V)), k) ->
            occursInG
              (n, G,
                (function | n' -> (occursInExp (n', V)) || (k (n' + 1)))) in
      let rec occursBlock (G, (Psi2, L)) =
        let rec occursBlock =
          function
          | (I.Null, n) -> false__
          | (Decl (G, D), n) ->
              (occursInPsi (n, (Psi2, L))) || (occursBlock (G, (n + 1))) in
        occursBlock (G, 1) in
      let rec inBlock =
        function
        | (I.Null, (bw, w1)) -> (bw, w1)
        | (Decl (G, D), (bw, w1)) ->
            if isIdx1 (I.bvarSub (1, w1))
            then inBlock (G, (true__, (dot1inv w1)))
            else inBlock (G, (bw, (strengthenSub (w1, I.shift)))) in
      let rec blockSub =
        function
        | (I.Null, w) -> (I.Null, w)
        | (Decl (G, Dec (name, V)), w) ->
            let (G', w') = blockSub (G, w) in
            let V' = strengthenExp (V, w') in
            ((I.Decl (G', (I.Dec (name, V')))), (I.dot1 w')) in
      let rec strengthen' =
        function
        | (I.Null, Psi2, L, w1) -> (I.Null, I.id, I.id)
        | (Decl (Psi1, (UDec (Dec (name, V)) as LD)), Psi2, L, w1) ->
            if isIdx1 (I.bvarSub (1, w1))
            then
              let w1' = dot1inv w1 in
              let (Psi1', w', z') = strengthen' (Psi1, (LD :: Psi2), L, w1') in
              let V' = strengthenExp (V, w') in
              ((I.Decl (Psi1', (T.UDec (I.Dec (name, V'))))), (I.dot1 w'),
                (I.dot1 z'))
            else
              if occursInPsi (1, (Psi2, L))
              then
                (let w1' = strengthenSub (w1, I.shift) in
                 let (Psi1', w', z') =
                   strengthen' (Psi1, (LD :: Psi2), L, w1') in
                 let V' = strengthenExp (V, w') in
                 ((I.Decl (Psi1', (T.UDec (I.Dec (name, V'))))), (I.dot1 w'),
                   (I.comp (z', I.shift))))
              else
                (let w1' = strengthenSub (w1, I.shift) in
                 let w2 = I.shift in
                 let (Psi2', w2') = strengthenPsi' (Psi2, w2) in
                 let L' = strengthenArgs (L, w2') in
                 let (Psi1'', w', z') = strengthen' (Psi1, Psi2', L', w1') in
                 (Psi1'', (I.comp (w', I.shift)), z'))
        | (Decl (Psi1, (PDec (name, F, NONE, NONE) as D)), Psi2, L, w1) ->
            let w1' = dot1inv w1 in
            let (Psi1', w', z') = strengthen' (Psi1, (D :: Psi2), L, w1') in
            let F' = strengthenFor (F, w') in
            ((I.Decl (Psi1', (T.PDec (name, F', NONE, NONE)))), (I.dot1 w'),
              (I.dot1 z'))
        | (Decl (Psi1, (UDec (BDec (name, (cid, s))) as LD)), Psi2, L, w1) ->
            let w1' = dot1inv w1 in
            let (Psi1', w', z') = strengthen' (Psi1, (LD :: Psi2), L, w1') in
            let s' = strengthenSub (s, w') in
            ((I.Decl (Psi1', (T.UDec (I.BDec (name, (cid, s')))))),
              (I.dot1 w'), (I.dot1 z')) in
      strengthen' (Psi, nil, (args (S, mS)), w)
    let rec lookupIH (Psi, L, a) =
      let rec lookupIH' (b::L, a, k) =
        if a = b then k else lookupIH' (L, a, (k - 1)) in
      lookupIH' (L, a, (I.ctxLength Psi))
    let rec createIHSub (Psi, L) = T.Shift ((I.ctxLength Psi) - 1)
    let rec transformInit (Psi, L, (a, S), w1) =
      let mS = modeSpine a in
      let V = typeOf a in
      let rec transformInit' =
        function
        | ((I.Nil, M.Mnil), Uni (I.Type), (w, s)) -> (w, s)
        | ((App (U, S), Mapp (Marg (M.Minus, _), mS)), Pi (_, V2), (w, s)) ->
            let w' = I.comp (w, I.shift) in
            let s' = s in transformInit' ((S, mS), V2, (w', s'))
        | ((App (U, S), Mapp (Marg (M.Plus, _), mS)), Pi
           ((Dec (name, V1), _), V2), (w, s)) ->
            let V1' = strengthenExp (V1, w) in
            let w' = I.dot1 w in
            let U' = strengthenExp (U, w1) in
            let s' = T.dotEta ((T.Exp U'), s) in
            transformInit' ((S, mS), V2, (w', s')) in
      transformInit' ((S, mS), V, (I.id, (createIHSub (Psi, L))))
    let rec transformConc ((a, S), w) =
      let rec transformConc' =
        function
        | (I.Nil, M.Mnil) -> T.Unit
        | (App (U, S'), Mapp (Marg (M.Plus, _), mS')) ->
            transformConc' (S', mS')
        | (App (U, S'), Mapp (Marg (M.Minus, _), mS')) ->
            T.PairExp ((strengthenExp (U, w)), (transformConc' (S', mS'))) in
      transformConc' (S, (modeSpine a))
    let rec renameExp arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (f, (Uni _ as U)) -> U
      | (f, Pi ((D, DP), V)) -> I.Pi (((renameDec f D), DP), (renameExp f V))
      | (f, Root (H, S)) -> I.Root ((renameHead f H), (renameSpine f S))
      | (f, Lam (D, U)) -> I.Lam ((renameDec f D), (renameExp f U))
    let rec renameDec f (Dec (x, V)) = I.Dec (x, (renameExp f V))
    let rec renameHead arg__0 arg__1 =
      match (arg__0, arg__1) with | (f, Proj bi) -> f bi | (f, H) -> H
    let rec renameSpine arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (f, I.Nil) -> I.Nil
      | (f, App (U, S)) -> I.App ((renameExp f U), (renameSpine f S))
    let rec rename (BDec (_, (c, s)), V) =
      let (G, L) = I.constBlock c in
      let rec makeSubst =
        function
        | (n, G, s, nil, f) -> (G, f)
        | (n, G, s, (Dec (x, V') as D)::L, f) ->
            if Subordinate.belowEq ((I.targetFam V'), (I.targetFam V))
            then
              makeSubst
                ((n + 1), (I.Decl (G, (I.decSub (D, s)))), (I.dot1 s), L, f)
            else makeSubst (n, G, (I.comp (s, I.shift)), L, f) in
      let (G', f) = makeSubst (1, G, s, L, (function | x -> I.Proj x)) in
      (G, (renameExp f V))
    let rec append =
      function
      | (G, I.Null) -> G
      | (G, Decl (G', D)) -> I.Decl ((append (G, G')), D)
    let rec traverseNeg arg__0 arg__1 =
      match (arg__0, arg__1) with
      | ((L, wmap, projs),
         ((Psi0, Psi), Pi (((Dec (_, V1) as D), I.Maybe), V2), w)) ->
          (match traverseNeg (L, wmap, projs)
                   ((Psi0, (I.Decl (Psi, (T.UDec D)))), V2, (I.dot1 w))
           with
           | SOME (w', PQ') -> SOME ((peel w'), PQ'))
      | ((L, wmap, projs),
         ((Psi0, Psi), Pi (((Dec (_, V1) as D), I.No), V2), w)) ->
          (match traverseNeg (L, wmap, projs)
                   ((Psi0, (I.Decl (Psi, (T.UDec D)))), V2,
                     (I.comp (w, I.shift)))
           with
           | SOME (w', PQ') ->
               traversePos (L, wmap, projs)
                 ((Psi0, Psi, I.Null), V1, (SOME ((peel w'), PQ'))))
      | ((L, wmap, projs), ((Psi0, Psi), Root (Const a, S), w)) ->
          let Psi1 = append (Psi0, Psi) in
          let w0 = I.Shift (I.ctxLength Psi) in
          let (Psi', w', _) = strengthen (Psi1, (a, S), w0, M.Plus) in
          let (w'', s'') = transformInit (Psi', L, (a, S), w') in
          let _ = TomegaTypeCheck.checkCtx Psi' in
          SOME
            (w',
              ((function | P -> (Psi', s'', P)), (transformConc ((a, S), w))))
    let rec traversePos arg__0 arg__1 =
      match (arg__0, arg__1) with
      | ((L, wmap, projs),
         ((Psi0, Psi, G), Pi (((BDec (x, (c, s)) as D), _), V), SOME
          (w1, (P, Q)))) ->
          let c' = wmap c in
          let n = (+) (I.ctxLength Psi0) I.ctxLength G in
          let (Gsome, Lpi) = I.constBlock c in
          let _ =
            TypeCheck.typeCheckCtx
              (T.coerceCtx (append ((append (Psi0, Psi)), (T.embedCtx G)))) in
          let _ =
            TypeCheck.typeCheckSub
              ((T.coerceCtx (append ((append (Psi0, Psi)), (T.embedCtx G)))),
                s, Gsome) in
          let (Gsome', Lpi') = I.constBlock c' in
          let _ =
            TypeCheck.typeCheckCtx
              (T.coerceCtx (append ((append (Psi0, Psi)), (T.embedCtx G)))) in
          let _ =
            TypeCheck.typeCheckSub
              ((T.coerceCtx (append ((append (Psi0, Psi)), (T.embedCtx G)))),
                s, Gsome') in
          traversePos (L, wmap, projs)
            ((Psi0, Psi, (I.Decl (G, (I.BDec (x, (c', s)))))), V,
              (SOME ((I.dot1 w1), (P, Q))))
      | ((L, wmap, projs),
         ((Psi0, G, B), (Root (Const a, S) as V), SOME (w1, (P, Q)))) ->
          let Psi1 = append (Psi0, (append (G, (T.embedCtx B)))) in
          let _ =
            TomegaTypeCheck.checkCtx
              (append ((append (Psi0, G)), (T.embedCtx B))) in
          let n = domain (Psi1, w1) in
          let m = I.ctxLength Psi0 in
          let rec lookupbase a =
            let s = I.conDecName (I.sgnLookup a) in
            let l = T.lemmaName s in
            let ValDec (_, P, F) = T.lemmaLookup l in ((T.Const l), F) in
          let rec lookup =
            function
            | ((b::[], NONE, F), a) ->
                if a = b then let P = T.Var n in (P, F) else lookupbase a
            | ((b::[], SOME (lemma::[]), F), a) ->
                if a = b
                then
                  let P =
                    T.Redex ((T.Const lemma), (T.AppPrg ((T.Var n), T.Nil))) in
                  (P, F)
                else lookupbase a
            | ((b::L, SOME (lemma::lemmas), And (F1, F2)), a) ->
                if a = b
                then
                  let P =
                    T.Redex ((T.Const lemma), (T.AppPrg ((T.Var n), T.Nil))) in
                  (P, F1)
                else lookup ((L, (SOME lemmas), F2), a) in
          let (HP, F) =
            if (I.ctxLength Psi0) > 0
            then
              let PDec (_, F0, _, _) = I.ctxLookup (Psi0, 1) in
              lookup ((L, projs, F0), a)
            else lookupbase a in
          let rec apply ((S, mS), Ft) = applyW ((S, mS), (T.whnfFor Ft))
          and applyW =
            function
            | ((I.Nil, M.Mnil), Ft') -> (T.Nil, (T.forSub Ft'))
            | ((App (U, S), Mapp (Marg (M.Plus, _), mS)), (All (D, F'), t'))
                ->
                let U' = strengthenExp (U, w1) in
                let (S'', F'') =
                  apply ((S, mS), (F', (T.Dot ((T.Exp U'), t')))) in
                ((T.AppExp (U', S'')), F'')
            | ((App (U, S), Mapp (Marg (M.Minus, _), mS)), Ft) ->
                applyW ((S, mS), Ft) in
          let (S'', F'') = apply ((S, (modeSpine a)), (F, T.id)) in
          let _ =
            TomegaTypeCheck.checkFor
              ((append ((append (Psi0, G)), (T.embedCtx B))),
                (T.forSub (F'', (T.embedSub w1)))) in
          let P'' = T.Redex (HP, S'') in
          let b = I.ctxLength B in
          let w1' = peeln (b, w1) in
          let (B', _) = strengthenCtx (B, w1') in
          let n' = (-) n I.ctxLength B' in
          let rec subCtx =
            function
            | (I.Null, s) -> (I.Null, s)
            | (Decl (G, D), s) ->
                let (G', s') = subCtx (G, s) in
                ((I.Decl (G', (I.decSub (D, s')))), (I.dot1 s')) in
          let (B'', _) = subCtx (B', w1') in
          let _ =
            TomegaTypeCheck.checkCtx
              (append ((append (Psi0, G)), (T.embedCtx B''))) in
          let (GB', iota) = T.deblockify B' in
          let _ =
            try TypeCheck.typeCheckSub (GB', (T.coerceSub iota), B')
            with | Error _ -> raise (Error' iota) in
          let RR = T.forSub (F'', iota) in
          let F''' = TA.raiseFor (GB', (RR, I.id)) in
          let rec lift =
            function
            | (I.Null, P) -> P
            | (Decl (G, D), P) ->
                let (Bint, _) = T.deblockify (I.Decl (I.Null, D)) in
                lift (G, (T.New (T.Lam ((T.UDec D), P)))) in
          let P''' = lift (B', P'') in
          let _ = TomegaTypeCheck.checkCtx (append (Psi0, G)) in
          let _ =
            TomegaTypeCheck.checkFor
              ((append (Psi0, G)), (T.forSub (F''', (T.embedSub w1')))) in
          let (Psi1'', w2, z2) = strengthen (Psi1, (a, S), w1, M.Minus) in
          let w3 = peeln (b, w2) in
          let z3 = peeln (b, z2) in
          let (Psi2, B3') = popn (b, Psi1'') in
          let Pat' = transformConc ((a, S), w2) in
          let F4 = T.forSub (F''', (T.embedSub z3)) in
          let _ = TomegaTypeCheck.checkCtx Psi1'' in
          let _ = TomegaTypeCheck.checkCtx (append (Psi2, (T.embedCtx B3'))) in
          let _ =
            try TomegaTypeCheck.checkFor (Psi2, F4)
            with | _ -> raise (Error "") in
          let (B3, sigma3) = T.deblockify B3' in
          let Pat'' = T.normalizePrg (Pat', sigma3) in
          let Pat = TA.raisePrg (B3, Pat'', F4) in
          let _ = TomegaTypeCheck.checkPrg (Psi2, (Pat, F4)) in
          let t = T.Dot ((T.Prg Pat), (T.embedSub z3)) in
          SOME
            (w3,
              ((function
                | p ->
                    P
                      (T.Let
                         ((T.PDec (NONE, F''', NONE, NONE)), P''',
                           (T.Case (T.Cases [(Psi2, t, p)]))))), Q))
    let rec traverse (Psi0, L, Sig, wmap, projs) =
      let rec traverseSig' =
        function
        | nil -> nil
        | (G, V)::Sig ->
            (TypeCheck.typeCheck
               ((append ((T.coerceCtx Psi0), G)), (V, (I.Uni I.Type)));
             (match traverseNeg (L, wmap, projs)
                      ((Psi0, (T.embedCtx G)), V, I.id)
              with
              | SOME (wf, (P', Q')) -> (traverseSig' Sig) @ [P' Q'])) in
      traverseSig' Sig
    let rec transformWorlds (fams, Worlds cids) =
      let rec transformList =
        function
        | (nil, w) -> nil
        | ((Dec (x, V) as D)::L, w) ->
            if
              List.foldr
                (function
                 | (a, b) -> b && (Subordinate.belowEq (a, (I.targetFam V))))
                true__ fams
            then transformList (L, (I.comp (w, I.shift)))
            else
              (let L' = transformList (L, (I.dot1 w)) in
               (I.Dec (x, (strengthenExp (V, w)))) :: L') in
      let rec transformWorlds' =
        function
        | nil -> (nil, ((function | c -> raise (Error "World not found"))))
        | cid::cids' ->
            let BlockDec (s, m, G, L) = I.sgnLookup cid in
            let L' = transformList (L, I.id) in
            let (cids'', wmap) = transformWorlds' cids' in
            let cid' = I.sgnAdd (I.BlockDec (s, m, G, L')) in
            ((cid' :: cids''),
              ((function | c -> if c = cid then cid' else wmap c))) in
      let (cids', wmap) = transformWorlds' cids in ((T.Worlds cids'), wmap)
    let rec dynamicSig (Psi0, a, Worlds cids) =
      let rec findDec =
        function
        | (G, _, nil, w, Sig) -> Sig
        | (G, n, (D)::L, w, Sig) ->
            let Dec (x, V') as D' = I.decSub (D, w) in
            let b = I.targetFam V' in
            let Sig' =
              if b = a then (G, (Whnf.normalize (V', I.id))) :: Sig else Sig in
            findDec
              (G, (n + 1), L,
                (I.Dot
                   ((I.Exp (I.Root ((I.Proj ((I.Bidx 1), n)), I.Nil))), w)),
                Sig') in
      let rec mediateSub =
        function
        | I.Null -> (I.Null, (I.Shift (I.ctxLength Psi0)))
        | Decl (G, D) ->
            let (G0, s') = mediateSub G in
            let D' = I.decSub (D, s') in ((I.Decl (G0, D')), (I.dot1 s')) in
      let rec findDecs' =
        function
        | (nil, Sig) -> Sig
        | (cid::cids', Sig) ->
            let BlockDec (s, m, G, L) = I.sgnLookup cid in
            let (G0, s') = mediateSub G in
            let D' = Names.decName (G0, (I.BDec (NONE, (cid, s')))) in
            let s'' = I.comp (s', I.shift) in
            let Sig' = findDec ((I.Decl (G0, D')), 1, L, s'', Sig) in
            findDecs' (cids', Sig') in
      findDecs' (cids, nil)
    let rec staticSig =
      function
      | (Psi0, nil) -> nil
      | (Psi0, (ConDec (name, _, _, _, V, I.Type))::Sig) ->
          (::) (I.Null, (Whnf.normalize (V, (I.Shift (I.ctxLength Psi0)))))
            staticSig (Psi0, Sig)
    let rec name =
      function
      | a::[] -> I.conDecName (I.sgnLookup a)
      | a::L -> ((I.conDecName (I.sgnLookup a)) ^ "/") ^ (name L)
    let rec convertPrg (L, projs) =
      let (name, F0) = createIH L in
      let D0 = T.PDec ((SOME name), F0, NONE, NONE) in
      let Psi0 = I.Decl (I.Null, D0) in
      let Prec = function | p -> T.Rec (D0, p) in
      let rec convertWorlds =
        function
        | a::[] -> let W = WorldSyn.lookup a in W
        | a::L' ->
            let W = WorldSyn.lookup a in
            let W' = convertWorlds L' in
            if T.eqWorlds (W, W')
            then W'
            else raise (Error "Type families different in different worlds") in
      let W = convertWorlds L in
      let (W', wmap) = transformWorlds (L, W) in
      let rec convertOnePrg (a, F) =
        let name = nameOf a in
        let V = typeOf a in
        let mS = modeSpine a in
        let Sig = Worldify.worldify a in
        let dynSig = dynamicSig (Psi0, a, W) in
        let statSig = staticSig (Psi0, Sig) in
        let _ =
          map
            (function
             | ConDec (_, _, _, _, U, V) -> TypeCheck.check (U, (I.Uni V)))
            Sig in
        let _ = validSig (Psi0, statSig) in
        let _ = validSig (Psi0, dynSig) in
        let C0 = traverse (Psi0, L, dynSig, wmap, projs) in
        let rec init =
          function
          | All ((D, _), F') ->
              let (F'', P') = init F' in
              (F'', ((function | p -> T.Lam (D, (P' p)))))
          | F' -> (F', ((function | p -> p))) in
        let (F', Pinit) = init F in
        let C = traverse (Psi0, L, statSig, wmap, projs) in
        Pinit (T.Case (T.Cases (C0 @ C))) in
      let rec convertPrg' =
        function
        | (nil, _) -> raise (Error "Cannot convert Empty program")
        | (a::[], F) -> convertOnePrg (a, F)
        | (a::L', And (F1, F2)) ->
            T.PairPrg ((convertOnePrg (a, F1)), (convertPrg' (L', F2))) in
      let P = Prec (convertPrg' (L, F0)) in P
    let rec installFor (cid::[]) =
      let F = convertFor [cid] in
      let name = I.conDecName (I.sgnLookup cid) in
      let _ = T.lemmaAdd (T.ForDec (name, F)) in ()
    let rec depthConj =
      function | And (F1, F2) -> (+) 1 depthConj F2 | F -> 1
    let rec createProjection =
      function
      | (Psi, depth, (And (F1, F2) as F), Pattern) ->
          createProjection
            ((I.Decl (Psi, (T.PDec (NONE, F1, NONE, NONE)))), (depth + 1),
              (T.forSub (F2, (T.Shift 1))),
              (T.PairPrg ((T.Var (depth + 2)), Pattern)))
      | (Psi, depth, F, Pattern) ->
          let Psi' = I.Decl (Psi, (T.PDec (NONE, F, NONE, NONE))) in
          let depth' = depth + 1 in
          (function
           | k ->
               let PDec (_, F', _, _) = T.ctxDec (Psi', k) in
               ((T.Case
                   (T.Cases
                      [(Psi', (T.Dot ((T.Prg Pattern), (T.Shift depth'))),
                         (T.Var k))])), F'))
    let rec installProjection =
      function
      | (nil, _, F, Proj) -> nil
      | (cid::cids, n, F, Proj) ->
          let (P', F') = Proj n in
          let P = T.Lam ((T.PDec (NONE, F, NONE, NONE)), P') in
          let F'' = T.All (((T.PDec (NONE, F, NONE, NONE)), T.Explicit), F') in
          let name = I.conDecName (I.sgnLookup cid) in
          let _ = TomegaTypeCheck.checkPrg (I.Null, (P, F'')) in
          let lemma = T.lemmaAdd (T.ValDec (("#" ^ name), P, F'')) in
          (::) lemma installProjection (cids, (n - 1), F, Proj)
    let rec installSelection =
      function
      | (cid::[], lemma::[], F1, main) ->
          let P =
            T.Redex ((T.Const lemma), (T.AppPrg ((T.Const main), T.Nil))) in
          let name = I.conDecName (I.sgnLookup cid) in
          let _ = TomegaTypeCheck.checkPrg (I.Null, (P, F1)) in
          let lemma' = T.lemmaAdd (T.ValDec (name, P, F1)) in [lemma']
      | (cid::cids, lemma::lemmas, And (F1, F2), main) ->
          let P =
            T.Redex ((T.Const lemma), (T.AppPrg ((T.Const main), T.Nil))) in
          let name = I.conDecName (I.sgnLookup cid) in
          let _ = TomegaTypeCheck.checkPrg (I.Null, (P, F1)) in
          let lemma' = T.lemmaAdd (T.ValDec (name, P, F1)) in
          (::) lemma' installSelection (cids, lemmas, F2, main)
    let rec installPrg =
      function
      | cid::[] ->
          let F = convertFor [cid] in
          let P = convertPrg ([cid], NONE) in
          let name = I.conDecName (I.sgnLookup cid) in
          let _ = TomegaTypeCheck.checkPrg (I.Null, (P, F)) in
          let _ =
            if (!Global.chatter) >= 4
            then print "[Redundancy Checker (factoring) ..."
            else () in
          let factP = Redundant.convert P in
          let _ = if (!Global.chatter) >= 4 then print "done]\n" else () in
          let lemma = T.lemmaAdd (T.ValDec (name, factP, F)) in
          (lemma, [], [])
      | cids ->
          let F = convertFor cids in
          let _ = TomegaTypeCheck.checkFor (I.Null, F) in
          let Proj = createProjection (I.Null, 0, F, (T.Var 1)) in
          let projs = installProjection (cids, (depthConj F), F, Proj) in
          let P = convertPrg (cids, (SOME projs)) in
          let s = name cids in
          let _ = TomegaTypeCheck.checkPrg (I.Null, (P, F)) in
          let _ =
            if (!Global.chatter) >= 4
            then print "[Redundancy Checker (factoring) ..."
            else () in
          let factP = Redundant.convert P in
          let _ = if (!Global.chatter) >= 4 then print "done]\n" else () in
          let lemma = T.lemmaAdd (T.ValDec (s, factP, F)) in
          let sels = installSelection (cids, projs, F, lemma) in
          (lemma, projs, sels)
    let rec mkResult =
      function
      | 0 -> T.Unit
      | n -> T.PairExp ((I.Root ((I.BVar n), I.Nil)), (mkResult (n - 1)))
    let rec convertGoal (G, V) =
      let a = I.targetFam V in
      let W = WorldSyn.lookup a in
      let (W', wmap) = transformWorlds ([a], W) in
      let SOME (_, (P', Q')) =
        traversePos ([], wmap, NONE)
          ((I.Null, G, I.Null), V,
            (SOME
               ((I.Shift (I.ctxLength G)),
                 ((function | P -> (I.Null, T.id, P)),
                   (mkResult (I.ctxLength G)))))) in
      let (_, _, P'') = P' Q' in P''
    (* ABP - 4/20/03, determine if Front is (I.Idx 1) *)
    (* strengthenExp (U, s) = U'

       Invariant:
       If   G |- s : G'
       and  G |- U : V
       then G' |- U' = U[s^-1] : V [s^-1]
    *)
    (* strengthenDec (x:V, s) = x:V'

       Invariant:
       If   G |- s : G'
       and  G |- V : L
       then G' |- V' = V[s^-1] : L
    *)
    (* G0 |- t : Gsome *)
    (* G0  |- s : G' *)
    (* to show  G' |- t o s^1 : Gsome *)
    (* strengthenCtx (G, s) = (G', s')

       If   G0 |- G ctx
       and  G0 |- w : G1
       then G1 |- G' = G[w^-1] ctx
       and  G0 |- w' : G1, G'
    *)
    (* strengthenFor (F, s) = F'

       If   Psi0 |- F for
       and  Psi0 |- s :: Psi1
       then Psi1 |- F' = F[s^-1] ctx
    *)
    (* strengthenOrder (O, s) = O'

       If   Psi0 |- O order
       and  Psi0 |- s :: Psi1
       then Psi1 |- O' = O[s^-1] ctx
    *)
    (* strengthenTC (TC, s) = TC'

       If   Psi0 |- TC : termination condition
       and  Psi0 |- s :: Psi1
       then Psi1 |- TC' = TC[s^-1] ctx
    *)
    (* strengthenPsi (Psi, s) = (Psi', s')

       If   Psi0 |- Psi ctx
       and  Psi0 |- s :: Psi1
       then Psi1 |- Psi' = Psi[s^-1] ctx
       and  Psi0 |- s' :: Psi1, Psi'
    *)
    (* strengthenPsi' (Psi, s) = (Psi', s')

       If   Psi0 |- Psi ctx
       and  Psi0 |- s : Psi1
       then Psi1 |- Psi' = Psi[s^-1] ctx
       and  Psi0 |- s' : Psi1, Psi'  weakening substitution
    *)
    (* ctxSub (G, s) = (G', s')

       Invariant:
       if   Psi |- G ctx
       and  Psi' |- s : Psi
       then Psi' |- G' ctx
       and  Psi', G' |- s' : G
       and  G' = G [s],  declarationwise defined
    *)
    (* convertFor' (V, mS, w1, w2, n) = (F', F'')

           Invariant:
           If   G |- V = {{G'}} type :kind
           and  G |- w1 : G+
           and  G+, G'+, G- |- w2 : G
           and  G+, G'+, G- |- ^n : G+
           and  mS is a spine for G'
           then F'  is a formula excepting a another formula as argument s.t.
                If G+, G'+ |- F formula,
                then . |- F' F formula
           and  G+, G'+ |- F'' formula
        *)
    (* shiftPlus (mS) = s'

         Invariant:
         s' = ^(# of +'s in mS)
         *)
    (* createIH L = (Psi', P', F')

       Invariant:
       If   L is a list of type families
       and  Psi is a context
       then Psi' extends Psi' by declarations in L
       and  F' is the conjunction of the formuals
            that corresponds to each type family in L
       and  Psi' |- P' in F'
    *)
    (* occursInExpN (k, U) = B,

       Invariant:
       If    U in nf
       then  B iff k occurs in U
    *)
    (* | occursInExpN (k, I.FgnExp (cs, ops)) =
         occursInExpN (k, Whnf.normalize (#toInternal(ops) (), I.id)) MERGE Fri Aug 22 23:09:53 2003 --cs *)
    (* no case for Redex, EVar, EClo *)
    (* no case for FVar *)
    (* no case for SClo *)
    (* dot1inv w = w'

       Invariant:
       If   G, A |- w : G', A
       then G |- w' : G'
       and  w = 1.w' o ^
    *)
    (* shiftinv (w) = w'

       Invariant:
       If   G, A |- w : G'
       and  1 does not occur in w
       then w  = w' o ^
    *)
    (* domain (G2, w) = n'

       Invariant:
       If   G2 |- w: G1   and w weakening substitution
       then n' = |G1|
    *)
    (* strengthen (Psi, (a, S), w, m) = (Psi', w')

       This function traverses the spine, and finds
       all variables in a position input/output position m
       (hence strenghten might not be a good name for it, because it is to general.)

       Invariant:
       If   |- Psi ctx
       and  |- Psi1 ctx      where Psi1 is a subcontext of Psi
       and  Sigma (a) = {x1:A1} .. {xn:An} type
       and  Psi |- S : m1{x1:A1} .. mn{xn:An} > type
       and  Psi |- w : Psi1
       and  m mode
       then |- Psi' ctx
       and  Psi |- w' : Psi'
       where Psi' extends Psi1 (but is a subset of Psi?)
    *)
    (* is this ok? -- cs *)
    (* no other cases *)
    (* testBlock (G, (bw, w1)) = (bw', w')

           Invariant:
           If   |- G ctx
           and  |- G1 ctx
           and  |- G2 ctx
           and  G1 |- w1 : G2, G
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
    (* blocks are always used! *)
    (* createSub (Psi, L) = t'

       Invariant:
       If  |- Psi = Psi0, Psi1 ctx
       and Psi0 contains all declarations for invariants in L
       and |Psi0| = n
       and |L| = k
       and n = k + m - 1
       then Psi |- t' = m, m+1 ... n. ^n :  Psi0
    *)
    (*List.length L *)
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
    (* transformConc ((a, S), w) = P

       Invariant:
       If   Sigma (a) = {x1:A1} .. {xn:An} type
       and  Psi |- S : m1{x1:A1} .. mn{xn:An} type > type
       and  Psi |- w : PsiAll
       then P is proof term consisting of all - objects of S,
            defined in PsiAll
    *)
    (* renameExp f U = U'

       Invariant:
       U' = U module application of f to any projectoin contained
       in U.
    *)
    (* traverseNeg (L, wmap, projs)  (Psi0, Psi, V) = ([w', PQ'], L')    [] means optional

           Invariant:
           If   |- Psi0 ctx      (context that contains induction hypotheses)
           and  Psi0 |- Psi ctx  (context of all assumptions)
           and  Psi0, Psi |- V : type
           then L' list of cases
           and  Psi0, Psi |- w' : Psi0, Psi'
           and  PQ'  is a pair that can generate a proof term
        *)
    (* Psi0, Psi |- w : Psi0, Psi' *)
    (* Sigma (a) = Va *)
    (* Psi0, Psi |- S : {G} type > type *)
    (* Psi1 = Psi0, Psi *)
    (* Psi1 |- w0 : Psi0 *)
    (* |- Psi' ctx *)
    (* Psi1 |- w' : Psi' *)
    (* Psi' |- s'' : G+ *)
    (* G |- w'' : G+ *)
    (* T.UDec *)
    (* Psi0 = x1::F1 ... xn::Fn *)
    (* |- Psi0 matches L *)
    (* Psi0, G, B |- V : type *)
    (* Psi0, G, B |- w1 : Psi0, G', B' *)
    (* Psi1 = Psi0, G, B *)
    (* n = |Psi0, G', B'| *)
    (* m = |Psi0| *)
    (* strengthened invariant Psi0 might be empty --cs Fri Apr 11 15:25:32 2003 *)
    (* apply ((S, mS), F')= (S'', F'')

                 Invariant:
                 Psi0, G, B |- S : V >> type
                   (mS is the corresponding mode spine)
                 and  Psi0, G', B |- F'  :: for
                 then Psi0, G', B |- F'' :: for
                 and  Psi0, G', B |- S'' :: F' >> F''
              *)
    (* Psi0, G', B' |- D = x:V' : type *)
    (* Psi0, G', B', x:V' |- F' :: for *)
    (* Psi0, G', B' |- U' : V' *)
    (* Psi0, G', B' |- F'' :: for *)
    (* Psi0, G', B' |- S'' : F' [t'] >> F'' *)
    (* Psi0, G', B' |- U' ; S''
                                                       : all {x:V'} F' >> F'' *)
    (* Psi0, G', B' |- F'' :: for *)
    (* Psi0, G', B' |- S'' :: F' >> F'' *)
    (*T.Var k' *)
    (* was T.Root  -cs Sun Jan  5 23:15:06 2003 *)
    (* Psi0, G', B' |- P'' :: F'' *)
    (* b = |B| = |B'| *)
    (* Psi0, G |- w1' : Psi0, G' *)
    (* |- Psi0, G', B' ctx *)
    (* n' = |Psi0, G'| *)
    (* Psi0, G' |- GB' ctx *)
    (* Psi0, G, B |- w1 : Psi0, G', B' *)
    (* Psi0, G', GB'  |- s' : Psi0, G', B' *)
    (* Psi0, G', GB' |- RR for *)
    (* Psi0, G |- w1' : Psi0, G' *)
    (* Psi0, G' |- F''' for *)
    (* lift (B, (P, F)) = (P', F')

                 Invariant:
                 If   Psi0, G, B |- P :: F
                 then Psi0, G |- P'  :: F'
                 and  P' =  (lam B. P)
                 and  F' = raiseFor (B, F)
              *)
    (* Psi0, G' |- P''' :: F''' *)
    (* |- Psi0, Psi1'' ctx *)
    (* Psi0, G, B |- w2 : Psi1'' *)
    (* Psi1'' = Psi0, G3, B3' *)
    (* |B| = |GB'| *)
    (* Psi'' |-  z2 : Psi0, G', B' *)
    (* Psi0, G, B |- w2 : Psi0, G3, B3' *)
    (* Psi0, G |- w3 : Psi0, G3 *)
    (* Psi0, G3 |-  z3 : Psi0, G' *)
    (* Psi2 = Psi0, G3 *)
    (* Psi0, G3, B3' |- Pat' :: For *)
    (* Psi0, G3 |- F4 for *)
    (* ' F4 *)
    (* Psi0, G3 |- Pat :: F4  *)
    (* Here's a commutative diagram
                                           at work which one has to prove
                                           correct
                                        *)
    (* Psi0, G3 |- t :: Psi0, G', x :: F4  *)
    (* traverse (Psi0, L, Sig, wmap) = C'

       Invariant:
       If   |- Psi0  ctx
       and  L is a the theorem we would like to transform
       and  Sig is a signature
       and  forall (G, V) in Sig the following holds:
                    Psi0, G |- V : type
               and  head (V) in L
       and  wmap is a mapping of old labels L to L'
            where L' is a new label and w' is a weakensub
            with the following properties.
            If   Sig (L) = (Gsome, Lblock)
            and  Sig (L') = (Gsome, Lblock')
       then C' is a list of cases (corresponding to each (G, V) in Sig)
    *)
    (* transformWorlds (fams, W) = (W', wmap)

       Invariant:
       If   fams is the theorem to be compiled
       and  W a world with declarations,
       then W' is the new world stripped of all dynamic extensions
       and  wmap is a mapping of old labels L to L'
            where L' is a new label and w' is a weakensub
            with the following properties.
            If   Sig (L) = (Gsome, Lblock)
            and  Sig (L') = (Gsome, Lblock')
    *)
    (* convertList (a, L, w) = L'

             Invariant:
             If   G0 |- G, L : ctx
             and  G0, G |- w : G0, G'
             then G0 |- G', L' ctx
          *)
    (* Design decision: Let's keep all of G *)
    (* dynamicSig (Psi0, fams, W) = Sig'

       Invariant:
       If   |- Psi0 ctx
       and  fams are the typfamilies to be converted
       and  W is the world in which the translation takes place
       then Sig' = (G1;V1) ... (Gn;Vn)
       and  |- Psi0, Gi ctx
       and  Psi, Gi |- Vi : type.
    *)
    (* findDec (G, n, L, s, S) = S'

             Invariant:
             If   G |-  L : ctx
             and  G |- w: G'
             then |- G', L' ctx
          *)
    (* mediateSub G = (G0, s)

             Invariant:
             If   . |- G ctx
             then Psi0 |- G0 ctx
             and  Psi0, G0 |- s : G
          *)
    (* G |- L ctx *)
    (* Psi0, G0 |- s'' : G *)
    (* Psi0, G0 |- D : dec *)
    (* Psi0, G0, D' |- s'' : G *)
    (* staticSig Sig = Sig'

       Invariant:
       If   |- Psi0 ctx
       then Sig' = (c1:V1) ... (cn:Vn)
       and  . |- Vi : type.
    *)
    (* convertPrg L = P'

       Invariant:
       If   L is a list of type families
       then P' is a conjunction of all programs resulting from converting
            the relational encoding of the function expressed by each type
            family in L into functional form
    *)
    (* W describes the world of a *)
    (* W describes the world of a *)
    (* Psi0 |- {x1:V1} ... {xn:Vn} type *)
    (* |- mS : {x1:V1} ... {xn:Vn} > type *)
    (* Sig in LF(reg)   *)
    (* init' F = P'

               Invariant:
               If   F = All x1:A1. ... All xn:An. F'
               and  f' does not start with a universal quantifier
               then P' P'' = Lam x1:A1. ... Lam xn:An P''
                    for any P''
            *)
    (* Psi0, x1:V1, ..., xn:Vn |- C :: F *)
    (* F', *)
    let convertFor = convertFor
    let convertPrg = function | L -> convertPrg (L, NONE)
    let installFor = installFor
    let installPrg = installPrg
    let traverse = traverse
    let convertGoal = convertGoal
  end ;;
