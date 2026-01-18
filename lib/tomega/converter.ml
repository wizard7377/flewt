
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
      | None -> raise (Error "Mode declaration expected")
      | Some mS -> mS
    let rec typeOf a =
      match I.sgnLookup a with
      | ConDec (name, _, _, _, __v, I.Kind) -> __v
      | _ -> raise (Error "Type Constant declaration expected")
    let rec nameOf a =
      match I.sgnLookup a with
      | ConDec (name, _, _, _, __v, I.Kind) -> name
      | _ -> raise (Error "Type Constant declaration expected")
    let rec chatter chlev f =
      if (!Global.chatter) >= chlev then print ((^) "[tomega] " f ()) else ()
    let rec strengthenExp (__u, s) =
      Whnf.normalize ((Whnf.cloInv (__u, s)), I.id)
    let rec strengthenSub (s, t) = Whnf.compInv (s, t)
    let rec strengthenDec =
      function
      | (Dec (name, __v), s) -> I.Dec (name, (strengthenExp (__v, s)))
      | (BDec (name, (__l, t)), s) ->
          I.BDec (name, (__l, (strengthenSub (t, s))))
    let rec strengthenCtx =
      function
      | (I.Null, s) -> (I.Null, s)
      | (Decl (__g, __d), s) ->
          let (__g', s') = strengthenCtx (__g, s) in
          ((I.Decl (__g', (strengthenDec (__d, s')))), (I.dot1 s'))
    let rec strengthenFor =
      function
      | (T.True, s) -> T.True
      | (And (__F1, __F2), s) ->
          T.And ((strengthenFor (__F1, s)), (strengthenFor (__F2, s)))
      | (All ((UDec (__d), Q), F), s) ->
          T.All
            (((T.UDec (strengthenDec (__d, s))), Q),
              (strengthenFor (F, (I.dot1 s))))
      | (Ex ((__d, Q), F), s) ->
          T.Ex (((strengthenDec (__d, s)), Q), (strengthenFor (F, (I.dot1 s))))
    let rec strengthenOrder =
      function
      | (Arg ((__u, s1), (__v, s2)), s) ->
          Order.Arg
            ((__u, (strengthenSub (s1, s))), (__v, (strengthenSub (s2, s))))
      | (Simul (__Os), s) ->
          Order.Simul (map (function | O -> strengthenOrder (O, s)) __Os)
      | (Lex (__Os), s) ->
          Order.Lex (map (function | O -> strengthenOrder (O, s)) __Os)
    let rec strengthenTC =
      function
      | (Base (O), s) -> T.Base (strengthenOrder (O, s))
      | (Conj (TC1, TC2), s) ->
          T.Conj ((strengthenTC (TC1, s)), (strengthenTC (TC2, s)))
      | (Abs (__d, TC), s) ->
          T.Abs ((strengthenDec (__d, s)), (strengthenTC (TC, (I.dot1 s))))
    let rec strengthenSpine =
      function
      | (I.Nil, t) -> I.Nil
      | (App (__u, S), t) ->
          I.App ((strengthenExp (__u, t)), (strengthenSpine (S, t)))
    let rec strengthenPsi =
      function
      | (I.Null, s) -> (I.Null, s)
      | (Decl (Psi, UDec (__d)), s) ->
          let (Psi', s') = strengthenPsi (Psi, s) in
          ((I.Decl (Psi', (T.UDec (strengthenDec (__d, s'))))), (I.dot1 s'))
      | (Decl (Psi, PDec (name, F, None, None)), s) ->
          let (Psi', s') = strengthenPsi (Psi, s) in
          ((I.Decl
              (Psi', (T.PDec (name, (strengthenFor (F, s')), None, None)))),
            (I.dot1 s'))
    let rec strengthenPsi' =
      function
      | (nil, s) -> (nil, s)
      | ((UDec (__d))::Psi, s) ->
          let __d' = strengthenDec (__d, s) in
          let s' = I.dot1 s in
          let (Psi'', s'') = strengthenPsi' (Psi, s') in
          (((T.UDec __d') :: Psi''), s'')
    let rec ctxSub =
      function
      | (I.Null, s) -> (I.Null, s)
      | (Decl (__g, __d), s) ->
          let (__g', s') = ctxSub (__g, s) in
          ((I.Decl (__g', (I.decSub (__d, s')))), (I.dot1 s))
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
      | (Psi0, (__g, __v)::Sig) ->
          let rec append =
            function
            | (__g, I.Null) -> __g
            | (__g, Decl (__g', __d)) -> I.Decl ((append (__g, __g')), __d) in
          (TypeCheck.typeCheck
             ((T.coerceCtx (append (Psi0, (T.embedCtx __g)))),
               (__v, (I.Uni I.Type)));
           validSig (Psi0, Sig))
    let rec convertOneFor cid =
      let __v =
        match I.sgnLookup cid with
        | ConDec (name, _, _, _, __v, I.Kind) -> __v
        | _ -> raise (Error "Type Constant declaration expected") in
      let mS =
        match ModeTable.modeLookup cid with
        | None -> raise (Error "Mode declaration expected")
        | Some mS -> mS in
      let _ = validMode mS in
      let rec convertFor' =
        function
        | (Pi ((__d, _), __v), Mapp (Marg (M.Plus, _), mS), w1, w2, n) ->
            let (__F', __F'') =
              convertFor'
                (__v, mS, (I.dot1 w1), (I.Dot ((I.Idx n), w2)), (n - 1)) in
            (((function
               | F ->
                   T.All
                     (((T.UDec (strengthenDec (__d, w1))), T.Explicit), (__F' F)))),
              __F'')
        | (Pi ((__d, _), __v), Mapp (Marg (M.Minus, _), mS), w1, w2, n) ->
            let (__F', __F'') =
              convertFor'
                (__v, mS, (I.comp (w1, I.shift)), (I.dot1 w2), (n + 1)) in
            (__F', (T.Ex (((I.decSub (__d, w2)), T.Explicit), __F'')))
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
      let (F, __F') = convertFor' (__v, mS, I.id, (I.Shift n), n) in F __F'
    let rec createIH =
      function
      | nil -> raise (Error "Empty theorem")
      | a::[] ->
          let name = I.conDecName (I.sgnLookup a) in
          let F = convertOneFor a in (name, F)
      | a::__l ->
          let name = I.conDecName (I.sgnLookup a) in
          let F = convertOneFor a in
          let (name', __F') = createIH __l in
          (((name ^ "/") ^ name'), (T.And (F, __F')))
    let rec convertFor (__l) = let (_, __F') = createIH __l in __F'
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
             | (__u, DP) -> DP || (occursInExp (k, (Whnf.normalize (__u, I.id)))))
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
      | (k, App (__u, S)) -> (occursInExpN (k, __u)) || (occursInSpine (k, S))
    let rec occursInDec (k, Dec (_, __v)) = occursInExpN (k, __v)
    let rec occursInDecP (k, (__d, _)) = occursInDec (k, __d)
    let rec occursInExp (k, __u) = occursInExpN (k, (Whnf.normalize (__u, I.id)))
    let rec dot1inv w = strengthenSub ((I.comp (I.shift, w)), I.shift)
    let rec shiftinv w = strengthenSub (w, I.shift)
    let rec peel w =
      if isIdx1 (I.bvarSub (1, w)) then dot1inv w else shiftinv w
    let rec peeln =
      function | (0, w) -> w | (n, w) -> peeln ((n - 1), (peel w))
    let rec popn =
      function
      | (0, Psi) -> (Psi, I.Null)
      | (n, Decl (Psi, UDec (__d))) ->
          let (Psi', __g') = popn ((n - 1), Psi) in (Psi', (I.Decl (__g', __d)))
    let rec domain =
      function
      | (__g, Dot (Idx _, s)) -> (domain (__g, s)) + 1
      | (I.Null, Shift 0) -> 0
      | ((Decl _ as __g), Shift 0) ->
          domain (__g, (I.Dot ((I.Idx 1), (I.Shift 1))))
      | (Decl (__g, _), Shift n) -> domain (__g, (I.Shift (n - 1)))
    let rec strengthen (Psi, (a, S), w, m) =
      let mS = modeSpine a in
      let rec args =
        function
        | (I.Nil, M.Mnil) -> nil
        | (App (__u, S'), Mapp (Marg (m', _), mS)) ->
            let __l = args (S', mS) in
            (match M.modeEqual (m, m') with | true__ -> __u :: __l | false__ -> __l) in
      let rec strengthenArgs =
        function
        | (nil, s) -> nil
        | ((__u)::__l, s) -> (::) (strengthenExp (__u, s)) strengthenArgs (__l, s) in
      let rec occursInArgs =
        function
        | (n, nil) -> false__
        | (n, (__u)::__l) -> (occursInExp (n, __u)) || (occursInArgs (n, __l)) in
      let rec occursInPsi =
        function
        | (n, (nil, __l)) -> occursInArgs (n, __l)
        | (n, ((UDec (Dec (_, __v)))::Psi1, __l)) ->
            (occursInExp (n, __v)) || (occursInPsi ((n + 1), (Psi1, __l)))
        | (n, ((UDec (BDec (_, (cid, s))))::Psi1, __l)) ->
            let BlockDec (_, _, __g, _) = I.sgnLookup cid in
            (occursInSub (n, s, __g)) || (occursInPsi ((n + 1), (Psi1, __l)))
      and occursInSub =
        function
        | (_, _, I.Null) -> false__
        | (n, Shift k, __g) ->
            occursInSub (n, (I.Dot ((I.Idx (k + 1)), (I.Shift (k + 1)))), __g)
        | (n, Dot (Idx k, s), Decl (__g, _)) ->
            (n = k) || (occursInSub (n, s, __g))
        | (n, Dot (Exp (__u), s), Decl (__g, _)) ->
            (occursInExp (n, __u)) || (occursInSub (n, s, __g))
        | (n, Dot (Block _, s), Decl (__g, _)) -> occursInSub (n, s, __g)
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
            if isIdx1 (I.bvarSub (1, w1))
            then inBlock (__g, (true__, (dot1inv w1)))
            else inBlock (__g, (bw, (strengthenSub (w1, I.shift)))) in
      let rec blockSub =
        function
        | (I.Null, w) -> (I.Null, w)
        | (Decl (__g, Dec (name, __v)), w) ->
            let (__g', w') = blockSub (__g, w) in
            let __v' = strengthenExp (__v, w') in
            ((I.Decl (__g', (I.Dec (name, __v')))), (I.dot1 w')) in
      let rec strengthen' =
        function
        | (I.Null, Psi2, __l, w1) -> (I.Null, I.id, I.id)
        | (Decl (Psi1, (UDec (Dec (name, __v)) as LD)), Psi2, __l, w1) ->
            if isIdx1 (I.bvarSub (1, w1))
            then
              let w1' = dot1inv w1 in
              let (Psi1', w', z') = strengthen' (Psi1, (LD :: Psi2), __l, w1') in
              let __v' = strengthenExp (__v, w') in
              ((I.Decl (Psi1', (T.UDec (I.Dec (name, __v'))))), (I.dot1 w'),
                (I.dot1 z'))
            else
              if occursInPsi (1, (Psi2, __l))
              then
                (let w1' = strengthenSub (w1, I.shift) in
                 let (Psi1', w', z') =
                   strengthen' (Psi1, (LD :: Psi2), __l, w1') in
                 let __v' = strengthenExp (__v, w') in
                 ((I.Decl (Psi1', (T.UDec (I.Dec (name, __v'))))), (I.dot1 w'),
                   (I.comp (z', I.shift))))
              else
                (let w1' = strengthenSub (w1, I.shift) in
                 let w2 = I.shift in
                 let (Psi2', w2') = strengthenPsi' (Psi2, w2) in
                 let __l' = strengthenArgs (__l, w2') in
                 let (Psi1'', w', z') = strengthen' (Psi1, Psi2', __l', w1') in
                 (Psi1'', (I.comp (w', I.shift)), z'))
        | (Decl (Psi1, (PDec (name, F, None, None) as __d)), Psi2, __l, w1) ->
            let w1' = dot1inv w1 in
            let (Psi1', w', z') = strengthen' (Psi1, (__d :: Psi2), __l, w1') in
            let __F' = strengthenFor (F, w') in
            ((I.Decl (Psi1', (T.PDec (name, __F', None, None)))), (I.dot1 w'),
              (I.dot1 z'))
        | (Decl (Psi1, (UDec (BDec (name, (cid, s))) as LD)), Psi2, __l, w1) ->
            let w1' = dot1inv w1 in
            let (Psi1', w', z') = strengthen' (Psi1, (LD :: Psi2), __l, w1') in
            let s' = strengthenSub (s, w') in
            ((I.Decl (Psi1', (T.UDec (I.BDec (name, (cid, s')))))),
              (I.dot1 w'), (I.dot1 z')) in
      strengthen' (Psi, nil, (args (S, mS)), w)
    let rec lookupIH (Psi, __l, a) =
      let rec lookupIH' (b::__l, a, k) =
        if a = b then k else lookupIH' (__l, a, (k - 1)) in
      lookupIH' (__l, a, (I.ctxLength Psi))
    let rec createIHSub (Psi, __l) = T.Shift ((I.ctxLength Psi) - 1)
    let rec transformInit (Psi, __l, (a, S), w1) =
      let mS = modeSpine a in
      let __v = typeOf a in
      let rec transformInit' =
        function
        | ((I.Nil, M.Mnil), Uni (I.Type), (w, s)) -> (w, s)
        | ((App (__u, S), Mapp (Marg (M.Minus, _), mS)), Pi (_, V2), (w, s)) ->
            let w' = I.comp (w, I.shift) in
            let s' = s in transformInit' ((S, mS), V2, (w', s'))
        | ((App (__u, S), Mapp (Marg (M.Plus, _), mS)), Pi
           ((Dec (name, V1), _), V2), (w, s)) ->
            let V1' = strengthenExp (V1, w) in
            let w' = I.dot1 w in
            let __u' = strengthenExp (__u, w1) in
            let s' = T.dotEta ((T.Exp __u'), s) in
            transformInit' ((S, mS), V2, (w', s')) in
      transformInit' ((S, mS), __v, (I.id, (createIHSub (Psi, __l))))
    let rec transformConc ((a, S), w) =
      let rec transformConc' =
        function
        | (I.Nil, M.Mnil) -> T.Unit
        | (App (__u, S'), Mapp (Marg (M.Plus, _), mS')) ->
            transformConc' (S', mS')
        | (App (__u, S'), Mapp (Marg (M.Minus, _), mS')) ->
            T.PairExp ((strengthenExp (__u, w)), (transformConc' (S', mS'))) in
      transformConc' (S, (modeSpine a))
    let rec renameExp arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (f, (Uni _ as __u)) -> __u
      | (f, Pi ((__d, DP), __v)) -> I.Pi (((renameDec f __d), DP), (renameExp f __v))
      | (f, Root (H, S)) -> I.Root ((renameHead f H), (renameSpine f S))
      | (f, Lam (__d, __u)) -> I.Lam ((renameDec f __d), (renameExp f __u))
    let rec renameDec f (Dec (x, __v)) = I.Dec (x, (renameExp f __v))
    let rec renameHead arg__0 arg__1 =
      match (arg__0, arg__1) with | (f, Proj bi) -> f bi | (f, H) -> H
    let rec renameSpine arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (f, I.Nil) -> I.Nil
      | (f, App (__u, S)) -> I.App ((renameExp f __u), (renameSpine f S))
    let rec rename (BDec (_, (c, s)), __v) =
      let (__g, __l) = I.constBlock c in
      let rec makeSubst =
        function
        | (n, __g, s, nil, f) -> (__g, f)
        | (n, __g, s, (Dec (x, __v') as __d)::__l, f) ->
            if Subordinate.belowEq ((I.targetFam __v'), (I.targetFam __v))
            then
              makeSubst
                ((n + 1), (I.Decl (__g, (I.decSub (__d, s)))), (I.dot1 s), __l, f)
            else makeSubst (n, __g, (I.comp (s, I.shift)), __l, f) in
      let (__g', f) = makeSubst (1, __g, s, __l, (function | x -> I.Proj x)) in
      (__g, (renameExp f __v))
    let rec append =
      function
      | (__g, I.Null) -> __g
      | (__g, Decl (__g', __d)) -> I.Decl ((append (__g, __g')), __d)
    let rec traverseNeg arg__0 arg__1 =
      match (arg__0, arg__1) with
      | ((__l, wmap, projs),
         ((Psi0, Psi), Pi (((Dec (_, V1) as __d), I.Maybe), V2), w)) ->
          (match traverseNeg (__l, wmap, projs)
                   ((Psi0, (I.Decl (Psi, (T.UDec __d)))), V2, (I.dot1 w))
           with
           | Some (w', PQ') -> Some ((peel w'), PQ'))
      | ((__l, wmap, projs),
         ((Psi0, Psi), Pi (((Dec (_, V1) as __d), I.No), V2), w)) ->
          (match traverseNeg (__l, wmap, projs)
                   ((Psi0, (I.Decl (Psi, (T.UDec __d)))), V2,
                     (I.comp (w, I.shift)))
           with
           | Some (w', PQ') ->
               traversePos (__l, wmap, projs)
                 ((Psi0, Psi, I.Null), V1, (Some ((peel w'), PQ'))))
      | ((__l, wmap, projs), ((Psi0, Psi), Root (Const a, S), w)) ->
          let Psi1 = append (Psi0, Psi) in
          let w0 = I.Shift (I.ctxLength Psi) in
          let (Psi', w', _) = strengthen (Psi1, (a, S), w0, M.Plus) in
          let (w'', s'') = transformInit (Psi', __l, (a, S), w') in
          let _ = TomegaTypeCheck.checkCtx Psi' in
          Some
            (w',
              ((function | P -> (Psi', s'', P)), (transformConc ((a, S), w))))
    let rec traversePos arg__0 arg__1 =
      match (arg__0, arg__1) with
      | ((__l, wmap, projs),
         ((Psi0, Psi, __g), Pi (((BDec (x, (c, s)) as __d), _), __v), Some
          (w1, (P, Q)))) ->
          let c' = wmap c in
          let n = (+) (I.ctxLength Psi0) I.ctxLength __g in
          let (Gsome, Lpi) = I.constBlock c in
          let _ =
            TypeCheck.typeCheckCtx
              (T.coerceCtx (append ((append (Psi0, Psi)), (T.embedCtx __g)))) in
          let _ =
            TypeCheck.typeCheckSub
              ((T.coerceCtx (append ((append (Psi0, Psi)), (T.embedCtx __g)))),
                s, Gsome) in
          let (Gsome', Lpi') = I.constBlock c' in
          let _ =
            TypeCheck.typeCheckCtx
              (T.coerceCtx (append ((append (Psi0, Psi)), (T.embedCtx __g)))) in
          let _ =
            TypeCheck.typeCheckSub
              ((T.coerceCtx (append ((append (Psi0, Psi)), (T.embedCtx __g)))),
                s, Gsome') in
          traversePos (__l, wmap, projs)
            ((Psi0, Psi, (I.Decl (__g, (I.BDec (x, (c', s)))))), __v,
              (Some ((I.dot1 w1), (P, Q))))
      | ((__l, wmap, projs),
         ((Psi0, __g, B), (Root (Const a, S) as __v), Some (w1, (P, Q)))) ->
          let Psi1 = append (Psi0, (append (__g, (T.embedCtx B)))) in
          let _ =
            TomegaTypeCheck.checkCtx
              (append ((append (Psi0, __g)), (T.embedCtx B))) in
          let n = domain (Psi1, w1) in
          let m = I.ctxLength Psi0 in
          let rec lookupbase a =
            let s = I.conDecName (I.sgnLookup a) in
            let l = T.lemmaName s in
            let ValDec (_, P, F) = T.lemmaLookup l in ((T.Const l), F) in
          let rec lookup =
            function
            | ((b::[], None, F), a) ->
                if a = b then let P = T.Var n in (P, F) else lookupbase a
            | ((b::[], Some (lemma::[]), F), a) ->
                if a = b
                then
                  let P =
                    T.Redex ((T.Const lemma), (T.AppPrg ((T.Var n), T.Nil))) in
                  (P, F)
                else lookupbase a
            | ((b::__l, Some (lemma::lemmas), And (__F1, __F2)), a) ->
                if a = b
                then
                  let P =
                    T.Redex ((T.Const lemma), (T.AppPrg ((T.Var n), T.Nil))) in
                  (P, __F1)
                else lookup ((__l, (Some lemmas), __F2), a) in
          let (HP, F) =
            if (I.ctxLength Psi0) > 0
            then
              let PDec (_, __F0, _, _) = I.ctxLookup (Psi0, 1) in
              lookup ((__l, projs, __F0), a)
            else lookupbase a in
          let rec apply ((S, mS), Ft) = applyW ((S, mS), (T.whnfFor Ft))
          and applyW =
            function
            | ((I.Nil, M.Mnil), Ft') -> (T.Nil, (T.forSub Ft'))
            | ((App (__u, S), Mapp (Marg (M.Plus, _), mS)), (All (__d, __F'), t'))
                ->
                let __u' = strengthenExp (__u, w1) in
                let (S'', __F'') =
                  apply ((S, mS), (__F', (T.Dot ((T.Exp __u'), t')))) in
                ((T.AppExp (__u', S'')), __F'')
            | ((App (__u, S), Mapp (Marg (M.Minus, _), mS)), Ft) ->
                applyW ((S, mS), Ft) in
          let (S'', __F'') = apply ((S, (modeSpine a)), (F, T.id)) in
          let _ =
            TomegaTypeCheck.checkFor
              ((append ((append (Psi0, __g)), (T.embedCtx B))),
                (T.forSub (__F'', (T.embedSub w1)))) in
          let __P'' = T.Redex (HP, S'') in
          let b = I.ctxLength B in
          let w1' = peeln (b, w1) in
          let (B', _) = strengthenCtx (B, w1') in
          let n' = (-) n I.ctxLength B' in
          let rec subCtx =
            function
            | (I.Null, s) -> (I.Null, s)
            | (Decl (__g, __d), s) ->
                let (__g', s') = subCtx (__g, s) in
                ((I.Decl (__g', (I.decSub (__d, s')))), (I.dot1 s')) in
          let (B'', _) = subCtx (B', w1') in
          let _ =
            TomegaTypeCheck.checkCtx
              (append ((append (Psi0, __g)), (T.embedCtx B''))) in
          let (GB', iota) = T.deblockify B' in
          let _ =
            try TypeCheck.typeCheckSub (GB', (T.coerceSub iota), B')
            with | Error _ -> raise (Error' iota) in
          let RR = T.forSub (__F'', iota) in
          let __F''' = TA.raiseFor (GB', (RR, I.id)) in
          let rec lift =
            function
            | (I.Null, P) -> P
            | (Decl (__g, __d), P) ->
                let (Bint, _) = T.deblockify (I.Decl (I.Null, __d)) in
                lift (__g, (T.New (T.Lam ((T.UDec __d), P)))) in
          let __P''' = lift (B', __P'') in
          let _ = TomegaTypeCheck.checkCtx (append (Psi0, __g)) in
          let _ =
            TomegaTypeCheck.checkFor
              ((append (Psi0, __g)), (T.forSub (__F''', (T.embedSub w1')))) in
          let (Psi1'', w2, z2) = strengthen (Psi1, (a, S), w1, M.Minus) in
          let w3 = peeln (b, w2) in
          let z3 = peeln (b, z2) in
          let (Psi2, B3') = popn (b, Psi1'') in
          let Pat' = transformConc ((a, S), w2) in
          let __F4 = T.forSub (__F''', (T.embedSub z3)) in
          let _ = TomegaTypeCheck.checkCtx Psi1'' in
          let _ = TomegaTypeCheck.checkCtx (append (Psi2, (T.embedCtx B3'))) in
          let _ =
            try TomegaTypeCheck.checkFor (Psi2, __F4)
            with | _ -> raise (Error "") in
          let (B3, sigma3) = T.deblockify B3' in
          let Pat'' = T.normalizePrg (Pat', sigma3) in
          let Pat = TA.raisePrg (B3, Pat'', __F4) in
          let _ = TomegaTypeCheck.checkPrg (Psi2, (Pat, __F4)) in
          let t = T.Dot ((T.Prg Pat), (T.embedSub z3)) in
          Some
            (w3,
              ((function
                | p ->
                    P
                      (T.Let
                         ((T.PDec (None, __F''', None, None)), __P''',
                           (T.Case (T.Cases [(Psi2, t, p)]))))), Q))
    let rec traverse (Psi0, __l, Sig, wmap, projs) =
      let rec traverseSig' =
        function
        | nil -> nil
        | (__g, __v)::Sig ->
            (TypeCheck.typeCheck
               ((append ((T.coerceCtx Psi0), __g)), (__v, (I.Uni I.Type)));
             (match traverseNeg (__l, wmap, projs)
                      ((Psi0, (T.embedCtx __g)), __v, I.id)
              with
              | Some (wf, (__P', Q')) -> (traverseSig' Sig) @ [__P' Q'])) in
      traverseSig' Sig
    let rec transformWorlds (fams, Worlds cids) =
      let rec transformList =
        function
        | (nil, w) -> nil
        | ((Dec (x, __v) as __d)::__l, w) ->
            if
              List.foldr
                (function
                 | (a, b) -> b && (Subordinate.belowEq (a, (I.targetFam __v))))
                true__ fams
            then transformList (__l, (I.comp (w, I.shift)))
            else
              (let __l' = transformList (__l, (I.dot1 w)) in
               (I.Dec (x, (strengthenExp (__v, w)))) :: __l') in
      let rec transformWorlds' =
        function
        | nil -> (nil, ((function | c -> raise (Error "World not found"))))
        | cid::cids' ->
            let BlockDec (s, m, __g, __l) = I.sgnLookup cid in
            let __l' = transformList (__l, I.id) in
            let (cids'', wmap) = transformWorlds' cids' in
            let cid' = I.sgnAdd (I.BlockDec (s, m, __g, __l')) in
            ((cid' :: cids''),
              ((function | c -> if c = cid then cid' else wmap c))) in
      let (cids', wmap) = transformWorlds' cids in ((T.Worlds cids'), wmap)
    let rec dynamicSig (Psi0, a, Worlds cids) =
      let rec findDec =
        function
        | (__g, _, nil, w, Sig) -> Sig
        | (__g, n, (__d)::__l, w, Sig) ->
            let Dec (x, __v') as __d' = I.decSub (__d, w) in
            let b = I.targetFam __v' in
            let Sig' =
              if b = a then (__g, (Whnf.normalize (__v', I.id))) :: Sig else Sig in
            findDec
              (__g, (n + 1), __l,
                (I.Dot
                   ((I.Exp (I.Root ((I.Proj ((I.Bidx 1), n)), I.Nil))), w)),
                Sig') in
      let rec mediateSub =
        function
        | I.Null -> (I.Null, (I.Shift (I.ctxLength Psi0)))
        | Decl (__g, __d) ->
            let (G0, s') = mediateSub __g in
            let __d' = I.decSub (__d, s') in ((I.Decl (G0, __d')), (I.dot1 s')) in
      let rec findDecs' =
        function
        | (nil, Sig) -> Sig
        | (cid::cids', Sig) ->
            let BlockDec (s, m, __g, __l) = I.sgnLookup cid in
            let (G0, s') = mediateSub __g in
            let __d' = Names.decName (G0, (I.BDec (None, (cid, s')))) in
            let s'' = I.comp (s', I.shift) in
            let Sig' = findDec ((I.Decl (G0, __d')), 1, __l, s'', Sig) in
            findDecs' (cids', Sig') in
      findDecs' (cids, nil)
    let rec staticSig =
      function
      | (Psi0, nil) -> nil
      | (Psi0, (ConDec (name, _, _, _, __v, I.Type))::Sig) ->
          (::) (I.Null, (Whnf.normalize (__v, (I.Shift (I.ctxLength Psi0)))))
            staticSig (Psi0, Sig)
    let rec name =
      function
      | a::[] -> I.conDecName (I.sgnLookup a)
      | a::__l -> ((I.conDecName (I.sgnLookup a)) ^ "/") ^ (name __l)
    let rec convertPrg (__l, projs) =
      let (name, __F0) = createIH __l in
      let D0 = T.PDec ((Some name), __F0, None, None) in
      let Psi0 = I.Decl (I.Null, D0) in
      let Prec = function | p -> T.Rec (D0, p) in
      let rec convertWorlds =
        function
        | a::[] -> let W = WorldSyn.lookup a in W
        | a::__l' ->
            let W = WorldSyn.lookup a in
            let W' = convertWorlds __l' in
            if T.eqWorlds (W, W')
            then W'
            else raise (Error "Type families different in different worlds") in
      let W = convertWorlds __l in
      let (W', wmap) = transformWorlds (__l, W) in
      let rec convertOnePrg (a, F) =
        let name = nameOf a in
        let __v = typeOf a in
        let mS = modeSpine a in
        let Sig = Worldify.worldify a in
        let dynSig = dynamicSig (Psi0, a, W) in
        let statSig = staticSig (Psi0, Sig) in
        let _ =
          map
            (function
             | ConDec (_, _, _, _, __u, __v) -> TypeCheck.check (__u, (I.Uni __v)))
            Sig in
        let _ = validSig (Psi0, statSig) in
        let _ = validSig (Psi0, dynSig) in
        let C0 = traverse (Psi0, __l, dynSig, wmap, projs) in
        let rec init =
          function
          | All ((__d, _), __F') ->
              let (__F'', __P') = init __F' in
              (__F'', ((function | p -> T.Lam (__d, (__P' p)))))
          | __F' -> (__F', ((function | p -> p))) in
        let (__F', Pinit) = init F in
        let C = traverse (Psi0, __l, statSig, wmap, projs) in
        Pinit (T.Case (T.Cases (C0 @ C))) in
      let rec convertPrg' =
        function
        | (nil, _) -> raise (Error "Cannot convert Empty program")
        | (a::[], F) -> convertOnePrg (a, F)
        | (a::__l', And (__F1, __F2)) ->
            T.PairPrg ((convertOnePrg (a, __F1)), (convertPrg' (__l', __F2))) in
      let P = Prec (convertPrg' (__l, __F0)) in P
    let rec installFor (cid::[]) =
      let F = convertFor [cid] in
      let name = I.conDecName (I.sgnLookup cid) in
      let _ = T.lemmaAdd (T.ForDec (name, F)) in ()
    let rec depthConj =
      function | And (__F1, __F2) -> (+) 1 depthConj __F2 | F -> 1
    let rec createProjection =
      function
      | (Psi, depth, (And (__F1, __F2) as F), Pattern) ->
          createProjection
            ((I.Decl (Psi, (T.PDec (None, __F1, None, None)))), (depth + 1),
              (T.forSub (__F2, (T.Shift 1))),
              (T.PairPrg ((T.Var (depth + 2)), Pattern)))
      | (Psi, depth, F, Pattern) ->
          let Psi' = I.Decl (Psi, (T.PDec (None, F, None, None))) in
          let depth' = depth + 1 in
          (function
           | k ->
               let PDec (_, __F', _, _) = T.ctxDec (Psi', k) in
               ((T.Case
                   (T.Cases
                      [(Psi', (T.Dot ((T.Prg Pattern), (T.Shift depth'))),
                         (T.Var k))])), __F'))
    let rec installProjection =
      function
      | (nil, _, F, Proj) -> nil
      | (cid::cids, n, F, Proj) ->
          let (__P', __F') = Proj n in
          let P = T.Lam ((T.PDec (None, F, None, None)), __P') in
          let __F'' = T.All (((T.PDec (None, F, None, None)), T.Explicit), __F') in
          let name = I.conDecName (I.sgnLookup cid) in
          let _ = TomegaTypeCheck.checkPrg (I.Null, (P, __F'')) in
          let lemma = T.lemmaAdd (T.ValDec (("#" ^ name), P, __F'')) in
          (::) lemma installProjection (cids, (n - 1), F, Proj)
    let rec installSelection =
      function
      | (cid::[], lemma::[], __F1, main) ->
          let P =
            T.Redex ((T.Const lemma), (T.AppPrg ((T.Const main), T.Nil))) in
          let name = I.conDecName (I.sgnLookup cid) in
          let _ = TomegaTypeCheck.checkPrg (I.Null, (P, __F1)) in
          let lemma' = T.lemmaAdd (T.ValDec (name, P, __F1)) in [lemma']
      | (cid::cids, lemma::lemmas, And (__F1, __F2), main) ->
          let P =
            T.Redex ((T.Const lemma), (T.AppPrg ((T.Const main), T.Nil))) in
          let name = I.conDecName (I.sgnLookup cid) in
          let _ = TomegaTypeCheck.checkPrg (I.Null, (P, __F1)) in
          let lemma' = T.lemmaAdd (T.ValDec (name, P, __F1)) in
          (::) lemma' installSelection (cids, lemmas, __F2, main)
    let rec installPrg =
      function
      | cid::[] ->
          let F = convertFor [cid] in
          let P = convertPrg ([cid], None) in
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
          let P = convertPrg (cids, (Some projs)) in
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
    let rec convertGoal (__g, __v) =
      let a = I.targetFam __v in
      let W = WorldSyn.lookup a in
      let (W', wmap) = transformWorlds ([a], W) in
      let Some (_, (__P', Q')) =
        traversePos ([], wmap, None)
          ((I.Null, __g, I.Null), __v,
            (Some
               ((I.Shift (I.ctxLength __g)),
                 ((function | P -> (I.Null, T.id, P)),
                   (mkResult (I.ctxLength __g)))))) in
      let (_, _, __P'') = __P' Q' in __P''
    (* ABP - 4/20/03, determine if Front is (I.Idx 1) *)
    (* strengthenExp (__u, s) = __u'

       Invariant:
       If   __g |- s : __g'
       and  __g |- __u : __v
       then __g' |- __u' = __u[s^-1] : __v [s^-1]
    *)
    (* strengthenDec (x:__v, s) = x:__v'

       Invariant:
       If   __g |- s : __g'
       and  __g |- __v : __l
       then __g' |- __v' = __v[s^-1] : __l
    *)
    (* G0 |- t : Gsome *)
    (* G0  |- s : __g' *)
    (* to show  __g' |- t o s^1 : Gsome *)
    (* strengthenCtx (__g, s) = (__g', s')

       If   G0 |- __g ctx
       and  G0 |- w : G1
       then G1 |- __g' = __g[w^-1] ctx
       and  G0 |- w' : G1, __g'
    *)
    (* strengthenFor (F, s) = __F'

       If   Psi0 |- F for
       and  Psi0 |- s :: Psi1
       then Psi1 |- __F' = F[s^-1] ctx
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
    (* createIH __l = (Psi', __P', __F')

       Invariant:
       If   __l is a list of type families
       and  Psi is a context
       then Psi' extends Psi' by declarations in __l
       and  __F' is the conjunction of the formuals
            that corresponds to each type family in __l
       and  Psi' |- __P' in __F'
    *)
    (* occursInExpN (k, __u) = B,

       Invariant:
       If    __u in nf
       then  B iff k occurs in __u
    *)
    (* | occursInExpN (k, I.FgnExp (cs, ops)) =
         occursInExpN (k, Whnf.normalize (#toInternal(ops) (), I.id)) MERGE Fri Aug 22 23:09:53 2003 --cs *)
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
    (* blocks are always used! *)
    (* createSub (Psi, __l) = t'

       Invariant:
       If  |- Psi = Psi0, Psi1 ctx
       and Psi0 contains all declarations for invariants in __l
       and |Psi0| = n
       and |__l| = k
       and n = k + m - 1
       then Psi |- t' = m, m+1 ... n. ^n :  Psi0
    *)
    (*List.length __l *)
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
    (* transformConc ((a, S), w) = P

       Invariant:
       If   Sigma (a) = {x1:A1} .. {xn:An} type
       and  Psi |- S : m1{x1:A1} .. mn{xn:An} type > type
       and  Psi |- w : PsiAll
       then P is proof term consisting of all - objects of S,
            defined in PsiAll
    *)
    (* renameExp f __u = __u'

       Invariant:
       __u' = __u module application of f to any projectoin contained
       in U.
    *)
    (* traverseNeg (__l, wmap, projs)  (Psi0, Psi, __v) = ([w', PQ'], __l')    [] means optional

           Invariant:
           If   |- Psi0 ctx      (context that contains induction hypotheses)
           and  Psi0 |- Psi ctx  (context of all assumptions)
           and  Psi0, Psi |- __v : type
           then __l' list of cases
           and  Psi0, Psi |- w' : Psi0, Psi'
           and  PQ'  is a pair that can generate a proof term
        *)
    (* Psi0, Psi |- w : Psi0, Psi' *)
    (* Sigma (a) = Va *)
    (* Psi0, Psi |- S : {__g} type > type *)
    (* Psi1 = Psi0, Psi *)
    (* Psi1 |- w0 : Psi0 *)
    (* |- Psi' ctx *)
    (* Psi1 |- w' : Psi' *)
    (* Psi' |- s'' : __g+ *)
    (* __g |- w'' : __g+ *)
    (* T.UDec *)
    (* Psi0 = x1::__F1 ... xn::Fn *)
    (* |- Psi0 matches __l *)
    (* Psi0, __g, B |- __v : type *)
    (* Psi0, __g, B |- w1 : Psi0, __g', B' *)
    (* Psi1 = Psi0, __g, B *)
    (* n = |Psi0, __g', B'| *)
    (* m = |Psi0| *)
    (* strengthened invariant Psi0 might be empty --cs Fri Apr 11 15:25:32 2003 *)
    (* apply ((S, mS), __F')= (S'', __F'')

                 Invariant:
                 Psi0, __g, B |- S : __v >> type
                   (mS is the corresponding mode spine)
                 and  Psi0, __g', B |- __F'  :: for
                 then Psi0, __g', B |- __F'' :: for
                 and  Psi0, __g', B |- S'' :: __F' >> __F''
              *)
    (* Psi0, __g', B' |- __d = x:__v' : type *)
    (* Psi0, __g', B', x:__v' |- __F' :: for *)
    (* Psi0, __g', B' |- __u' : __v' *)
    (* Psi0, __g', B' |- __F'' :: for *)
    (* Psi0, __g', B' |- S'' : __F' [t'] >> __F'' *)
    (* Psi0, __g', B' |- __u' ; S''
                                                       : all {x:__v'} __F' >> __F'' *)
    (* Psi0, __g', B' |- __F'' :: for *)
    (* Psi0, __g', B' |- S'' :: __F' >> __F'' *)
    (*T.Var k' *)
    (* was T.Root  -cs Sun Jan  5 23:15:06 2003 *)
    (* Psi0, __g', B' |- __P'' :: __F'' *)
    (* b = |B| = |B'| *)
    (* Psi0, __g |- w1' : Psi0, __g' *)
    (* |- Psi0, __g', B' ctx *)
    (* n' = |Psi0, __g'| *)
    (* Psi0, __g' |- GB' ctx *)
    (* Psi0, __g, B |- w1 : Psi0, __g', B' *)
    (* Psi0, __g', GB'  |- s' : Psi0, __g', B' *)
    (* Psi0, __g', GB' |- RR for *)
    (* Psi0, __g |- w1' : Psi0, __g' *)
    (* Psi0, __g' |- __F''' for *)
    (* lift (B, (P, F)) = (__P', __F')

                 Invariant:
                 If   Psi0, __g, B |- P :: F
                 then Psi0, __g |- __P'  :: __F'
                 and  __P' =  (lam B. P)
                 and  __F' = raiseFor (B, F)
              *)
    (* Psi0, __g' |- __P''' :: __F''' *)
    (* |- Psi0, Psi1'' ctx *)
    (* Psi0, __g, B |- w2 : Psi1'' *)
    (* Psi1'' = Psi0, G3, B3' *)
    (* |B| = |GB'| *)
    (* Psi'' |-  z2 : Psi0, __g', B' *)
    (* Psi0, __g, B |- w2 : Psi0, G3, B3' *)
    (* Psi0, __g |- w3 : Psi0, G3 *)
    (* Psi0, G3 |-  z3 : Psi0, __g' *)
    (* Psi2 = Psi0, G3 *)
    (* Psi0, G3, B3' |- Pat' :: For *)
    (* Psi0, G3 |- __F4 for *)
    (* ' __F4 *)
    (* Psi0, G3 |- Pat :: __F4  *)
    (* Here's a commutative diagram
                                           at work which one has to prove
                                           correct
                                        *)
    (* Psi0, G3 |- t :: Psi0, __g', x :: __F4  *)
    (* traverse (Psi0, __l, Sig, wmap) = C'

       Invariant:
       If   |- Psi0  ctx
       and  __l is a the theorem we would like to transform
       and  Sig is a signature
       and  forall (__g, __v) in Sig the following holds:
                    Psi0, __g |- __v : type
               and  head (__v) in __l
       and  wmap is a mapping of old labels __l to __l'
            where __l' is a new label and w' is a weakensub
            with the following properties.
            If   Sig (__l) = (Gsome, Lblock)
            and  Sig (__l') = (Gsome, Lblock')
       then C' is a list of cases (corresponding to each (__g, __v) in Sig)
    *)
    (* transformWorlds (fams, W) = (W', wmap)

       Invariant:
       If   fams is the theorem to be compiled
       and  W a world with declarations,
       then W' is the new world stripped of all dynamic extensions
       and  wmap is a mapping of old labels __l to __l'
            where __l' is a new label and w' is a weakensub
            with the following properties.
            If   Sig (__l) = (Gsome, Lblock)
            and  Sig (__l') = (Gsome, Lblock')
    *)
    (* convertList (a, __l, w) = __l'

             Invariant:
             If   G0 |- __g, __l : ctx
             and  G0, __g |- w : G0, __g'
             then G0 |- __g', __l' ctx
          *)
    (* Design decision: Let's keep all of __g *)
    (* dynamicSig (Psi0, fams, W) = Sig'

       Invariant:
       If   |- Psi0 ctx
       and  fams are the typfamilies to be converted
       and  W is the world in which the translation takes place
       then Sig' = (G1;V1) ... (Gn;Vn)
       and  |- Psi0, Gi ctx
       and  Psi, Gi |- Vi : type.
    *)
    (* findDec (__g, n, __l, s, S) = S'

             Invariant:
             If   __g |-  __l : ctx
             and  __g |- w: __g'
             then |- __g', __l' ctx
          *)
    (* mediateSub __g = (G0, s)

             Invariant:
             If   . |- __g ctx
             then Psi0 |- G0 ctx
             and  Psi0, G0 |- s : __g
          *)
    (* __g |- __l ctx *)
    (* Psi0, G0 |- s'' : __g *)
    (* Psi0, G0 |- __d : dec *)
    (* Psi0, G0, __d' |- s'' : __g *)
    (* staticSig Sig = Sig'

       Invariant:
       If   |- Psi0 ctx
       then Sig' = (c1:V1) ... (cn:Vn)
       and  . |- Vi : type.
    *)
    (* convertPrg __l = __P'

       Invariant:
       If   __l is a list of type families
       then __P' is a conjunction of all programs resulting from converting
            the relational encoding of the function expressed by each type
            family in __l into functional form
    *)
    (* W describes the world of a *)
    (* W describes the world of a *)
    (* Psi0 |- {x1:V1} ... {xn:Vn} type *)
    (* |- mS : {x1:V1} ... {xn:Vn} > type *)
    (* Sig in LF(reg)   *)
    (* init' F = __P'

               Invariant:
               If   F = All x1:A1. ... All xn:An. __F'
               and  f' does not start with a universal quantifier
               then __P' __P'' = Lam x1:A1. ... Lam xn:An __P''
                    for any __P''
            *)
    (* Psi0, x1:V1, ..., xn:Vn |- C :: F *)
    (* __F', *)
    let convertFor = convertFor
    let convertPrg = function | __l -> convertPrg (__l, None)
    let installFor = installFor
    let installPrg = installPrg
    let traverse = traverse
    let convertGoal = convertGoal
  end ;;
