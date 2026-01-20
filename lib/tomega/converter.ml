
module type CONVERTER  =
  sig
    exception Error of string 
    exception Error' of Tomega.__Sub 
    val convertFor : IntSyn.cid list -> Tomega.__For
    val convertPrg : IntSyn.cid list -> Tomega.__Prg
    val installPrg :
      IntSyn.cid list ->
        (((IntSyn.cid * Tomega.lemma list * Tomega.lemma list))(* projections *))
    val convertGoal :
      Tomega.__Dec IntSyn.__Ctx -> IntSyn.__Exp -> Tomega.__Prg
  end;;




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
                             module TomegaAbstract : TOMEGAABSTRACT
                           end) : CONVERTER =
  struct
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
      | Some mS -> mS
    let rec typeOf a =
      match I.sgnLookup a with
      | ConDec (name, _, _, _, __V, I.Kind) -> __V
      | _ -> raise (Error "Type Constant declaration expected")
    let rec nameOf a =
      match I.sgnLookup a with
      | ConDec (name, _, _, _, __V, I.Kind) -> name
      | _ -> raise (Error "Type Constant declaration expected")
    let rec chatter chlev f =
      if (!Global.chatter) >= chlev then print ((^) "[tomega] " f ()) else ()
    let rec strengthenExp (__U) s =
      Whnf.normalize ((Whnf.cloInv (__U, s)), I.id)
    let rec strengthenSub s t = Whnf.compInv (s, t)
    let rec strengthenDec __0__ __1__ =
      match (__0__, __1__) with
      | (Dec (name, __V), s) -> I.Dec (name, (strengthenExp (__V, s)))
      | (BDec (name, (__L, t)), s) ->
          I.BDec (name, (__L, (strengthenSub (t, s))))(* to show  G' |- t o s^1 : Gsome *)
      (* G0  |- s : G' *)(* G0 |- t : Gsome *)
    let rec strengthenCtx __2__ __3__ =
      match (__2__, __3__) with
      | (I.Null, s) -> (I.Null, s)
      | (Decl (__G, __D), s) ->
          let (__G', s') = strengthenCtx (__G, s) in
          ((I.Decl (__G', (strengthenDec (__D, s')))), (I.dot1 s'))
    let rec strengthenFor __4__ __5__ =
      match (__4__, __5__) with
      | (T.True, s) -> T.True
      | (And (__F1, __F2), s) ->
          T.And ((strengthenFor (__F1, s)), (strengthenFor (__F2, s)))
      | (All ((UDec (__D), __Q), __F), s) ->
          T.All
            (((T.UDec (strengthenDec (__D, s))), __Q),
              (strengthenFor (__F, (I.dot1 s))))
      | (Ex ((__D, __Q), __F), s) ->
          T.Ex
            (((strengthenDec (__D, s)), __Q),
              (strengthenFor (__F, (I.dot1 s))))
    let rec strengthenOrder __6__ __7__ =
      match (__6__, __7__) with
      | (Arg ((__U, s1), (__V, s2)), s) ->
          Order.Arg
            ((__U, (strengthenSub (s1, s))), (__V, (strengthenSub (s2, s))))
      | (Simul (__Os), s) ->
          Order.Simul (map (fun (__O) -> strengthenOrder (__O, s)) __Os)
      | (Lex (__Os), s) ->
          Order.Lex (map (fun (__O) -> strengthenOrder (__O, s)) __Os)
    let rec strengthenTC __8__ __9__ =
      match (__8__, __9__) with
      | (Base (__O), s) -> T.Base (strengthenOrder (__O, s))
      | (Conj (TC1, TC2), s) ->
          T.Conj ((strengthenTC (TC1, s)), (strengthenTC (TC2, s)))
      | (Abs (__D, TC), s) ->
          T.Abs ((strengthenDec (__D, s)), (strengthenTC (TC, (I.dot1 s))))
    let rec strengthenSpine __10__ __11__ =
      match (__10__, __11__) with
      | (I.Nil, t) -> I.Nil
      | (App (__U, __S), t) ->
          I.App ((strengthenExp (__U, t)), (strengthenSpine (__S, t)))
    let rec strengthenPsi __12__ __13__ =
      match (__12__, __13__) with
      | (I.Null, s) -> (I.Null, s)
      | (Decl (Psi, UDec (__D)), s) ->
          let (Psi', s') = strengthenPsi (Psi, s) in
          ((I.Decl (Psi', (T.UDec (strengthenDec (__D, s'))))), (I.dot1 s'))
      | (Decl (Psi, PDec (name, __F, NONE, NONE)), s) ->
          let (Psi', s') = strengthenPsi (Psi, s) in
          ((I.Decl
              (Psi', (T.PDec (name, (strengthenFor (__F, s')), NONE, NONE)))),
            (I.dot1 s'))
    let rec strengthenPsi' __14__ __15__ =
      match (__14__, __15__) with
      | (nil, s) -> (nil, s)
      | ((UDec (__D))::Psi, s) ->
          let __D' = strengthenDec (__D, s) in
          let s' = I.dot1 s in
          let (Psi'', s'') = strengthenPsi' (Psi, s') in
          (((T.UDec __D') :: Psi''), s'')
    let rec ctxSub __16__ __17__ =
      match (__16__, __17__) with
      | (I.Null, s) -> (I.Null, s)
      | (Decl (__G, __D), s) ->
          let (__G', s') = ctxSub (__G, s) in
          ((I.Decl (__G', (I.decSub (__D, s')))), (I.dot1 s))
    let rec validMode =
      function
      | M.Mnil -> ()
      | Mapp (Marg (M.Plus, _), mS) -> validMode mS
      | Mapp (Marg (M.Minus, _), mS) -> validMode mS
      | Mapp (Marg (M.Star, _), mS) ->
          raise (Error "+ or - mode expected, * found")
    let rec validSig __20__ __21__ =
      match (__20__, __21__) with
      | (Psi0, nil) -> ()
      | (Psi0, (__G, __V)::Sig) ->
          let rec append __18__ __19__ =
            match (__18__, __19__) with
            | (__G, I.Null) -> __G
            | (__G, Decl (__G', __D)) -> I.Decl ((append (__G, __G')), __D) in
          (TypeCheck.typeCheck
             ((T.coerceCtx (append (Psi0, (T.embedCtx __G)))),
               (__V, (I.Uni I.Type)));
           validSig (Psi0, Sig))
    let rec convertOneFor cid =
      let __V =
        match I.sgnLookup cid with
        | ConDec (name, _, _, _, __V, I.Kind) -> __V
        | _ -> raise (Error "Type Constant declaration expected") in
      let mS =
        match ModeTable.modeLookup cid with
        | NONE -> raise (Error "Mode declaration expected")
        | Some mS -> mS in
      let _ = validMode mS in
      let rec convertFor' __22__ __23__ __24__ __25__ __26__ =
        match (__22__, __23__, __24__, __25__, __26__) with
        | (Pi ((__D, _), __V), Mapp (Marg (M.Plus, _), mS), w1, w2, n) ->
            let (__F', F'') =
              convertFor'
                (__V, mS, (I.dot1 w1), (I.Dot ((I.Idx n), w2)), (n - 1)) in
            (((fun (__F) ->
                 T.All
                   (((T.UDec (strengthenDec (__D, w1))), T.Explicit),
                     (__F' __F)))), F'')
        | (Pi ((__D, _), __V), Mapp (Marg (M.Minus, _), mS), w1, w2, n) ->
            let (__F', F'') =
              convertFor'
                (__V, mS, (I.comp (w1, I.shift)), (I.dot1 w2), (n + 1)) in
            (__F', (T.Ex (((I.decSub (__D, w2)), T.Explicit), F'')))
        | (Uni (I.Type), M.Mnil, _, _, _) -> (((fun (__F) -> __F)), T.True)
        | _ -> raise (Error "type family must be +/- moded") in
      let rec shiftPlus mS =
        let rec shiftPlus' __27__ __28__ =
          match (__27__, __28__) with
          | (M.Mnil, n) -> n
          | (Mapp (Marg (M.Plus, _), mS'), n) -> shiftPlus' (mS', (n + 1))
          | (Mapp (Marg (M.Minus, _), mS'), n) -> shiftPlus' (mS', n) in
        shiftPlus' (mS, 0) in
      let n = shiftPlus mS in
      let (__F, __F') = convertFor' (__V, mS, I.id, (I.Shift n), n) in
      ((__F __F')
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
         *))
    let rec createIH =
      function
      | nil -> raise (Error "Empty theorem")
      | a::[] ->
          let name = I.conDecName (I.sgnLookup a) in
          let __F = convertOneFor a in (name, __F)
      | a::__L ->
          let name = I.conDecName (I.sgnLookup a) in
          let __F = convertOneFor a in
          let (name', __F') = createIH __L in
          (((name ^ "/") ^ name'), (T.And (__F, __F')))
    let rec convertFor (__L) = let (_, __F') = createIH __L in __F'
    let rec occursInExpN __29__ __30__ =
      match (__29__, __30__) with
      | (k, Uni _) -> false__
      | (k, Pi (DP, __V)) ->
          (occursInDecP (k, DP)) || (occursInExpN ((k + 1), __V))
      | (k, Root (__H, __S)) ->
          (occursInHead (k, __H)) || (occursInSpine (k, __S))
      | (k, Lam (__D, __V)) ->
          (occursInDec (k, __D)) || (occursInExpN ((k + 1), __V))
      | (k, FgnExp csfe) ->
          I.FgnExpStd.fold csfe
            (fun (__U) ->
               fun (DP) ->
                 DP || (occursInExp (k, (Whnf.normalize (__U, I.id)))))
            false__(* | occursInExpN (k, I.FgnExp (cs, ops)) =
         occursInExpN (k, Whnf.normalize (#toInternal(ops) (), I.id)) MERGE Fri Aug 22 23:09:53 2003 --cs *)
    let rec occursInHead __31__ __32__ =
      match (__31__, __32__) with
      | (k, BVar k') -> k = k'
      | (k, Const _) -> false__
      | (k, Def _) -> false__
      | (k, FgnConst _) -> false__
      | (k, Proj _) -> false__
    let rec occursInSpine __33__ __34__ =
      match (__33__, __34__) with
      | (_, I.Nil) -> false__
      | (k, App (__U, __S)) ->
          (occursInExpN (k, __U)) || (occursInSpine (k, __S))
    let rec occursInDec k (Dec (_, __V)) = occursInExpN (k, __V)
    let rec occursInDecP k (__D, _) = occursInDec (k, __D)
    let rec occursInExp k (__U) =
      occursInExpN (k, (Whnf.normalize (__U, I.id)))
    let rec dot1inv w = strengthenSub ((I.comp (I.shift, w)), I.shift)
    let rec shiftinv w = strengthenSub (w, I.shift)
    let rec peel w =
      if isIdx1 (I.bvarSub (1, w)) then dot1inv w else shiftinv w
    let rec peeln __35__ __36__ =
      match (__35__, __36__) with
      | (0, w) -> w
      | (n, w) -> peeln ((n - 1), (peel w))
    let rec popn __37__ __38__ =
      match (__37__, __38__) with
      | (0, Psi) -> (Psi, I.Null)
      | (n, Decl (Psi, UDec (__D))) ->
          let (Psi', __G') = popn ((n - 1), Psi) in
          (Psi', (I.Decl (__G', __D)))
    let rec domain __39__ __40__ =
      match (__39__, __40__) with
      | (__G, Dot (Idx _, s)) -> (domain (__G, s)) + 1
      | (I.Null, Shift 0) -> 0
      | ((Decl _ as G), Shift 0) ->
          domain (__G, (I.Dot ((I.Idx 1), (I.Shift 1))))
      | (Decl (__G, _), Shift n) -> domain (__G, (I.Shift (n - 1)))
    let rec strengthen (Psi) (a, __S) w m =
      let mS = modeSpine a in
      let rec args __41__ __42__ =
        match (__41__, __42__) with
        | (I.Nil, M.Mnil) -> nil
        | (App (__U, __S'), Mapp (Marg (m', _), mS)) ->
            let __L = args (__S', mS) in
            (match M.modeEqual (m, m') with
             | true__ -> __U :: __L
             | false__ -> __L) in
      let rec strengthenArgs __43__ __44__ =
        match (__43__, __44__) with
        | (nil, s) -> nil
        | ((__U)::__L, s) ->
            (::) (strengthenExp (__U, s)) strengthenArgs (__L, s) in
      let rec occursInArgs __45__ __46__ =
        match (__45__, __46__) with
        | (n, nil) -> false__
        | (n, (__U)::__L) ->
            (occursInExp (n, __U)) || (occursInArgs (n, __L)) in
      let rec occursInPsi __47__ __48__ =
        match (__47__, __48__) with
        | (n, (nil, __L)) -> occursInArgs (n, __L)
        | (n, ((UDec (Dec (_, __V)))::Psi1, __L)) ->
            (occursInExp (n, __V)) || (occursInPsi ((n + 1), (Psi1, __L)))
        | (n, ((UDec (BDec (_, (cid, s))))::Psi1, __L)) ->
            let BlockDec (_, _, __G, _) = I.sgnLookup cid in
            (occursInSub (n, s, __G)) || (occursInPsi ((n + 1), (Psi1, __L)))
      and occursInSub __49__ __50__ __51__ =
        match (__49__, __50__, __51__) with
        | (_, _, I.Null) -> false__
        | (n, Shift k, __G) ->
            occursInSub
              (n, (I.Dot ((I.Idx (k + 1)), (I.Shift (k + 1)))), __G)
        | (n, Dot (Idx k, s), Decl (__G, _)) ->
            (n = k) || (occursInSub (n, s, __G))
        | (n, Dot (Exp (__U), s), Decl (__G, _)) ->
            (occursInExp (n, __U)) || (occursInSub (n, s, __G))
        | (n, Dot (Block _, s), Decl (__G, _)) -> occursInSub (n, s, __G)
      and occursInG __52__ __53__ __54__ =
        match (__52__, __53__, __54__) with
        | (n, I.Null, k) -> k n
        | (n, Decl (__G, Dec (_, __V)), k) ->
            occursInG
              (n, __G, (fun n' -> (occursInExp (n', __V)) || (k (n' + 1)))) in
      let rec occursBlock (__G) (Psi2, __L) =
        let rec occursBlock __55__ __56__ =
          match (__55__, __56__) with
          | (I.Null, n) -> false__
          | (Decl (__G, __D), n) ->
              (occursInPsi (n, (Psi2, __L))) || (occursBlock (__G, (n + 1))) in
        occursBlock (__G, 1) in
      let rec inBlock __57__ __58__ =
        match (__57__, __58__) with
        | (I.Null, (bw, w1)) -> (bw, w1)
        | (Decl (__G, __D), (bw, w1)) ->
            if isIdx1 (I.bvarSub (1, w1))
            then inBlock (__G, (true__, (dot1inv w1)))
            else inBlock (__G, (bw, (strengthenSub (w1, I.shift)))) in
      let rec blockSub __59__ __60__ =
        match (__59__, __60__) with
        | (I.Null, w) -> (I.Null, w)
        | (Decl (__G, Dec (name, __V)), w) ->
            let (__G', w') = blockSub (__G, w) in
            let __V' = strengthenExp (__V, w') in
            ((I.Decl (__G', (I.Dec (name, __V')))), (I.dot1 w')) in
      let rec strengthen' __61__ __62__ __63__ __64__ =
        match (__61__, __62__, __63__, __64__) with
        | (I.Null, Psi2, __L, w1) -> (I.Null, I.id, I.id)
        | (Decl (Psi1, (UDec (Dec (name, __V)) as LD)), Psi2, __L, w1) ->
            if isIdx1 (I.bvarSub (1, w1))
            then
              let w1' = dot1inv w1 in
              let (Psi1', w', z') =
                strengthen' (Psi1, (LD :: Psi2), __L, w1') in
              let __V' = strengthenExp (__V, w') in
              ((I.Decl (Psi1', (T.UDec (I.Dec (name, __V'))))), (I.dot1 w'),
                (I.dot1 z'))
            else
              if occursInPsi (1, (Psi2, __L))
              then
                (let w1' = strengthenSub (w1, I.shift) in
                 let (Psi1', w', z') =
                   strengthen' (Psi1, (LD :: Psi2), __L, w1') in
                 let __V' = strengthenExp (__V, w') in
                 ((I.Decl (Psi1', (T.UDec (I.Dec (name, __V'))))),
                   (I.dot1 w'), (I.comp (z', I.shift))))
              else
                (let w1' = strengthenSub (w1, I.shift) in
                 let w2 = I.shift in
                 let (Psi2', w2') = strengthenPsi' (Psi2, w2) in
                 let __L' = strengthenArgs (__L, w2') in
                 let (Psi1'', w', z') = strengthen' (Psi1, Psi2', __L', w1') in
                 (Psi1'', (I.comp (w', I.shift)), z'))
        | (Decl (Psi1, (PDec (name, __F, NONE, NONE) as D)), Psi2, __L, w1)
            ->
            let w1' = dot1inv w1 in
            let (Psi1', w', z') = strengthen' (Psi1, (__D :: Psi2), __L, w1') in
            let __F' = strengthenFor (__F, w') in
            ((I.Decl (Psi1', (T.PDec (name, __F', NONE, NONE)))),
              (I.dot1 w'), (I.dot1 z'))
        | (Decl (Psi1, (UDec (BDec (name, (cid, s))) as LD)), Psi2, __L, w1)
            ->
            let w1' = dot1inv w1 in
            let (Psi1', w', z') = strengthen' (Psi1, (LD :: Psi2), __L, w1') in
            let s' = strengthenSub (s, w') in
            ((((I.Decl (Psi1', (T.UDec (I.BDec (name, (cid, s')))))),
                (I.dot1 w'), (I.dot1 z')))
              (* blocks are always used! *))(* =  I.id *) in
      ((strengthen' (Psi, nil, (args (__S, mS)), w))
        (* is this ok? -- cs *)(* no other cases *)
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
        *))
    let rec lookupIH (Psi) (__L) a =
      let rec lookupIH' (b::__L) a k =
        if a = b then k else lookupIH' (__L, a, (k - 1)) in
      lookupIH' (__L, a, (I.ctxLength Psi))
    let rec createIHSub (Psi) (__L) =
      T.Shift (((I.ctxLength Psi) - 1)(*List.length L *))
    let rec transformInit (Psi) (__L) (a, __S) w1 =
      let mS = modeSpine a in
      let __V = typeOf a in
      let rec transformInit' __65__ __66__ __67__ =
        match (__65__, __66__, __67__) with
        | ((I.Nil, M.Mnil), Uni (I.Type), (w, s)) -> (w, s)
        | ((App (__U, __S), Mapp (Marg (M.Minus, _), mS)), Pi (_, __V2),
           (w, s)) ->
            let w' = I.comp (w, I.shift) in
            let s' = s in transformInit' ((__S, mS), __V2, (w', s'))
        | ((App (__U, __S), Mapp (Marg (M.Plus, _), mS)), Pi
           ((Dec (name, __V1), _), __V2), (w, s)) ->
            let V1' = strengthenExp (__V1, w) in
            let w' = I.dot1 w in
            let __U' = strengthenExp (__U, w1) in
            let s' = T.dotEta ((T.Exp __U'), s) in
            transformInit' ((__S, mS), __V2, (w', s')) in
      ((transformInit' ((__S, mS), __V, (I.id, (createIHSub (Psi, __L)))))
        (* transformInit' ((S, mS), V, (w, s)) = (w', s')

           Invariant:
           If   Psi |- S : V > type
           and  x1:A1...x(j-1):A(j-1) |- V = mj{xj:Aj} .. mn{xn:An} type : kind
           and  x1:A1...x(j-1):A(j-1) |- w : +x1:A1... +x(j-1):A(j-1)
           and  Psi |- w1 : Psi+
           and  Psi+ |- s : +x1:A1... +x(j-1):A(j-1)
           then x1:A1...xn:An |- w' : +x1:A1... +xn:An
           and  Psi+ |- s' : +x1:A1 .. +xn:An
        *))
    let rec transformConc (a, __S) w =
      let rec transformConc' __68__ __69__ =
        match (__68__, __69__) with
        | (I.Nil, M.Mnil) -> T.Unit
        | (App (__U, __S'), Mapp (Marg (M.Plus, _), mS')) ->
            transformConc' (__S', mS')
        | (App (__U, __S'), Mapp (Marg (M.Minus, _), mS')) ->
            T.PairExp
              ((strengthenExp (__U, w)), (transformConc' (__S', mS'))) in
      transformConc' (__S, (modeSpine a))
    let rec renameExp __70__ __71__ =
      match (__70__, __71__) with
      | (f, (Uni _ as U)) -> __U
      | (f, Pi ((__D, DP), __V)) ->
          I.Pi (((renameDec f __D), DP), (renameExp f __V))
      | (f, Root (__H, __S)) ->
          I.Root ((renameHead f __H), (renameSpine f __S))
      | (f, Lam (__D, __U)) -> I.Lam ((renameDec f __D), (renameExp f __U))
    let rec renameDec f (Dec (x, __V)) = I.Dec (x, (renameExp f __V))
    let rec renameHead __72__ __73__ =
      match (__72__, __73__) with | (f, Proj bi) -> f bi | (f, __H) -> __H
    let rec renameSpine __74__ __75__ =
      match (__74__, __75__) with
      | (f, I.Nil) -> I.Nil
      | (f, App (__U, __S)) -> I.App ((renameExp f __U), (renameSpine f __S))
    let rec rename (BDec (_, (c, s))) (__V) =
      let (__G, __L) = I.constBlock c in
      let rec makeSubst __76__ __77__ __78__ __79__ __80__ =
        match (__76__, __77__, __78__, __79__, __80__) with
        | (n, __G, s, nil, f) -> (__G, f)
        | (n, __G, s, (Dec (x, __V') as D)::__L, f) ->
            if Subordinate.belowEq ((I.targetFam __V'), (I.targetFam __V))
            then
              makeSubst
                ((n + 1), (I.Decl (__G, (I.decSub (__D, s)))), (I.dot1 s),
                  __L, f)
            else makeSubst (n, __G, (I.comp (s, I.shift)), __L, f) in
      let (__G', f) = makeSubst (1, __G, s, __L, (fun x -> I.Proj x)) in
      (__G, (renameExp f __V))
    let rec append __81__ __82__ =
      match (__81__, __82__) with
      | (__G, I.Null) -> __G
      | (__G, Decl (__G', __D)) -> I.Decl ((append (__G, __G')), __D)
    let rec traverseNeg __83__ __84__ __85__ __86__ __87__ __88__ =
      match (__83__, __84__, __85__, __86__, __87__, __88__) with
      | (__L, wmap, projs, (Psi0, Psi), Pi
         (((Dec (_, __V1) as D), I.Maybe), __V2), w) ->
          (match traverseNeg (__L, wmap, projs)
                   ((Psi0, (I.Decl (Psi, (T.UDec __D)))), __V2, (I.dot1 w))
           with
           | Some (w', PQ') -> Some ((peel w'), PQ'))
      | (__L, wmap, projs, (Psi0, Psi), Pi
         (((Dec (_, __V1) as D), I.No), __V2), w) ->
          (match traverseNeg (__L, wmap, projs)
                   ((Psi0, (I.Decl (Psi, (T.UDec __D)))), __V2,
                     (I.comp (w, I.shift)))
           with
           | Some (w', PQ') ->
               traversePos (__L, wmap, projs)
                 ((Psi0, Psi, I.Null), __V1, (Some ((peel w'), PQ'))))
      | (__L, wmap, projs, (Psi0, Psi), Root (Const a, __S), w) ->
          let Psi1 = append (Psi0, Psi) in
          let w0 = I.Shift (I.ctxLength Psi) in
          let (Psi', w', _) = strengthen (Psi1, (a, __S), w0, M.Plus) in
          let (w'', s'') = transformInit (Psi', __L, (a, __S), w') in
          let _ = TomegaTypeCheck.checkCtx Psi' in
          ((Some
              (w',
                ((fun (__P) -> (Psi', s'', __P)),
                  (transformConc ((a, __S), w)))))
            (* Psi1 = Psi0, Psi *)(* Psi1 |- w0 : Psi0 *)
            (* |- Psi' ctx *)(* Psi1 |- w' : Psi' *)
            (* Psi' |- s'' : G+ *)(* G |- w'' : G+ *))
      (* Psi0, Psi |- S : {G} type > type *)(* Sigma (a) = Va *)
      (* Psi0, Psi |- w : Psi0, Psi' *)
    let rec traversePos __97__ __98__ __99__ __100__ __101__ __102__ =
      match (__97__, __98__, __99__, __100__, __101__, __102__) with
      | (__L, wmap, projs, (Psi0, Psi, __G), Pi
         (((BDec (x, (c, s)) as D), _), __V), Some (w1, (__P, __Q))) ->
          let c' = wmap c in
          let n = (+) (I.ctxLength Psi0) I.ctxLength __G in
          let (Gsome, Lpi) = I.constBlock c in
          let _ =
            TypeCheck.typeCheckCtx
              (T.coerceCtx (append ((append (Psi0, Psi)), (T.embedCtx __G)))) in
          let _ =
            TypeCheck.typeCheckSub
              ((T.coerceCtx (append ((append (Psi0, Psi)), (T.embedCtx __G)))),
                s, Gsome) in
          let (Gsome', Lpi') = I.constBlock c' in
          let _ =
            TypeCheck.typeCheckCtx
              (T.coerceCtx (append ((append (Psi0, Psi)), (T.embedCtx __G)))) in
          let _ =
            TypeCheck.typeCheckSub
              ((T.coerceCtx (append ((append (Psi0, Psi)), (T.embedCtx __G)))),
                s, Gsome') in
          traversePos (__L, wmap, projs)
            ((Psi0, Psi,
               (I.Decl (((__G, (I.BDec (x, (c', s)))))
                  (* T.UDec *)))), __V,
              (Some ((I.dot1 w1), (__P, __Q))))
      | (__L, wmap, projs, (Psi0, __G, __B), (Root (Const a, __S) as V), Some
         (w1, (__P, __Q))) ->
          let Psi1 = append (Psi0, (append (__G, (T.embedCtx __B)))) in
          let _ =
            TomegaTypeCheck.checkCtx
              (append ((append (Psi0, __G)), (T.embedCtx __B))) in
          let n = domain (Psi1, w1) in
          let m = I.ctxLength Psi0 in
          let rec lookupbase a =
            let s = I.conDecName (I.sgnLookup a) in
            let l = T.lemmaName s in
            let ValDec (_, __P, __F) = T.lemmaLookup l in ((T.Const l), __F) in
          let rec lookup __89__ __90__ =
            match (__89__, __90__) with
            | ((b::[], NONE, __F), a) ->
                if a = b
                then let __P = T.Var n in (__P, __F)
                else lookupbase a
            | ((b::[], Some (lemma::[]), __F), a) ->
                if a = b
                then
                  let __P =
                    T.Redex ((T.Const lemma), (T.AppPrg ((T.Var n), T.Nil))) in
                  (__P, __F)
                else lookupbase a
            | ((b::__L, Some (lemma::lemmas), And (__F1, __F2)), a) ->
                if a = b
                then
                  let __P =
                    T.Redex ((T.Const lemma), (T.AppPrg ((T.Var n), T.Nil))) in
                  (__P, __F1)
                else lookup ((__L, (Some lemmas), __F2), a) in
          let (HP, __F) =
            if (I.ctxLength Psi0) > 0
            then
              let PDec (_, __F0, _, _) = I.ctxLookup (Psi0, 1) in
              lookup ((__L, projs, __F0), a)
            else lookupbase a in
          let rec apply (__S, mS) (Ft) = applyW ((__S, mS), (T.whnfFor Ft))
          and applyW __91__ __92__ =
            match (__91__, __92__) with
            | ((I.Nil, M.Mnil), Ft') -> (T.Nil, (T.forSub Ft'))
            | ((App (__U, __S), Mapp (Marg (M.Plus, _), mS)),
               (All (__D, __F'), t')) ->
                let __U' = strengthenExp (__U, w1) in
                let (S'', F'') =
                  apply ((__S, mS), (__F', (T.Dot ((T.Exp __U'), t')))) in
                ((((T.AppExp (__U', S'')), F''))
                  (* Psi0, G', B' |- U' : V' *)(* Psi0, G', B' |- F'' :: for *)
                  (* Psi0, G', B' |- S'' : F' [t'] >> F'' *)
                  (* Psi0, G', B' |- U' ; S''
                                                       : all {x:V'} F' >> F'' *))
            | ((App (__U, __S), Mapp (Marg (M.Minus, _), mS)), Ft) ->
                applyW ((__S, mS), Ft)(* Psi0, G', B', x:V' |- F' :: for *)
          (* Psi0, G', B' |- D = x:V' : type *) in
          let (S'', F'') = apply ((__S, (modeSpine a)), (__F, T.id)) in
          let _ =
            TomegaTypeCheck.checkFor
              ((append ((append (Psi0, __G)), (T.embedCtx __B))),
                (T.forSub (F'', (T.embedSub w1)))) in
          let P'' = T.Redex (((HP, S''))(*T.Var k' *)) in
          let b = I.ctxLength __B in
          let w1' = peeln (b, w1) in
          let (__B', _) = strengthenCtx (__B, w1') in
          let n' = (-) n I.ctxLength __B' in
          let rec subCtx __93__ __94__ =
            match (__93__, __94__) with
            | (I.Null, s) -> (I.Null, s)
            | (Decl (__G, __D), s) ->
                let (__G', s') = subCtx (__G, s) in
                ((I.Decl (__G', (I.decSub (__D, s')))), (I.dot1 s')) in
          let (B'', _) = subCtx (__B', w1') in
          let _ =
            TomegaTypeCheck.checkCtx
              (append ((append (Psi0, __G)), (T.embedCtx B''))) in
          let (GB', iota) = T.deblockify __B' in
          let _ =
            try TypeCheck.typeCheckSub (GB', (T.coerceSub iota), __B')
            with | Error _ -> raise (Error' iota) in
          let RR = T.forSub (F'', iota) in
          let F''' = TA.raiseFor (GB', (RR, I.id)) in
          let rec lift __95__ __96__ =
            match (__95__, __96__) with
            | (I.Null, __P) -> __P
            | (Decl (__G, __D), __P) ->
                let (Bint, _) = T.deblockify (I.Decl (I.Null, __D)) in
                lift (__G, (T.New (T.Lam ((T.UDec __D), __P)))) in
          let P''' = lift (__B', P'') in
          let _ = TomegaTypeCheck.checkCtx (append (Psi0, __G)) in
          let _ =
            TomegaTypeCheck.checkFor
              ((append (Psi0, __G)), (T.forSub (F''', (T.embedSub w1')))) in
          let (Psi1'', w2, z2) = strengthen (Psi1, (a, __S), w1, M.Minus) in
          let w3 = peeln (b, w2) in
          let z3 = peeln (b, z2) in
          let (Psi2, B3') = popn (b, Psi1'') in
          let Pat' = transformConc ((a, __S), w2) in
          let __F4 = T.forSub (F''', (T.embedSub z3)) in
          let _ = TomegaTypeCheck.checkCtx Psi1'' in
          let _ = TomegaTypeCheck.checkCtx (append (Psi2, (T.embedCtx B3'))) in
          let _ =
            try TomegaTypeCheck.checkFor (Psi2, __F4)
            with | _ -> raise (Error "") in
          let (__B3, sigma3) = T.deblockify B3' in
          let Pat'' = T.normalizePrg (Pat', sigma3) in
          let Pat = TA.raisePrg (__B3, Pat'', __F4) in
          let _ = TomegaTypeCheck.checkPrg (Psi2, (Pat, __F4)) in
          let t = T.Dot ((T.Prg Pat), (T.embedSub z3)) in
          ((Some
              (w3,
                ((fun p ->
                    __P
                      (T.Let
                         ((T.PDec (NONE, F''', NONE, NONE)), P''',
                           (T.Case (T.Cases [(Psi2, t, p)]))))), __Q)))
            (* Psi1 = Psi0, G, B *)(* n = |Psi0, G', B'| *)
            (* m = |Psi0| *)(* strengthened invariant Psi0 might be empty --cs Fri Apr 11 15:25:32 2003 *)
            (* apply ((S, mS), F')= (S'', F'')

                 Invariant:
                 Psi0, G, B |- S : V >> type
                   (mS is the corresponding mode spine)
                 and  Psi0, G', B |- F'  :: for
                 then Psi0, G', B |- F'' :: for
                 and  Psi0, G', B |- S'' :: F' >> F''
              *)
            (* Psi0, G', B' |- F'' :: for *)(* Psi0, G', B' |- S'' :: F' >> F'' *)
            (* was T.Root  -cs Sun Jan  5 23:15:06 2003 *)
            (* Psi0, G', B' |- P'' :: F'' *)(* b = |B| = |B'| *)
            (* Psi0, G |- w1' : Psi0, G' *)(* |- Psi0, G', B' ctx *)
            (* n' = |Psi0, G'| *)(* Psi0, G' |- GB' ctx *)
            (* Psi0, G, B |- w1 : Psi0, G', B' *)(* Psi0, G', GB'  |- s' : Psi0, G', B' *)
            (* Psi0, G', GB' |- RR for *)(* Psi0, G |- w1' : Psi0, G' *)
            (* Psi0, G' |- F''' for *)(* lift (B, (P, F)) = (P', F')

                 Invariant:
                 If   Psi0, G, B |- P :: F
                 then Psi0, G |- P'  :: F'
                 and  P' =  (lam B. P)
                 and  F' = raiseFor (B, F)
              *)
            (* Psi0, G' |- P''' :: F''' *)(* |- Psi0, Psi1'' ctx *)
            (* Psi0, G, B |- w2 : Psi1'' *)(* Psi1'' = Psi0, G3, B3' *)
            (* |B| = |GB'| *)(* Psi'' |-  z2 : Psi0, G', B' *)
            (* Psi0, G, B |- w2 : Psi0, G3, B3' *)(* Psi0, G |- w3 : Psi0, G3 *)
            (* Psi0, G3 |-  z3 : Psi0, G' *)(* Psi2 = Psi0, G3 *)
            (* Psi0, G3, B3' |- Pat' :: For *)(* Psi0, G3 |- F4 for *)
            (* ' F4 *)(* Psi0, G3 |- Pat :: F4  *)
            (* Here's a commutative diagram
                                           at work which one has to prove
                                           correct
                                        *)
            (* Psi0, G3 |- t :: Psi0, G', x :: F4  *))
      (* Psi0, G, B |- w1 : Psi0, G', B' *)(* Psi0, G, B |- V : type *)
      (* |- Psi0 matches L *)(* Psi0 = x1::F1 ... xn::Fn *)
    let rec traverse (Psi0) (__L) (Sig) wmap projs =
      let rec traverseSig' =
        function
        | nil -> nil
        | (__G, __V)::Sig ->
            (TypeCheck.typeCheck
               ((append ((T.coerceCtx Psi0), __G)), (__V, (I.Uni I.Type)));
             (match traverseNeg (__L, wmap, projs)
                      ((Psi0, (T.embedCtx __G)), __V, I.id)
              with
              | Some (wf, (__P', __Q')) -> (traverseSig' Sig) @ [__P' __Q'])) in
      traverseSig' Sig
    let rec transformWorlds fams (Worlds cids) =
      let rec transformList __103__ __104__ =
        match (__103__, __104__) with
        | (nil, w) -> nil
        | ((Dec (x, __V) as D)::__L, w) ->
            if
              List.foldr
                (fun a ->
                   fun b -> b && (Subordinate.belowEq (a, (I.targetFam __V))))
                true__ fams
            then transformList (__L, (I.comp (w, I.shift)))
            else
              (let __L' = transformList (__L, (I.dot1 w)) in
               (I.Dec (x, (strengthenExp (__V, w)))) :: __L') in
      let rec transformWorlds' =
        function
        | nil -> (nil, ((fun c -> raise (Error "World not found"))))
        | cid::cids' ->
            let BlockDec (s, m, __G, __L) = I.sgnLookup cid in
            let __L' = transformList (__L, I.id) in
            let (cids'', wmap) = transformWorlds' cids' in
            let cid' = I.sgnAdd (I.BlockDec (s, m, __G, __L')) in
            ((((cid' :: cids''),
                ((fun c -> if c = cid then cid' else wmap c))))
              (* Design decision: Let's keep all of G *)) in
      let (cids', wmap) = transformWorlds' cids in
      ((((T.Worlds cids'), wmap))
        (* convertList (a, L, w) = L'

             Invariant:
             If   G0 |- G, L : ctx
             and  G0, G |- w : G0, G'
             then G0 |- G', L' ctx
          *))
    let rec dynamicSig (Psi0) a (Worlds cids) =
      let rec findDec __105__ __106__ __107__ __108__ __109__ =
        match (__105__, __106__, __107__, __108__, __109__) with
        | (__G, _, nil, w, Sig) -> Sig
        | (__G, n, (__D)::__L, w, Sig) ->
            let Dec (x, __V') as D' = I.decSub (__D, w) in
            let b = I.targetFam __V' in
            let Sig' =
              if b = a
              then (__G, (Whnf.normalize (__V', I.id))) :: Sig
              else Sig in
            findDec
              (__G, (n + 1), __L,
                (I.Dot
                   ((I.Exp (I.Root ((I.Proj ((I.Bidx 1), n)), I.Nil))), w)),
                Sig') in
      let rec mediateSub =
        function
        | I.Null -> (I.Null, (I.Shift (I.ctxLength Psi0)))
        | Decl (__G, __D) ->
            let (__G0, s') = mediateSub __G in
            let __D' = I.decSub (__D, s') in
            ((I.Decl (__G0, __D')), (I.dot1 s')) in
      let rec findDecs' __110__ __111__ =
        match (__110__, __111__) with
        | (nil, Sig) -> Sig
        | (cid::cids', Sig) ->
            let BlockDec (s, m, __G, __L) = I.sgnLookup cid in
            let (__G0, s') = mediateSub __G in
            let __D' = Names.decName (__G0, (I.BDec (NONE, (cid, s')))) in
            let s'' = I.comp (s', I.shift) in
            let Sig' = findDec ((I.Decl (__G0, __D')), 1, __L, s'', Sig) in
            ((findDecs' (cids', Sig'))
              (* G |- L ctx *)(* Psi0, G0 |- s'' : G *)
              (* Psi0, G0 |- D : dec *)(* Psi0, G0, D' |- s'' : G *)) in
      ((findDecs' (cids, nil))
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
          *))
    let rec staticSig __112__ __113__ =
      match (__112__, __113__) with
      | (Psi0, nil) -> nil
      | (Psi0, (ConDec (name, _, _, _, __V, I.Type))::Sig) ->
          (::) (I.Null, (Whnf.normalize (__V, (I.Shift (I.ctxLength Psi0)))))
            staticSig (Psi0, Sig)
    let rec name =
      function
      | a::[] -> I.conDecName (I.sgnLookup a)
      | a::__L -> ((I.conDecName (I.sgnLookup a)) ^ "/") ^ (name __L)
    let rec convertPrg (__L) projs =
      let (name, __F0) = createIH __L in
      let __D0 = T.PDec ((Some name), __F0, NONE, NONE) in
      let Psi0 = I.Decl (I.Null, __D0) in
      let Prec = fun p -> T.Rec (__D0, p) in
      let rec convertWorlds =
        function
        | a::[] ->
            let __W = WorldSyn.lookup a in ((__W)
              (* W describes the world of a *))
        | a::__L' ->
            let __W = WorldSyn.lookup a in
            let __W' = convertWorlds __L' in
            ((if T.eqWorlds (__W, __W')
              then __W'
              else
                raise (Error "Type families different in different worlds"))
              (* W describes the world of a *)) in
      let __W = convertWorlds __L in
      let (__W', wmap) = transformWorlds (__L, __W) in
      let rec convertOnePrg a (__F) =
        let name = nameOf a in
        let __V = typeOf a in
        let mS = modeSpine a in
        let Sig = Worldify.worldify a in
        let dynSig = dynamicSig (Psi0, a, __W) in
        let statSig = staticSig (Psi0, Sig) in
        let _ =
          map
            (fun (ConDec (_, _, _, _, __U, __V)) ->
               TypeCheck.check (__U, (I.Uni __V))) Sig in
        let _ = validSig (Psi0, statSig) in
        let _ = validSig (Psi0, dynSig) in
        let __C0 = traverse (Psi0, __L, dynSig, wmap, projs) in
        let rec init =
          function
          | All ((__D, _), __F') ->
              let (F'', __P') = init __F' in
              (F'', ((fun p -> T.Lam (__D, (__P' p)))))
          | __F' -> (__F', ((fun p -> p))) in
        let (__F', Pinit) = init __F in
        let __C = traverse (Psi0, __L, statSig, wmap, projs) in
        ((Pinit (T.Case ((T.Cases (__C0 @ __C))(* F', *))))
          (* Psi0 |- {x1:V1} ... {xn:Vn} type *)(* |- mS : {x1:V1} ... {xn:Vn} > type *)
          (* Sig in LF(reg)   *)(* init' F = P'

               Invariant:
               If   F = All x1:A1. ... All xn:An. F'
               and  f' does not start with a universal quantifier
               then P' P'' = Lam x1:A1. ... Lam xn:An P''
                    for any P''
            *)
          (* Psi0, x1:V1, ..., xn:Vn |- C :: F *)) in
      let rec convertPrg' __114__ __115__ =
        match (__114__, __115__) with
        | (nil, _) -> raise (Error "Cannot convert Empty program")
        | (a::[], __F) -> convertOnePrg (a, __F)
        | (a::__L', And (__F1, __F2)) ->
            T.PairPrg ((convertOnePrg (a, __F1)), (convertPrg' (__L', __F2))) in
      let __P = Prec (convertPrg' (__L, __F0)) in __P
    let rec installFor (cid::[]) =
      let __F = convertFor [cid] in
      let name = I.conDecName (I.sgnLookup cid) in
      let _ = T.lemmaAdd (T.ForDec (name, __F)) in ()
    let rec depthConj =
      function | And (__F1, __F2) -> (+) 1 depthConj __F2 | __F -> 1
    let rec createProjection __116__ __117__ __118__ __119__ =
      match (__116__, __117__, __118__, __119__) with
      | (Psi, depth, (And (__F1, __F2) as F), Pattern) ->
          createProjection
            ((I.Decl (Psi, (T.PDec (NONE, __F1, NONE, NONE)))), (depth + 1),
              (T.forSub (__F2, (T.Shift 1))),
              (T.PairPrg ((T.Var (depth + 2)), Pattern)))
      | (Psi, depth, __F, Pattern) ->
          let Psi' = I.Decl (Psi, (T.PDec (NONE, __F, NONE, NONE))) in
          let depth' = depth + 1 in
          (fun k ->
             let PDec (_, __F', _, _) = T.ctxDec (Psi', k) in
             ((T.Case
                 (T.Cases
                    [(Psi', (T.Dot ((T.Prg Pattern), (T.Shift depth'))),
                       (T.Var k))])), __F'))
    let rec installProjection __120__ __121__ __122__ __123__ =
      match (__120__, __121__, __122__, __123__) with
      | (nil, _, __F, Proj) -> nil
      | (cid::cids, n, __F, Proj) ->
          let (__P', __F') = Proj n in
          let __P = T.Lam ((T.PDec (NONE, __F, NONE, NONE)), __P') in
          let F'' =
            T.All (((T.PDec (NONE, __F, NONE, NONE)), T.Explicit), __F') in
          let name = I.conDecName (I.sgnLookup cid) in
          let _ = TomegaTypeCheck.checkPrg (I.Null, (__P, F'')) in
          let lemma = T.lemmaAdd (T.ValDec (("#" ^ name), __P, F'')) in
          (::) lemma installProjection (cids, (n - 1), __F, Proj)
    let rec installSelection __124__ __125__ __126__ __127__ =
      match (__124__, __125__, __126__, __127__) with
      | (cid::[], lemma::[], __F1, main) ->
          let __P =
            T.Redex ((T.Const lemma), (T.AppPrg ((T.Const main), T.Nil))) in
          let name = I.conDecName (I.sgnLookup cid) in
          let _ = TomegaTypeCheck.checkPrg (I.Null, (__P, __F1)) in
          let lemma' = T.lemmaAdd (T.ValDec (name, __P, __F1)) in [lemma']
      | (cid::cids, lemma::lemmas, And (__F1, __F2), main) ->
          let __P =
            T.Redex ((T.Const lemma), (T.AppPrg ((T.Const main), T.Nil))) in
          let name = I.conDecName (I.sgnLookup cid) in
          let _ = TomegaTypeCheck.checkPrg (I.Null, (__P, __F1)) in
          let lemma' = T.lemmaAdd (T.ValDec (name, __P, __F1)) in
          (::) lemma' installSelection (cids, lemmas, __F2, main)
    let rec installPrg =
      function
      | cid::[] ->
          let __F = convertFor [cid] in
          let __P = convertPrg ([cid], NONE) in
          let name = I.conDecName (I.sgnLookup cid) in
          let _ = TomegaTypeCheck.checkPrg (I.Null, (__P, __F)) in
          let _ =
            if (!Global.chatter) >= 4
            then print "[Redundancy Checker (factoring) ..."
            else () in
          let factP = Redundant.convert __P in
          let _ = if (!Global.chatter) >= 4 then print "done]\n" else () in
          let lemma = T.lemmaAdd (T.ValDec (name, factP, __F)) in
          (lemma, [], [])
      | cids ->
          let __F = convertFor cids in
          let _ = TomegaTypeCheck.checkFor (I.Null, __F) in
          let Proj = createProjection (I.Null, 0, __F, (T.Var 1)) in
          let projs = installProjection (cids, (depthConj __F), __F, Proj) in
          let __P = convertPrg (cids, (Some projs)) in
          let s = name cids in
          let _ = TomegaTypeCheck.checkPrg (I.Null, (__P, __F)) in
          let _ =
            if (!Global.chatter) >= 4
            then print "[Redundancy Checker (factoring) ..."
            else () in
          let factP = Redundant.convert __P in
          let _ = if (!Global.chatter) >= 4 then print "done]\n" else () in
          let lemma = T.lemmaAdd (T.ValDec (s, factP, __F)) in
          let sels = installSelection (cids, projs, __F, lemma) in
          (lemma, projs, sels)
    let rec mkResult =
      function
      | 0 -> T.Unit
      | n -> T.PairExp ((I.Root ((I.BVar n), I.Nil)), (mkResult (n - 1)))
    let rec convertGoal (__G) (__V) =
      let a = I.targetFam __V in
      let __W = WorldSyn.lookup a in
      let (__W', wmap) = transformWorlds ([a], __W) in
      let Some (_, (__P', __Q')) =
        traversePos ([], wmap, NONE)
          ((I.Null, __G, I.Null), __V,
            (Some
               ((I.Shift (I.ctxLength __G)),
                 ((fun (__P) -> (I.Null, T.id, __P)),
                   (mkResult (I.ctxLength __G)))))) in
      let (_, _, P'') = __P' __Q' in P''
    let convertFor = convertFor
    let convertPrg (__L) = convertPrg (__L, NONE)
    let installFor = installFor
    let installPrg = installPrg
    let traverse = traverse
    let convertGoal = convertGoal
  end ;;
