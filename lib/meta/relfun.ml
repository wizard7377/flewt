
module type RELFUN  =
  sig
    exception Error of string 
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
                       module FunNames : FUNNAMES
                     end) : RELFUN =
  struct
    exception Error of string 
    module F = FunSyn
    module I = IntSyn
    module M = ModeSyn
    let rec ctxSub __0__ __1__ =
      match (__0__, __1__) with
      | (I.Null, s) -> (I.Null, s)
      | (Decl (__G, __D), s) ->
          let (__G', s') = ctxSub (__G, s) in
          ((I.Decl (__G', (I.decSub (__D, s')))), (I.dot1 s))
    let rec convertOneFor cid =
      let __V =
        match I.sgnLookup cid with
        | ConDec (name, _, _, _, __V, I.Kind) -> __V
        | _ -> raise (Error "Type Constant declaration expected") in
      let mS =
        match ModeTable.modeLookup cid with
        | NONE -> raise (Error "Mode declaration expected")
        | Some mS -> mS in
      let rec convertFor' __2__ __3__ __4__ __5__ __6__ =
        match (__2__, __3__, __4__, __5__, __6__) with
        | (Pi ((__D, _), __V), Mapp (Marg (M.Plus, _), mS), w1, w2, n) ->
            let (__F', F'') =
              convertFor'
                (__V, mS, (I.dot1 w1), (I.Dot ((I.Idx n), w2)), (n - 1)) in
            (((fun (__F) ->
                 F.All
                   ((F.Prim (Weaken.strengthenDec (__D, w1))), (__F' __F)))),
              F'')
        | (Pi ((__D, _), __V), Mapp (Marg (M.Minus, _), mS), w1, w2, n) ->
            let (__F', F'') =
              convertFor'
                (__V, mS, (I.comp (w1, I.shift)), (I.dot1 w2), (n + 1)) in
            (__F', (F.Ex ((I.decSub (__D, w2)), F'')))
        | (Uni (I.Type), M.Mnil, _, _, _) -> (((fun (__F) -> __F)), F.True)
        | _ -> raise (Error "type family must be +/- moded") in
      let rec shiftPlus mS =
        let rec shiftPlus' __7__ __8__ =
          match (__7__, __8__) with
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
    let rec convertFor =
      function
      | nil -> raise (Error "Empty theorem")
      | a::[] -> convertOneFor a
      | a::__L -> F.And ((convertOneFor a), (convertFor __L))
    let rec occursInExpN __9__ __10__ =
      match (__9__, __10__) with
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
               fun (__B) ->
                 __B || (occursInExpN (k, (Whnf.normalize (__U, I.id)))))
            false__
    let rec occursInHead __11__ __12__ =
      match (__11__, __12__) with
      | (k, BVar k') -> k = k'
      | (k, Const _) -> false__
      | (k, Def _) -> false__
      | (k, FgnConst _) -> false__
    let rec occursInSpine __13__ __14__ =
      match (__13__, __14__) with
      | (_, I.Nil) -> false__
      | (k, App (__U, __S)) ->
          (occursInExpN (k, __U)) || (occursInSpine (k, __S))
    let rec occursInDec k (Dec (_, __V)) = occursInExpN (k, __V)
    let rec occursInDecP k (__D, _) = occursInDec (k, __D)
    let rec occursInExp k (__U) =
      occursInExpN (k, (Whnf.normalize (__U, I.id)))
    let rec dot1inv w = Weaken.strengthenSub ((I.comp (I.shift, w)), I.shift)
    let rec shiftinv w = Weaken.strengthenSub (w, I.shift)
    let rec eqIdx __15__ __16__ =
      match (__15__, __16__) with | (Idx n, Idx k) -> n = k | _ -> false__
    let rec peel w =
      if eqIdx ((I.bvarSub (1, w)), (I.Idx 1)) then dot1inv w else shiftinv w
    let rec peeln __17__ __18__ =
      match (__17__, __18__) with
      | (0, w) -> w
      | (n, w) -> peeln ((n - 1), (peel w))
    let rec domain __19__ __20__ =
      match (__19__, __20__) with
      | (__G, Dot (Idx _, s)) -> (domain (__G, s)) + 1
      | (I.Null, Shift 0) -> 0
      | ((Decl _ as G), Shift 0) ->
          domain (__G, (I.Dot ((I.Idx 1), (I.Shift 1))))
      | (Decl (__G, _), Shift n) -> domain (__G, (I.Shift (n - 1)))
    let rec strengthen (Psi) (a, __S) w m =
      let mS =
        match ModeTable.modeLookup a with
        | NONE -> raise (Error "Mode declaration expected")
        | Some mS -> mS in
      let rec args __21__ __22__ =
        match (__21__, __22__) with
        | (I.Nil, M.Mnil) -> nil
        | (App (__U, __S'), Mapp (Marg (m', _), mS)) ->
            let __L = args (__S', mS) in
            (match M.modeEqual (m, m') with
             | true__ -> __U :: __L
             | false__ -> __L) in
      let rec strengthenArgs __23__ __24__ =
        match (__23__, __24__) with
        | (nil, s) -> nil
        | ((__U)::__L, s) ->
            (::) (Weaken.strengthenExp (__U, s)) strengthenArgs (__L, s) in
      let rec occursInArgs __25__ __26__ =
        match (__25__, __26__) with
        | (n, nil) -> false__
        | (n, (__U)::__L) ->
            (occursInExp (n, __U)) || (occursInArgs (n, __L)) in
      let rec occursInPsi __27__ __28__ =
        match (__27__, __28__) with
        | (n, (nil, __L)) -> occursInArgs (n, __L)
        | (n, ((Prim (Dec (_, __V)))::Psi1, __L)) ->
            (occursInExp (n, __V)) || (occursInPsi ((n + 1), (Psi1, __L)))
        | (n, ((Block (CtxBlock (l, __G)))::Psi1, __L)) ->
            occursInG (n, __G, (fun n' -> occursInPsi (n', (Psi1, __L))))
      and occursInG __29__ __30__ __31__ =
        match (__29__, __30__, __31__) with
        | (n, I.Null, k) -> k n
        | (n, Decl (__G, Dec (_, __V)), k) ->
            occursInG
              (n, __G, (fun n' -> (occursInExp (n', __V)) || (k (n' + 1)))) in
      let rec occursBlock (__G) (Psi2, __L) =
        let rec occursBlock __32__ __33__ =
          match (__32__, __33__) with
          | (I.Null, n) -> false__
          | (Decl (__G, __D), n) ->
              (occursInPsi (n, (Psi2, __L))) || (occursBlock (__G, (n + 1))) in
        occursBlock (__G, 1) in
      let rec inBlock __34__ __35__ =
        match (__34__, __35__) with
        | (I.Null, (bw, w1)) -> (bw, w1)
        | (Decl (__G, __D), (bw, w1)) ->
            if eqIdx ((I.bvarSub (1, w1)), (I.Idx 1))
            then inBlock (__G, (true__, (dot1inv w1)))
            else inBlock (__G, (bw, (Weaken.strengthenSub (w1, I.shift)))) in
      let rec blockSub __36__ __37__ =
        match (__36__, __37__) with
        | (I.Null, w) -> (I.Null, w)
        | (Decl (__G, Dec (name, __V)), w) ->
            let (__G', w') = blockSub (__G, w) in
            let __V' = Weaken.strengthenExp (__V, w') in
            ((I.Decl (__G', (I.Dec (name, __V')))), (I.dot1 w')) in
      let rec strengthen' __38__ __39__ __40__ __41__ =
        match (__38__, __39__, __40__, __41__) with
        | (I.Null, Psi2, __L, w1) -> (I.Null, I.id)
        | (Decl (Psi1, (Prim (Dec (name, __V)) as LD)), Psi2, __L, w1) ->
            let (bw, w1') =
              if eqIdx ((I.bvarSub (1, w1)), (I.Idx 1))
              then (true__, (dot1inv w1))
              else (false__, (Weaken.strengthenSub (w1, I.shift))) in
            if bw || (occursInPsi (1, (Psi2, __L)))
            then
              let (Psi1', w') = strengthen' (Psi1, (LD :: Psi2), __L, w1') in
              let __V' = Weaken.strengthenExp (__V, w') in
              ((I.Decl (Psi1', (F.Prim (I.Dec (name, __V'))))), (I.dot1 w'))
            else
              (let w2 = I.shift in
               let (Psi2', w2') = FunWeaken.strengthenPsi' (Psi2, w2) in
               let __L' = strengthenArgs (__L, w2') in
               let (Psi1'', w') = strengthen' (Psi1, Psi2', __L', w1') in
               (Psi1'', (I.comp (w', I.shift))))
        | (Decl (Psi1, (Block (CtxBlock (name, __G)) as LD)), Psi2, __L, w1)
            ->
            let (bw, w1') = inBlock (__G, (false__, w1)) in
            if bw || (occursBlock (__G, (Psi2, __L)))
            then
              let (Psi1', w') = strengthen' (Psi1, (LD :: Psi2), __L, w1') in
              let (G'', w'') = blockSub (__G, w') in
              ((I.Decl (Psi1', (F.Block (F.CtxBlock (name, G''))))), w'')
            else
              (let w2 = I.Shift (I.ctxLength __G) in
               let (Psi2', w2') = FunWeaken.strengthenPsi' (Psi2, w2) in
               let __L' = strengthenArgs (__L, w2') in
               strengthen' (Psi1, Psi2', __L', w1'))(* =  I.id *) in
      ((strengthen' (Psi, nil, (args (__S, mS)), w))
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
    let rec recursion (__L) =
      let __F = convertFor __L in
      let rec name =
        function
        | a::[] -> I.conDecName (I.sgnLookup a)
        | a::__L -> ((I.conDecName (I.sgnLookup a)) ^ "/") ^ (name __L) in
      fun p -> F.Rec ((F.MDec ((Some (name __L)), __F)), p)
    let rec abstract a =
      let mS =
        match ModeTable.modeLookup a with
        | NONE -> raise (Error "Mode declaration expected")
        | Some mS -> mS in
      let __V =
        match I.sgnLookup a with
        | ConDec (name, _, _, _, __V, I.Kind) -> __V
        | _ -> raise (Error "Type Constant declaration expected") in
      let rec abstract' __42__ __43__ =
        match (__42__, __43__) with
        | ((_, M.Mnil), w) -> (fun p -> p)
        | ((Pi ((__D, _), __V2), Mapp (Marg (M.Plus, _), mS)), w) ->
            let __D' = Weaken.strengthenDec (__D, w) in
            let __P = abstract' ((__V2, mS), (I.dot1 w)) in
            (fun p -> F.Lam ((F.Prim __D'), (__P p)))
        | ((Pi (_, __V2), Mapp (Marg (M.Minus, _), mS)), w) ->
            abstract' ((__V2, mS), (I.comp (w, I.shift))) in
      ((abstract' ((__V, mS), I.id))
        (* abstract' ((V, mS), w) = P'

           Invariant:
           If  Sigma (a) = {x1:A1} .. {xn:An} type
           and  Psi |- S : m1{x1:A1} .. mn{xn:An} type > type
           and  Gamma= x1:A1, .. x(j-1):A(j-1)
           and  Gamma |- w : Gamma+
           then P' is a Lam abstraction
        *))
    let rec transformInit (Psi) (a, __S) w1 =
      let mS =
        match ModeTable.modeLookup a with
        | NONE -> raise (Error "Mode declaration expected")
        | Some mS -> mS in
      let __V =
        match I.sgnLookup a with
        | ConDec (name, _, _, _, __V, I.Kind) -> __V
        | _ -> raise (Error "Type Constant declaration expected") in
      let rec transformInit' __44__ __45__ __46__ =
        match (__44__, __45__, __46__) with
        | ((I.Nil, M.Mnil), Uni (I.Type), (w, s)) -> (w, s)
        | ((App (__U, __S), Mapp (Marg (M.Minus, _), mS)), Pi (_, __V2),
           (w, s)) ->
            let w' = I.comp (w, I.shift) in
            let s' = s in transformInit' ((__S, mS), __V2, (w', s'))
        | ((App (__U, __S), Mapp (Marg (M.Plus, _), mS)), Pi
           ((Dec (name, __V1), _), __V2), (w, s)) ->
            let V1' = Weaken.strengthenExp (__V1, w) in
            let w' = I.dot1 w in
            let __U' = Weaken.strengthenExp (__U, w1) in
            let s' = Whnf.dotEta ((I.Exp __U'), s) in
            transformInit' ((__S, mS), __V2, (w', s')) in
      ((transformInit'
          ((__S, mS), __V, (I.id, (I.Shift (F.lfctxLength Psi)))))
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
    let rec transformDec (__Ts) (Psi, __G0) d (a, __S) w1 w2 t0 =
      let mS =
        match ModeTable.modeLookup a with
        | NONE -> raise (Error "Mode declaration expected")
        | Some mS -> mS in
      let __V =
        match I.sgnLookup a with
        | ConDec (name, _, _, _, __V, I.Kind) -> __V
        | _ -> raise (Error "Type Constant declaration expected") in
      let rec raiseExp (__G) (__U) a =
        let rec raiseExp' =
          function
          | I.Null -> (I.id, ((fun x -> x)))
          | Decl (__G, (Dec (_, __V) as D)) ->
              let (w, k) = raiseExp' __G in
              if Subordinate.belowEq ((I.targetFam __V), a)
              then
                ((I.dot1 w),
                  ((fun x -> k (I.Lam ((Weaken.strengthenDec (__D, w)), x)))))
              else ((I.comp (w, I.shift)), k) in
        let (w, k) = raiseExp' __G in ((k (Weaken.strengthenExp (__U, w)))
          (* raiseExp G = (w', k)

               Invariant:
               If   |-  Psi ctx
               and  Psi |- G ctx
               and  Psi |- G' ctx   which ARE subordinate to a
               then Psi, G |- w : Psi, G'
               and  k is a continuation calculuting the right exprssion:
                    for all U, s.t. Psi, G |- U : V
                    Psi |- [[G']] U : {{G'}} V
            *)) in
      let rec raiseType (__G) (__U) a =
        let rec raiseType' __47__ __48__ =
          match (__47__, __48__) with
          | (I.Null, n) -> (I.id, ((fun x -> x)), ((fun (__S) -> __S)))
          | (Decl (__G, (Dec (_, __V) as D)), n) ->
              let (w, k, k') = raiseType' (__G, (n + 1)) in
              if Subordinate.belowEq ((I.targetFam __V), a)
              then
                ((I.dot1 w),
                  ((fun x ->
                      k
                        (I.Pi (((Weaken.strengthenDec (__D, w)), I.Maybe), x)))),
                  ((fun (__S) -> I.App ((I.Root ((I.BVar n), I.Nil)), __S))))
              else ((I.comp (w, I.shift)), k, k') in
        let (w, k, k') = raiseType' (__G, 2) in
        ((((k (Weaken.strengthenExp (__U, w))),
            (I.Root ((I.BVar 1), (k' I.Nil)))))
          (* raiseType (G, n) = (w', k, S')

              Invariant:
              If   |-  Psi ctx
              and  Psi |- G, Gv ctx
              and  Psi |- G' ctx   which ARE subordinate to a
              and  n = |Gv| + 1
              then Psi, G |- w : Psi, G'
              and  k is a continuation calculating the right exprssion:
                   for all U, s.t. Psi, G |- U : V
                   Psi |- [[G']] U : {{G'}} V
              and  k' is a continuation calculating the corresponding spine:
                   for all S, s.t. Psi, G, G0,|- ... refine
            *)) in
      let rec exchangeSub (__G0) =
        let g0 = I.ctxLength __G0 in
        let rec exchangeSub' __49__ __50__ =
          match (__49__, __50__) with
          | (0, s) -> s
          | (k, s) -> exchangeSub' ((k - 1), (I.Dot ((I.Idx k), s))) in
        I.Dot ((I.Idx (g0 + 1)), (exchangeSub' (g0, (I.Shift (g0 + 1))))) in
      let rec transformDec' __51__ __52__ __53__ __54__ __55__ =
        match (__51__, __52__, __53__, __54__, __55__) with
        | (d, (I.Nil, M.Mnil), Uni (I.Type), (z1, z2), (w, t)) ->
            (w, t,
              (d, ((fun k -> fun (__Ds) -> __Ds k)), ((fun _ -> F.Empty))))
        | (d, (App (__U, __S), Mapp (Marg (M.Minus, _), mS)), Pi
           ((Dec (_, __V1), DP), __V2), (z1, z2), (w, t)) ->
            let g = I.ctxLength __G0 in
            let w1' = peeln (g, w1) in
            let (__G1, _) = Weaken.strengthenCtx (__G0, w1') in
            let (__G2, _) = ctxSub (__G1, z1) in
            let (V1'', Ur) =
              raiseType (__G2, (I.EClo (__V1, z2)), (I.targetFam __V1)) in
            let w' =
              match DP with
              | I.Maybe -> I.dot1 w
              | I.No -> I.comp (w, I.shift) in
            let __U0 = raiseExp (__G0, __U, (I.targetFam V1'')) in
            let __U' = Weaken.strengthenExp (__U0, w2) in
            let t' = Whnf.dotEta ((I.Exp __U'), t) in
            let z1' = I.comp (z1, I.shift) in
            let xc = exchangeSub __G0 in
            let z2n = I.comp (z2, (I.comp (I.shift, xc))) in
            let Ur' = I.EClo (Ur, xc) in
            let z2' = Whnf.dotEta ((I.Exp Ur'), z2n) in
            let (w'', t'', (d', Dplus, Dminus)) =
              transformDec' ((d + 1), (__S, mS), __V2, (z1', z2'), (w', t')) in
            (w'', t'', (d', Dplus, ((fun k -> F.Split (k, (Dminus 1))))))
        | (d, (App (__U, __S), Mapp (Marg (M.Plus, _), mS)), Pi
           ((Dec (name, __V1), _), __V2), (z1, z2), (w, t)) ->
            let V1' = Weaken.strengthenExp (__V1, w) in
            let w' = I.dot1 w in
            let __U' = Weaken.strengthenExp (__U, w1) in
            let t' = t in
            let z1' = F.dot1n (__G0, z1) in
            let z2' = I.Dot ((I.Exp (I.EClo (__U', z1'))), z2) in
            let (w'', t'', (d', Dplus, Dminus)) =
              transformDec' ((d + 1), (__S, mS), __V2, (z1, z2'), (w', t')) in
            (w'', t'',
              (d',
                ((fun k -> fun (__Ds) -> F.App ((k, __U'), (Dplus (1, __Ds))))),
                Dminus)) in
      let (w'', t'', (d', Dplus, Dminus)) =
        transformDec'
          (d, (__S, mS), __V,
            (I.id, (I.Shift ((+) (domain (Psi, t0)) I.ctxLength __G0))),
            (I.id, t0)) in
      let rec varHead (__Ts) w'' t'' (d', Dplus, Dminus) =
        let rec head' __56__ __57__ __58__ =
          match (__56__, __57__, __58__) with
          | (a'::[], d1, k1) -> (d1, k1)
          | (a'::__Ts', d1, k1) ->
              if a = a'
              then ((d1 + 1), ((fun xx -> F.Left (xx, (k1 1)))))
              else
                (let (d2, k2) = head' (__Ts', (d1 + 1), k1) in
                 (d2, (fun xx -> F.Right (xx, (k2 1))))) in
        let (d2, k2) = head' (__Ts, d', (fun xx -> Dplus (xx, Dminus))) in
        (d2, w'', t'', (k2 d)) in
      let rec lemmaHead w'' t'' (d', Dplus, Dminus) =
        let name = I.conDecName (I.sgnLookup a) in
        let l =
          match FunNames.nameLookup name with
          | NONE -> raise (Error (("Lemma " ^ name) ^ " not defined"))
          | Some lemma -> lemma in
        ((d' + 1), w'', t'', (F.Lemma (l, (Dplus (1, Dminus))))) in
      ((if List.exists (fun x -> x = a) __Ts
        then varHead __Ts (w'', t'', (d', Dplus, Dminus))
        else lemmaHead (w'', t'', (d', Dplus, Dminus)))
        (* raiseExp (G, U, a) = U'

           Invariant:
           If   |- Psi ctx         (for some given Psi)
           and  Psi |- G ctx
           and  Psi, G |- U : V    (for some V)
           then Psi, G |- [[G]] U : {{G}} V     (wrt subordination)
        *)
        (* raiseType (G, U, a) = U'

           Invariant:
           If   |- Psi ctx         (for some given Psi)
           and  Psi |- G ctx
           and  Psi, G |- U : V    (for some V)
           then Psi, G |- [[G]] U : {{G}} V     (wrt subordination)
           and  Psi, G, x:{{G}} V |- x G : V
        *)
        (* exchangeSub (G0) = s'

           Invariant:
           For some Psi, some G, some V:
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
          *))
    let rec transformConc (a, __S) w =
      let mS =
        match ModeTable.modeLookup a with
        | NONE -> raise (Error "Mode declaration expected")
        | Some mS -> mS in
      let rec transformConc' __59__ __60__ =
        match (__59__, __60__) with
        | (I.Nil, M.Mnil) -> F.Unit
        | (App (__U, __S'), Mapp (Marg (M.Plus, _), mS')) ->
            transformConc' (__S', mS')
        | (App (__U, __S'), Mapp (Marg (M.Minus, _), mS')) ->
            F.Inx
              ((Weaken.strengthenExp (__U, w)), (transformConc' (__S', mS'))) in
      transformConc' (__S, mS)
    let rec traverse (__Ts) c =
      let rec traverseNeg __61__ __62__ __63__ __64__ =
        match (__61__, __62__, __63__, __64__) with
        | (c'', Psi, (Pi (((Dec (_, __V1) as D), I.Maybe), __V2), v), __L) ->
            (match traverseNeg
                     (((c'',
                         (I.Decl
                            (Psi, (F.Prim (Weaken.strengthenDec (__D, v))))),
                         (__V2, (I.dot1 v)), __L))
                     (*                                   (Names.decName (F.makectx Psi, Weaken.strengthenDec (D, v)))),
*))
             with
             | (Some (w', d', PQ'), __L') ->
                 ((Some ((peel w'), d', PQ')), __L')
             | (NONE, __L') -> (NONE, __L'))
        | (c'', Psi, (Pi (((Dec (_, __V1) as D), I.No), __V2), v), __L) ->
            (match traverseNeg (c'', Psi, (__V2, (I.comp (v, I.shift))), __L)
             with
             | (Some (w', d', PQ'), __L') ->
                 traversePos
                   (c'', Psi, I.Null,
                     ((Weaken.strengthenExp (__V1, v)), I.id),
                     (Some (w', d', PQ')), __L')
             | (NONE, __L') ->
                 traversePos
                   (c'', Psi, I.Null,
                     ((Weaken.strengthenExp (__V1, v)), I.id), NONE, __L'))
        | (c'', Psi, ((Root (Const c', __S) as V), v), __L) ->
            if c = c'
            then
              let __S' = Weaken.strengthenSpine (__S, v) in
              let (Psi', w') =
                strengthen
                  (Psi, (c', __S'), (I.Shift (F.lfctxLength Psi)), M.Plus) in
              let (w'', s'') = transformInit (Psi', (c', __S'), w') in
              ((((Some
                    (w', 1,
                      ((fun p -> (Psi', s'', p)),
                        (fun wf -> transformConc ((c', __S'), wf))))), __L))
                (* Clause head found *))
            else (NONE, __L)
      and traversePos __65__ __66__ __67__ __68__ __69__ __70__ =
        match (__65__, __66__, __67__, __68__, __69__, __70__) with
        | (c'', Psi, __G, (Pi (((Dec (_, __V1) as D), I.Maybe), __V2), v),
           Some (w, d, PQ), __L) ->
            (match traversePos
                     (c'', Psi,
                       (I.Decl (__G, (Weaken.strengthenDec (__D, v)))),
                       (__V2, (I.dot1 v)), (Some ((I.dot1 w), d, PQ)), __L)
             with
             | (Some (w', d', PQ'), __L') -> ((Some (w', d', PQ')), __L'))
        | (c'', Psi, __G, (Pi (((Dec (_, __V1) as D), I.No), __V2), v), Some
           (w, d, PQ), __L) ->
            (match traversePos
                     (c'', Psi, __G, (__V2, (I.comp (v, I.shift))),
                       (Some (w, d, PQ)), __L)
             with
             | (Some (w', d', PQ'), __L') ->
                 (match traverseNeg
                          (c'',
                            (I.Decl (Psi, (F.Block (F.CtxBlock (NONE, __G))))),
                            (__V1, v), __L')
                  with
                  | (Some (w'', d'', (P'', Q'')), L'') ->
                      ((Some (w', d', PQ')), ((P'' (Q'' w'')) :: L''))
                  | (NONE, L'') -> ((Some (w', d', PQ')), L'')))
        | (c'', Psi, I.Null, (__V, v), Some (w1, d, (__P, __Q)), __L) ->
            let Root (Const a', __S) =
              Whnf.normalize ((Weaken.strengthenExp (__V, v)), I.id) in
            let (Psi', w2) = strengthen (Psi, (a', __S), w1, M.Minus) in
            let _ =
              if !Global.doubleCheck
              then
                TypeCheck.typeCheck
                  ((F.makectx Psi'), ((I.Uni I.Type), (I.Uni I.Kind)))
              else () in
            let w3 = Weaken.strengthenSub (w1, w2) in
            let (d4, w4, t4, __Ds) =
              transformDec (__Ts, (Psi', I.Null), d, (a', __S), w1, w2, w3) in
            ((((Some
                  (w2, d4,
                    ((fun p ->
                        __P (F.Let (__Ds, (F.Case (F.Opts [(Psi', t4, p)]))))),
                      __Q))), __L))
              (* Lemma calls (no context block) *)(* provide typeCheckCtx from typecheck *))
        | (c'', Psi, __G, (__V, v), Some (w1, d, (__P, __Q)), __L) ->
            let Root (Const a', __S) = Weaken.strengthenExp (__V, v) in
            let ((Decl (Psi', Block (CtxBlock (name, __G2))) as dummy), w2) =
              strengthen
                ((I.Decl (Psi, (F.Block (F.CtxBlock (NONE, __G))))),
                  (a', __S), w1, M.Minus) in
            let _ =
              if !Global.doubleCheck
              then
                TypeCheck.typeCheck
                  ((F.makectx dummy), ((I.Uni I.Type), (I.Uni I.Kind)))
              else () in
            let g = I.ctxLength __G in
            let w1' = peeln (g, w1) in
            let w2' = peeln (g, w2) in
            let (__G1, _) = Weaken.strengthenCtx (__G, w1') in
            let w3 = Weaken.strengthenSub (w1', w2') in
            let (d4, w4, t4, __Ds) =
              transformDec (__Ts, (Psi', __G), d, (a', __S), w1, w2', w3) in
            ((((Some
                  (w2', d4,
                    ((fun p ->
                        __P
                          (F.Let
                             ((F.New ((F.CtxBlock (NONE, __G1)), __Ds)),
                               (F.Case (F.Opts [(Psi', t4, p)]))))), __Q))),
                __L))
              (* Lemma calls (under a context block) *)
              (* provide typeCheckCtx from typecheck *)
              (* change w1 to w1' and w2 to w2' below *))
        | (c'', Psi, __G, (Pi (((Dec (_, __V1) as D), I.Maybe), __V2), v),
           NONE, __L) ->
            traversePos
              (c'', Psi, (I.Decl (__G, (Weaken.strengthenDec (__D, v)))),
                (__V2, (I.dot1 v)), NONE, __L)
        | (c'', Psi, __G, (Pi (((Dec (_, __V1) as D), I.No), __V2), v), NONE,
           __L) ->
            (match traversePos
                     (c'', Psi, __G, (__V2, (I.comp (v, I.shift))), NONE,
                       __L)
             with
             | (NONE, __L') ->
                 (match traverseNeg
                          (c'',
                            (I.Decl (Psi, (F.Block (F.CtxBlock (NONE, __G))))),
                            (__V1, v), __L')
                  with
                  | (Some (w'', d'', (P'', Q'')), L'') ->
                      (NONE, ((P'' (Q'' w'')) :: L''))
                  | (NONE, L'') -> (NONE, L'')))
        | (c'', Psi, __G, (__V, v), NONE, __L) -> (NONE, __L) in
      let rec traverseSig' c'' (__L) =
        if (=) c'' (fun r -> r.1) (I.sgnSize ())
        then __L
        else
          (match I.sgnLookup c'' with
           | ConDec (name, _, _, _, __V, I.Type) ->
               (match traverseNeg (c'', I.Null, (__V, I.id), __L) with
                | (Some (wf, d', (__P', __Q')), __L') ->
                    traverseSig' ((c'' + 1), ((__P' (__Q' wf)) :: __L'))
                | (NONE, __L') -> traverseSig' ((c'' + 1), __L'))
           | _ -> traverseSig' ((c'' + 1), __L)) in
      ((traverseSig' (0, nil))
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
        (* traversePos (c, Psi, G, (V, v), [w', d', PQ'], L) =  ([w'', d'', PQ''], L'')

           Invariant:
           If   Psi, G |- V : type
           and  Psi, G |- v : Psi'       (s.t.  Psi' |- V[v^-1] : type exists)
           and V[v^-1] does not contain Skolem constants
           [ and Psi', G |- w' : Psi''
             and |Delta'| = d'    for a Delta'
             and PQ' can generate the proof term so far in Delta'; Psi''
           ]
           and  c is the name of the constant currently considered
           and  L is a list of cases
           then L'' list of cases and L'' extends L
           and  Psi |- w'' : Psi2
           and  |Delta''| = d''  for a Delta'
           and  PQ'' can genreate the proof term so far in Delta''; Psi2
        *))
    let rec convertPro (__Ts) =
      let rec convertOnePro a =
        let __V =
          match I.sgnLookup a with
          | ConDec (name, _, _, _, __V, I.Kind) -> __V
          | _ -> raise (Error "Type Constant declaration expected") in
        let mS =
          match ModeTable.modeLookup a with
          | NONE -> raise (Error "Mode declaration expected")
          | Some mS -> mS in
        let __P = abstract a in __P (F.Case (F.Opts (traverse (__Ts, a)))) in
      let rec convertPro' =
        function
        | nil -> raise (Error "Cannot convert Empty program")
        | a::[] -> convertOnePro a
        | a::__Ts' -> F.Pair ((convertOnePro a), (convertPro' __Ts')) in
      let __R = recursion __Ts in __R (convertPro' __Ts)
    let convertFor = convertFor
    let convertPro = convertPro
    let traverse = traverse
  end ;;
