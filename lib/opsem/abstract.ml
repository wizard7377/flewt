
module type ABSTRACTTABLED  =
  sig
    exception Error of string 
    val abstractEVarCtx :
      CompSyn.__DProg ->
        IntSyn.__Exp ->
          IntSyn.__Sub ->
            (IntSyn.dctx * IntSyn.dctx * IntSyn.dctx * IntSyn.__Exp *
              TableParam.__ResEqn * IntSyn.__Sub)
    val abstractAnswSub : IntSyn.__Sub -> (IntSyn.dctx * IntSyn.__Sub)
    val raiseType : IntSyn.dctx -> IntSyn.__Exp -> IntSyn.__Exp
  end;;




module AbstractTabled(AbstractTabled:sig
                                       module Whnf : WHNF
                                       module Unify : UNIFY
                                       module Constraints : CONSTRAINTS
                                       module Subordinate : SUBORDINATE
                                       module Print : PRINT
                                       module Conv : CONV
                                     end) : ABSTRACTTABLED =
  struct
    exception Error of string 
    module I = IntSyn
    module C = CompSyn
    type __Duplicates =
      | AV of (I.__Exp * int) 
      | FGN of int 
    type seenIn =
      | TypeLabel 
      | Body 
    type __ExistVars =
      | EV of I.__Exp 
    let rec lengthSub =
      function | Shift n -> 0 | Dot (__E, s) -> (+) 1 lengthSub s
    let rec compose' __0__ __1__ =
      match (__0__, __1__) with
      | (IntSyn.Null, __G) -> __G
      | (Decl (__G', __D), __G) -> IntSyn.Decl ((compose' (__G', __G)), __D)
    let rec isId =
      function
      | Shift n -> n = 0
      | Dot (Idx n, s') as s -> isId' (s, 0)
      | Dot (I.Undef, s') as s -> isId' (s, 0)
      | Dot (Exp _, s) -> false__
    let rec isId' __2__ __3__ =
      match (__2__, __3__) with
      | (Shift n, k) -> n = k
      | (Dot (Idx i, s), k) -> let k' = k + 1 in (i = k') && (isId' (s, k'))
      | (Dot (I.Undef, s), k) -> isId' (s, (k + 1))
    let rec equalCtx __4__ __5__ __6__ __7__ =
      match (__4__, __5__, __6__, __7__) with
      | (I.Null, s, I.Null, s') -> true__
      | (Decl (__G, __D), s, Decl (__G', __D'), s') ->
          (Conv.convDec ((__D, s), (__D', s'))) &&
            (equalCtx (__G, (I.dot1 s), __G', (I.dot1 s')))
      | (Decl (__G, __D), s, I.Null, s') -> false__
      | (I.Null, s, Decl (__G', __D'), s') -> false__
    let rec eqEVarW __8__ __9__ =
      match (__8__, __9__) with
      | (EVar (r1, _, _, _), EV (EVar (r2, _, _, _))) -> r1 = r2
      | (_, _) -> false__
    let rec eqEVar (__X1) (EV (__X2)) =
      let (X1', s) = Whnf.whnf (__X1, I.id) in
      let (X2', s) = Whnf.whnf (__X2, I.id) in eqEVarW X1' (EV X2')(* Sun Dec  1 14:04:17 2002 -bp  may raise exception
       if strengthening is applied,i.e. the substitution is not always id! *)
    let rec member' (__P) (__K) =
      let rec exists' =
        function
        | I.Null -> NONE
        | Decl (__K', (l, EV (__Y))) ->
            if __P (EV __Y) then Some l else exists' __K' in
      exists' __K
    let rec member (__P) (__K) =
      let rec exists' =
        function
        | I.Null -> NONE
        | Decl (__K', (i, __Y)) -> if __P __Y then Some i else exists' __K' in
      exists' __K
    let rec update' (__P) (__K) =
      let rec update' =
        function
        | I.Null -> I.Null
        | Decl (__K', (label, __Y)) ->
            if __P __Y
            then I.Decl (__K', (Body, __Y))
            else I.Decl ((update' __K'), (label, __Y)) in
      update' __K
    let rec update (__P) (__K) =
      let rec update' =
        function
        | I.Null -> I.Null
        | Decl (__K', ((label, i), __Y)) ->
            if __P __Y
            then I.Decl (__K', ((Body, i), __Y))
            else I.Decl ((update' __K'), ((label, i), __Y)) in
      update' __K
    let rec or__ __10__ __11__ =
      match (__10__, __11__) with
      | (I.Maybe, _) -> I.Maybe
      | (_, I.Maybe) -> I.Maybe
      | (I.Meta, _) -> I.Meta
      | (_, I.Meta) -> I.Meta
      | (I.No, I.No) -> I.No
    let rec occursInExp __12__ __13__ =
      match (__12__, __13__) with
      | (k, Uni _) -> I.No
      | (k, Pi (DP, __V)) ->
          or__ ((occursInDecP (k, DP)), (occursInExp ((k + 1), __V)))
      | (k, Root (__H, __S)) ->
          occursInHead (k, __H, (occursInSpine (k, __S)))
      | (k, Lam (__D, __V)) ->
          or__ ((occursInDec (k, __D)), (occursInExp ((k + 1), __V)))
      | (k, FgnExp csfe) ->
          I.FgnExpStd.fold csfe
            (fun (__U) ->
               fun (DP) ->
                 or__ (DP, (occursInExp (k, (Whnf.normalize (__U, I.id))))))
            I.No
    let rec occursInHead __14__ __15__ __16__ =
      match (__14__, __15__, __16__) with
      | (k, BVar k', DP) -> if k = k' then I.Maybe else DP
      | (k, Const _, DP) -> DP
      | (k, Def _, DP) -> DP
      | (k, FgnConst _, DP) -> DP
      | (k, Skonst _, I.No) -> I.No
      | (k, Skonst _, I.Meta) -> I.Meta
      | (k, Skonst _, I.Maybe) -> I.Meta
    let rec occursInSpine __17__ __18__ =
      match (__17__, __18__) with
      | (_, I.Nil) -> I.No
      | (k, App (__U, __S)) ->
          or__ ((occursInExp (k, __U)), (occursInSpine (k, __S)))
    let rec occursInDec k (Dec (_, __V)) = occursInExp (k, __V)
    let rec occursInDecP k (__D, _) = occursInDec (k, __D)
    let rec piDepend __19__ =
      match __19__ with
      | ((__D, I.No), __V) as DPV -> I.Pi DPV
      | ((__D, I.Meta), __V) as DPV -> I.Pi DPV
      | ((__D, I.Maybe), __V) -> I.Pi ((__D, (occursInExp (1, __V))), __V)
    let rec raiseType __20__ __21__ =
      match (__20__, __21__) with
      | (I.Null, __V) -> __V
      | (Decl (__G, __D), __V) ->
          raiseType (__G, (I.Pi ((__D, I.Maybe), __V)))
    let rec reverseCtx __22__ __23__ =
      match (__22__, __23__) with
      | (I.Null, __G) -> __G
      | (Decl (__G, __D), __G') -> reverseCtx (__G, (I.Decl (__G', __D)))
    let rec ctxToEVarSub __24__ __25__ =
      match (__24__, __25__) with
      | (IntSyn.Null, s) -> s
      | (Decl (__G, Dec (_, __A)), s) ->
          let s' = ctxToEVarSub (__G, s) in
          let __X = IntSyn.newEVar (IntSyn.Null, (I.EClo (__A, s'))) in
          IntSyn.Dot ((IntSyn.Exp __X), s')
    let rec collectExpW __26__ __27__ __28__ __29__ __30__ __31__ __32__ =
      match (__26__, __27__, __28__, __29__, __30__, __31__, __32__) with
      | (Gss, Gl, (Uni (__L), s), __K, DupVars, flag, d) -> (__K, DupVars)
      | (Gss, Gl, (Pi ((__D, _), __V), s), __K, DupVars, flag, d) ->
          let (__K', _) =
            collectDec (Gss, (__D, s), (__K, DupVars), d, false__) in
          ((collectExp
              (Gss, (I.Decl (Gl, (I.decSub (__D, s)))), (__V, (I.dot1 s)),
                __K', DupVars, flag, d))
            (* should we apply I.dot1(ss) ? Tue Oct 15 21:55:16 2002 -bp *))
      | (Gss, Gl, (Root (_, __S), s), __K, DupVars, flag, d) ->
          collectSpine (Gss, Gl, (__S, s), __K, DupVars, flag, d)
      | (Gss, Gl, (Lam (__D, __U), s), __K, DupVars, flag, d) ->
          let (__K', _) =
            collectDec (Gss, (__D, s), (__K, DupVars), d, false__) in
          collectExp
            (Gss, (I.Decl (Gl, (I.decSub (__D, s)))), (__U, (I.dot1 s)),
              __K', DupVars, flag, (d + 1))
      | (Gss, Gl, ((EVar (r, GX, __V, cnstrs) as X), s), __K, DupVars, flag,
         d) -> collectEVar (Gss, Gl, (__X, s), __K, DupVars, flag, d)
      | (Gss, Gl, (FgnExp csfe, s), __K, DupVars, flag, d) ->
          I.FgnExpStd.fold csfe
            (fun (__U) ->
               fun (KD') ->
                 let (__K', Dup) = KD' in
                 collectExp (Gss, Gl, (__U, s), __K', Dup, false__, d))
            (__K, (I.Decl (DupVars, (FGN d))))
    let rec collectExp (Gss) (Gl) (__Us) (__K) (DupVars) flag d =
      collectExpW (Gss, Gl, (Whnf.whnf __Us), __K, DupVars, flag, d)
    let rec collectSpine __33__ __34__ __35__ __36__ __37__ __38__ __39__ =
      match (__33__, __34__, __35__, __36__, __37__, __38__, __39__) with
      | (Gss, Gl, (I.Nil, _), __K, DupVars, flag, d) -> (__K, DupVars)
      | (Gss, Gl, (SClo (__S, s'), s), __K, DupVars, flag, d) ->
          collectSpine
            (Gss, Gl, (__S, (I.comp (s', s))), __K, DupVars, flag, d)
      | (Gss, Gl, (App (__U, __S), s), __K, DupVars, flag, d) ->
          let (__K', DupVars') =
            collectExp (Gss, Gl, (__U, s), __K, DupVars, flag, d) in
          collectSpine (Gss, Gl, (__S, s), __K', DupVars', flag, d)
    let rec collectEVarFapStr (Gss) (Gl) ((__X', __V'), w)
      ((EVar (r, GX, __V, cnstrs) as X), s) (__K) (DupVars) flag d =
      ((match member' (eqEVar __X) __K with
        | Some label ->
            ((if flag
              then
                collectSub
                  (Gss, Gl, s, __K, (I.Decl (DupVars, (AV (__X, d)))), flag,
                    d)
              else collectSub (Gss, Gl, s, __K, DupVars, flag, d))
            (* case label of
                     Body => collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(X,d)), flag, d)
                   | TypeLabel =>
                       let
                         val K' = update' (eqEVar X) K
                       in
                         collectSub(Gss, Gl, s, K', DupVars, flag, d)
                       end *)
            (* since X has occurred before, we do not traverse its type V' *))
        | NONE ->
            let label = if flag then Body else TypeLabel in
            let (__K', DupVars') =
              collectExp
                ((I.Null, I.id), I.Null, (__V', I.id), __K, DupVars, false__,
                  d) in
            ((collectSub
                (Gss, Gl, (I.comp (w, s)),
                  (I.Decl (__K', (label, (EV __X')))), DupVars', flag, d))
              (*          val V' = raiseType (GX, V)  inefficient! *)))
      (* we have seen X before *))
    let rec collectEVarNFapStr (Gss) (Gl) ((__X', __V'), w)
      ((EVar (r, GX, __V, cnstrs) as X), s) (__K) (DupVars) flag d =
      ((match member' (eqEVar __X) __K with
        | Some label ->
            ((if flag
              then
                collectSub
                  (Gss, Gl, s, __K, (I.Decl (DupVars, (AV (__X, d)))), flag,
                    d)
              else collectSub (Gss, Gl, s, __K, DupVars, flag, d))
            (* -bp this is a possible optimization for the variant case
                   case label of
                   Body => (print "Collect DupVar\n"; collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(X, d)), flag, d) )
                 | TypeLabel =>
                    let
                      val _ = print "TypeLabel\n"
                      val K' = update' (eqEVar X) K
                    in
                      collectSub(Gss, Gl, s, K', DupVars, flag, d)
                    end*))
        | NONE ->
            let label = if flag then Body else TypeLabel in
            let (__K', DupVars') =
              collectExp
                ((I.Null, I.id), I.Null, (__V', I.id), __K, DupVars, false__,
                  d) in
            ((if flag
              then
                collectSub
                  (Gss, Gl, (I.comp (w, s)),
                    (I.Decl (__K', (label, (EV __X')))),
                    (I.Decl (DupVars', (AV (__X', d)))), flag, d)
              else
                collectSub
                  (Gss, Gl, (I.comp (w, s)),
                    (I.Decl (__K', (label, (EV __X')))), DupVars', flag, d))
              (* val V' = raiseType (GX, V)  inefficient! *)))
      (* we have seen X before, i.e. it was already strengthened *))
    let rec collectEVarStr ((__Gs, ss) as Gss) (Gl)
      ((EVar (r, GX, __V, cnstrs) as X), s) (__K) (DupVars) flag d =
      let w = Subordinate.weaken (GX, (I.targetFam __V)) in
      let iw = Whnf.invert w in
      let GX' = Whnf.strengthen (iw, GX) in
      let EVar (r', _, _, _) as X' = I.newEVar (GX', (I.EClo (__V, iw))) in
      let _ = Unify.instantiateEVar (r, (I.EClo (__X', w)), nil) in
      let __V' = raiseType (GX', (I.EClo (__V, iw))) in
      ((if isId (I.comp (w, (I.comp (ss, s))))
        then
          collectEVarFapStr
            (Gss, Gl, ((__X', __V'), w), (__X, s), __K, DupVars, flag, d)
        else
          collectEVarNFapStr
            (Gss, Gl, ((__X', __V'), w), (__X, s), __K, DupVars, flag, d))
        (* equalCtx (Gs, I.id, GX', s) *)(* fully applied *)
        (* not fully applied *)(* ? *))
    let rec collectEVarFap (Gss) (Gl) ((EVar (r, GX, __V, cnstrs) as X), s)
      (__K) (DupVars) flag d =
      ((match member (eqEVar __X) __K with
        | Some label ->
            ((if flag
              then
                collectSub
                  (Gss, Gl, s, __K, (I.Decl (DupVars, (AV (__X, d)))), flag,
                    d)
              else collectSub (Gss, Gl, s, __K, DupVars, flag, d))
            (*
                 case label of
                   Body => collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(X, d)), flag, d)
                 | TypeLabel =>
                     let
                       val K' = update' (eqEVar X) K
                     in
                       collectSub(Gss, Gl, s, K', DupVars, flag, d)
                     end *)
            (* since X has occurred before, we do not traverse its type V' *))
        | NONE ->
            let label = if flag then Body else TypeLabel in
            let __V' = raiseType (GX, __V) in
            let (__K', DupVars') =
              collectExp
                ((I.Null, I.id), I.Null, (__V', I.id), __K, DupVars, false__,
                  d) in
            ((collectSub
                (Gss, Gl, s, (I.Decl (__K', (label, (EV __X)))), DupVars',
                  flag, d))
              (* val _ = checkEmpty !cnstrs *)(* inefficient! *)))
      (* we have seen X before *))
    let rec collectEVarNFap (Gss) (Gl) ((EVar (r, GX, __V, cnstrs) as X), s)
      (__K) (DupVars) flag d =
      match member' (eqEVar __X) __K with
      | Some label ->
          ((if flag
            then
              collectSub
                (Gss, Gl, s, __K, (I.Decl (DupVars, (AV (__X, d)))), flag, d)
            else collectSub (Gss, Gl, s, __K, DupVars, flag, d))
          (* case label of
                   Body => collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(X, d)), flag, d)
                   | TypeLabel =>
                     let
                       val K' = update' (eqEVar X) K
                     in
                       collectSub(Gss, Gl, s, K', DupVars, flag, d)
                     end             *))
      | NONE ->
          let label = if flag then Body else TypeLabel in
          let __V' = raiseType (GX, __V) in
          let (__K', DupVars') =
            collectExp
              ((I.Null, I.id), I.Null, (__V', I.id), __K, DupVars, false__,
                d) in
          ((if flag
            then
              collectSub
                (Gss, Gl, s, (I.Decl (__K', (label, (EV __X)))),
                  (I.Decl (DupVars, (AV (__X, d)))), flag, d)
            else
              collectSub
                (Gss, Gl, s, (I.Decl (__K', (label, (EV __X)))), DupVars,
                  flag, d))
            (* inefficient! *))
    let rec collectEVar (Gss) (Gl) ((EVar (r, GX, __V, cnstrs) as X), s)
      (__K) (DupVars) flag d =
      if !TableParam.strengthen
      then collectEVarStr (Gss, Gl, (__X, s), __K, DupVars, flag, d)
      else
        ((if isId s
          then collectEVarFap (Gss, Gl, (__X, s), __K, DupVars, flag, d)
          else collectEVarNFap (Gss, Gl, (__X, s), __K, DupVars, flag, d))
        (* equalCtx (compose'(Gl, G), s, GX, s)  *)(* X is fully applied *)
        (* X is not fully applied *))
    let rec collectDec (Gss) (Dec (_, __V), s) (__K, DupVars) d flag =
      let (__K', DupVars') =
        collectExp (Gss, I.Null, (__V, s), __K, DupVars, flag, d) in
      (((__K', DupVars'))
        (*      val (K',DupVars') =  collectExp (Gss, I.Null, (V, s), K, I.Null, false, d)*))
    let rec collectSub __40__ __41__ __42__ __43__ __44__ __45__ __46__ =
      match (__40__, __41__, __42__, __43__, __44__, __45__, __46__) with
      | (Gss, Gl, Shift _, __K, DupVars, flag, d) -> (__K, DupVars)
      | (Gss, Gl, Dot (Idx _, s), __K, DupVars, flag, d) ->
          collectSub (Gss, Gl, s, __K, DupVars, flag, d)
      | (Gss, Gl, Dot
         (Exp (EVar ({ contents = Some (__U) }, _, _, _) as X), s), __K,
         DupVars, flag, d) ->
          let __U' = Whnf.normalize (__U, I.id) in
          let (__K', DupVars') =
            collectExp (Gss, Gl, (__U', I.id), __K, DupVars, flag, d) in
          ((collectSub (Gss, Gl, s, __K', DupVars', flag, d))
            (* inefficient? *))
      | (Gss, Gl, Dot (Exp (AVar { contents = Some (__U') } as U), s), __K,
         DupVars, flag, d) ->
          let (__K', DupVars') =
            collectExp (Gss, Gl, (__U', I.id), __K, DupVars, flag, d) in
          collectSub (Gss, Gl, s, __K', DupVars', flag, d)
      | (Gss, Gl, Dot (Exp (EClo (__U', s')), s), __K, DupVars, flag, d) ->
          let __U = Whnf.normalize (__U', s') in
          let (__K', DupVars') =
            collectExp (Gss, Gl, (__U, I.id), __K, DupVars, flag, d) in
          ((collectSub (Gss, Gl, s, __K', DupVars', flag, d))
            (* inefficient? *))
      | (Gss, Gl, Dot (Exp (__U), s), __K, DupVars, flag, d) ->
          let (__K', DupVars') =
            collectExp (Gss, Gl, (__U, I.id), __K, DupVars, flag, d) in
          collectSub (Gss, Gl, s, __K', DupVars', flag, d)
      | (Gss, Gl, Dot (I.Undef, s), __K, DupVars, flag, d) ->
          collectSub (Gss, Gl, s, __K, DupVars, flag, d)
    let rec collectCtx __47__ __48__ __49__ __50__ =
      match (__47__, __48__, __49__, __50__) with
      | (Gss, DProg (I.Null, I.Null), (__K, DupVars), d) -> (__K, DupVars)
      | (Gss, DProg (Decl (__G, __D), Decl (dPool, C.Parameter)),
         (__K, DupVars), d) ->
          let (__K', DupVars') =
            collectCtx (Gss, (C.DProg (__G, dPool)), (__K, DupVars), (d - 1)) in
          collectDec (Gss, (__D, I.id), (__K', DupVars'), (d - 1), false__)
      | (Gss, DProg (Decl (__G, __D), Decl (dPool, Dec (r, s, Ha))),
         (__K, DupVars), d) ->
          let (__K', DupVars') =
            collectCtx (Gss, (C.DProg (__G, dPool)), (__K, DupVars), (d - 1)) in
          collectDec (Gss, (__D, I.id), (__K', DupVars'), (d - 1), false__)
    let rec abstractExpW __51__ __52__ __53__ __54__ __55__ __56__ __57__
      __58__ __59__ =
      match (__51__, __52__, __53__, __54__, __55__, __56__, __57__, __58__,
              __59__)
      with
      | (flag, __Gs, posEA, Vars, Gl, total, depth, ((Uni (__L) as U), s),
         eqn) -> (posEA, Vars, __U, eqn)
      | (flag, __Gs, posEA, Vars, Gl, total, depth,
         (Pi ((__D, __P), __V), s), eqn) ->
          let (posEA', Vars', __D, _) =
            abstractDec (__Gs, posEA, Vars, Gl, total, depth, (__D, s), NONE) in
          let (posEA'', Vars'', __V', eqn2) =
            abstractExp
              (flag, __Gs, posEA', Vars', Gl, total, (depth + 1),
                (__V, (I.dot1 s)), eqn) in
          (posEA'', Vars'', (piDepend ((__D, __P), __V')), eqn2)
      | (flag, __Gs, posEA, Vars, Gl, total, depth, (Root (__H, __S), s),
         eqn) ->
          let (posEA', Vars', __S, eqn') =
            abstractSpine
              (flag, __Gs, posEA, Vars, Gl, total, depth, (__S, s), eqn) in
          (posEA', Vars', (I.Root (__H, __S)), eqn')
      | (flag, __Gs, posEA, Vars, Gl, total, depth, (Lam (__D, __U), s), eqn)
          ->
          let (posEA', Vars', __D', _) =
            abstractDec (__Gs, posEA, Vars, Gl, total, depth, (__D, s), NONE) in
          let (posEA'', Vars'', __U', eqn2) =
            abstractExp
              (flag, __Gs, posEA', Vars', (I.Decl (Gl, __D')), total,
                (depth + 1), (__U, (I.dot1 s)), eqn) in
          (posEA'', Vars'', (I.Lam (__D', __U')), eqn2)
      | (flag, ((Gss, ss) as Gs), ((epos, apos) as posEA), Vars, Gl, total,
         depth, ((EVar (_, GX, VX, _) as X), s), eqn) ->
          ((if isId (I.comp (ss, s))
            then
              abstractEVarFap
                (flag, __Gs, posEA, Vars, Gl, total, depth, (__X, s), eqn)
            else
              abstractEVarNFap
                (flag, __Gs, posEA, Vars, Gl, total, depth, (__X, s), eqn))
          (* X is fully applied *)(* s =/= id, i.e. X is not fully applied *))
      (* X is possibly strengthened ! *)
    let rec abstractExp flag (__Gs) posEA (Vars) (Gl) total depth (__Us) eqn
      =
      abstractExpW
        (flag, __Gs, posEA, Vars, Gl, total, depth, (Whnf.whnf __Us), eqn)
    let rec abstractEVarFap flag (__Gs) ((epos, apos) as posEA) (Vars) (Gl)
      total depth (__X, s) eqn =
      ((match member (eqEVar __X) Vars with
        | Some (label, i) ->
            ((if flag
              then
                (match label with
                 | Body ->
                     let BV = I.BVar (apos + depth) in
                     let BV' = I.BVar (i + depth) in
                     let BV1 = I.BVar (apos + depth) in
                     let (posEA', Vars', __S, eqn1) =
                       abstractSub
                         (flag, __Gs, (epos, (apos - 1)), Vars, Gl, total,
                           depth, s, I.Nil, eqn) in
                     (posEA', Vars', (I.Root (BV, I.Nil)),
                       (TableParam.Unify
                          (Gl, (I.Root (BV', __S)), (I.Root (BV1, I.Nil)),
                            eqn1)))
                 | TypeLabel ->
                     let Vars' = update (eqEVar __X) Vars in
                     let (posEA', Vars'', __S, eqn1) =
                       abstractSub
                         (flag, __Gs, (epos, apos), Vars', Gl, total, depth,
                           s, I.Nil, eqn) in
                     (posEA', Vars'', (I.Root ((I.BVar (i + depth)), __S)),
                       eqn1))
              else
                (let (posEA', Vars', __S, eqn1) =
                   abstractSub
                     (flag, __Gs, (epos, apos), Vars, Gl, total, depth, s,
                       I.Nil, eqn) in
                 (posEA', Vars', (I.Root ((I.BVar (i + depth)), __S)), eqn1)))
            (* enforce linearization *)(* do not enforce linearization -- used for type labels *))
        | NONE ->
            let label = if flag then Body else TypeLabel in
            let BV = I.BVar (epos + depth) in
            let pos = ((epos - 1), apos) in
            let (posEA', Vars', __S, eqn1) =
              abstractSub
                (flag, __Gs, pos, (I.Decl (Vars, ((label, epos), (EV __X)))),
                  Gl, total, depth, s, I.Nil, eqn) in
            (posEA', Vars', (I.Root (BV, __S)), eqn1))
      (* we have seen X before *)(* we see X for the first time *))
    let rec abstractEVarNFap flag (__Gs) ((epos, apos) as posEA) (Vars) (Gl)
      total depth (__X, s) eqn =
      ((match member (eqEVar __X) Vars with
        | Some (label, i) ->
            ((if flag
              then
                let BV = I.BVar (apos + depth) in
                let BV' = I.BVar (i + depth) in
                let BV1 = I.BVar (apos + depth) in
                let (posEA', Vars', __S, eqn1) =
                  abstractSub
                    (flag, __Gs, (epos, (apos - 1)), Vars, Gl, total, depth,
                      s, I.Nil, eqn) in
                (posEA', Vars', (I.Root (BV, I.Nil)),
                  (TableParam.Unify
                     (Gl, (I.Root (BV', __S)), (I.Root (BV1, I.Nil)), eqn1)))
              else
                (let (posEA', Vars', __S, eqn1) =
                   abstractSub
                     (flag, __Gs, (epos, apos), Vars, Gl, total, depth, s,
                       I.Nil, eqn) in
                 (posEA', Vars', (I.Root ((I.BVar (i + depth)), __S)), eqn1)))
            (* enforce linearization *)(* (case label of
               Body =>
                 let
                  val _ = print "abstractEVarNFap -- flag true; we have seen X before\n"
                   val BV = I.BVar(apos + depth)
                   val BV' = I.BVar(i + depth)
                   val BV1 = I.BVar(apos + depth)
                   val (posEA', Vars', S, eqn1) = abstractSub (flag, Gs, (epos, apos - 1), Vars, Gl, total, depth, s, I.Nil, eqn)
                 in
                   (posEA', Vars', I.Root(BV, I.Nil), TableParam.Unify(Gl, I.Root(BV', S), I.Root(BV1, I.Nil ), eqn1))
                 end
              | TyeLabel =>
                 let
                   val Vars' = update (eqEVar X) Vars
                   val (posEA', Vars'', S, eqn1) = abstractSub (flag, Gs, (epos, apos), Vars', Gl, total, depth, s, I.Nil, eqn)
                 in
                   (posEA', Vars'', I.Root(I.BVar(i + depth), S), eqn1)
                 end) *)
            (* do not enforce linearization -- used for type labels *))
        | NONE ->
            ((if flag
              then
                let label = if flag then Body else TypeLabel in
                let BV = I.BVar (apos + depth) in
                let BV' = I.BVar (epos + depth) in
                let BV1 = I.BVar (apos + depth) in
                let (posEA', Vars', __S, eqn1) =
                  abstractSub
                    (flag, __Gs, ((epos - 1), (apos - 1)),
                      (I.Decl (Vars, ((label, epos), (EV __X)))), Gl, total,
                      depth, s, I.Nil, eqn) in
                (posEA', Vars', (I.Root (BV, I.Nil)),
                  (TableParam.Unify
                     (Gl, (I.Root (BV', __S)), (I.Root (BV1, I.Nil)), eqn1)))
              else
                (let (posEA', Vars', __S, eqn1) =
                   abstractSub
                     (flag, __Gs, ((epos - 1), apos),
                       (I.Decl (Vars, ((TypeLabel, epos), (EV __X)))), Gl,
                       total, depth, s, I.Nil, eqn) in
                 (posEA', Vars', (I.Root ((I.BVar (epos + depth)), __S)),
                   eqn1)))
            (* enforce linearization since X is not fully applied *)
            (* do not enforce linearization -- used for type labels *)))
      (* we have seen X before *)(* we have not seen X before *))
    let rec abstractSub __60__ __61__ __62__ __63__ __64__ __65__ __66__
      __67__ __68__ __69__ =
      match (__60__, __61__, __62__, __63__, __64__, __65__, __66__, __67__,
              __68__, __69__)
      with
      | (flag, __Gs, posEA, Vars, Gl, total, depth, Shift k, __S, eqn) ->
          ((if k < depth
            then
              abstractSub
                (flag, __Gs, posEA, Vars, Gl, total, depth,
                  (I.Dot ((I.Idx (k + 1)), (I.Shift (k + 1)))), __S, eqn)
            else (posEA, Vars, __S, eqn))
          (* k = depth *))
      | (flag, __Gs, posEA, Vars, Gl, total, depth, Dot (Idx k, s), __S, eqn)
          ->
          abstractSub
            (flag, __Gs, posEA, Vars, Gl, total, depth, s,
              (I.App ((I.Root ((I.BVar k), I.Nil)), __S)), eqn)
      | (flag, __Gs, posEA, Vars, Gl, total, depth, Dot (Exp (__U), s), __S,
         eqn) ->
          let (posEA', Vars', __U', eqn') =
            abstractExp
              (flag, __Gs, posEA, Vars, Gl, total, depth, (__U, I.id), eqn) in
          abstractSub
            (flag, __Gs, posEA', Vars', Gl, total, depth, s,
              (I.App (__U', __S)), eqn')
    let rec abstractSpine __70__ __71__ __72__ __73__ __74__ __75__ __76__
      __77__ __78__ =
      match (__70__, __71__, __72__, __73__, __74__, __75__, __76__, __77__,
              __78__)
      with
      | (flag, __Gs, posEA, Vars, Gl, total, depth, (I.Nil, _), eqn) ->
          (posEA, Vars, I.Nil, eqn)
      | (flag, __Gs, posEA, Vars, Gl, total, depth, (SClo (__S, s'), s), eqn)
          ->
          abstractSpine
            (flag, __Gs, posEA, Vars, Gl, total, depth,
              (__S, (I.comp (s', s))), eqn)
      | (flag, __Gs, posEA, Vars, Gl, total, depth, (App (__U, __S), s), eqn)
          ->
          let (posEA', Vars', __U', eqn') =
            abstractExp
              (flag, __Gs, posEA, Vars, Gl, total, depth, (__U, s), eqn) in
          let (posEA'', Vars'', __S', eqn'') =
            abstractSpine
              (flag, __Gs, posEA', Vars', Gl, total, depth, (__S, s), eqn') in
          (posEA'', Vars'', (I.App (__U', __S')), eqn'')
    let rec abstractSub' __79__ __80__ __81__ __82__ __83__ __84__ =
      match (__79__, __80__, __81__, __82__, __83__, __84__) with
      | (flag, __Gs, epos, Vars, total, Shift k) ->
          if k < 0
          then raise (Error "Substitution out of range\n")
          else (epos, Vars, (I.Shift (k + total)))
      | (flag, __Gs, epos, Vars, total, Dot (Idx k, s)) ->
          let (epos', Vars', s') =
            abstractSub' (flag, __Gs, epos, Vars, total, s) in
          (epos', Vars', (I.Dot ((I.Idx k), s')))
      | (flag, __Gs, epos, Vars, total, Dot (Exp (__U), s)) ->
          let ((ep, _), Vars', __U', _) =
            abstractExp
              (false__, __Gs, (epos, 0), Vars, I.Null, total, 0, (__U, I.id),
                TableParam.Trivial) in
          let (epos'', Vars'', s') =
            abstractSub' (flag, __Gs, ep, Vars', total, s) in
          (epos'', Vars'', (I.Dot ((I.Exp __U'), s')))
    let rec abstractDec __85__ __86__ __87__ __88__ __89__ __90__ __91__
      __92__ =
      match (__85__, __86__, __87__, __88__, __89__, __90__, __91__, __92__)
      with
      | (__Gs, posEA, Vars, Gl, total, depth, (Dec (x, __V), s), NONE) ->
          let (posEA', Vars', __V', eqn) =
            abstractExp
              (false__, __Gs, posEA, Vars, Gl, total, depth, (__V, s),
                TableParam.Trivial) in
          (((posEA', Vars', (I.Dec (x, __V')), eqn))
            (*      val (posEA', Vars', V', _) = abstractExp (false, Gs, posEA, Vars, Gl, total, depth, (V, s), TableParam.Trivial)*))
      | (__Gs, posEA, Vars, Gl, total, depth, (Dec (x, __V), s), Some eqn) ->
          let (posEA', Vars', __V', eqn') =
            abstractExp
              (true__, __Gs, posEA, Vars, Gl, total, depth, (__V, s), eqn) in
          (((posEA', Vars', (I.Dec (x, __V')), eqn'))
            (*      val (posEA', Vars', V', _) = abstractExp (false, Gs, posEA, Vars, Gl, total, depth, (V, s), TableParam.Trivial)*))
    let rec abstractCtx' __93__ __94__ __95__ __96__ __97__ __98__ __99__
      __100__ =
      match (__93__, __94__, __95__, __96__, __97__, __98__, __99__, __100__)
      with
      | (__Gs, epos, Vars, total, depth, DProg (I.Null, I.Null), __G', eqn)
          -> (epos, Vars, __G', eqn)
      | (__Gs, epos, Vars, total, depth, DProg
         (Decl (__G, __D), Decl (dPool, C.Parameter)), __G', eqn) ->
          let d = IntSyn.ctxLength __G in
          let ((epos', _), Vars', __D', _) =
            abstractDec
              (__Gs, (epos, total), Vars, I.Null, total, (depth - 1),
                (__D, I.id), NONE) in
          abstractCtx'
            (__Gs, epos', Vars', total, (depth - 1), (C.DProg (__G, dPool)),
              (I.Decl (__G', __D')), eqn)
      | (__Gs, epos, Vars, total, depth, DProg
         (Decl (__G, __D), Decl (dPool, _)), __G', eqn) ->
          let d = IntSyn.ctxLength __G in
          let ((epos', _), Vars', __D', _) =
            abstractDec
              (__Gs, (epos, total), Vars, I.Null, total, (depth - 1),
                (__D, I.id), NONE) in
          abstractCtx'
            (__Gs, epos', Vars', total, (depth - 1), (C.DProg (__G, dPool)),
              (I.Decl (__G', __D')), eqn)
    let rec abstractCtx (__Gs) epos (Vars) total depth dProg =
      abstractCtx'
        (__Gs, epos, Vars, total, depth, dProg, I.Null, TableParam.Trivial)
    let rec makeEVarCtx __101__ __102__ __103__ __104__ __105__ =
      match (__101__, __102__, __103__, __104__, __105__) with
      | (__Gs, Vars, DEVars, I.Null, total) -> DEVars
      | (__Gs, Vars, DEVars, Decl (__K', (_, EV (EVar (_, GX, VX, _) as E))),
         total) ->
          let __V' = raiseType (GX, VX) in
          let (_, Vars', V'', _) =
            abstractExp
              (false__, __Gs, (0, 0), Vars, I.Null, 0, (total - 1),
                (__V', I.id), TableParam.Trivial) in
          let DEVars' = makeEVarCtx (__Gs, Vars', DEVars, __K', (total - 1)) in
          let DEVars'' = I.Decl (DEVars', (I.Dec (NONE, V''))) in DEVars''
    let rec makeAVarCtx (Vars) (DupVars) =
      let rec avarCtx __106__ __107__ __108__ =
        match (__106__, __107__, __108__) with
        | (Vars, I.Null, k) -> I.Null
        | (Vars, Decl
           (__K', AV ((EVar ({ contents = NONE }, GX, VX, _) as E), d)), k)
            ->
            I.Decl
              ((avarCtx (Vars, __K', (k + 1))),
                (I.ADec
                   ((Some
                       ((^) (((^) "AVar " Int.toString k) ^ "--")
                          Int.toString d)), d)))
        | (Vars, Decl (__K', AV ((EVar (_, GX, VX, _) as E), d)), k) ->
            I.Decl
              ((avarCtx (Vars, __K', (k + 1))),
                (I.ADec
                   ((Some
                       ((^) (((^) "AVar " Int.toString k) ^ "--")
                          Int.toString d)), d))) in
      avarCtx (Vars, DupVars, 0)
    let rec lowerEVar' __109__ __110__ __111__ =
      match (__109__, __110__, __111__) with
      | (__X, __G, (Pi ((__D', _), __V'), s')) ->
          let D'' = I.decSub (__D', s') in
          let (__X', __U) =
            lowerEVar'
              (__X, (I.Decl (__G, D'')), (Whnf.whnf (__V', (I.dot1 s')))) in
          (__X', (I.Lam (D'', __U)))
      | (__X, __G, __Vs') -> let __X' = __X in (__X', __X')
    let rec lowerEVar1 __112__ __113__ __114__ =
      match (__112__, __113__, __114__) with
      | (__X, EVar (r, __G, _, _), ((Pi _ as V), s)) ->
          let (__X', __U) = lowerEVar' (__X, __G, (__V, s)) in
          I.EVar ((ref (Some __U)), I.Null, __V, (ref nil))
      | (_, __X, _) -> __X
    let rec lowerEVar __115__ __116__ =
      match (__115__, __116__) with
      | (__E, (EVar (r, __G, __V, { contents = nil }) as X)) ->
          lowerEVar1 (__E, __X, (Whnf.whnf (__V, I.id)))
      | (__E, EVar _) ->
          raise
            (Error
               "abstraction : LowerEVars: Typing ambiguous -- constraint of functional type cannot be simplified")
      (* pre-Twelf 1.2 code walk, Fri May  8 11:05:08 1998 *)(* It is not clear if this case can happen *)
    let rec evarsToSub __117__ __118__ =
      match (__117__, __118__) with
      | (I.Null, s) -> s
      | (Decl
         (__K',
          (_, EV (EVar (({ contents = NONE } as I), GX, VX, cnstr) as E))),
         s) ->
          let __V' = raiseType (GX, VX) in
          let __X =
            lowerEVar1
              (__E, (I.EVar (__I, I.Null, __V', cnstr)),
                (Whnf.whnf (__V', I.id))) in
          let s' = evarsToSub (__K', s) in ((I.Dot ((I.Exp __X), s'))
            (* redundant ? *))
    let rec avarsToSub __119__ __120__ =
      match (__119__, __120__) with
      | (I.Null, s) -> s
      | (Decl (Vars', AV ((EVar (__I, GX, VX, cnstr) as E), d)), s) ->
          let s' = avarsToSub (Vars', s) in
          let AVar r as X' = I.newAVar () in
          I.Dot ((I.Exp (I.EClo (__X', (I.Shift (~ d))))), s')
    let rec abstractEVarCtx (DProg (__G, dPool) as dp) p s =
      let (__Gs, ss, d) =
        if !TableParam.strengthen
        then
          let w' = Subordinate.weaken (__G, (I.targetFam p)) in
          let iw = Whnf.invert w' in
          let __G' = Whnf.strengthen (iw, __G) in
          let d' = I.ctxLength __G' in (__G', iw, d')
        else (__G, I.id, (I.ctxLength __G)) in
      let (__K, DupVars) = collectCtx ((__Gs, ss), dp, (I.Null, I.Null), d) in
      let (__K', DupVars') =
        collectExp ((__Gs, ss), I.Null, (p, s), __K, DupVars, true__, d) in
      let epos = I.ctxLength __K' in
      let apos = I.ctxLength DupVars' in
      let total = epos + apos in
      let (epos', Vars', __G', eqn) =
        abstractCtx ((__Gs, ss), epos, I.Null, total, d, dp) in
      let (((posEA'', Vars'', __U', eqn'))(* = 0 *)) =
        abstractExp
          (true__, (__Gs, ss), (epos', total), Vars', I.Null, total, d,
            (p, s), eqn) in
      let DAVars = makeAVarCtx (Vars'', DupVars') in
      let DEVars =
        makeEVarCtx ((((__Gs, ss), Vars'', I.Null, Vars'', 0))
          (* depth *)) in
      let s' = avarsToSub (DupVars', I.id) in
      let s'' = evarsToSub (Vars'', s') in
      let G'' = reverseCtx (__G', I.Null) in
      ((if !TableParam.strengthen
        then
          let w' = Subordinate.weaken (G'', (I.targetFam __U')) in
          let iw = Whnf.invert w' in
          let __Gs' = Whnf.strengthen (iw, G'') in
          (__Gs', DAVars, DEVars, __U', eqn', s'')
        else (G'', DAVars, DEVars, __U', eqn', s''))
        (* K ||- G i.e. K contains all EVars in G *)
        (* DupVars' , K' ||- p[s]  i.e. K' contains all EVars in (p,s) and G and
                                         DupVars' contains all duplicate EVars p[s] *)
        (* {{G}}_Vars' , i.e. abstract over the existential variables in G*)
        (* abstract over existential variables in p[s] and linearize the expression *)
        (* note: depth will become negative during makeEVarCtx *))
    let abstractEVarCtx = abstractEVarCtx
    let abstractAnswSub s =
      let (__K, _) =
        collectSub ((I.Null, I.id), I.Null, s, I.Null, I.Null, false__, 0) in
      let epos = I.ctxLength __K in
      let (((_, Vars, s'))(*0 *)) =
        abstractSub' (((false__, (I.Null, I.id), epos, I.Null, epos, s))
          (* total *)) in
      let DEVars = makeEVarCtx ((I.Null, I.id), Vars, I.Null, Vars, 0) in
      let s1' = ctxToEVarSub (DEVars, I.id) in (((DEVars, s'))
        (* no linearization for answer substitution *))
    let raiseType (__G) (__U) = raiseType (__G, __U)
  end ;;
