
module type METAABSTRACT  =
  sig
    module MetaSyn : METASYN
    exception Error of string 
    val abstract : MetaSyn.__State -> MetaSyn.__State
  end;;




module MetaAbstract(MetaAbstract:sig
                                   module Global : GLOBAL
                                   module MetaSyn' : METASYN
                                   module MetaGlobal : METAGLOBAL
                                   module Abstract : ABSTRACT
                                   module ModeTable : MODETABLE
                                   module Whnf : WHNF
                                   module Print : PRINT
                                   module Constraints : CONSTRAINTS
                                   module Unify : UNIFY
                                   module Names : NAMES
                                   module TypeCheck : TYPECHECK
                                   module Subordinate : SUBORDINATE
                                 end) : METAABSTRACT =
  struct
    module MetaSyn = MetaSyn'
    exception Error of string 
    module I = IntSyn
    module S = Stream
    module M = MetaSyn
    module C = Constraints
    type __Var =
      | EV of
      (((I.__Exp option ref * I.__Exp * MetaSyn.__Mode))(* Var ::= EVar <r_, V, St>       *))
      
      | BV 
    let rec checkEmpty =
      function
      | nil -> ()
      | Cnstr ->
          (match C.simplify Cnstr with
           | nil -> ()
           | _ -> raise (Error "Unresolved constraints"))
    let rec typecheck (Prefix (__G, __M, __B)) (__V) =
      TypeCheck.typeCheck (__G, (__V, (I.Uni I.Type)))
    let rec modeEq __0__ __1__ =
      match (__0__, __1__) with
      | (Marg (ModeSyn.Plus, _), M.Top) -> true
      | (Marg (ModeSyn.Minus, _), M.Bot) -> true
      | _ -> false
    let rec atxLookup __2__ __3__ =
      match (__2__, __3__) with
      | (I.Null, _) -> None
      | (Decl (__M, BV), r) -> atxLookup (__M, r)
      | (Decl (__M, (EV (r', _, _) as E)), r) ->
          if r = r' then Some __E else atxLookup (__M, r)
    let rec raiseType __4__ __5__ __6__ =
      match (__4__, __5__, __6__) with
      | (0, __G, __V) -> __V
      | (depth, Decl (__G, __D), __V) ->
          raiseType ((depth - 1), __G, (I.Pi ((__D, I.Maybe), __V)))
    let rec weaken __7__ __8__ __9__ =
      match (__7__, __8__, __9__) with
      | (0, __G, a) -> I.id
      | (depth, Decl (__G', (Dec (name, __V) as D)), a) ->
          let w' = weaken ((depth - 1), __G', a) in
          if Subordinate.belowEq ((I.targetFam __V), a)
          then I.dot1 w'
          else I.comp (w', I.shift)
    let rec countPi (__V) =
      let rec countPi' __10__ __11__ =
        match (__10__, __11__) with
        | (Root _, n) -> n
        | (Pi (_, __V), n) -> countPi' (__V, (n + 1))
        | (EClo (__V, _), n) -> countPi' (__V, n) in
      countPi' (__V, 0)
    let rec collectExp lG0 (__G) (__Us) mode (Adepth) =
      collectExpW (lG0, __G, (Whnf.whnf __Us), mode, Adepth)
    let rec collectExpW __12__ __13__ __14__ __15__ __16__ =
      match (__12__, __13__, __14__, __15__, __16__) with
      | (lG0, __G, (Uni _, s), mode, Adepth) -> Adepth
      | (lG0, __G, (Pi ((__D, _), __V), s), mode, Adepth) ->
          collectExp
            (lG0, (I.Decl (__G, (I.decSub (__D, s)))), (__V, (I.dot1 s)),
              mode, (collectDec (lG0, __G, (__D, s), mode, Adepth)))
      | (lG0, __G, (Lam (__D, __U), s), mode, Adepth) ->
          collectExp
            (lG0, (I.Decl (__G, (I.decSub (__D, s)))), (__U, (I.dot1 s)),
              mode, (collectDec (lG0, __G, (__D, s), mode, Adepth)))
      | (lG0, __G, ((Root (BVar k, __S), s) as Us), mode,
         ((__A, depth) as Adepth)) ->
          let l = I.ctxLength __G in
          if (((k = l) + depth) - lG0) && (depth > 0)
          then
            let Dec (_, __V) = I.ctxDec (__G, k) in
            ((collectSpine
                (lG0, __G, (__S, s), mode, ((I.Decl (__A, BV)), (depth - 1))))
              (* invariant: all variables (EV or BV) in V already seen! *))
          else collectSpine (lG0, __G, (__S, s), mode, Adepth)
      | (lG0, __G, (Root (__C, __S), s), mode, Adepth) ->
          collectSpine (lG0, __G, (__S, s), mode, Adepth)
      | (lG0, __G, (EVar (r, GX, __V, cnstrs), s), mode,
         ((__A, depth) as Adepth)) ->
          (match atxLookup (__A, r) with
           | None ->
               let _ = checkEmpty (!cnstrs) in
               let lGp' = ((I.ctxLength GX) - lG0) + depth in
               let w = weaken (lGp', GX, (I.targetFam __V)) in
               let iw = Whnf.invert w in
               let GX' = Whnf.strengthen (iw, GX) in
               let lGp'' = ((I.ctxLength GX') - lG0) + depth in
               let Vraised = raiseType (lGp'', GX', (I.EClo (__V, iw))) in
               let EVar (r', _, _, _) as X' =
                 I.newEVar (GX', (I.EClo (__V, iw))) in
               let _ = Unify.instantiateEVar (r, (I.EClo (__X', w)), nil) in
               ((collectSub
                   (lG0, __G, lGp'', s, mode,
                     ((I.Decl (__A, (EV (r', Vraised, mode)))), depth)))
                 (* lGp' >= 0 *)(* lGp'' >= 0 *)
                 (* invariant: all variables (EV) in Vraised already seen *))
           | Some (EV (_, __V, _)) ->
               let lGp' = countPi __V in
               collectSub (lG0, __G, lGp', s, mode, Adepth))
      | (lGO, __G, (FgnExp csfe, s), mode, Adepth) ->
          I.FgnExpStd.fold csfe
            (fun (__U) ->
               fun (Adepth') ->
                 collectExp (lGO, __G, (__U, s), mode, Adepth')) Adepth
      (* s = id *)(* impossible? *)
    let rec collectSub __17__ __18__ __19__ __20__ __21__ __22__ =
      match (__17__, __18__, __19__, __20__, __21__, __22__) with
      | (_, _, 0, _, _, Adepth) -> Adepth
      | (lG0, __G, lG', Shift k, mode, Adepth) ->
          collectSub
            (lG0, __G, lG', (I.Dot ((I.Idx (k + 1)), (I.Shift (k + 1)))),
              mode, Adepth)
      | (lG0, __G, lG', Dot (Idx k, s), mode, ((__A, depth) as Adepth)) ->
          collectSub (lG0, __G, (lG' - 1), s, mode, Adepth)
      | (lG0, __G, lG', Dot (Exp (__U), s), mode, Adepth) ->
          collectSub
            (lG0, __G, (lG' - 1), s, mode,
              (collectExp (lG0, __G, (__U, I.id), mode, Adepth)))(* typing invariant guarantees that (EV, BV) in V already
             collected !! *)
      (* typing invariant guarantees that (EV, BV) in k : V already
             collected !! *)
      (* eta expansion *)
    let rec collectSpine __23__ __24__ __25__ __26__ __27__ =
      match (__23__, __24__, __25__, __26__, __27__) with
      | (lG0, __G, (I.Nil, _), mode, Adepth) -> Adepth
      | (lG0, __G, (SClo (__S, s'), s), mode, Adepth) ->
          collectSpine (lG0, __G, (__S, (I.comp (s', s))), mode, Adepth)
      | (lG0, __G, (App (__U, __S), s), mode, Adepth) ->
          collectSpine
            (lG0, __G, (__S, s), mode,
              (collectExp (lG0, __G, (__U, s), mode, Adepth)))
    let rec collectDec lG0 (__G) (Dec (x, __V), s) mode (Adepth) =
      collectExp (lG0, __G, (__V, s), mode, Adepth)
    let rec collectModeW __30__ __31__ __32__ __33__ __34__ __35__ =
      match (__30__, __31__, __32__, __33__, __34__, __35__) with
      | (lG0, __G, modeIn, modeRec, (Root (Const cid, __S), s), Adepth) ->
          let rec collectModeW' __28__ __29__ =
            match (__28__, __29__) with
            | (((I.Nil, _), ModeSyn.Mnil), Adepth) -> Adepth
            | (((SClo (__S, s'), s), __M), Adepth) ->
                collectModeW' (((__S, (I.comp (s', s))), __M), Adepth)
            | (((App (__U, __S), s), Mapp (m, mS)), Adepth) ->
                collectModeW'
                  (((__S, s), mS),
                    (if modeEq (m, modeIn)
                     then collectExp (lG0, __G, (__U, s), modeRec, Adepth)
                     else Adepth)) in
          let mS = valOf (ModeTable.modeLookup cid) in
          collectModeW' (((__S, s), mS), Adepth)
      | (lG0, __G, modeIn, modeRec, (Pi ((__D, __P), __V), s), Adepth) ->
          raise
            (Error
               "Implementation restricted to the Horn fragment of the meta logic")
      (* s = id *)
    let rec collectG lG0 (__G) (__Vs) (Adepth) =
      collectGW (lG0, __G, (Whnf.whnf __Vs), Adepth)
    let rec collectGW lG0 (__G) (__Vs) (Adepth) =
      collectModeW
        (lG0, __G, M.Bot, M.Top, __Vs,
          (collectModeW (lG0, __G, M.Top, M.Bot, __Vs, Adepth)))
    let rec collectDTop lG0 (__G) (__Vs) (Adepth) =
      collectDTopW (lG0, __G, (Whnf.whnf __Vs), Adepth)
    let rec collectDTopW __36__ __37__ __38__ __39__ =
      match (__36__, __37__, __38__, __39__) with
      | (lG0, __G, (Pi (((Dec (x, __V1) as D), I.No), __V2), s), Adepth) ->
          collectG
            (lG0, __G, (__V1, s),
              (collectDTop
                 (lG0, (I.Decl (__G, (I.decSub (__D, s)))),
                   (__V2, (I.dot1 s)), Adepth)))
      | (lG0, __G, ((Root _, s) as Vs), Adepth) ->
          collectModeW (lG0, __G, M.Top, M.Top, __Vs, Adepth)(* s = id *)
      (* only arrows *)
    let rec collectDBot lG0 (__G) (__Vs) (Adepth) =
      collectDBotW (lG0, __G, (Whnf.whnf __Vs), Adepth)
    let rec collectDBotW __40__ __41__ __42__ __43__ =
      match (__40__, __41__, __42__, __43__) with
      | (lG0, __G, (Pi ((__D, _), __V), s), Adepth) ->
          collectDBot
            (lG0, (I.Decl (__G, (I.decSub (__D, s)))), (__V, (I.dot1 s)),
              Adepth)
      | (lG0, __G, ((Root _, s) as Vs), Adepth) ->
          collectModeW (lG0, __G, M.Bot, M.Bot, __Vs, Adepth)(* s = id *)
    let rec collect (Prefix (__G, __M, __B)) (__V) =
      let lG0 = I.ctxLength __G in
      let (__A, k) =
        collectDBot
          (lG0, __G, (__V, I.id),
            (collectDTop (lG0, __G, (__V, I.id), (I.Null, lG0)))) in
      __A
    let rec lookupEV (__A) r =
      let rec lookupEV' __44__ __45__ __46__ =
        match (__44__, __45__, __46__) with
        | (Decl (__A, EV (r, __V, _)), r', k) ->
            if r = r' then (k, __V) else lookupEV' (__A, r', (k + 1))
        | (Decl (__A, BV), r', k) -> lookupEV' (__A, r', (k + 1)) in
      ((lookupEV' (__A, r, 1))
        (* lookupEV' I.Null cannot occur by invariant *))
    let rec lookupBV (__A) i =
      let rec lookupBV' __47__ __48__ __49__ =
        match (__47__, __48__, __49__) with
        | (Decl (__A, EV (r, __V, _)), i, k) -> lookupBV' (__A, i, (k + 1))
        | (Decl (__A, BV), 1, k) -> k
        | (Decl (__A, BV), i, k) -> lookupBV' (__A, (i - 1), (k + 1)) in
      ((lookupBV' (__A, i, 1))
        (* lookupBV' I.Null cannot occur by invariant *))
    let rec abstractExpW __50__ __51__ __52__ __53__ =
      match (__50__, __51__, __52__, __53__) with
      | (__A, __G, depth, ((Uni (__L) as V), s)) -> __V
      | (__A, __G, depth, (Pi ((__D, __P), __V), s)) ->
          Abstract.piDepend
            (((abstractDec (__A, __G, depth, (__D, s))), __P),
              (abstractExp
                 (__A, (I.Decl (__G, (I.decSub (__D, s)))), (depth + 1),
                   (__V, (I.dot1 s)))))
      | (__A, __G, depth, (Lam (__D, __U), s)) ->
          I.Lam
            ((abstractDec (__A, __G, depth, (__D, s))),
              (abstractExp
                 (__A, (I.Decl (__G, (I.decSub (__D, s)))), (depth + 1),
                   (__U, (I.dot1 s)))))
      | (__A, __G, depth, (Root ((BVar k as C), __S), s)) ->
          if k > depth
          then
            let k' = lookupBV (__A, (k - depth)) in
            I.Root
              ((I.BVar (k' + depth)),
                (abstractSpine (__A, __G, depth, (__S, s))))
          else I.Root (__C, (abstractSpine (__A, __G, depth, (__S, s))))
      | (__A, __G, depth, (Root (__C, __S), s)) ->
          I.Root (__C, (abstractSpine (__A, __G, depth, (__S, s))))
      | (__A, __G, depth, (EVar (r, _, __V, _), s)) ->
          let (k, Vraised) = lookupEV (__A, r) in
          ((I.Root
              ((I.BVar (k + depth)),
                (abstractSub
                   (__A, __G, depth, (Vraised, I.id), s, (I.targetFam __V),
                     I.Nil))))
            (* IMPROVE: remove the raised variable, replace by V -cs ?-fp *))
      | (__A, __G, depth, (FgnExp csfe, s)) ->
          I.FgnExpStd.Map.apply csfe
            (fun (__U) -> abstractExp (__A, __G, depth, (__U, s)))(* s = id *)
      (* s = id *)
    let rec abstractExp (__A) (__G) depth (__Us) =
      abstractExpW (__A, __G, depth, (Whnf.whnf __Us))
    let rec abstractSpine __54__ __55__ __56__ __57__ =
      match (__54__, __55__, __56__, __57__) with
      | (__A, __G, depth, (I.Nil, _)) -> I.Nil
      | (__A, __G, depth, (App (__U, __S), s)) ->
          I.App
            ((abstractExp (__A, __G, depth, (__U, s))),
              (abstractSpine (__A, __G, depth, (__S, s))))
      | (__A, __G, depth, (SClo (__S, s'), s)) ->
          abstractSpine (__A, __G, depth, (__S, (I.comp (s', s))))
    let rec abstractSub (__A) (__G) depth (XVt) s b (__S) =
      abstractSubW (__A, __G, depth, (Whnf.whnf XVt), s, b, __S)
    let rec abstractSubW __58__ __59__ __60__ __61__ __62__ __63__ __64__ =
      match (__58__, __59__, __60__, __61__, __62__, __63__, __64__) with
      | (__A, __G, depth, (Root _, _), s, b, __S) -> __S
      | (__A, __G, depth, ((Pi _, _) as XVt), Shift k, b, __S) ->
          abstractSub
            (__A, __G, depth, XVt,
              (I.Dot ((I.Idx (k + 1)), (I.Shift (k + 1)))), b, __S)
      | (__A, __G, depth, ((Pi (_, XV'), t) as XVt), Dot (Idx k, s), b, __S)
          ->
          let Dec (x, __V) = I.ctxDec (__G, k) in
          if k > depth
          then
            let k' = lookupBV (__A, (k - depth)) in
            abstractSub
              (__A, __G, depth, (XV', (I.dot1 t)), s, b,
                (I.App ((I.Root ((I.BVar (k' + depth)), I.Nil)), __S)))
          else
            abstractSub
              (__A, __G, depth, (XV', (I.dot1 t)), s, b,
                (I.App ((I.Root ((I.BVar k), I.Nil)), __S)))
      | (__A, __G, depth, ((Pi (_, XV'), t) as XVt), Dot (Exp (__U), s), b,
         __S) ->
          abstractSub
            (__A, __G, depth, (XV', (I.dot1 t)), s, b,
              (I.App ((abstractExp (__A, __G, depth, (__U, I.id))), __S)))
    let rec abstractDec (__A) (__G) depth (Dec (xOpt, __V), s) =
      I.Dec (xOpt, (abstractExp (__A, __G, depth, (__V, s))))
    let rec abstractCtx __65__ __66__ =
      match (__65__, __66__) with
      | (I.Null, (Prefix (I.Null, I.Null, I.Null) as GM)) -> (GM, I.Null)
      | (Decl (__A, BV), Prefix
         (Decl (__G, __D), Decl (__M, marg), Decl (__B, b))) ->
          let (Prefix (__G', __M', __B'), lG') =
            abstractCtx (__A, (M.Prefix (__G, __M, __B))) in
          let __D' = abstractDec (__A, __G, 0, (__D, I.id)) in
          let Dec (_, __V) = __D' in
          let _ =
            if !Global.doubleCheck
            then typecheck ((M.Prefix (__G', __M', __B')), __V)
            else () in
          ((M.Prefix
              ((I.Decl (__G', (Names.decName (__G', __D')))),
                (I.Decl (__M', marg)), (I.Decl (__B', b)))),
            (I.Decl (lG', __D')))
      | (Decl (__A, EV (r, __V, m)), GM) ->
          let (Prefix (__G', __M', __B'), lG') = abstractCtx (__A, GM) in
          let V'' = abstractExp (__A, lG', 0, (__V, I.id)) in
          let _ =
            if !Global.doubleCheck
            then typecheck ((M.Prefix (__G', __M', __B')), V'')
            else () in
          ((M.Prefix
              ((I.Decl (__G', (Names.decName (__G', (I.Dec (None, V'')))))),
                (I.Decl (__M', m)),
                (I.Decl
                   (__B',
                     (match m with
                      | M.Top -> !MetaGlobal.maxSplit
                      | M.Bot -> 0))))), lG')
    let rec abstract (State (name, (Prefix (__G, __M, __B) as GM), __V) as S)
      =
      let _ = Names.varReset I.Null in
      let __A = collect (GM, __V) in
      let (GM', _) = abstractCtx (__A, GM) in
      let __V' = abstractExp (__A, __G, 0, (__V, I.id)) in
      let __S = M.State (name, GM', __V') in
      let _ = if !Global.doubleCheck then typecheck (GM', __V') else () in
      __S
    let abstract = abstract
  end ;;
