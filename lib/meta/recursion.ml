
module type MTPRECURSION  =
  sig
    module StateSyn : STATESYN
    exception Error of string 
    type nonrec operator
    val expand : StateSyn.__State -> operator
    val apply : operator -> StateSyn.__State
    val menu : operator -> string
  end;;




module MTPRecursion(MTPRecursion:sig
                                   module MTPGlobal : MTPGLOBAL
                                   module Global : GLOBAL
                                   module StateSyn' : STATESYN
                                   module Abstract : ABSTRACT
                                   module MTPAbstract : MTPABSTRACT
                                   module FunTypeCheck : FUNTYPECHECK
                                   module MTPrint : MTPRINT
                                   module Whnf : WHNF
                                   module Unify : UNIFY
                                   module Conv : CONV
                                   module Names : NAMES
                                   module Subordinate : SUBORDINATE
                                   module Print : PRINT
                                   module TypeCheck : TYPECHECK
                                   module Formatter : FORMATTER
                                   module FunPrint : FUNPRINT
                                 end) : MTPRECURSION =
  struct
    module StateSyn = StateSyn'
    exception Error of string 
    type nonrec operator = StateSyn.__State
    module I = IntSyn
    module F = FunSyn
    module S = StateSyn
    module N = Names
    module Fmt = Formatter
    module A = MTPAbstract
    type __Dec =
      | Lemma of (int * F.__For) 
    let rec closedCtx =
      function
      | I.Null -> ()
      | Decl (__G, __D) ->
          if Abstract.closedDec (__G, (__D, I.id))
          then raise Domain
          else closedCtx __G
    let rec spine =
      function
      | 0 -> I.Nil
      | n -> I.App ((I.Root ((I.BVar n), I.Nil)), (spine (n - 1)))
    let rec someEVars __0__ __1__ __2__ =
      match (__0__, __1__, __2__) with
      | (__G, nil, s) -> s
      | (__G, (Dec (_, __V))::__L, s) ->
          someEVars
            (__G, __L,
              (I.Dot ((I.Exp (I.newEVar (__G, (I.EClo (__V, s))))), s)))
    let rec ctxSub __3__ __4__ =
      match (__3__, __4__) with
      | (nil, s) -> nil
      | ((__D)::__G, s) -> (::) (I.decSub (__D, s)) ctxSub (__G, (I.dot1 s))
    let rec appendCtx __5__ __6__ __7__ =
      match (__5__, __6__, __7__) with
      | (GB1, __T, nil) -> GB1
      | ((__G1, __B1), __T, (__D)::__G2) ->
          appendCtx (((I.Decl (__G1, __D)), (I.Decl (__B1, __T))), __T, __G2)
    let rec createCtx __8__ __9__ __10__ =
      match (__8__, __9__, __10__) with
      | ((__G, __B), nil, s) -> ((__G, __B), s, ((fun (AF) -> AF)))
      | ((__G, __B), n::ll, s) ->
          let LabelDec (l, __G1, __G2) = F.labelLookup n in
          let t = someEVars (__G, __G1, I.id) in
          let G2' = ctxSub (__G2, t) in
          let (__G', __B') =
            appendCtx ((__G, __B), (S.Parameter (Some n)), G2') in
          let s' = I.comp (s, (I.Shift (List.length G2'))) in
          let (GB'', s'', af'') = createCtx ((__G', __B'), ll, s') in
          (((GB'', s'',
              ((fun (AF) ->
                  A.Block ((__G, t, (List.length __G1), G2'), (af'' AF))))))
            (* G |- s' : G1 *)(* G |- G2' ctx *)
            (* . |- G' = G, G2' ctx *)(* G' |- s'' : G0 *))
    let rec createEVars __11__ __12__ =
      match (__11__, __12__) with
      | (__G, I.Null) -> I.Shift (I.ctxLength __G)
      | (__G, Decl (__G0, Dec (_, __V))) ->
          let s = createEVars (__G, __G0) in
          I.Dot ((I.Exp (I.newEVar (__G, (I.EClo (__V, s))))), s)
    let rec checkCtx __13__ __14__ __15__ =
      match (__13__, __14__, __15__) with
      | (__G, nil, (__V2, s)) -> false
      | (__G, (Dec (_, __V1) as D)::__G2, (__V2, s)) ->
          (CSManager.trail
             (fun () -> Unify.unifiable (__G, (__V1, I.id), (__V2, s))))
            ||
            (checkCtx
               ((I.Decl (__G, __D)), __G2, (__V2, (I.comp (s, I.shift)))))
    let rec checkLabels (__G', __B') (__V, s) ll l =
      if l < 0
      then None
      else
        (let LabelDec (name, __G1, __G2) = F.labelLookup l in
         let s = someEVars (__G', __G1, I.id) in
         let G2' = ctxSub (__G2, s) in
         let t = someEVars (__G', __G1, I.id) in
         let G2' = ctxSub (__G2, t) in
         ((if
             (not (List.exists (fun l' -> l = l') ll)) &&
               (checkCtx (__G', G2', (__V, s)))
           then Some l
           else checkLabels ((__G', __B'), (__V, s), ll, (l - 1)))
           (* G' |- t : G1 *)(* G |- G2' ctx *)))
      (* as nil *)
    let rec appendRL __16__ __17__ =
      match (__16__, __17__) with
      | (nil, __Ds) -> __Ds
      | ((Lemma (n, __F) as L)::__Ds1, __Ds2) ->
          let __Ds' = appendRL (__Ds1, __Ds2) in
          if
            List.exists
              (fun (Lemma (n', __F')) ->
                 (n = n') && (F.convFor ((__F, I.id), (__F', I.id)))) __Ds'
          then __Ds'
          else __L :: __Ds'
    let rec recursion (nih, Gall, Fex, Oex)
      (ncurrent, (__G0, __B0), ll, Ocurrent, __H, __F) =
      let ((__G', __B'), s', af) = createCtx ((__G0, __B0), ll, I.id) in
      let t' = createEVars (__G', Gall) in
      let AF = af (A.Head (__G', (Fex, t'), (I.ctxLength Gall))) in
      let Oex' = S.orderSub (Oex, t') in
      let Ocurrent' = S.orderSub (Ocurrent, s') in
      let rec sc (__Ds) =
        let Fnew = A.abstractApproxFor AF in
        if
          List.exists
            (fun nhist ->
               fun (Fhist) ->
                 (nih = nhist) && (F.convFor ((Fnew, I.id), (Fhist, I.id))))
            __H
        then __Ds
        else (Lemma (nih, Fnew)) :: __Ds in
      let rec ac (__G', __B') (__Vs) (__Ds) =
        match checkLabels ((__G', __B'), __Vs, ll, ((F.labelSize ()) - 1))
        with
        | None -> __Ds
        | Some l' ->
            let __Ds' =
              recursion
                ((nih, Gall, Fex, Oex),
                  (ncurrent, (__G0, __B0), (l' :: ll), Ocurrent, __H, __F)) in
            appendRL (__Ds', __Ds) in
      ((if ncurrent < nih
        then ordle ((__G', __B'), Oex', Ocurrent', sc, ac, nil)
        else ordlt ((__G', __B'), Oex', Ocurrent', sc, ac, nil))
        (* G' |- s' : G0 *)(* G' |- t' : Gall *))
    let rec set_parameter ((__G1, __B1) as GB) (EVar (r, _, __V, _) as X) k
      sc ac (__Ds) =
      let rec set_parameter' __18__ __19__ __20__ =
        match (__18__, __19__, __20__) with
        | ((I.Null, I.Null), _, __Ds) -> __Ds
        | ((Decl (__G, __D), Decl (__B, Parameter _)), k, __Ds) ->
            let Dec (_, __V') as D' = I.decSub (__D, (I.Shift k)) in
            let __Ds' =
              CSManager.trail
                (fun () ->
                   if
                     (Unify.unifiable (__G1, (__V, I.id), (__V', I.id))) &&
                       (Unify.unifiable
                          (__G1, (__X, I.id),
                            ((I.Root ((I.BVar k), I.Nil)), I.id)))
                   then sc __Ds
                   else __Ds) in
            set_parameter' ((__G, __B), (k + 1), __Ds')
        | ((Decl (__G, __D), Decl (__B, _)), k, __Ds) ->
            set_parameter' ((__G, __B), (k + 1), __Ds) in
      ((set_parameter' (GB, 1, __Ds))
        (* set_parameter' ((G, B), k, Ds) = Ds'

           Invariant:
           If    G1, D < G
        *))
    let rec ltinit (GB) k (__Us, __Vs) (UsVs') sc ac (__Ds) =
      ltinitW (GB, k, (Whnf.whnfEta (__Us, __Vs)), UsVs', sc, ac, __Ds)
    let rec ltinitW __21__ __22__ __23__ __24__ __25__ __26__ __27__ =
      match (__21__, __22__, __23__, __24__, __25__, __26__, __27__) with
      | (GB, k, (__Us, ((Root _, _) as Vs)), UsVs', sc, ac, __Ds) ->
          lt (GB, k, (__Us, __Vs), UsVs', sc, ac, __Ds)
      | ((__G, __B), k, ((Lam (__D1, __U), s1), (Pi (__D2, __V), s2)),
         ((__U', s1'), (__V', s2')), sc, ac, __Ds) ->
          ltinit
            (((I.Decl (((__G, (I.decSub (__D1, s1))))
                 (* = I.decSub (D2, s2) *))),
               (I.Decl (__B, (S.Parameter None)))), (k + 1),
              ((__U, (I.dot1 s1)), (__V, (I.dot1 s2))),
              ((__U', (I.comp (s1', I.shift))),
                (__V', (I.comp (s2', I.shift)))), sc, ac, __Ds)
    let rec lt (GB) k (__Us, __Vs) (__Us', __Vs') sc ac (__Ds) =
      ltW (GB, k, (__Us, __Vs), (Whnf.whnfEta (__Us', __Vs')), sc, ac, __Ds)
    let rec ltW __28__ __29__ __30__ __31__ __32__ __33__ __34__ =
      match (__28__, __29__, __30__, __31__, __32__, __33__, __34__) with
      | (GB, k, (__Us, __Vs), ((Root (Const c, __S'), s'), __Vs'), sc, ac,
         __Ds) ->
          ltSpine
            (GB, k, (__Us, __Vs), ((__S', s'), ((I.constType c), I.id)), sc,
              ac, __Ds)
      | (((__G, __B) as GB), k, (__Us, __Vs),
         ((Root (BVar n, __S'), s'), __Vs'), sc, ac, __Ds) ->
          (match I.ctxLookup (__B, n) with
           | Parameter _ ->
               let Dec (_, __V') = I.ctxDec (__G, n) in
               ltSpine
                 (GB, k, (__Us, __Vs), ((__S', s'), (__V', I.id)), sc, ac,
                   __Ds)
           | Lemma _ -> __Ds)
      | (GB, _, _, ((EVar _, _), _), _, _, __Ds) -> __Ds
      | (((__G, __B) as GB), k, ((__U, s1), (__V, s2)),
         ((Lam ((Dec (_, V1') as D), __U'), s1'),
          (Pi ((Dec (_, V2'), _), __V'), s2')),
         sc, ac, __Ds) ->
          let __Ds' = __Ds in
          ((if Subordinate.equiv ((I.targetFam __V), (I.targetFam V1'))
            then
              let __X = I.newEVar (__G, (I.EClo (V1', s1'))) in
              let sc' (Ds'') = set_parameter (GB, __X, k, sc, ac, Ds'') in
              ((lt
                  (GB, k, ((__U, s1), (__V, s2)),
                    ((__U', (I.Dot ((I.Exp __X), s1'))),
                      (__V', (I.Dot ((I.Exp __X), s2')))), sc', ac, __Ds'))
                (* enforce that X gets only bound to parameters *)
                (* = I.newEVar (I.EClo (V2', s2')) *))
            else
              if Subordinate.below ((I.targetFam V1'), (I.targetFam __V))
              then
                (let __X = I.newEVar (__G, (I.EClo (V1', s1'))) in
                 ((lt
                     (GB, k, ((__U, s1), (__V, s2)),
                       ((__U', (I.Dot ((I.Exp __X), s1'))),
                         (__V', (I.Dot ((I.Exp __X), s2')))), sc, ac, __Ds'))
                   (* = I.newEVar (I.EClo (V2', s2')) *)))
              else __Ds')
            (* == I.targetFam V2' *)(* ctxBlock (GB, I.EClo (V1', s1'), k, sc, ac, Ds) *))
      (*            else Ds *)(* k might not be needed any more: Check --cs *)
      (*          if n <= k then   n must be a local variable *)
    let rec ltSpine (GB) k (__Us, __Vs) (__Ss', __Vs') sc ac (__Ds) =
      ltSpineW
        (GB, k, (__Us, __Vs), (__Ss', (Whnf.whnf __Vs')), sc, ac, __Ds)
    let rec ltSpineW __35__ __36__ __37__ __38__ __39__ __40__ __41__ =
      match (__35__, __36__, __37__, __38__, __39__, __40__, __41__) with
      | (GB, k, (__Us, __Vs), ((I.Nil, _), _), _, _, __Ds) -> __Ds
      | (GB, k, (__Us, __Vs), ((SClo (__S, s'), s''), __Vs'), sc, ac, __Ds)
          ->
          ltSpineW
            (GB, k, (__Us, __Vs), ((__S, (I.comp (s', s''))), __Vs'), sc, ac,
              __Ds)
      | (GB, k, (__Us, __Vs),
         ((App (__U', __S'), s1'), (Pi ((Dec (_, V1'), _), V2'), s2')), sc,
         ac, __Ds) ->
          let __Ds' =
            le (GB, k, (__Us, __Vs), ((__U', s1'), (V1', s2')), sc, ac, __Ds) in
          ltSpine
            (GB, k, (__Us, __Vs),
              ((__S', s1'),
                (V2', (I.Dot ((I.Exp (I.EClo (__U', s1'))), s2')))), sc, ac,
              __Ds')
    let rec eq (__G, __B) (__Us, __Vs) (__Us', __Vs') sc ac (__Ds) =
      CSManager.trail
        (fun () ->
           if
             (Unify.unifiable (__G, __Vs, __Vs')) &&
               (Unify.unifiable (__G, __Us, __Us'))
           then sc __Ds
           else __Ds)
    let rec le (GB) k (__Us, __Vs) (__Us', __Vs') sc ac (__Ds) =
      let __Ds' = eq (GB, (__Us, __Vs), (__Us', __Vs'), sc, ac, __Ds) in
      leW (GB, k, (__Us, __Vs), (Whnf.whnfEta (__Us', __Vs')), sc, ac, __Ds')
    let rec leW __42__ __43__ __44__ __45__ __46__ __47__ __48__ =
      match (__42__, __43__, __44__, __45__, __46__, __47__, __48__) with
      | (((__G, __B) as GB), k, ((__U, s1), (__V, s2)),
         ((Lam ((Dec (_, V1') as D), __U'), s1'),
          (Pi ((Dec (_, V2'), _), __V'), s2')),
         sc, ac, __Ds) ->
          let __Ds' = ac (GB, (V1', s1'), __Ds) in
          ((if Subordinate.equiv ((I.targetFam __V), (I.targetFam V1'))
            then
              let __X = I.newEVar (__G, (I.EClo (V1', s1'))) in
              let sc' (Ds'') = set_parameter (GB, __X, k, sc, ac, Ds'') in
              ((le
                  (GB, k, ((__U, s1), (__V, s2)),
                    ((__U', (I.Dot ((I.Exp __X), s1'))),
                      (__V', (I.Dot ((I.Exp __X), s2')))), sc', ac, __Ds'))
                (* = I.newEVar (I.EClo (V2', s2')) *)
                (* enforces that X can only bound to parameter *))
            else
              if Subordinate.below ((I.targetFam V1'), (I.targetFam __V))
              then
                (let __X = I.newEVar (__G, (I.EClo (V1', s1'))) in
                 let sc' = sc in
                 let Ds'' =
                   le
                     (GB, k, ((__U, s1), (__V, s2)),
                       ((__U', (I.Dot ((I.Exp __X), s1'))),
                         (__V', (I.Dot ((I.Exp __X), s2')))), sc', ac, __Ds') in
                 ((Ds'')
                   (* = I.newEVar (I.EClo (V2', s2')) *)
                   (*              val sc'' = fn Ds'' => set_parameter (GB, X, k, sc, ac, Ds'')    BUG -cs *)))
              else __Ds')
            (* == I.targetFam V2' *))
      | (GB, k, (__Us, __Vs), (__Us', __Vs'), sc, ac, __Ds) ->
          lt (GB, k, (__Us, __Vs), (__Us', __Vs'), sc, ac, __Ds)
    let rec ordlt __49__ __50__ __51__ __52__ __53__ __54__ =
      match (__49__, __50__, __51__, __52__, __53__, __54__) with
      | (GB, Arg (UsVs), Arg (UsVs'), sc, ac, __Ds) ->
          ltinit (GB, 0, UsVs, UsVs', sc, ac, __Ds)
      | (GB, Lex (__L), Lex (__L'), sc, ac, __Ds) ->
          ordltLex (GB, __L, __L', sc, ac, __Ds)
      | (GB, Simul (__L), Simul (__L'), sc, ac, __Ds) ->
          ordltSimul (GB, __L, __L', sc, ac, __Ds)
    let rec ordltLex __55__ __56__ __57__ __58__ __59__ __60__ =
      match (__55__, __56__, __57__, __58__, __59__, __60__) with
      | (GB, nil, nil, sc, ac, __Ds) -> __Ds
      | (GB, (__O)::__L, (__O')::__L', sc, ac, __Ds) ->
          let __Ds' =
            CSManager.trail (fun () -> ordlt (GB, __O, __O', sc, ac, __Ds)) in
          ordeq
            (GB, __O, __O',
              (fun (Ds'') -> ordltLex (GB, __L, __L', sc, ac, Ds'')), ac,
              __Ds')
    let rec ordltSimul __61__ __62__ __63__ __64__ __65__ __66__ =
      match (__61__, __62__, __63__, __64__, __65__, __66__) with
      | (GB, nil, nil, sc, ac, __Ds) -> __Ds
      | (GB, (__O)::__L, (__O')::__L', sc, ac, __Ds) ->
          let Ds'' =
            CSManager.trail
              (fun () ->
                 ordlt
                   (GB, __O, __O',
                     (fun (__Ds') ->
                        ordleSimul (GB, __L, __L', sc, ac, __Ds')), ac, __Ds)) in
          ordeq
            (GB, __O, __O',
              (fun (__Ds') -> ordltSimul (GB, __L, __L', sc, ac, __Ds')), ac,
              Ds'')
    let rec ordleSimul __67__ __68__ __69__ __70__ __71__ __72__ =
      match (__67__, __68__, __69__, __70__, __71__, __72__) with
      | (GB, nil, nil, sc, ac, __Ds) -> sc __Ds
      | (GB, (__O)::__L, (__O')::__L', sc, ac, __Ds) ->
          ordle
            (GB, __O, __O',
              (fun (__Ds') -> ordleSimul (GB, __L, __L', sc, ac, __Ds')), ac,
              __Ds)
    let rec ordeq __73__ __74__ __75__ __76__ __77__ __78__ =
      match (__73__, __74__, __75__, __76__, __77__, __78__) with
      | ((__G, __B), Arg (__Us, __Vs), Arg (__Us', __Vs'), sc, ac, __Ds) ->
          if
            (Unify.unifiable (__G, __Vs, __Vs')) &&
              (Unify.unifiable (__G, __Us, __Us'))
          then sc __Ds
          else __Ds
      | (GB, Lex (__L), Lex (__L'), sc, ac, __Ds) ->
          ordeqs (GB, __L, __L', sc, ac, __Ds)
      | (GB, Simul (__L), Simul (__L'), sc, ac, __Ds) ->
          ordeqs (GB, __L, __L', sc, ac, __Ds)
    let rec ordeqs __79__ __80__ __81__ __82__ __83__ __84__ =
      match (__79__, __80__, __81__, __82__, __83__, __84__) with
      | (GB, nil, nil, sc, ac, __Ds) -> sc __Ds
      | (GB, (__O)::__L, (__O')::__L', sc, ac, __Ds) ->
          ordeq
            (GB, __O, __O',
              (fun (__Ds') -> ordeqs (GB, __L, __L', sc, ac, __Ds')), ac,
              __Ds)
    let rec ordle (GB) (__O) (__O') sc ac (__Ds) =
      let __Ds' =
        CSManager.trail (fun () -> ordeq (GB, __O, __O', sc, ac, __Ds)) in
      ordlt (GB, __O, __O', sc, ac, __Ds')
    let rec skolem __85__ __86__ __87__ __88__ __89__ =
      match (__85__, __86__, __87__, __88__, __89__) with
      | ((du, de), GB, w, F.True, sc) -> (GB, w)
      | ((du, de), GB, w, All (Prim (__D), __F), sc) ->
          skolem
            (((du + 1), de), GB, w, __F,
              ((fun s ->
                  fun de' ->
                    let (s', __V', __F') = sc (s, de') in
                    ((((I.dot1 s'),
                        (fun (__V) ->
                           __V'
                             (Abstract.piDepend
                                (((Whnf.normalizeDec (__D, s')), I.Meta),
                                  (Whnf.normalize (__V, I.id))))),
                        (fun (__F) ->
                           __F' (F.All ((F.Prim (I.decSub (__D, s'))), __F)))))
                      (* _   : GB, Ds, G'[...], D[?] |- _ : GB, G, D *)
                      (* _   : maps (GB, Ds, G'[....], D[?] |- V : type) to  (GB, Ds, |- {G[....], D[?]} V : type) *)
                      (* _   : maps (GB, Ds, G'[....], D[?] |- F : for) to  (GB, Ds, |- {{G[....], D[?]}} F : for) *)
                      (* s'  : GB, Ds, G'[...] |- s' : GB, G *)(* V'  : maps (GB, Ds, G'[...] |- V type) to (GB, Ds |- {G'[...]} V type) *)
                      (* F'  : maps (GB, Ds, G'[...] |- F for) to (GB, Ds |- {{G'[...]}} F for) *)))
              (* s'  :  GB, Ds |- s : GB   *)))
      | ((du, de), (__G, __B), w, Ex (Dec (name, __V), __F), sc) ->
          let (s', __V', __F') = sc (w, de) in
          let __V1 = I.EClo (__V, s') in
          let __V2 = Whnf.normalize ((__V' __V1), I.id) in
          let __F1 = F.Ex ((I.Dec (name, __V1)), F.True) in
          let __F2 = __F' __F1 in
          let _ =
            if !Global.doubleCheck
            then FunTypeCheck.isFor (__G, __F2)
            else () in
          let __D2 = I.Dec (None, __V2) in
          let __T2 =
            match __F2 with
            | All _ -> S.Lemma S.RL
            | _ -> S.Lemma (S.Splits (!MTPGlobal.maxSplit)) in
          ((skolem
              ((du, (de + 1)), ((I.Decl (__G, __D2)), (I.Decl (__B, __T2))),
                (I.comp (w, I.shift)), __F,
                ((fun s ->
                    fun de' ->
                      let (s', __V', __F') = sc (s, de') in
                      ((((I.Dot
                            ((I.Exp
                                (I.Root
                                   ((I.BVar (du + (de' - de))), (spine du)))),
                              s')), __V', __F'))
                        (* _ : GB, Ds, D2, G'[...] |- s'' : GB, G, D *)
                        (* s'  : GB, Ds, D2, G'[...] |- s' : GB, G *)
                        (* V'  : maps (GB, Ds, D2, G'[...] |- V type) to (GB, Ds, D2 |- {G'[...]} V type) *)
                        (* F'  : maps (GB, Ds, D2, G'[...] |- F for) to (GB, Ds, D2 |- {{G'[...]}} F for) *)))
                (* s   : GB, Ds, D2 |- s : GB *))))
            (* s'  : GB, Ds, G'[...] |- s' : GB, G *)
            (* V'  : maps  (GB, Ds, G'[...] |- V : type)   to   (GB, Ds |- {G'[...]} V : type) *)
            (* F'  : maps  (GB, Ds, G'[...] |- F : for)    to   (GB, Ds |- {{G'[...]}} F : for) *)
            (* V1  : GB, Ds, G'[...] |- V1 = V [s'] : type *)(* V2  : GB, Ds |- {G'[...]} V2 : type *)
            (* F1  : GB, Ds, G'[...] |- F1 : for *)(* F2  : GB, Ds |- {{G'[...]}} F2 : for *)
            (* D2  : GB, Ds |- D2 : type *)(* T2  : GB, Ds |- T2 : tag *))
      (* V   : GB, G |- V type *)
    let rec updateState __90__ __91__ =
      match (__90__, __91__) with
      | (__S, (nil, s)) -> __S
      | ((State (n, (__G, __B), (IH, OH), d, __O, __H, __F) as S),
         ((Lemma (n', Frl'))::__L, s)) ->
          let ((G'', B''), s') =
            skolem
              ((0, 0), (__G, __B), I.id, (F.forSub (Frl', s)),
                (fun s' ->
                   fun _ -> (s', (fun (__V') -> __V'), (fun (__F') -> __F')))) in
          let s'' = I.comp (s, s') in
          updateState
            ((S.State
                (n, (G'', B''), (IH, OH), d, (S.orderSub (__O, s')),
                  ((::) (n', (F.forSub (Frl', s''))) map
                     (fun n' -> fun (__F') -> (n', (F.forSub (__F', s'))))
                     __H), (F.forSub (__F, s')))), (__L, s''))
    let rec selectFormula __92__ __93__ __94__ =
      match (__92__, __93__, __94__) with
      | (n, (__G0, All (Prim (Dec (_, __V) as D), __F), All (_, __O)), __S)
          -> selectFormula (n, ((I.Decl (__G0, __D)), __F, __O), __S)
      | (n, (__G0, And (__F1, __F2), And (__O1, __O2)), __S) ->
          let (n', __S') = selectFormula (n, (__G0, __F1, __O1), __S) in
          selectFormula (n, (__G0, __F2, __O2), __S')
      | (nih, (Gall, Fex, Oex),
         (State (ncurrent, (__G0, __B0), (_, _), _, Ocurrent, __H, __F) as S))
          ->
          let __Ds =
            recursion
              ((nih, Gall, Fex, Oex),
                (ncurrent, (__G0, __B0), nil, Ocurrent, __H, __F)) in
          ((nih + 1), (updateState (__S, (__Ds, I.id))))
    let rec expand (State (n, (__G, __B), (IH, OH), d, __O, __H, __F) as S) =
      let _ = if !Global.doubleCheck then FunTypeCheck.isState __S else () in
      let (_, __S') = selectFormula (1, (I.Null, IH, OH), __S) in __S'
    let rec apply (__S) =
      if !Global.doubleCheck then FunTypeCheck.isState __S else (); __S
    let rec menu _ =
      "Recursion (calculates ALL new assumptions & residual lemmas)"
    let rec handleExceptions f (__P) =
      try f __P with | Error s -> raise (Error s)
    let expand = handleExceptions expand
    let apply = apply
    let menu = menu
  end ;;
