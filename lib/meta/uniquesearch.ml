
module type UNIQUESEARCH  =
  sig
    module StateSyn : STATESYN
    exception Error of string 
    type nonrec acctype = IntSyn.__Exp
    val searchEx :
      int ->
        IntSyn.__Exp list -> (acctype list -> acctype list) -> acctype list
  end;;




module UniqueSearch(UniqueSearch:sig
                                   module Global : GLOBAL
                                   module StateSyn' : STATESYN
                                   module Abstract : ABSTRACT
                                   module MTPGlobal : MTPGLOBAL
                                   module Whnf : WHNF
                                   module Unify : UNIFY
                                   module Assign : ASSIGN
                                   module Index : INDEX
                                   module Compile : COMPILE
                                   module CPrint : CPRINT
                                   module Print : PRINT
                                   module Names : NAMES
                                 end) : UNIQUESEARCH =
  struct
    module StateSyn = StateSyn'
    exception Error of string 
    type nonrec acctype = IntSyn.__Exp
    module I = IntSyn
    module C = CompSyn
    let rec isInstantiated =
      function
      | Root (Const cid, _) -> true__
      | Pi (_, __V) -> isInstantiated __V
      | Root (Def cid, _) -> true__
      | Redex (__V, __S) -> isInstantiated __V
      | Lam (_, __V) -> isInstantiated __V
      | EVar ({ contents = Some (__V) }, _, _, _) -> isInstantiated __V
      | EClo (__V, s) -> isInstantiated __V
      | _ -> false__
    let rec compose' __0__ __1__ =
      match (__0__, __1__) with
      | (IntSyn.Null, __G) -> __G
      | (Decl (__G, __D), __G') -> IntSyn.Decl ((compose' (__G, __G')), __D)
    let rec shift __2__ __3__ =
      match (__2__, __3__) with
      | (IntSyn.Null, s) -> s
      | (Decl (__G, __D), s) -> I.dot1 (shift (__G, s))
    let rec exists (__P) (__K) =
      let rec exists' =
        function
        | I.Null -> false__
        | Decl (__K', __Y) -> (__P __Y) || (exists' __K') in
      exists' __K
    let rec occursInExp r (__Vs) = occursInExpW (r, (Whnf.whnf __Vs))
    let rec occursInExpW __4__ __5__ =
      match (__4__, __5__) with
      | (r, (Uni _, _)) -> false__
      | (r, (Pi ((__D, _), __V), s)) ->
          (occursInDec (r, (__D, s))) || (occursInExp (r, (__V, (I.dot1 s))))
      | (r, (Root (_, __S), s)) -> occursInSpine (r, (__S, s))
      | (r, (Lam (__D, __V), s)) ->
          (occursInDec (r, (__D, s))) || (occursInExp (r, (__V, (I.dot1 s))))
      | (r, (EVar (r', _, __V', _), s)) ->
          (r = r') || (occursInExp (r, (__V', s)))
      | (r, (FgnExp csfe, s)) ->
          I.FgnExpStd.fold csfe
            (fun (__U) -> fun (__B) -> __B || (occursInExp (r, (__U, s))))
            false__
    let rec occursInSpine __6__ __7__ =
      match (__6__, __7__) with
      | (_, (I.Nil, _)) -> false__
      | (r, (SClo (__S, s'), s)) ->
          occursInSpine (r, (__S, (I.comp (s', s))))
      | (r, (App (__U, __S), s)) ->
          (occursInExp (r, (__U, s))) || (occursInSpine (r, (__S, s)))
    let rec occursInDec r (Dec (_, __V), s) = occursInExp (r, (__V, s))
    let rec nonIndex __8__ __9__ =
      match (__8__, __9__) with
      | (_, nil) -> true__
      | (r, (EVar (_, _, __V, _))::GE) ->
          (not (occursInExp (r, (__V, I.id)))) && (nonIndex (r, GE))
    let rec selectEVar =
      function
      | nil -> nil
      | (EVar (r, _, _, { contents = nil }) as X)::GE ->
          let __Xs = selectEVar GE in
          if nonIndex (r, __Xs) then __Xs @ [__X] else __Xs
      | (EVar (r, _, _, cnstrs) as X)::GE ->
          let __Xs = selectEVar GE in
          if nonIndex (r, __Xs) then __X :: __Xs else __Xs(* Constraint case *)
    let rec pruneCtx __10__ __11__ =
      match (__10__, __11__) with
      | (__G, 0) -> __G
      | (Decl (__G, _), n) -> pruneCtx (__G, (n - 1))
    let rec cidFromHead =
      function | Const a -> a | Def a -> a | Skonst a -> a
    let rec eqHead __12__ __13__ =
      match (__12__, __13__) with
      | (Const a, Const a') -> a = a'
      | (Def a, Def a') -> a = a'
      | _ -> false__
    let rec solve __14__ __15__ __16__ __17__ __18__ __19__ =
      match (__14__, __15__, __16__, __17__, __18__, __19__) with
      | (max, depth, (Atom p, s), dp, sc, acc) ->
          matchAtom (max, depth, (p, s), dp, sc, acc)
      | (max, depth, (Impl (r, __A, __H, g), s), DProg (__G, dPool), sc, acc)
          ->
          let __D' = I.Dec (NONE, (I.EClo (__A, s))) in
          solve
            (max, (depth + 1), (g, (I.dot1 s)),
              (C.DProg
                 ((I.Decl (__G, __D')),
                   (I.Decl (dPool, (C.Dec (r, s, __H)))))),
              (fun (__M) -> fun acc' -> sc ((I.Lam (__D', __M)), acc')), acc)
      | (max, depth, (All (__D, g), s), DProg (__G, dPool), sc, acc) ->
          let __D' = I.decSub (__D, s) in
          solve
            (max, (depth + 1), (g, (I.dot1 s)),
              (C.DProg ((I.Decl (__G, __D')), (I.Decl (dPool, C.Parameter)))),
              (fun (__M) -> fun acc' -> sc ((I.Lam (__D', __M)), acc')), acc)
    let rec rSolve __20__ __21__ __22__ __23__ __24__ __25__ __26__ =
      match (__20__, __21__, __22__, __23__, __24__, __25__, __26__) with
      | (max, depth, ps', (Eq (__Q), s), DProg (__G, dPool), sc, acc) ->
          if Unify.unifiable (__G, ps', (__Q, s))
          then sc (I.Nil, acc)
          else acc
      | (max, depth, ps', (Assign (__Q, eqns), s),
         (DProg (__G, dPool) as dp), sc, acc) ->
          (match Assign.assignable (__G, ps', (__Q, s)) with
           | Some cnstr ->
               aSolve
                 ((eqns, s), dp, cnstr, (fun () -> sc (I.Nil, acc)), acc)
           | NONE -> acc)
      | (max, depth, ps', (And (r, __A, g), s), (DProg (__G, dPool) as dp),
         sc, acc) ->
          let __X = I.newEVar (__G, (I.EClo (__A, s))) in
          ((rSolve
              (max, depth, ps', (r, (I.Dot ((I.Exp __X), s))), dp,
                (fun (__S) ->
                   fun acc' ->
                     solve
                       (max, depth, (g, s), dp,
                         (fun (__M) ->
                            fun acc'' -> sc ((I.App (__M, __S)), acc'')),
                         acc')), acc))
            (* is this EVar redundant? -fp *))
      | (max, depth, ps', (In (r, __A, g), s), (DProg (__G, dPool) as dp),
         sc, acc) ->
          let __G0 = pruneCtx (__G, depth) in
          let dPool0 = pruneCtx (dPool, depth) in
          let w = I.Shift depth in
          let iw = Whnf.invert w in
          let s' = I.comp (s, iw) in
          let __X = I.newEVar (__G0, (I.EClo (__A, s'))) in
          let __X' = I.EClo (__X, w) in
          ((rSolve
              (max, depth, ps', (r, (I.Dot ((I.Exp __X'), s))), dp,
                (fun (__S) ->
                   fun acc' ->
                     if isInstantiated __X
                     then sc ((I.App (__X', __S)), acc')
                     else
                       solve
                         (max, 0, (g, s'), (C.DProg (__G0, dPool0)),
                           (fun (__M) ->
                              fun acc'' ->
                                try
                                  Unify.unify
                                    (__G0, (__X, I.id), (__M, I.id));
                                  sc
                                    ((I.App ((I.EClo (__M, w)), __S)), acc'')
                                with | Unify _ -> acc''), acc')), acc))
            (* G |- g goal *)(* G |- A : type *)
            (* G, A |- r resgoal *)(* G0, Gl  |- s : G *)
            (* G0, Gl  |- w : G0 *)(* G0 |- iw : G0, Gl *)
            (* G0 |- w : G *)(* G0 |- X : A[s'] *)
            (* G0, Gl |- X' : A[s'][w] = A[s] *))
      | (max, depth, ps', (Exists (Dec (_, __A), r), s),
         (DProg (__G, dPool) as dp), sc, acc) ->
          let __X = I.newEVar (__G, (I.EClo (__A, s))) in
          rSolve
            (max, depth, ps', (r, (I.Dot ((I.Exp __X), s))), dp,
              (fun (__S) -> fun acc' -> sc ((I.App (__X, __S)), acc')), acc)
      | (max, depth, ps', (Axists (ADec (Some (__X), d), r), s),
         (DProg (__G, dPool) as dp), sc, acc) ->
          let __X' = I.newAVar () in
          ((rSolve
              (max, depth, ps',
                (r, (I.Dot ((I.Exp (I.EClo (__X', (I.Shift (~ d))))), s))),
                dp, sc, acc))
            (* we don't increase the proof term here! *))
      (* replaced below by above.  -fp Mon Aug 17 10:41:09 1998
        ((Unify.unify (ps', (Q, s)); sc (I.Nil, acck)) handle Unify.Unify _ => acc) *)
    let rec aSolve __27__ __28__ __29__ __30__ __31__ =
      match (__27__, __28__, __29__, __30__, __31__) with
      | ((C.Trivial, s), dp, cnstr, sc, acc) ->
          if Assign.solveCnstr cnstr then sc () else acc
      | ((UnifyEq (__G', e1, __N, eqns), s), (DProg (__G, dPool) as dp),
         cnstr, sc, acc) ->
          let G'' = compose' (__G', __G) in
          let s' = shift (__G', s) in
          if Assign.unifiable (G'', (__N, s'), (e1, s'))
          then aSolve ((eqns, s), dp, cnstr, sc, acc)
          else acc
    let rec matchAtom __37__ __38__ __39__ __40__ __41__ __42__ =
      match (__37__, __38__, __39__, __40__, __41__, __42__) with
      | (0, _, _, _, _, acc) -> acc
      | (max, depth, ((Root (Ha, _), _) as ps'), (DProg (__G, dPool) as dp),
         sc, acc) ->
          let rec matchSig' __32__ __33__ =
            match (__32__, __33__) with
            | (nil, acc') -> acc'
            | ((Hc)::sgn', acc') ->
                let SClause r = C.sProgLookup (cidFromHead Hc) in
                let acc''' =
                  CSManager.trail
                    (fun () ->
                       rSolve
                         ((max - 1), depth, ps', (r, I.id), dp,
                           (fun (__S) ->
                              fun acc'' -> sc ((I.Root (Hc, __S)), acc'')),
                           acc')) in
                matchSig' (sgn', acc''') in
          let rec matchDProg __34__ __35__ __36__ =
            match (__34__, __35__, __36__) with
            | (I.Null, _, acc') ->
                matchSig' ((Index.lookup (cidFromHead Ha)), acc')
            | (Decl (dPool', Dec (r, s, Ha')), n, acc') ->
                if eqHead (Ha, Ha')
                then
                  let acc''' =
                    CSManager.trail
                      (fun () ->
                         rSolve
                           ((max - 1), depth, ps',
                             (r, (I.comp (s, (I.Shift n)))), dp,
                             (fun (__S) ->
                                fun acc'' ->
                                  sc ((I.Root ((I.BVar n), __S)), acc'')),
                             acc')) in
                  matchDProg (dPool', (n + 1), acc''')
                else matchDProg (dPool', (n + 1), acc')
            | (Decl (dPool', C.Parameter), n, acc') ->
                matchDProg (dPool', (n + 1), acc') in
          matchDProg (dPool, 1, acc)
    let rec searchEx' __43__ __44__ __45__ __46__ =
      match (__43__, __44__, __45__, __46__) with
      | (max, nil, sc, acc) -> sc acc
      | (max, (EVar (r, __G, __V, _) as X)::GE, sc, acc) ->
          solve
            (max, 0, ((Compile.compileGoal (__G, __V)), I.id),
              (Compile.compileCtx false__ __G),
              (fun (__U') ->
                 fun acc' ->
                   try
                     Unify.unify (__G, (__X, I.id), (__U', I.id));
                     searchEx' max (GE, sc, acc')
                   with | Unify _ -> acc'), acc)(* Possible optimization:
           Check if there are still variables left over
        *)
    let rec searchEx it depth (GE) sc acc =
      if (!Global.chatter) > 5 then print "[Search: " else ();
      searchEx' depth
        ((selectEVar GE),
          (fun acc' ->
             if (!Global.chatter) > 5 then print "OK]\n" else ();
             (let GE' =
                foldr
                  (fun (EVar (_, __G, _, _) as X) ->
                     fun (__L) ->
                       Abstract.collectEVars (__G, (__X, I.id), __L)) nil GE in
              let gE' = List.length GE' in
              ((if gE' > 0
                then
                  (if it > 0
                   then searchEx ((it - 1), depth) (GE', sc, acc')
                   else raise (Error "not found"))
                else sc acc')
                (* warning: iterative deepening depth is not propably updated.
                                             possible that it runs into an endless loop ? *)))),
          acc)
    let rec search maxFill (GE) sc = searchEx (1, maxFill) (GE, sc, nil)
    let searchEx = search
  end ;;
