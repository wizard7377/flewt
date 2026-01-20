
module type OLDSEARCH  =
  sig
    module MetaSyn : METASYN
    exception Error of string 
    val searchEx :
      IntSyn.dctx ->
        IntSyn.__Exp list ->
          (IntSyn.__Exp * IntSyn.__Sub) ->
            (unit -> unit) -> MetaSyn.__State list
    val searchAll :
      IntSyn.dctx ->
        IntSyn.__Exp list ->
          (IntSyn.__Exp * IntSyn.__Sub) ->
            (MetaSyn.__State list -> MetaSyn.__State list) ->
              MetaSyn.__State list
  end;;




module OLDSearch(OLDSearch:sig
                             module MetaGlobal : METAGLOBAL
                             module MetaSyn' : METASYN
                             module Whnf : WHNF
                             module Unify : UNIFY
                             module Index : INDEX
                             module Compile : COMPILE
                             module CPrint : CPRINT
                             module Print : PRINT
                             module Names : NAMES
                           end) : OLDSEARCH =
  struct
    module MetaSyn = MetaSyn'
    exception Error of string 
    module I = IntSyn
    module M = MetaSyn
    module C = CompSyn
    let rec cidFromHead =
      function | Const a -> a | Def a -> a | Skonst a -> a
    let rec eqHead __0__ __1__ =
      match (__0__, __1__) with
      | (Const a, Const a') -> a = a'
      | (Def a, Def a') -> a = a'
      | _ -> false
    let rec solve __2__ __3__ __4__ __5__ =
      match (__2__, __3__, __4__, __5__) with
      | ((Atom p, s), dp, sc, acck) -> matchAtom ((p, s), dp, sc, acck)
      | ((Impl (r, __A, __H, g), s), DProg (__G, dPool), sc, acck) ->
          let __D' = I.Dec (None, (I.EClo (__A, s))) in
          solve
            ((g, (I.dot1 s)),
              (C.DProg
                 ((I.Decl (__G, __D')),
                   (I.Decl (dPool, (C.Dec (r, s, __H)))))),
              (fun (__M) -> fun acck' -> sc ((I.Lam (__D', __M)), acck')),
              acck)
      | ((All (__D, g), s), DProg (__G, dPool), sc, acck) ->
          let __D' = I.decSub (__D, s) in
          solve
            ((g, (I.dot1 s)),
              (C.DProg ((I.Decl (__G, __D')), (I.Decl (dPool, C.Parameter)))),
              (fun (__M) -> fun acck' -> sc ((I.Lam (__D', __M)), acck')),
              acck)
    let rec rSolve __6__ __7__ __8__ __9__ __10__ =
      match (__6__, __7__, __8__, __9__, __10__) with
      | (ps', (Eq (__Q), s), DProg (__G, dPool), sc, ((acc, k) as acck)) ->
          if Unify.unifiable (__G, ps', (__Q, s))
          then sc (I.Nil, acck)
          else acc
      | (ps', (And (r, __A, g), s), (DProg (__G, dPool) as dp), sc, acck) ->
          let __X = I.newEVar (__G, (I.EClo (__A, s))) in
          rSolve
            (ps', (r, (I.Dot ((I.Exp __X), s))), dp,
              (fun (__S) ->
                 fun acck' ->
                   solve
                     ((g, s), dp,
                       (fun (__M) ->
                          fun acck'' ->
                            try
                              ((Unify.unify (__G, (__X, I.id), (__M, I.id));
                                sc ((I.App (__M, __S)), acck''))
                              (* why doesn't it always succeed?
                                                                --cs *))
                            with | Unify _ -> []), acck')), acck)
      | (ps', (Exists (Dec (_, __A), r), s), (DProg (__G, dPool) as dp), sc,
         acck) ->
          let __X = I.newEVar (__G, (I.EClo (__A, s))) in
          rSolve
            (ps', (r, (I.Dot ((I.Exp __X), s))), dp,
              (fun (__S) -> fun acck' -> sc ((I.App (__X, __S)), acck')),
              acck)(*
    | rSolve (ps', (C.Assign (Q, ag), s), dp, sc, acck as (acc, k)) =
        ((Assign.assign (ps', (Q, s));
          aSolve ((ag, s), dp, (fn () => sc (I.Nil, acck)) , acc))
          handle Unify.Unify _ => acc
               | Assign.Assign _ => acc)
    *)
      (* replaced below by above.  -fp Mon Aug 17 10:41:09 1998
        ((Unify.unify (ps', (Q, s)); sc (I.Nil, acck)) handle Unify.Unify _ => acc) *)
    let rec aSolve (C.Trivial, s) dp sc acc = sc ()
    let rec matchAtom ((Root (Ha, _), _) as ps') (DProg (__G, dPool) as dp)
      sc (acc, k) =
      let rec matchSig acc' =
        let rec matchSig' __11__ __12__ =
          match (__11__, __12__) with
          | (nil, acc'') -> acc''
          | ((Hc)::sgn', acc'') ->
              let SClause r = C.sProgLookup (cidFromHead Hc) in
              let acc''' =
                CSManager.trail
                  (fun () ->
                     rSolve
                       (ps', (r, I.id), dp,
                         (fun (__S) ->
                            fun acck' -> sc ((I.Root (Hc, __S)), acck')),
                         (acc'', (k - 1)))) in
              matchSig' (sgn', acc''') in
        matchSig' ((Index.lookup (cidFromHead Ha)), acc') in
      let rec matchDProg __13__ __14__ __15__ =
        match (__13__, __14__, __15__) with
        | (I.Null, _, acc') -> matchSig acc'
        | (Decl (dPool', Dec (r, s, Ha')), n, acc') ->
            if eqHead (Ha, Ha')
            then
              let acc'' =
                CSManager.trail
                  (fun () ->
                     rSolve
                       (ps', (r, (I.comp (s, (I.Shift n)))), dp,
                         (fun (__S) ->
                            fun acck' ->
                              sc ((I.Root ((I.BVar n), __S)), acck')),
                         (acc', (k - 1)))) in
              matchDProg (dPool', (n + 1), acc'')
            else matchDProg (dPool', (n + 1), acc')
        | (Decl (dPool', C.Parameter), n, acc') ->
            matchDProg (dPool', (n + 1), acc') in
      if k < 0 then acc else matchDProg (dPool, 1, acc)
    let rec occursInExp r (__Vs) = occursInExpW (r, (Whnf.whnf __Vs))
    let rec occursInExpW __16__ __17__ =
      match (__16__, __17__) with
      | (r, (Uni _, _)) -> false
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
            false
    let rec occursInSpine __18__ __19__ =
      match (__18__, __19__) with
      | (_, (I.Nil, _)) -> false
      | (r, (SClo (__S, s'), s)) ->
          occursInSpine (r, (__S, (I.comp (s', s))))
      | (r, (App (__U, __S), s)) ->
          (occursInExp (r, (__U, s))) || (occursInSpine (r, (__S, s)))
    let rec occursInDec r (Dec (_, __V), s) = occursInExp (r, (__V, s))
    let rec nonIndex __20__ __21__ =
      match (__20__, __21__) with
      | (_, nil) -> true
      | (r, (EVar (_, _, __V, _))::GE) ->
          (not (occursInExp (r, (__V, I.id)))) && (nonIndex (r, GE))
    let rec selectEVar __22__ __23__ __24__ =
      match (__22__, __23__, __24__) with
      | (nil, _, acc) -> acc
      | ((EVar (r, _, _, _) as X)::GE, __Vs, acc) ->
          if (occursInExp (r, __Vs)) && (nonIndex (r, acc))
          then selectEVar (GE, __Vs, (__X :: acc))
          else selectEVar (GE, __Vs, acc)
    let rec searchEx' __25__ __26__ __27__ =
      match (__25__, __26__, __27__) with
      | (max, nil, sc) -> [sc ()]
      | (max, (EVar (r, __G, __V, _))::GE, sc) ->
          solve
            (((Compile.compileGoal (__G, __V)), I.id),
              (Compile.compileCtx false __G),
              (fun (__U') ->
                 fun (acc', _) ->
                   Unify.instantiateEVar (r, __U', nil);
                   searchEx' max (GE, sc)), (nil, max))(* Possible optimization:
           Check if there are still variables left over
        *)
    let rec deepen f (__P) =
      let rec deepen' level acc =
        if level > (!MetaGlobal.maxFill)
        then acc
        else
          (if (!Global.chatter) > 5 then print "#" else ();
           deepen' ((level + 1), (f level __P))) in
      deepen' (1, nil)
    let rec searchEx (__G) (GE) (__Vs) sc =
      if (!Global.chatter) > 5 then print "[Search: " else ();
      deepen searchEx'
        ((selectEVar (GE, __Vs, nil)),
          (fun (Params) ->
             if (!Global.chatter) > 5 then print "OK]\n" else (); sc Params));
      if (!Global.chatter) > 5 then print "FAIL]\n" else ();
      raise (Error "No object found")
    let rec searchAll' __28__ __29__ __30__ =
      match (__28__, __29__, __30__) with
      | (nil, acc, sc) -> sc acc
      | ((EVar (r, __G, __V, _))::GE, acc, sc) ->
          solve
            (((Compile.compileGoal (__G, __V)), I.id),
              (Compile.compileCtx false __G),
              (fun (__U') ->
                 fun (acc', _) ->
                   Unify.instantiateEVar (r, __U', nil);
                   searchAll' (GE, acc', sc)), (acc, (!MetaGlobal.maxFill)))
    let rec searchAll (__G) (GE) (__Vs) sc =
      searchAll' ((selectEVar (GE, __Vs, nil)), nil, sc)
    let searchEx = searchEx
    let searchAll = searchAll
  end ;;
