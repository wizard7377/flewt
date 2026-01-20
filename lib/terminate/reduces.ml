
module type REDUCES  =
  sig
    exception Error of string 
    val reset : unit -> unit
    val checkFamReduction : IntSyn.cid -> unit
    val checkFam : IntSyn.cid -> unit
  end;;




module Reduces(Reduces:sig
                         module Global : GLOBAL
                         module Whnf : WHNF
                         module Names : NAMES
                         module Index : INDEX
                         module Subordinate : SUBORDINATE
                         module Formatter : FORMATTER
                         module Print : PRINT
                         module Order : ORDER
                         module Checking : CHECKING
                         module Origins : ORIGINS
                       end) : REDUCES =
  struct
    exception Error of string 
    module I = IntSyn
    module P = Paths
    module N = Names
    module F = Formatter
    module R = Order
    module C = Checking
    exception Error' of (P.occ * string) 
    let rec error c occ msg =
      match Origins.originLookup c with
      | (fileName, NONE) -> raise (Error ((fileName ^ ":") ^ msg))
      | (fileName, Some occDec) ->
          raise
            (Error
               (P.wrapLoc'
                  ((P.Loc (fileName, (P.occToRegionDec occDec occ))),
                    (Origins.linesInfoLookup fileName), msg)))
    let rec concat __0__ __1__ =
      match (__0__, __1__) with
      | (__G', I.Null) -> __G'
      | (__G', Decl (__G, __D)) -> I.Decl ((concat (__G', __G)), __D)
    let rec fmtOrder (__G) (__O) =
      let rec fmtOrder' =
        function
        | Arg (((__U, s) as Us), ((__V, s') as Vs)) ->
            F.Hbox
              [F.String "(";
              Print.formatExp (__G, (I.EClo __Us));
              F.String ")"]
        | Lex (__L) ->
            F.Hbox
              [F.String "{"; F.HOVbox0 1 0 1 (fmtOrders __L); F.String "}"]
        | Simul (__L) ->
            F.Hbox
              [F.String "["; F.HOVbox0 1 0 1 (fmtOrders __L); F.String "]"]
      and fmtOrders =
        function
        | [] -> []
        | (__O)::[] -> (fmtOrder' __O) :: []
        | (__O)::__L -> (::) ((fmtOrder' __O) :: F.Break) fmtOrders __L in
      fmtOrder' __O
    let rec fmtComparison (__G) (__O) comp (__O') =
      F.HOVbox0 1 0 1
        [fmtOrder (__G, __O);
        F.Break;
        F.String comp;
        F.Break;
        fmtOrder (__G, __O')]
    let rec fmtPredicate __2__ __3__ =
      match (__2__, __3__) with
      | (__G, Less (__O, __O')) -> fmtComparison (__G, __O, "<", __O')
      | (__G, Leq (__O, __O')) -> fmtComparison (__G, __O, "<=", __O')
      | (__G, Eq (__O, __O')) -> fmtComparison (__G, __O, "=", __O')
      | (__G, Pi (__D, __P)) ->
          F.Hbox [F.String "Pi "; fmtPredicate ((I.Decl (__G, __D)), __P)]
    let rec rlistToString' __4__ __5__ =
      match (__4__, __5__) with
      | (__G, nil) -> ""
      | (__G, (__P)::[]) -> F.makestring_fmt (fmtPredicate (__G, __P))
      | (__G, (__P)::Rl) ->
          (^) ((F.makestring_fmt (fmtPredicate (__G, __P))) ^ " ,")
            rlistToString' (__G, Rl)
    let rec rlistToString (__G) (Rl) =
      rlistToString' ((Names.ctxName __G), Rl)
    let rec orderToString (__G) (__P) =
      F.makestring_fmt (fmtPredicate ((Names.ctxName __G), __P))
    let rec select c (__S, s) =
      let SO = R.selLookup c in
      let Vid = ((I.constType c), I.id) in
      let rec select'' n (__Ss', Vs'') =
        select''W (n, (__Ss', (Whnf.whnf Vs'')))
      and select''W __6__ __7__ =
        match (__6__, __7__) with
        | (1, ((App (__U', __S'), s'), (Pi ((Dec (_, V''), _), _), s''))) ->
            ((__U', s'), (V'', s''))
        | (n, ((SClo (__S', s1'), s2'), Vs'')) ->
            select''W (n, ((__S', (I.comp (s1', s2'))), Vs''))
        | (n, ((App (__U', __S'), s'), (Pi ((Dec (_, V1''), _), V2''), s'')))
            ->
            select''
              ((n - 1),
                ((__S', s'),
                  (V2'', (I.Dot ((I.Exp (I.EClo (__U', s'))), s''))))) in
      let rec select' =
        function
        | Arg n -> R.Arg (select'' (n, ((__S, s), Vid)))
        | Lex (__L) -> R.Lex (map select' __L)
        | Simul (__L) -> R.Simul (map select' __L) in
      select' (R.selLookup c)
    let rec selectOcc c (__S, s) occ =
      try select (c, (__S, s))
      with
      | Error msg ->
          raise
            (Error'
               (occ,
                 ((^) "Termination violation: no order assigned for "
                    N.qidToString (N.constQid c))))
    let rec selectROrder c (__S, s) =
      let Vid = ((I.constType c), I.id) in
      let rec select'' n (__Ss', Vs'') =
        select''W (n, (__Ss', (Whnf.whnf Vs'')))
      and select''W __8__ __9__ =
        match (__8__, __9__) with
        | (1, ((App (__U', __S'), s'), (Pi ((Dec (_, V''), _), _), s''))) ->
            ((__U', s'), (V'', s''))
        | (n, ((SClo (__S', s1'), s2'), Vs'')) ->
            select''W (n, ((__S', (I.comp (s1', s2'))), Vs''))
        | (n, ((App (__U', __S'), s'), (Pi ((Dec (_, V1''), _), V2''), s'')))
            ->
            select''
              ((n - 1),
                ((__S', s'),
                  (V2'', (I.Dot ((I.Exp (I.EClo (__U', s'))), s''))))) in
      let rec select' =
        function
        | Arg n -> R.Arg (select'' (n, ((__S, s), Vid)))
        | Lex (__L) -> R.Lex (map select' __L)
        | Simul (__L) -> R.Simul (map select' __L) in
      let rec selectP =
        function
        | Less (__O1, __O2) -> C.Less ((select' __O1), (select' __O2))
        | Leq (__O1, __O2) -> C.Leq ((select' __O1), (select' __O2))
        | Eq (__O1, __O2) -> C.Eq ((select' __O1), (select' __O2)) in
      try Some (selectP (R.selLookupROrder c)) with | Error s -> NONE
    let rec abstractRO (__G) (__D) (__O) = C.Pi (__D, __O)
    let rec getROrder (__G) (__Q) (__Vs) occ =
      getROrderW (__G, __Q, (Whnf.whnf __Vs), occ)
    let rec getROrderW __10__ __11__ __12__ __13__ =
      match (__10__, __11__, __12__, __13__) with
      | (__G, __Q, ((Root (Const a, __S), s) as Vs), occ) ->
          let __O = selectROrder (a, (__S, s)) in
          let _ =
            match __O with
            | NONE -> ()
            | Some (__O) ->
                if (!Global.chatter) > 5
                then
                  print
                    (((^) (((^) "Reduction predicate for " N.qidToString
                              (N.constQid a))
                             ^ " added : ")
                        orderToString (__G, __O))
                       ^ "\n")
                else () in
          __O
      | (__G, __Q, (Pi ((__D, I.Maybe), __V), s), occ) ->
          let __O =
            getROrder
              ((I.Decl (__G, (N.decLUName (__G, (I.decSub (__D, s)))))),
                (I.Decl (__Q, C.All)), (__V, (I.dot1 s)), (P.body occ)) in
          (match __O with
           | NONE -> NONE
           | Some (__O') ->
               Some (abstractRO (__G, (I.decSub (__D, s)), __O')))
      | (__G, __Q, (Pi (((Dec (_, __V1) as D), I.No), __V2), s), occ) ->
          let __O =
            getROrder
              (__G, __Q, (__V2, (I.comp (I.invShift, s))), (P.body occ)) in
          (match __O with | NONE -> NONE | Some (__O') -> Some __O')
      | (__G, __Q, ((Root (Def a, __S), s) as Vs), occ) ->
          raise
            (Error'
               (occ,
                 (((^) ("Reduction checking for defined type families not yet available:\n"
                          ^ "Illegal use of ")
                     N.qidToString (N.constQid a))
                    ^ ".")))
    let rec checkGoal (__G0) (__Q0) (Rl) (__Vs) (__Vs') occ =
      checkGoalW (__G0, __Q0, Rl, (Whnf.whnf __Vs), __Vs', occ)
    let rec checkGoalW __16__ __17__ __18__ __19__ __20__ __21__ =
      match (__16__, __17__, __18__, __19__, __20__, __21__) with
      | (__G0, __Q0, Rl, (Pi (((Dec (_, __V1) as D), I.No), __V2), s), __Vs',
         occ) ->
          (checkClause
             ((__G0, __Q0, Rl), I.Null, I.Null, (__V1, s), (P.label occ));
           checkGoal
             (__G0, __Q0, Rl, (__V2, (I.comp (I.invShift, s))), __Vs',
               (P.body occ)))
      | (__G0, __Q0, Rl, (Pi ((__D, I.Maybe), __V), s), (__V', s'), occ) ->
          checkGoal
            ((I.Decl (__G0, (N.decLUName (__G0, (I.decSub (__D, s)))))),
              (I.Decl (__Q0, C.All)),
              (C.shiftRCtx Rl (fun s -> I.comp (s, I.shift))),
              (__V, (I.dot1 s)), (__V', (I.comp (s', I.shift))),
              (P.body occ))
      | (__G0, __Q0, Rl, ((Root (Const a, __S), s) as Vs),
         ((Root (Const a', __S'), s') as Vs'), occ) ->
          let rec lookup __14__ __15__ =
            match (__14__, __15__) with
            | (R.Empty, f) -> R.Empty
            | ((LE (a, a's') as a's), f) ->
                if f a then a's else lookup (a's', f)
            | ((LT (a, a's') as a's), f) ->
                if f a then a's else lookup (a's', f) in
          let __P = selectOcc (a, (__S, s), occ) in
          let __P' = select (a', (__S', s')) in
          let a's = Order.mutLookup a in
          (((match lookup (a's, (fun x' -> x' = a')) with
             | R.Empty -> ()
             | LE _ ->
                 (if (!Global.chatter) > 4
                  then
                    (print "Verifying termination order:\n";
                     print (rlistToString (__G0, Rl));
                     print
                       (((^) " ---> " orderToString
                           (__G0, (C.Leq (__P, __P'))))
                          ^ "\n"))
                  else ();
                  if C.deduce (__G0, __Q0, Rl, (C.Leq (__P, __P')))
                  then ()
                  else
                    raise
                      (Error'
                         (occ,
                           ((^) (((^) "Termination violation:\n"
                                    rlistToString (__G0, Rl))
                                   ^ " ---> ")
                              orderToString (__G0, (C.Leq (__P, __P')))))))
             | LT _ ->
                 (if (!Global.chatter) > 4
                  then
                    (print "Verifying termination order:\n";
                     print ((rlistToString (__G0, Rl)) ^ " ---> ");
                     print
                       ((orderToString (__G0, (C.Less (__P, __P')))) ^ "\n"))
                  else ();
                  if C.deduce (__G0, __Q0, Rl, (C.Less (__P, __P')))
                  then ()
                  else
                    raise
                      (Error'
                         (occ,
                           ((^) (((^) "Termination violation:\n"
                                    rlistToString (__G0, Rl))
                                   ^ " ---> ")
                              orderToString (__G0, (C.Less (__P, __P')))))))))
            (* only if a terminates? *)(* always succeeds? -fp *)
            (* always succeeds? -fp *))
      | (__G0, __Q0, Rl, ((Root (Def a, __S), s) as Vs), __Vs', occ) ->
          raise
            (Error'
               (occ,
                 (((^) ("Reduction checking for defined type families not yet available:\n"
                          ^ "Illegal use of ")
                     N.qidToString (N.constQid a))
                    ^ ".")))
      | (__G0, __Q0, Rl, __Vs, ((Root (Def a', __S'), s') as Vs'), occ) ->
          raise
            (Error'
               (occ,
                 (((^) ("Reduction checking for defined type families not yet available:\n"
                          ^ "Illegal use of ")
                     N.qidToString (N.constQid a'))
                    ^ ".")))
    let rec checkSubgoals __22__ __23__ __24__ __25__ __26__ __27__ =
      match (__22__, __23__, __24__, __25__, __26__, __27__) with
      | (__G0, __Q0, Rl, __Vs, n,
         (Decl (__G, (Dec (_, __V') as D)), Decl (__Q, And occ))) ->
          let _ =
            checkGoal (__G0, __Q0, Rl, (__V', (I.Shift (n + 1))), __Vs, occ) in
          let RO = getROrder (__G0, __Q0, (__V', (I.Shift (n + 1))), occ) in
          let Rl' = match RO with | NONE -> Rl | Some (__O) -> __O :: Rl in
          checkSubgoals (__G0, __Q0, Rl', __Vs, (n + 1), (__G, __Q))
      | (__G0, __Q0, Rl, __Vs, n, (Decl (__G, __D), Decl (__Q, C.Exist))) ->
          checkSubgoals (__G0, __Q0, Rl, __Vs, (n + 1), (__G, __Q))
      | (__G0, __Q0, Rl, __Vs, n, (Decl (__G, __D), Decl (__Q, C.All))) ->
          checkSubgoals (__G0, __Q0, Rl, __Vs, (n + 1), (__G, __Q))
      | (__G0, __Q0, Rl, __Vs, n, (I.Null, I.Null)) -> ()
    let rec checkClause (GQR) (__G) (__Q) (__Vs) occ =
      checkClauseW (GQR, __G, __Q, (Whnf.whnf __Vs), occ)
    let rec checkClauseW __28__ __29__ __30__ __31__ __32__ =
      match (__28__, __29__, __30__, __31__, __32__) with
      | (GQR, __G, __Q, (Pi ((__D, I.Maybe), __V), s), occ) ->
          checkClause
            (GQR, (I.Decl (__G, (N.decEName (__G, (I.decSub (__D, s)))))),
              (I.Decl (__Q, C.Exist)), (__V, (I.dot1 s)), (P.body occ))
      | (GQR, __G, __Q, (Pi (((Dec (_, __V1) as D), I.No), __V2), s), occ) ->
          checkClause
            (GQR, (I.Decl (__G, (I.decSub (__D, s)))),
              (I.Decl (__Q, (C.And (P.label occ)))), (__V2, (I.dot1 s)),
              (P.body occ))
      | (((__G0, __Q0, Rl) as GQR), __G, __Q,
         ((Root (Const a, __S), s) as Vs), occ) ->
          let n = I.ctxLength __G in
          let Rl' = C.shiftRCtx Rl (fun s -> I.comp (s, (I.Shift n))) in
          checkSubgoals
            ((concat (__G0, __G)), (concat (__Q0, __Q)), Rl', __Vs, 0,
              (__G, __Q))
      | (GQR, __G, __Q, (Root (Def a, __S), s), occ) ->
          raise
            (Error'
               (occ,
                 (((^) ("Termination checking for defined type families not yet available:\n"
                          ^ "Illegal use of ")
                     N.qidToString (N.constQid a))
                    ^ ".")))
    let rec checkClause' (__Vs) occ =
      checkClause ((I.Null, I.Null, nil), I.Null, I.Null, __Vs, occ)
    let rec checkRGoal (__G) (__Q) (Rl) (__Vs) occ =
      checkRGoalW (__G, __Q, Rl, (Whnf.whnf __Vs), occ)
    let rec checkRGoalW __33__ __34__ __35__ __36__ __37__ =
      match (__33__, __34__, __35__, __36__, __37__) with
      | (__G, __Q, Rl, ((Root (Const a, __S), s) as Vs), occ) -> ()
      | (__G, __Q, Rl, (Pi ((__D, I.Maybe), __V), s), occ) ->
          checkRGoal
            ((I.Decl (__G, (N.decLUName (__G, (I.decSub (__D, s)))))),
              (I.Decl (__Q, C.All)),
              (C.shiftRCtx Rl (fun s -> I.comp (s, I.shift))),
              (__V, (I.dot1 s)), (P.body occ))
      | (__G, __Q, Rl, (Pi (((Dec (_, __V1) as D), I.No), __V2), s), occ) ->
          (checkRClause (__G, __Q, Rl, (__V1, s), (P.label occ));
           checkRGoal
             (__G, __Q, Rl, (__V2, (I.comp (I.invShift, s))), (P.body occ)))
      | (__G, __Q, Rl, (Root (Def a, __S), s), occ) ->
          raise
            (Error'
               (occ,
                 (((^) ("Reduction checking for defined type families not yet available:\n"
                          ^ "Illegal use of ")
                     N.qidToString (N.constQid a))
                    ^ ".")))(* trivial *)
    let rec checkRImp (__G) (__Q) (Rl) (__Vs) (__Vs') occ =
      checkRImpW (__G, __Q, Rl, (Whnf.whnf __Vs), __Vs', occ)
    let rec checkRImpW __38__ __39__ __40__ __41__ __42__ __43__ =
      match (__38__, __39__, __40__, __41__, __42__, __43__) with
      | (__G, __Q, Rl, (Pi ((__D', I.Maybe), __V'), s'), (__V, s), occ) ->
          checkRImp
            ((I.Decl (__G, (N.decEName (__G, (I.decSub (__D', s')))))),
              (I.Decl (__Q, C.Exist)),
              (C.shiftRCtx Rl (fun s -> I.comp (s, I.shift))),
              (__V', (I.dot1 s')), (__V, (I.comp (s, I.shift))), occ)
      | (__G, __Q, Rl, (Pi (((Dec (_, __V1) as D'), I.No), __V2), s'),
         (__V, s), occ) ->
          let Rl' =
            match getROrder (__G, __Q, (__V1, s'), occ) with
            | NONE -> Rl
            | Some (__O) -> __O :: Rl in
          checkRImp
            (__G, __Q, Rl', (__V2, (I.comp (I.invShift, s'))), (__V, s), occ)
      | (__G, __Q, Rl, ((Root (Const a, __S), s) as Vs'), __Vs, occ) ->
          checkRGoal (__G, __Q, Rl, __Vs, occ)
      | (__G, __Q, Rl, ((Root (Def a, __S), s) as Vs'), __Vs, occ) ->
          raise
            (Error'
               (occ,
                 (((^) ("Reduction checking for defined type families not yet available:\n"
                          ^ "Illegal use of ")
                     N.qidToString (N.constQid a))
                    ^ ".")))
    let rec checkRClause (__G) (__Q) (Rl) (__Vs) occ =
      checkRClauseW (__G, __Q, Rl, (Whnf.whnf __Vs), occ)
    let rec checkRClauseW __44__ __45__ __46__ __47__ __48__ =
      match (__44__, __45__, __46__, __47__, __48__) with
      | (__G, __Q, Rl, (Pi ((__D, I.Maybe), __V), s), occ) ->
          checkRClause
            ((I.Decl (__G, (N.decEName (__G, (I.decSub (__D, s)))))),
              (I.Decl (__Q, C.Exist)),
              (C.shiftRCtx Rl (fun s -> I.comp (s, I.shift))),
              (__V, (I.dot1 s)), (P.body occ))
      | (__G, __Q, Rl, (Pi (((Dec (_, __V1) as D), I.No), __V2), s), occ) ->
          let __G' = I.Decl (__G, (I.decSub (__D, s))) in
          let __Q' = I.Decl (__Q, C.Exist) in
          let Rl' = C.shiftRCtx Rl (fun s -> I.comp (s, I.shift)) in
          let Rl'' =
            match getROrder (__G', __Q', (__V1, (I.comp (s, I.shift))), occ)
            with
            | NONE -> Rl'
            | Some (__O) -> __O :: Rl' in
          (((checkRClause
               (__G', __Q', Rl'', (__V2, (I.dot1 s)), (P.body occ));
             checkRImp
               (__G', __Q', Rl'', (__V2, (I.dot1 s)),
                 (__V1, (I.comp (s, I.shift))), (P.label occ))))
            (* N.decEName (G, I.decSub (D, s)) *)(* will not be used *))
      | (__G, __Q, Rl, ((Root (Const a, __S), s) as Vs), occ) ->
          let RO =
            match selectROrder (a, (__S, s)) with
            | NONE ->
                raise
                  (Error'
                     (occ,
                       (((^) "No reduction order assigned for " N.qidToString
                           (N.constQid a))
                          ^ ".")))
            | Some (__O) -> __O in
          let _ =
            if (!Global.chatter) > 4
            then
              print
                (((^) (((^) "Verifying reduction property:\n" rlistToString
                          (__G, Rl))
                         ^ " ---> ")
                    orderToString (__G, RO))
                   ^ " \n")
            else () in
          if C.deduce (__G, __Q, Rl, RO)
          then ()
          else
            raise
              (Error'
                 (occ,
                   (((^) (((^) "Reduction violation:\n" rlistToString
                             (__G, Rl))
                            ^ " ---> ")
                       orderToString (__G, RO))
                   (* rename ctx ??? *))))
      | (__G, __Q, Rl, ((Root (Def a, __S), s) as VS), occ) ->
          raise
            (Error'
               (occ,
                 (((^) ("Reduction checking for defined type families not yet available:\n"
                          ^ "Illegal use of ")
                     N.qidToString (N.constQid a))
                    ^ ".")))
    let rec checkFamReduction a =
      let rec checkFam' =
        function
        | [] -> (if (!Global.chatter) > 3 then print "\n" else (); ())
        | (Const b)::bs ->
            (((if (!Global.chatter) > 3
               then print ((N.qidToString (N.constQid b)) ^ " ")
               else ();
               if (!Global.chatter) > 4
               then (N.varReset IntSyn.Null; print "\n")
               else ();
               (try
                  checkRClause
                    (I.Null, I.Null, nil, ((I.constType b), I.id), P.top)
                with | Error' (occ, msg) -> error (b, occ, msg)
                | Error msg -> raise (Error msg));
               checkFam' bs))
            (* reuse variable names when tracing *))
        | (Def d)::bs ->
            (((if (!Global.chatter) > 3
               then print ((N.qidToString (N.constQid d)) ^ " ")
               else ();
               if (!Global.chatter) > 4
               then (N.varReset IntSyn.Null; print "\n")
               else ();
               (try
                  checkRClause
                    (I.Null, I.Null, nil, ((I.constType d), I.id), P.top)
                with | Error' (occ, msg) -> error (d, occ, msg)
                | Error msg -> raise (Error msg));
               checkFam' bs))
            (* reuse variable names when tracing *)) in
      let _ =
        if (!Global.chatter) > 3
        then
          print
            (((^) "Reduction checking family " N.qidToString (N.constQid a))
               ^ ":\n")
        else () in
      checkFam' (Index.lookup a)
    let rec checkFam a =
      let rec checkFam' =
        function
        | [] -> (if (!Global.chatter) > 3 then print "\n" else (); ())
        | (Const b)::bs ->
            (((if (!Global.chatter) > 3
               then print ((N.qidToString (N.constQid b)) ^ " ")
               else ();
               if (!Global.chatter) > 4
               then (N.varReset IntSyn.Null; print "\n")
               else ();
               (try checkClause' (((I.constType b), I.id), P.top)
                with | Error' (occ, msg) -> error (b, occ, msg)
                | Error msg -> raise (Error msg));
               checkFam' bs))
            (* reuse variable names when tracing *))
        | (Def d)::bs ->
            (((if (!Global.chatter) > 3
               then print ((N.qidToString (N.constQid d)) ^ " ")
               else ();
               if (!Global.chatter) > 4
               then (N.varReset IntSyn.Null; print "\n")
               else ();
               (try checkClause' (((I.constType d), I.id), P.top)
                with | Error' (occ, msg) -> error (d, occ, msg)
                | Error msg -> raise (Error msg));
               checkFam' bs))
            (* reuse variable names when tracing *)) in
      let _ =
        if (!Global.chatter) > 3
        then
          print
            (((^) "Termination checking family " N.qidToString (N.constQid a))
               ^ "\n")
        else () in
      checkFam' (Index.lookup a)
    let rec reset () = R.reset (); R.resetROrder ()
    let reset = reset
    let checkFamReduction = checkFamReduction
    let checkFam = checkFam
  end ;;
