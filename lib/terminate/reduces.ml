
(* Reduction and Termination checker *)
(* Author: Brigitte Pientka *)
module type REDUCES  =
  sig
    (*! structure IntSyn : INTSYN !*)
    exception Error of string 
    val reset : unit -> unit
    val checkFamReduction : IntSyn.cid -> unit
    val checkFam : IntSyn.cid -> unit
  end;;




(* Reduction and Termination checker *)
(* Author: Brigitte Pientka *)
(* for termination checking see [Rohwedder,Pfenning ESOP'96]
   for a revised version incorporating reducation checking see
   tech report CMU-CS-01-115
 *)
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
                         (*! structure IntSyn' : INTSYN !*)
                         (*! sharing Whnf.IntSyn = IntSyn' !*)
                         (*! sharing Names.IntSyn = IntSyn' !*)
                         (*! sharing Index.IntSyn = IntSyn' !*)
                         (*! sharing Subordinate.IntSyn = IntSyn' !*)
                         (*! sharing Print.IntSyn = IntSyn' !*)
                         (*! sharing Order.IntSyn = IntSyn' !*)
                         (*! structure Paths  : PATHS !*)
                         (*! sharing Checking.IntSyn = IntSyn' !*)
                         (*! sharing Checking.Paths = Paths !*)
                         module Origins : ORIGINS
                       end) : REDUCES =
  struct
    (*! sharing Origins.Paths = Paths !*)
    (*! sharing Origins.IntSyn = IntSyn' !*)
    (*! structure CSManager : CS_MANAGER !*)
    (*! sharing CSManager.IntSyn = IntSyn' !*)
    (*! structure IntSyn = IntSyn' !*)
    exception Error of string 
    module I = IntSyn
    module P = Paths
    module N = Names
    module F = Formatter
    module R = Order
    module C = Checking
    exception Error' of (P.occ * string) 
    let rec error (c, occ, msg) =
      match Origins.originLookup c with
      | (fileName, None) -> raise (Error ((fileName ^ ":") ^ msg))
      | (fileName, Some occDec) ->
          raise
            (Error
               (P.wrapLoc'
                  ((P.Loc (fileName, (P.occToRegionDec occDec occ))),
                    (Origins.linesInfoLookup fileName), msg)))
    let rec concat =
      function
      | (__g', I.Null) -> __g'
      | (__g', Decl (__g, __d)) -> I.Decl ((concat (__g', __g)), __d)
    let rec fmtOrder (__g, O) =
      let rec fmtOrder' =
        function
        | Arg (((__u, s) as __Us), ((__v, s') as __Vs)) ->
            F.hbox
              [F.String "("; Print.formatExp (__g, (I.EClo __Us)); F.String ")"]
        | Lex (__l) ->
            F.hbox
              [F.String "{"; F.hOVbox0 1 0 1 (fmtOrders __l); F.String "}"]
        | Simul (__l) ->
            F.hbox
              [F.String "["; F.hOVbox0 1 0 1 (fmtOrders __l); F.String "]"]
      and fmtOrders =
        function
        | [] -> []
        | (O)::[] -> (fmtOrder' O) :: []
        | (O)::__l -> (::) ((fmtOrder' O) :: F.Break) fmtOrders __l in
      fmtOrder' O
    let rec fmtComparison (__g, O, comp, O') =
      F.hOVbox0 1 0 1
        [fmtOrder (__g, O); F.Break; F.String comp; F.Break; fmtOrder (__g, O')]
    let rec fmtPredicate =
      function
      | (__g, Less (O, O')) -> fmtComparison (__g, O, "<", O')
      | (__g, Leq (O, O')) -> fmtComparison (__g, O, "<=", O')
      | (__g, Eq (O, O')) -> fmtComparison (__g, O, "=", O')
      | (__g, Pi (__d, P)) ->
          F.hbox [F.String "Pi "; fmtPredicate ((I.Decl (__g, __d)), P)]
    let rec rlistToString' =
      function
      | (__g, nil) -> ""
      | (__g, (P)::[]) -> F.makestring_fmt (fmtPredicate (__g, P))
      | (__g, (P)::Rl) ->
          (^) ((F.makestring_fmt (fmtPredicate (__g, P))) ^ " ,")
            rlistToString' (__g, Rl)
    let rec rlistToString (__g, Rl) = rlistToString' ((Names.ctxName __g), Rl)
    let rec orderToString (__g, P) =
      F.makestring_fmt (fmtPredicate ((Names.ctxName __g), P))
    let rec select (c, (S, s)) =
      let SO = R.selLookup c in
      let Vid = ((I.constType c), I.id) in
      let rec select'' (n, (__Ss', __Vs'')) =
        select''W (n, (__Ss', (Whnf.whnf __Vs'')))
      and select''W =
        function
        | (1, ((App (__u', S'), s'), (Pi ((Dec (_, __v''), _), _), s''))) ->
            ((__u', s'), (__v'', s''))
        | (n, ((SClo (S', s1'), s2'), __Vs'')) ->
            select''W (n, ((S', (I.comp (s1', s2'))), __Vs''))
        | (n, ((App (__u', S'), s'), (Pi ((Dec (_, V1''), _), V2''), s''))) ->
            select''
              ((n - 1),
                ((S', s'), (V2'', (I.Dot ((I.Exp (I.EClo (__u', s'))), s''))))) in
      let rec select' =
        function
        | Arg n -> R.Arg (select'' (n, ((S, s), Vid)))
        | Lex (__l) -> R.Lex (map select' __l)
        | Simul (__l) -> R.Simul (map select' __l) in
      select' (R.selLookup c)
    let rec selectOcc (c, (S, s), occ) =
      try select (c, (S, s))
      with
      | Error msg ->
          raise
            (Error'
               (occ,
                 ((^) "Termination violation: no order assigned for "
                    N.qidToString (N.constQid c))))
    let rec selectROrder (c, (S, s)) =
      let Vid = ((I.constType c), I.id) in
      let rec select'' (n, (__Ss', __Vs'')) =
        select''W (n, (__Ss', (Whnf.whnf __Vs'')))
      and select''W =
        function
        | (1, ((App (__u', S'), s'), (Pi ((Dec (_, __v''), _), _), s''))) ->
            ((__u', s'), (__v'', s''))
        | (n, ((SClo (S', s1'), s2'), __Vs'')) ->
            select''W (n, ((S', (I.comp (s1', s2'))), __Vs''))
        | (n, ((App (__u', S'), s'), (Pi ((Dec (_, V1''), _), V2''), s''))) ->
            select''
              ((n - 1),
                ((S', s'), (V2'', (I.Dot ((I.Exp (I.EClo (__u', s'))), s''))))) in
      let rec select' =
        function
        | Arg n -> R.Arg (select'' (n, ((S, s), Vid)))
        | Lex (__l) -> R.Lex (map select' __l)
        | Simul (__l) -> R.Simul (map select' __l) in
      let rec selectP =
        function
        | Less (O1, O2) -> C.Less ((select' O1), (select' O2))
        | Leq (O1, O2) -> C.Leq ((select' O1), (select' O2))
        | Eq (O1, O2) -> C.Eq ((select' O1), (select' O2)) in
      try Some (selectP (R.selLookupROrder c)) with | Error s -> None
    let rec abstractRO (__g, __d, O) = C.Pi (__d, O)
    let rec getROrder (__g, Q, __Vs, occ) =
      getROrderW (__g, Q, (Whnf.whnf __Vs), occ)
    let rec getROrderW =
      function
      | (__g, Q, ((Root (Const a, S), s) as __Vs), occ) ->
          let O = selectROrder (a, (S, s)) in
          let _ =
            match O with
            | None -> ()
            | Some (O) ->
                if (!Global.chatter) > 5
                then
                  print
                    (((^) (((^) "Reduction predicate for " N.qidToString
                              (N.constQid a))
                             ^ " added : ")
                        orderToString (__g, O))
                       ^ "\n")
                else () in
          O
      | (__g, Q, (Pi ((__d, I.Maybe), __v), s), occ) ->
          let O =
            getROrder
              ((I.Decl (__g, (N.decLUName (__g, (I.decSub (__d, s)))))),
                (I.Decl (Q, C.All)), (__v, (I.dot1 s)), (P.body occ)) in
          (match O with
           | None -> None
           | Some (O') -> Some (abstractRO (__g, (I.decSub (__d, s)), O')))
      | (__g, Q, (Pi (((Dec (_, V1) as __d), I.No), V2), s), occ) ->
          let O =
            getROrder (__g, Q, (V2, (I.comp (I.invShift, s))), (P.body occ)) in
          (match O with | None -> None | Some (O') -> Some O')
      | (__g, Q, ((Root (Def a, S), s) as __Vs), occ) ->
          raise
            (Error'
               (occ,
                 (((^) ("Reduction checking for defined type families not yet available:\n"
                          ^ "Illegal use of ")
                     N.qidToString (N.constQid a))
                    ^ ".")))
    let rec checkGoal (G0, Q0, Rl, __Vs, __Vs', occ) =
      checkGoalW (G0, Q0, Rl, (Whnf.whnf __Vs), __Vs', occ)
    let rec checkGoalW =
      function
      | (G0, Q0, Rl, (Pi (((Dec (_, V1) as __d), I.No), V2), s), __Vs', occ) ->
          (checkClause ((G0, Q0, Rl), I.Null, I.Null, (V1, s), (P.label occ));
           checkGoal
             (G0, Q0, Rl, (V2, (I.comp (I.invShift, s))), __Vs', (P.body occ)))
      | (G0, Q0, Rl, (Pi ((__d, I.Maybe), __v), s), (__v', s'), occ) ->
          checkGoal
            ((I.Decl (G0, (N.decLUName (G0, (I.decSub (__d, s)))))),
              (I.Decl (Q0, C.All)),
              (C.shiftRCtx Rl (function | s -> I.comp (s, I.shift))),
              (__v, (I.dot1 s)), (__v', (I.comp (s', I.shift))), (P.body occ))
      | (G0, Q0, Rl, ((Root (Const a, S), s) as __Vs),
         ((Root (Const a', S'), s') as __Vs'), occ) ->
          let rec lookup =
            function
            | (R.Empty, f) -> R.Empty
            | ((LE (a, a's') as a's), f) ->
                if f a then a's else lookup (a's', f)
            | ((LT (a, a's') as a's), f) ->
                if f a then a's else lookup (a's', f) in
          let P = selectOcc (a, (S, s), occ) in
          let __P' = select (a', (S', s')) in
          let a's = Order.mutLookup a in
          (match lookup (a's, (function | x' -> x' = a')) with
           | R.Empty -> ()
           | LE _ ->
               (if (!Global.chatter) > 4
                then
                  (print "Verifying termination order:\n";
                   print (rlistToString (G0, Rl));
                   print
                     (((^) " ---> " orderToString (G0, (C.Leq (P, __P')))) ^
                        "\n"))
                else ();
                if C.deduce (G0, Q0, Rl, (C.Leq (P, __P')))
                then ()
                else
                  raise
                    (Error'
                       (occ,
                         ((^) (((^) "Termination violation:\n" rlistToString
                                  (G0, Rl))
                                 ^ " ---> ")
                            orderToString (G0, (C.Leq (P, __P')))))))
           | LT _ ->
               (if (!Global.chatter) > 4
                then
                  (print "Verifying termination order:\n";
                   print ((rlistToString (G0, Rl)) ^ " ---> ");
                   print ((orderToString (G0, (C.Less (P, __P')))) ^ "\n"))
                else ();
                if C.deduce (G0, Q0, Rl, (C.Less (P, __P')))
                then ()
                else
                  raise
                    (Error'
                       (occ,
                         ((^) (((^) "Termination violation:\n" rlistToString
                                  (G0, Rl))
                                 ^ " ---> ")
                            orderToString (G0, (C.Less (P, __P'))))))))
      | (G0, Q0, Rl, ((Root (Def a, S), s) as __Vs), __Vs', occ) ->
          raise
            (Error'
               (occ,
                 (((^) ("Reduction checking for defined type families not yet available:\n"
                          ^ "Illegal use of ")
                     N.qidToString (N.constQid a))
                    ^ ".")))
      | (G0, Q0, Rl, __Vs, ((Root (Def a', S'), s') as __Vs'), occ) ->
          raise
            (Error'
               (occ,
                 (((^) ("Reduction checking for defined type families not yet available:\n"
                          ^ "Illegal use of ")
                     N.qidToString (N.constQid a'))
                    ^ ".")))
    let rec checkSubgoals =
      function
      | (G0, Q0, Rl, __Vs, n,
         (Decl (__g, (Dec (_, __v') as __d)), Decl (Q, And occ))) ->
          let _ = checkGoal (G0, Q0, Rl, (__v', (I.Shift (n + 1))), __Vs, occ) in
          let RO = getROrder (G0, Q0, (__v', (I.Shift (n + 1))), occ) in
          let Rl' = match RO with | None -> Rl | Some (O) -> O :: Rl in
          checkSubgoals (G0, Q0, Rl', __Vs, (n + 1), (__g, Q))
      | (G0, Q0, Rl, __Vs, n, (Decl (__g, __d), Decl (Q, C.Exist))) ->
          checkSubgoals (G0, Q0, Rl, __Vs, (n + 1), (__g, Q))
      | (G0, Q0, Rl, __Vs, n, (Decl (__g, __d), Decl (Q, C.All))) ->
          checkSubgoals (G0, Q0, Rl, __Vs, (n + 1), (__g, Q))
      | (G0, Q0, Rl, __Vs, n, (I.Null, I.Null)) -> ()
    let rec checkClause (GQR, __g, Q, __Vs, occ) =
      checkClauseW (GQR, __g, Q, (Whnf.whnf __Vs), occ)
    let rec checkClauseW =
      function
      | (GQR, __g, Q, (Pi ((__d, I.Maybe), __v), s), occ) ->
          checkClause
            (GQR, (I.Decl (__g, (N.decEName (__g, (I.decSub (__d, s)))))),
              (I.Decl (Q, C.Exist)), (__v, (I.dot1 s)), (P.body occ))
      | (GQR, __g, Q, (Pi (((Dec (_, V1) as __d), I.No), V2), s), occ) ->
          checkClause
            (GQR, (I.Decl (__g, (I.decSub (__d, s)))),
              (I.Decl (Q, (C.And (P.label occ)))), (V2, (I.dot1 s)),
              (P.body occ))
      | (((G0, Q0, Rl) as GQR), __g, Q, ((Root (Const a, S), s) as __Vs), occ) ->
          let n = I.ctxLength __g in
          let Rl' = C.shiftRCtx Rl (function | s -> I.comp (s, (I.Shift n))) in
          checkSubgoals
            ((concat (G0, __g)), (concat (Q0, Q)), Rl', __Vs, 0, (__g, Q))
      | (GQR, __g, Q, (Root (Def a, S), s), occ) ->
          raise
            (Error'
               (occ,
                 (((^) ("Termination checking for defined type families not yet available:\n"
                          ^ "Illegal use of ")
                     N.qidToString (N.constQid a))
                    ^ ".")))
    let rec checkClause' (__Vs, occ) =
      checkClause ((I.Null, I.Null, nil), I.Null, I.Null, __Vs, occ)
    let rec checkRGoal (__g, Q, Rl, __Vs, occ) =
      checkRGoalW (__g, Q, Rl, (Whnf.whnf __Vs), occ)
    let rec checkRGoalW =
      function
      | (__g, Q, Rl, ((Root (Const a, S), s) as __Vs), occ) -> ()
      | (__g, Q, Rl, (Pi ((__d, I.Maybe), __v), s), occ) ->
          checkRGoal
            ((I.Decl (__g, (N.decLUName (__g, (I.decSub (__d, s)))))),
              (I.Decl (Q, C.All)),
              (C.shiftRCtx Rl (function | s -> I.comp (s, I.shift))),
              (__v, (I.dot1 s)), (P.body occ))
      | (__g, Q, Rl, (Pi (((Dec (_, V1) as __d), I.No), V2), s), occ) ->
          (checkRClause (__g, Q, Rl, (V1, s), (P.label occ));
           checkRGoal
             (__g, Q, Rl, (V2, (I.comp (I.invShift, s))), (P.body occ)))
      | (__g, Q, Rl, (Root (Def a, S), s), occ) ->
          raise
            (Error'
               (occ,
                 (((^) ("Reduction checking for defined type families not yet available:\n"
                          ^ "Illegal use of ")
                     N.qidToString (N.constQid a))
                    ^ ".")))
    let rec checkRImp (__g, Q, Rl, __Vs, __Vs', occ) =
      checkRImpW (__g, Q, Rl, (Whnf.whnf __Vs), __Vs', occ)
    let rec checkRImpW =
      function
      | (__g, Q, Rl, (Pi ((__d', I.Maybe), __v'), s'), (__v, s), occ) ->
          checkRImp
            ((I.Decl (__g, (N.decEName (__g, (I.decSub (__d', s')))))),
              (I.Decl (Q, C.Exist)),
              (C.shiftRCtx Rl (function | s -> I.comp (s, I.shift))),
              (__v', (I.dot1 s')), (__v, (I.comp (s, I.shift))), occ)
      | (__g, Q, Rl, (Pi (((Dec (_, V1) as __d'), I.No), V2), s'), (__v, s), occ)
          ->
          let Rl' =
            match getROrder (__g, Q, (V1, s'), occ) with
            | None -> Rl
            | Some (O) -> O :: Rl in
          checkRImp (__g, Q, Rl', (V2, (I.comp (I.invShift, s'))), (__v, s), occ)
      | (__g, Q, Rl, ((Root (Const a, S), s) as __Vs'), __Vs, occ) ->
          checkRGoal (__g, Q, Rl, __Vs, occ)
      | (__g, Q, Rl, ((Root (Def a, S), s) as __Vs'), __Vs, occ) ->
          raise
            (Error'
               (occ,
                 (((^) ("Reduction checking for defined type families not yet available:\n"
                          ^ "Illegal use of ")
                     N.qidToString (N.constQid a))
                    ^ ".")))
    let rec checkRClause (__g, Q, Rl, __Vs, occ) =
      checkRClauseW (__g, Q, Rl, (Whnf.whnf __Vs), occ)
    let rec checkRClauseW =
      function
      | (__g, Q, Rl, (Pi ((__d, I.Maybe), __v), s), occ) ->
          checkRClause
            ((I.Decl (__g, (N.decEName (__g, (I.decSub (__d, s)))))),
              (I.Decl (Q, C.Exist)),
              (C.shiftRCtx Rl (function | s -> I.comp (s, I.shift))),
              (__v, (I.dot1 s)), (P.body occ))
      | (__g, Q, Rl, (Pi (((Dec (_, V1) as __d), I.No), V2), s), occ) ->
          let __g' = I.Decl (__g, (I.decSub (__d, s))) in
          let Q' = I.Decl (Q, C.Exist) in
          let Rl' = C.shiftRCtx Rl (function | s -> I.comp (s, I.shift)) in
          let Rl'' =
            match getROrder (__g', Q', (V1, (I.comp (s, I.shift))), occ) with
            | None -> Rl'
            | Some (O) -> O :: Rl' in
          (checkRClause (__g', Q', Rl'', (V2, (I.dot1 s)), (P.body occ));
           checkRImp
             (__g', Q', Rl'', (V2, (I.dot1 s)), (V1, (I.comp (s, I.shift))),
               (P.label occ)))
      | (__g, Q, Rl, ((Root (Const a, S), s) as __Vs), occ) ->
          let RO =
            match selectROrder (a, (S, s)) with
            | None ->
                raise
                  (Error'
                     (occ,
                       (((^) "No reduction order assigned for " N.qidToString
                           (N.constQid a))
                          ^ ".")))
            | Some (O) -> O in
          let _ =
            if (!Global.chatter) > 4
            then
              print
                (((^) (((^) "Verifying reduction property:\n" rlistToString
                          (__g, Rl))
                         ^ " ---> ")
                    orderToString (__g, RO))
                   ^ " \n")
            else () in
          if C.deduce (__g, Q, Rl, RO)
          then ()
          else
            raise
              (Error'
                 (occ,
                   ((^) (((^) "Reduction violation:\n" rlistToString (__g, Rl))
                           ^ " ---> ")
                      orderToString (__g, RO))))
      | (__g, Q, Rl, ((Root (Def a, S), s) as VS), occ) ->
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
            (if (!Global.chatter) > 3
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
             checkFam' bs)
        | (Def d)::bs ->
            (if (!Global.chatter) > 3
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
             checkFam' bs) in
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
            (if (!Global.chatter) > 3
             then print ((N.qidToString (N.constQid b)) ^ " ")
             else ();
             if (!Global.chatter) > 4
             then (N.varReset IntSyn.Null; print "\n")
             else ();
             (try checkClause' (((I.constType b), I.id), P.top)
              with | Error' (occ, msg) -> error (b, occ, msg)
              | Error msg -> raise (Error msg));
             checkFam' bs)
        | (Def d)::bs ->
            (if (!Global.chatter) > 3
             then print ((N.qidToString (N.constQid d)) ^ " ")
             else ();
             if (!Global.chatter) > 4
             then (N.varReset IntSyn.Null; print "\n")
             else ();
             (try checkClause' (((I.constType d), I.id), P.top)
              with | Error' (occ, msg) -> error (d, occ, msg)
              | Error msg -> raise (Error msg));
             checkFam' bs) in
      let _ =
        if (!Global.chatter) > 3
        then
          print
            (((^) "Termination checking family " N.qidToString (N.constQid a))
               ^ "\n")
        else () in
      checkFam' (Index.lookup a)
    let rec reset () = R.reset (); R.resetROrder ()
    (*--------------------------------------------------------------------*)
    (* Printing *)
    (*--------------------------------------------------------------------*)
    (* select (c, (S, s)) = P

      select parameters according to termination order

      Invariant:
      If   . |- c : __v   __g |- s : __g'    __g' |- S : __v > type
      and  __v = {x1:V1} ... {xn:Vn} type.
      then P = __U1[s1] .. Un[sn] is parameter select of S[s] according to sel (c)
      and  __g |- si : Gi  Gi |- Ui : Vi
      and  __g |- Vi[s]  == __v[si] : type   forall 1<=i<=n
    *)
    (* selectROrder (c, (S, s)) = P

       select parameters according to reduction order

       Invariant:
       If   . |- c : __v   __g |- s : __g'    __g' |- S : __v > type
       and  __v = {x1:V1} ... {xn:Vn} type.
       then P = __U1[s1] .. Un[sn] is parameter select of S[s] according to sel (c)
       and  __g |- si : Gi  Gi |- Ui : Vi
       and  __g |- Vi[s]  == __v[si] : type   forall 1<=i<=n
    *)
    (*--------------------------------------------------------------*)
    (* abstractRO (__g, __d, RO) = Pi D. RO
       Invariant:

       If  __g, __d |- RO
       then  __g |- Pi __d . RO

    *)
    (* getROrder (__g, Q, (__v, s)) = O
       If __g: Q
       and  __g |- s : G1    and   G1 |- __v : __l
       then O is the reduction order associated to __v[s]
       and  __g |- O

     *)
    (*--------------------------------------------------------------------*)
    (* Termination Checker *)
    (* checkGoal (G0, Q0, Rl, (__v, s), (__v', s'), occ) = ()

       Invariant:
       If   G0 : Q0
       and  G0 |- s : G1     and   G1 |- __v : __l     (__v, s) in whnf
       and  __v[s], __v'[s'] does not contain Skolem constants
       and  G0 |- s' : G2    and   G2 |- __v' : __l'   (__v', s') in whnf
       and  __v' = a' @ S'
       and  __g |- __l = __l'
       and  __v[s] < __v'[s']  (< termination ordering)
         then ()
       else Error is raised.
    *)
    (* only if a terminates? *)
    (* always succeeds? -fp *)
    (* always succeeds? -fp *)
    (* checkSubgoals (G0, Q0, Rl, __Vs, n, (__g, Q), __Vs, occ)

      if    G0 |- Q0
       and  G0 |- s : G1    and   G1 |- __v : __l
       and  __v[s] does not contain any skolem constants
       and  Rl is a list of reduction propositions
       and  G0 |- Rl
       and  G0 |- __v[s]
       and  G0 = G0', __g' where __g' <= __g
       and  n = |__g'| - |__g|
       and  G0 |- __g[^n]
       and  __g |- Q
     and
       __v[s] satisfies the associated termination order

     *)
    (* checkClause (GQR as (G0, Q0, Rl), __g, Q, __Vs, occ)

      if   G0, __g |- Q0, Q
       and  G0, __g |- s : G1    and   G1 |- __v : __l
       and  __v[s] does not contain any skolem constants
       and  Rl is a list of reduction propositions
       and  G0, __g |- Rl
       and  G0, __g |- __v[s]
     and
       __v[s] satisfies the associated termination order
     *)
    (*-------------------------------------------------------------------*)
    (* Reduction Checker *)
    (* checkRGoal (__g, Q, Rl, (V1, s1), occ) = Rl''

       Invariant
       If   __g : Q
       and  __g |- s1 : G1   and   G1 |- V1 : type
       and  V1[s1], V2[s2] does not contain Skolem constants
       and  __g |- s2 : G2   and   G2 |- V2 : type
       and occ locates V1 in declaration
       and Rl is a context of reduction predicates
       and  __g |- Rl
       and Rl implies that V1[s1] satisfies its associated reduction order

     *)
    (* trivial *)
    (* checkRImp (__g, Q, Rl, (V1, s1), (V2, s2), occ) = ()

       Invariant
       If   __g : Q
       and  __g |- s1 : G1   and   G1 |- V1 : type
       and  V1[s1], V2[s2] does not contain Skolem constants
       and  __g |- s2 : G2   and   G2 |- V2 : type
       and occ locates V1 in declaration
       and Rl is a context for derived reduction order assumptions
       and __g |- Rl

       then Rl implies that  V2[s2] satisfies its associated reduction order
            with respect to V1[s1]
    *)
    (* checkRClause (__g, Q, Rl, (__v, s)) = ()

       Invariant:
       If __g: Q
       and  __g |- s : G1    and   G1 |- __v : __l
       and  __v[s] does not contain any Skolem constants
       and  Rl is a context of reduction predicates
       and  __g |- Rl
       then Rl implies that __v[s] satifies the reduction order
    *)
    (* N.decEName (__g, I.decSub (__d, s)) *)
    (* will not be used *)
    (* rename ctx ??? *)
    (* checkFamReduction a = ()

       Invariant:
       a is name of type family in the signature
       raises invariant, if clauses for a does not fulfill
       specified reducation property

       Note: checking reduction is a separate property of termination
    *)
    (* reuse variable names when tracing *)
    (* reuse variable names when tracing *)
    (* checkFam a = ()

       Invariant:
       a is name of type family in the signature
       raises invariant, if clauses for a do not terminate
       according to specified termination order

       Note: termination checking takes into account proven
             reduction properties.
    *)
    (* reuse variable names when tracing *)
    (* reuse variable names when tracing *)
    let reset = reset
    let checkFamReduction = checkFamReduction
    let checkFam = checkFam
  end ;;
