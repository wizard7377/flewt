
module type REDUCES  =
  sig
    exception Error of
      ((string)(*! structure IntSyn : INTSYN !*)(* Author: Brigitte Pientka *)
      (* Reduction and Termination checker *)) 
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
                         module Origins :
                         ((ORIGINS)(* Reduction and Termination checker *)
                         (* Author: Brigitte Pientka *)
                         (* for termination checking see [Rohwedder,Pfenning ESOP'96]
   for a revised version incorporating reducation checking see
   tech report CMU-CS-01-115
 *)
                         (*! structure IntSyn' : INTSYN !*)
                         (*! sharing Whnf.IntSyn = IntSyn' !*)(*! sharing Names.IntSyn = IntSyn' !*)
                         (*! sharing Index.IntSyn = IntSyn' !*)(*! sharing Subordinate.IntSyn = IntSyn' !*)
                         (*! sharing Print.IntSyn = IntSyn' !*)(*! sharing Order.IntSyn = IntSyn' !*)
                         (*! structure Paths  : PATHS !*)
                         (*! sharing Checking.IntSyn = IntSyn' !*)
                         (*! sharing Checking.Paths = Paths !*))
                       end) : REDUCES =
  struct
    exception Error of
      ((string)(*! structure IntSyn = IntSyn' !*)(*! sharing CSManager.IntSyn = IntSyn' !*)
      (*! structure CSManager : CS_MANAGER !*)(*! sharing Origins.IntSyn = IntSyn' !*)
      (*! sharing Origins.Paths = Paths !*)) 
    module I = IntSyn
    module P = Paths
    module N = Names
    module F = Formatter
    module R = Order
    module C = Checking
    exception Error' of (P.occ * string) 
    let rec error (c, occ, msg) =
      match Origins.originLookup c with
      | (fileName, NONE) -> raise (Error ((fileName ^ ":") ^ msg))
      | (fileName, SOME occDec) ->
          raise
            (Error
               (P.wrapLoc'
                  ((P.Loc (fileName, (P.occToRegionDec occDec occ))),
                    (Origins.linesInfoLookup fileName), msg)))
    let rec concat =
      function
      | (g', I.Null) -> g'
      | (g', Decl (g, D)) -> I.Decl ((concat (g', g)), D)
    let rec fmtOrder (g, O) =
      let fmtOrder' =
        function
        | Arg (((U, s) as Us), ((V, s') as Vs)) ->
            F.Hbox
              [F.String "("; Print.formatExp (g, (I.EClo Us)); F.String ")"]
        | Lex (L) ->
            F.Hbox
              [F.String "{"; F.HOVbox0 1 0 1 (fmtOrders L); F.String "}"]
        | Simul (L) ->
            F.Hbox
              [F.String "["; F.HOVbox0 1 0 1 (fmtOrders L); F.String "]"]
      and fmtOrders =
        function
        | [] -> []
        | (O)::[] -> (fmtOrder' O) :: []
        | (O)::L -> (::) ((fmtOrder' O) :: F.Break) fmtOrders L in
      fmtOrder' O
    let rec fmtComparison (g, O, comp, O') =
      F.HOVbox0 1 0 1
        [fmtOrder (g, O); F.Break; F.String comp; F.Break; fmtOrder (g, O')]
    let rec fmtPredicate =
      function
      | (g, Less (O, O')) -> fmtComparison (g, O, "<", O')
      | (g, Leq (O, O')) -> fmtComparison (g, O, "<=", O')
      | (g, Eq (O, O')) -> fmtComparison (g, O, "=", O')
      | (g, Pi (D, P)) ->
          F.Hbox [F.String "Pi "; fmtPredicate ((I.Decl (g, D)), P)]
    let rec rlistToString' =
      function
      | (g, nil) -> ""
      | (g, (P)::[]) -> F.makestring_fmt (fmtPredicate (g, P))
      | (g, (P)::Rl) ->
          (^) ((F.makestring_fmt (fmtPredicate (g, P))) ^ " ,")
            rlistToString' (g, Rl)
    let rec rlistToString (g, Rl) = rlistToString' ((Names.ctxName g), Rl)
    let rec orderToString (g, P) =
      F.makestring_fmt (fmtPredicate ((Names.ctxName g), P))
    let rec select (c, (S, s)) =
      let SO = R.selLookup c in
      let Vid = ((I.constType c), I.id) in
      let select'' (n, (Ss', Vs'')) = select''W (n, (Ss', (Whnf.whnf Vs'')))
      and select''W =
        function
        | (1, ((App (U', S'), s'), (Pi ((Dec (_, V''), _), _), s''))) ->
            ((U', s'), (V'', s''))
        | (n, ((SClo (S', s1'), s2'), Vs'')) ->
            select''W (n, ((S', (I.comp (s1', s2'))), Vs''))
        | (n, ((App (U', S'), s'), (Pi ((Dec (_, V1''), _), V2''), s''))) ->
            select''
              ((n - 1),
                ((S', s'), (V2'', (I.Dot ((I.Exp (I.EClo (U', s'))), s''))))) in
      let select' =
        function
        | Arg n -> R.Arg (select'' (n, ((S, s), Vid)))
        | Lex (L) -> R.Lex (map select' L)
        | Simul (L) -> R.Simul (map select' L) in
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
      let select'' (n, (Ss', Vs'')) = select''W (n, (Ss', (Whnf.whnf Vs'')))
      and select''W =
        function
        | (1, ((App (U', S'), s'), (Pi ((Dec (_, V''), _), _), s''))) ->
            ((U', s'), (V'', s''))
        | (n, ((SClo (S', s1'), s2'), Vs'')) ->
            select''W (n, ((S', (I.comp (s1', s2'))), Vs''))
        | (n, ((App (U', S'), s'), (Pi ((Dec (_, V1''), _), V2''), s''))) ->
            select''
              ((n - 1),
                ((S', s'), (V2'', (I.Dot ((I.Exp (I.EClo (U', s'))), s''))))) in
      let select' =
        function
        | Arg n -> R.Arg (select'' (n, ((S, s), Vid)))
        | Lex (L) -> R.Lex (map select' L)
        | Simul (L) -> R.Simul (map select' L) in
      let selectP =
        function
        | Less (O1, O2) -> C.Less ((select' O1), (select' O2))
        | Leq (O1, O2) -> C.Leq ((select' O1), (select' O2))
        | Eq (O1, O2) -> C.Eq ((select' O1), (select' O2)) in
      try SOME (selectP (R.selLookupROrder c)) with | Error s -> NONE
    let rec abstractRO (g, D, O) = C.Pi (D, O)
    let rec getROrder (g, Q, Vs, occ) =
      getROrderW (g, Q, (Whnf.whnf Vs), occ)
    let rec getROrderW =
      function
      | (g, Q, ((Root (Const a, S), s) as Vs), occ) ->
          let O = selectROrder (a, (S, s)) in
          let _ =
            match O with
            | NONE -> ()
            | SOME (O) ->
                if (!Global.chatter) > 5
                then
                  print
                    (((^) (((^) "Reduction predicate for " N.qidToString
                              (N.constQid a))
                             ^ " added : ")
                        orderToString (g, O))
                       ^ "\n")
                else () in
          O
      | (g, Q, (Pi ((D, I.Maybe), V), s), occ) ->
          let O =
            getROrder
              ((I.Decl (g, (N.decLUName (g, (I.decSub (D, s)))))),
                (I.Decl (Q, C.All)), (V, (I.dot1 s)), (P.body occ)) in
          (match O with
           | NONE -> NONE
           | SOME (O') -> SOME (abstractRO (g, (I.decSub (D, s)), O')))
      | (g, Q, (Pi (((Dec (_, V1) as D), I.No), V2), s), occ) ->
          let O =
            getROrder (g, Q, (V2, (I.comp (I.invShift, s))), (P.body occ)) in
          (match O with | NONE -> NONE | SOME (O') -> SOME O')
      | (g, Q, ((Root (Def a, S), s) as Vs), occ) ->
          raise
            (Error'
               (occ,
                 (((^) ("Reduction checking for defined type families not yet available:\n"
                          ^ "Illegal use of ")
                     N.qidToString (N.constQid a))
                    ^ ".")))
    let rec checkGoal (G0, Q0, Rl, Vs, Vs', occ) =
      checkGoalW (G0, Q0, Rl, (Whnf.whnf Vs), Vs', occ)
    let rec checkGoalW =
      function
      | (G0, Q0, Rl, (Pi (((Dec (_, V1) as D), I.No), V2), s), Vs', occ) ->
          (checkClause ((G0, Q0, Rl), I.Null, I.Null, (V1, s), (P.label occ));
           checkGoal
             (G0, Q0, Rl, (V2, (I.comp (I.invShift, s))), Vs', (P.body occ)))
      | (G0, Q0, Rl, (Pi ((D, I.Maybe), V), s), (V', s'), occ) ->
          checkGoal
            ((I.Decl (G0, (N.decLUName (G0, (I.decSub (D, s)))))),
              (I.Decl (Q0, C.All)),
              (C.shiftRCtx Rl (function | s -> I.comp (s, I.shift))),
              (V, (I.dot1 s)), (V', (I.comp (s', I.shift))), (P.body occ))
      | (G0, Q0, Rl, ((Root (Const a, S), s) as Vs),
         ((Root (Const a', S'), s') as Vs'), occ) ->
          let lookup =
            function
            | (R.Empty, f) -> R.Empty
            | ((LE (a, a's') as a's), f) ->
                if f a then a's else lookup (a's', f)
            | ((LT (a, a's') as a's), f) ->
                if f a then a's else lookup (a's', f) in
          let P = selectOcc (a, (S, s), occ) in
          let P' = select (a', (S', s')) in
          let a's = Order.mutLookup a in
          (match lookup (a's, (function | x' -> x' = a')) with
           | R.Empty -> ()
           | LE _ ->
               (if (!Global.chatter) > 4
                then
                  (print "Verifying termination order:\n";
                   print (rlistToString (G0, Rl));
                   print
                     (((^) " ---> " orderToString (G0, (C.Leq (P, P')))) ^
                        "\n"))
                else ();
                if C.deduce (G0, Q0, Rl, (C.Leq (P, P')))
                then ()
                else
                  raise
                    (Error'
                       (occ,
                         ((^) (((^) "Termination violation:\n" rlistToString
                                  (G0, Rl))
                                 ^ " ---> ")
                            orderToString (G0, (C.Leq (P, P')))))))
           | LT _ ->
               (if (!Global.chatter) > 4
                then
                  (print "Verifying termination order:\n";
                   print ((rlistToString (G0, Rl)) ^ " ---> ");
                   print ((orderToString (G0, (C.Less (P, P')))) ^ "\n"))
                else ();
                if C.deduce (G0, Q0, Rl, (C.Less (P, P')))
                then ()
                else
                  raise
                    (Error'
                       (occ,
                         ((^) (((^) "Termination violation:\n" rlistToString
                                  (G0, Rl))
                                 ^ " ---> ")
                            orderToString (G0, (C.Less (P, P'))))))))
      | (G0, Q0, Rl, ((Root (Def a, S), s) as Vs), Vs', occ) ->
          raise
            (Error'
               (occ,
                 (((^) ("Reduction checking for defined type families not yet available:\n"
                          ^ "Illegal use of ")
                     N.qidToString (N.constQid a))
                    ^ ".")))
      | (G0, Q0, Rl, Vs, ((Root (Def a', S'), s') as Vs'), occ) ->
          raise
            (Error'
               (occ,
                 (((^) ("Reduction checking for defined type families not yet available:\n"
                          ^ "Illegal use of ")
                     N.qidToString (N.constQid a'))
                    ^ ".")))
    let rec checkSubgoals =
      function
      | (G0, Q0, Rl, Vs, n,
         (Decl (g, (Dec (_, V') as D)), Decl (Q, And occ))) ->
          let _ = checkGoal (G0, Q0, Rl, (V', (I.Shift (n + 1))), Vs, occ) in
          let RO = getROrder (G0, Q0, (V', (I.Shift (n + 1))), occ) in
          let Rl' = match RO with | NONE -> Rl | SOME (O) -> O :: Rl in
          checkSubgoals (G0, Q0, Rl', Vs, (n + 1), (g, Q))
      | (G0, Q0, Rl, Vs, n, (Decl (g, D), Decl (Q, C.Exist))) ->
          checkSubgoals (G0, Q0, Rl, Vs, (n + 1), (g, Q))
      | (G0, Q0, Rl, Vs, n, (Decl (g, D), Decl (Q, C.All))) ->
          checkSubgoals (G0, Q0, Rl, Vs, (n + 1), (g, Q))
      | (G0, Q0, Rl, Vs, n, (I.Null, I.Null)) -> ()
    let rec checkClause (GQR, g, Q, Vs, occ) =
      checkClauseW (GQR, g, Q, (Whnf.whnf Vs), occ)
    let rec checkClauseW =
      function
      | (GQR, g, Q, (Pi ((D, I.Maybe), V), s), occ) ->
          checkClause
            (GQR, (I.Decl (g, (N.decEName (g, (I.decSub (D, s)))))),
              (I.Decl (Q, C.Exist)), (V, (I.dot1 s)), (P.body occ))
      | (GQR, g, Q, (Pi (((Dec (_, V1) as D), I.No), V2), s), occ) ->
          checkClause
            (GQR, (I.Decl (g, (I.decSub (D, s)))),
              (I.Decl (Q, (C.And (P.label occ)))), (V2, (I.dot1 s)),
              (P.body occ))
      | (((G0, Q0, Rl) as GQR), g, Q, ((Root (Const a, S), s) as Vs), occ) ->
          let n = I.ctxLength g in
          let Rl' = C.shiftRCtx Rl (function | s -> I.comp (s, (I.Shift n))) in
          checkSubgoals
            ((concat (G0, g)), (concat (Q0, Q)), Rl', Vs, 0, (g, Q))
      | (GQR, g, Q, (Root (Def a, S), s), occ) ->
          raise
            (Error'
               (occ,
                 (((^) ("Termination checking for defined type families not yet available:\n"
                          ^ "Illegal use of ")
                     N.qidToString (N.constQid a))
                    ^ ".")))
    let rec checkClause' (Vs, occ) =
      checkClause ((I.Null, I.Null, nil), I.Null, I.Null, Vs, occ)
    let rec checkRGoal (g, Q, Rl, Vs, occ) =
      checkRGoalW (g, Q, Rl, (Whnf.whnf Vs), occ)
    let rec checkRGoalW =
      function
      | (g, Q, Rl, ((Root (Const a, S), s) as Vs), occ) -> ()
      | (g, Q, Rl, (Pi ((D, I.Maybe), V), s), occ) ->
          checkRGoal
            ((I.Decl (g, (N.decLUName (g, (I.decSub (D, s)))))),
              (I.Decl (Q, C.All)),
              (C.shiftRCtx Rl (function | s -> I.comp (s, I.shift))),
              (V, (I.dot1 s)), (P.body occ))
      | (g, Q, Rl, (Pi (((Dec (_, V1) as D), I.No), V2), s), occ) ->
          (checkRClause (g, Q, Rl, (V1, s), (P.label occ));
           checkRGoal
             (g, Q, Rl, (V2, (I.comp (I.invShift, s))), (P.body occ)))
      | (g, Q, Rl, (Root (Def a, S), s), occ) ->
          raise
            (Error'
               (occ,
                 (((^) ("Reduction checking for defined type families not yet available:\n"
                          ^ "Illegal use of ")
                     N.qidToString (N.constQid a))
                    ^ ".")))
    let rec checkRImp (g, Q, Rl, Vs, Vs', occ) =
      checkRImpW (g, Q, Rl, (Whnf.whnf Vs), Vs', occ)
    let rec checkRImpW =
      function
      | (g, Q, Rl, (Pi ((D', I.Maybe), V'), s'), (V, s), occ) ->
          checkRImp
            ((I.Decl (g, (N.decEName (g, (I.decSub (D', s')))))),
              (I.Decl (Q, C.Exist)),
              (C.shiftRCtx Rl (function | s -> I.comp (s, I.shift))),
              (V', (I.dot1 s')), (V, (I.comp (s, I.shift))), occ)
      | (g, Q, Rl, (Pi (((Dec (_, V1) as D'), I.No), V2), s'), (V, s), occ)
          ->
          let Rl' =
            match getROrder (g, Q, (V1, s'), occ) with
            | NONE -> Rl
            | SOME (O) -> O :: Rl in
          checkRImp (g, Q, Rl', (V2, (I.comp (I.invShift, s'))), (V, s), occ)
      | (g, Q, Rl, ((Root (Const a, S), s) as Vs'), Vs, occ) ->
          checkRGoal (g, Q, Rl, Vs, occ)
      | (g, Q, Rl, ((Root (Def a, S), s) as Vs'), Vs, occ) ->
          raise
            (Error'
               (occ,
                 (((^) ("Reduction checking for defined type families not yet available:\n"
                          ^ "Illegal use of ")
                     N.qidToString (N.constQid a))
                    ^ ".")))
    let rec checkRClause (g, Q, Rl, Vs, occ) =
      checkRClauseW (g, Q, Rl, (Whnf.whnf Vs), occ)
    let rec checkRClauseW =
      function
      | (g, Q, Rl, (Pi ((D, I.Maybe), V), s), occ) ->
          checkRClause
            ((I.Decl (g, (N.decEName (g, (I.decSub (D, s)))))),
              (I.Decl (Q, C.Exist)),
              (C.shiftRCtx Rl (function | s -> I.comp (s, I.shift))),
              (V, (I.dot1 s)), (P.body occ))
      | (g, Q, Rl, (Pi (((Dec (_, V1) as D), I.No), V2), s), occ) ->
          let g' = I.Decl (g, (I.decSub (D, s))) in
          let Q' = I.Decl (Q, C.Exist) in
          let Rl' = C.shiftRCtx Rl (function | s -> I.comp (s, I.shift)) in
          let Rl'' =
            match getROrder (g', Q', (V1, (I.comp (s, I.shift))), occ) with
            | NONE -> Rl'
            | SOME (O) -> O :: Rl' in
          (checkRClause (g', Q', Rl'', (V2, (I.dot1 s)), (P.body occ));
           checkRImp
             (g', Q', Rl'', (V2, (I.dot1 s)), (V1, (I.comp (s, I.shift))),
               (P.label occ)))
      | (g, Q, Rl, ((Root (Const a, S), s) as Vs), occ) ->
          let RO =
            match selectROrder (a, (S, s)) with
            | NONE ->
                raise
                  (Error'
                     (occ,
                       (((^) "No reduction order assigned for " N.qidToString
                           (N.constQid a))
                          ^ ".")))
            | SOME (O) -> O in
          let _ =
            if (!Global.chatter) > 4
            then
              print
                (((^) (((^) "Verifying reduction property:\n" rlistToString
                          (g, Rl))
                         ^ " ---> ")
                    orderToString (g, RO))
                   ^ " \n")
            else () in
          if C.deduce (g, Q, Rl, RO)
          then ()
          else
            raise
              (Error'
                 (occ,
                   ((^) (((^) "Reduction violation:\n" rlistToString (g, Rl))
                           ^ " ---> ")
                      orderToString (g, RO))))
      | (g, Q, Rl, ((Root (Def a, S), s) as VS), occ) ->
          raise
            (Error'
               (occ,
                 (((^) ("Reduction checking for defined type families not yet available:\n"
                          ^ "Illegal use of ")
                     N.qidToString (N.constQid a))
                    ^ ".")))
    let rec checkFamReduction a =
      let checkFam' =
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
      let checkFam' =
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
    let ((reset)(*--------------------------------------------------------------------*)
      (* Printing *)(*--------------------------------------------------------------------*)
      (* select (c, (S, s)) = P

      select parameters according to termination order

      Invariant:
      If   . |- c : V   g |- s : g'    g' |- S : V > type
      and  V = {x1:V1} ... {xn:Vn} type.
      then P = u1[s1] .. Un[sn] is parameter select of S[s] according to sel (c)
      and  g |- si : Gi  Gi |- Ui : Vi
      and  g |- Vi[s]  == V[si] : type   forall 1<=i<=n
    *)
      (* selectROrder (c, (S, s)) = P

       select parameters according to reduction order

       Invariant:
       If   . |- c : V   g |- s : g'    g' |- S : V > type
       and  V = {x1:V1} ... {xn:Vn} type.
       then P = u1[s1] .. Un[sn] is parameter select of S[s] according to sel (c)
       and  g |- si : Gi  Gi |- Ui : Vi
       and  g |- Vi[s]  == V[si] : type   forall 1<=i<=n
    *)
      (*--------------------------------------------------------------*)
      (* abstractRO (g, D, RO) = Pi D. RO
       Invariant:

       If  g, D |- RO
       then  g |- Pi D . RO

    *)
      (* getROrder (g, Q, (V, s)) = O
       If g: Q
       and  g |- s : G1    and   G1 |- V : L
       then O is the reduction order associated to V[s]
       and  g |- O

     *)
      (*--------------------------------------------------------------------*)
      (* Termination Checker *)(* checkGoal (G0, Q0, Rl, (V, s), (V', s'), occ) = ()

       Invariant:
       If   G0 : Q0
       and  G0 |- s : G1     and   G1 |- V : L     (V, s) in whnf
       and  V[s], V'[s'] does not contain Skolem constants
       and  G0 |- s' : G2    and   G2 |- V' : L'   (V', s') in whnf
       and  V' = a' @ S'
       and  g |- L = L'
       and  V[s] < V'[s']  (< termination ordering)
         then ()
       else Error is raised.
    *)
      (* only if a terminates? *)(* always succeeds? -fp *)
      (* always succeeds? -fp *)(* checkSubgoals (G0, Q0, Rl, Vs, n, (g, Q), Vs, occ)

      if    G0 |- Q0
       and  G0 |- s : G1    and   G1 |- V : L
       and  V[s] does not contain any skolem constants
       and  Rl is a list of reduction propositions
       and  G0 |- Rl
       and  G0 |- V[s]
       and  G0 = G0', g' where g' <= g
       and  n = |g'| - |g|
       and  G0 |- g[^n]
       and  g |- Q
     and
       V[s] satisfies the associated termination order

     *)
      (* checkClause (GQR as (G0, Q0, Rl), g, Q, Vs, occ)

      if   G0, g |- Q0, Q
       and  G0, g |- s : G1    and   G1 |- V : L
       and  V[s] does not contain any skolem constants
       and  Rl is a list of reduction propositions
       and  G0, g |- Rl
       and  G0, g |- V[s]
     and
       V[s] satisfies the associated termination order
     *)
      (*-------------------------------------------------------------------*)
      (* Reduction Checker *)(* checkRGoal (g, Q, Rl, (V1, s1), occ) = Rl''

       Invariant
       If   g : Q
       and  g |- s1 : G1   and   G1 |- V1 : type
       and  V1[s1], V2[s2] does not contain Skolem constants
       and  g |- s2 : G2   and   G2 |- V2 : type
       and occ locates V1 in declaration
       and Rl is a context of reduction predicates
       and  g |- Rl
       and Rl implies that V1[s1] satisfies its associated reduction order

     *)
      (* trivial *)(* checkRImp (g, Q, Rl, (V1, s1), (V2, s2), occ) = ()

       Invariant
       If   g : Q
       and  g |- s1 : G1   and   G1 |- V1 : type
       and  V1[s1], V2[s2] does not contain Skolem constants
       and  g |- s2 : G2   and   G2 |- V2 : type
       and occ locates V1 in declaration
       and Rl is a context for derived reduction order assumptions
       and g |- Rl

       then Rl implies that  V2[s2] satisfies its associated reduction order
            with respect to V1[s1]
    *)
      (* checkRClause (g, Q, Rl, (V, s)) = ()

       Invariant:
       If g: Q
       and  g |- s : G1    and   G1 |- V : L
       and  V[s] does not contain any Skolem constants
       and  Rl is a context of reduction predicates
       and  g |- Rl
       then Rl implies that V[s] satifies the reduction order
    *)
      (* N.decEName (g, I.decSub (D, s)) *)(* will not be used *)
      (* rename ctx ??? *)(* checkFamReduction a = ()

       Invariant:
       a is name of type family in the signature
       raises invariant, if clauses for a does not fulfill
       specified reducation property

       Note: checking reduction is a separate property of termination
    *)
      (* reuse variable names when tracing *)(* reuse variable names when tracing *)
      (* checkFam a = ()

       Invariant:
       a is name of type family in the signature
       raises invariant, if clauses for a do not terminate
       according to specified termination order

       Note: termination checking takes into account proven
             reduction properties.
    *)
      (* reuse variable names when tracing *)(* reuse variable names when tracing *))
      = reset
    let checkFamReduction = checkFamReduction
    let checkFam = checkFam
  end ;;
