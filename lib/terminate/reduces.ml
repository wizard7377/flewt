
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
      | (fileName, NONE) -> raise (Error ((fileName ^ ":") ^ msg))
      | (fileName, SOME occDec) ->
          raise
            (Error
               (P.wrapLoc'
                  ((P.Loc (fileName, (P.occToRegionDec occDec occ))),
                    (Origins.linesInfoLookup fileName), msg)))
    let rec concat =
      function
      | (G', I.Null) -> G'
      | (G', Decl (G, D)) -> I.Decl ((concat (G', G)), D)
    let rec fmtOrder (G, O) =
      let rec fmtOrder' =
        function
        | Arg (((U, s) as Us), ((V, s') as Vs)) ->
            F.Hbox
              [F.String "("; Print.formatExp (G, (I.EClo Us)); F.String ")"]
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
    let rec fmtComparison (G, O, comp, O') =
      F.HOVbox0 1 0 1
        [fmtOrder (G, O); F.Break; F.String comp; F.Break; fmtOrder (G, O')]
    let rec fmtPredicate =
      function
      | (G, Less (O, O')) -> fmtComparison (G, O, "<", O')
      | (G, Leq (O, O')) -> fmtComparison (G, O, "<=", O')
      | (G, Eq (O, O')) -> fmtComparison (G, O, "=", O')
      | (G, Pi (D, P)) ->
          F.Hbox [F.String "Pi "; fmtPredicate ((I.Decl (G, D)), P)]
    let rec rlistToString' =
      function
      | (G, nil) -> ""
      | (G, (P)::[]) -> F.makestring_fmt (fmtPredicate (G, P))
      | (G, (P)::Rl) ->
          (^) ((F.makestring_fmt (fmtPredicate (G, P))) ^ " ,")
            rlistToString' (G, Rl)
    let rec rlistToString (G, Rl) = rlistToString' ((Names.ctxName G), Rl)
    let rec orderToString (G, P) =
      F.makestring_fmt (fmtPredicate ((Names.ctxName G), P))
    let rec select (c, (S, s)) =
      let SO = R.selLookup c in
      let Vid = ((I.constType c), I.id) in
      let rec select'' (n, (Ss', Vs'')) =
        select''W (n, (Ss', (Whnf.whnf Vs'')))
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
      let rec select' =
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
      let rec select'' (n, (Ss', Vs'')) =
        select''W (n, (Ss', (Whnf.whnf Vs'')))
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
      let rec select' =
        function
        | Arg n -> R.Arg (select'' (n, ((S, s), Vid)))
        | Lex (L) -> R.Lex (map select' L)
        | Simul (L) -> R.Simul (map select' L) in
      let rec selectP =
        function
        | Less (O1, O2) -> C.Less ((select' O1), (select' O2))
        | Leq (O1, O2) -> C.Leq ((select' O1), (select' O2))
        | Eq (O1, O2) -> C.Eq ((select' O1), (select' O2)) in
      try SOME (selectP (R.selLookupROrder c)) with | Error s -> NONE
    let rec abstractRO (G, D, O) = C.Pi (D, O)
    let rec getROrder (G, Q, Vs, occ) =
      getROrderW (G, Q, (Whnf.whnf Vs), occ)
    let rec getROrderW =
      function
      | (G, Q, ((Root (Const a, S), s) as Vs), occ) ->
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
                        orderToString (G, O))
                       ^ "\n")
                else () in
          O
      | (G, Q, (Pi ((D, I.Maybe), V), s), occ) ->
          let O =
            getROrder
              ((I.Decl (G, (N.decLUName (G, (I.decSub (D, s)))))),
                (I.Decl (Q, C.All)), (V, (I.dot1 s)), (P.body occ)) in
          (match O with
           | NONE -> NONE
           | SOME (O') -> SOME (abstractRO (G, (I.decSub (D, s)), O')))
      | (G, Q, (Pi (((Dec (_, V1) as D), I.No), V2), s), occ) ->
          let O =
            getROrder (G, Q, (V2, (I.comp (I.invShift, s))), (P.body occ)) in
          (match O with | NONE -> NONE | SOME (O') -> SOME O')
      | (G, Q, ((Root (Def a, S), s) as Vs), occ) ->
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
          let rec lookup =
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
         (Decl (G, (Dec (_, V') as D)), Decl (Q, And occ))) ->
          let _ = checkGoal (G0, Q0, Rl, (V', (I.Shift (n + 1))), Vs, occ) in
          let RO = getROrder (G0, Q0, (V', (I.Shift (n + 1))), occ) in
          let Rl' = match RO with | NONE -> Rl | SOME (O) -> O :: Rl in
          checkSubgoals (G0, Q0, Rl', Vs, (n + 1), (G, Q))
      | (G0, Q0, Rl, Vs, n, (Decl (G, D), Decl (Q, C.Exist))) ->
          checkSubgoals (G0, Q0, Rl, Vs, (n + 1), (G, Q))
      | (G0, Q0, Rl, Vs, n, (Decl (G, D), Decl (Q, C.All))) ->
          checkSubgoals (G0, Q0, Rl, Vs, (n + 1), (G, Q))
      | (G0, Q0, Rl, Vs, n, (I.Null, I.Null)) -> ()
    let rec checkClause (GQR, G, Q, Vs, occ) =
      checkClauseW (GQR, G, Q, (Whnf.whnf Vs), occ)
    let rec checkClauseW =
      function
      | (GQR, G, Q, (Pi ((D, I.Maybe), V), s), occ) ->
          checkClause
            (GQR, (I.Decl (G, (N.decEName (G, (I.decSub (D, s)))))),
              (I.Decl (Q, C.Exist)), (V, (I.dot1 s)), (P.body occ))
      | (GQR, G, Q, (Pi (((Dec (_, V1) as D), I.No), V2), s), occ) ->
          checkClause
            (GQR, (I.Decl (G, (I.decSub (D, s)))),
              (I.Decl (Q, (C.And (P.label occ)))), (V2, (I.dot1 s)),
              (P.body occ))
      | (((G0, Q0, Rl) as GQR), G, Q, ((Root (Const a, S), s) as Vs), occ) ->
          let n = I.ctxLength G in
          let Rl' = C.shiftRCtx Rl (function | s -> I.comp (s, (I.Shift n))) in
          checkSubgoals
            ((concat (G0, G)), (concat (Q0, Q)), Rl', Vs, 0, (G, Q))
      | (GQR, G, Q, (Root (Def a, S), s), occ) ->
          raise
            (Error'
               (occ,
                 (((^) ("Termination checking for defined type families not yet available:\n"
                          ^ "Illegal use of ")
                     N.qidToString (N.constQid a))
                    ^ ".")))
    let rec checkClause' (Vs, occ) =
      checkClause ((I.Null, I.Null, nil), I.Null, I.Null, Vs, occ)
    let rec checkRGoal (G, Q, Rl, Vs, occ) =
      checkRGoalW (G, Q, Rl, (Whnf.whnf Vs), occ)
    let rec checkRGoalW =
      function
      | (G, Q, Rl, ((Root (Const a, S), s) as Vs), occ) -> ()
      | (G, Q, Rl, (Pi ((D, I.Maybe), V), s), occ) ->
          checkRGoal
            ((I.Decl (G, (N.decLUName (G, (I.decSub (D, s)))))),
              (I.Decl (Q, C.All)),
              (C.shiftRCtx Rl (function | s -> I.comp (s, I.shift))),
              (V, (I.dot1 s)), (P.body occ))
      | (G, Q, Rl, (Pi (((Dec (_, V1) as D), I.No), V2), s), occ) ->
          (checkRClause (G, Q, Rl, (V1, s), (P.label occ));
           checkRGoal
             (G, Q, Rl, (V2, (I.comp (I.invShift, s))), (P.body occ)))
      | (G, Q, Rl, (Root (Def a, S), s), occ) ->
          raise
            (Error'
               (occ,
                 (((^) ("Reduction checking for defined type families not yet available:\n"
                          ^ "Illegal use of ")
                     N.qidToString (N.constQid a))
                    ^ ".")))
    let rec checkRImp (G, Q, Rl, Vs, Vs', occ) =
      checkRImpW (G, Q, Rl, (Whnf.whnf Vs), Vs', occ)
    let rec checkRImpW =
      function
      | (G, Q, Rl, (Pi ((D', I.Maybe), V'), s'), (V, s), occ) ->
          checkRImp
            ((I.Decl (G, (N.decEName (G, (I.decSub (D', s')))))),
              (I.Decl (Q, C.Exist)),
              (C.shiftRCtx Rl (function | s -> I.comp (s, I.shift))),
              (V', (I.dot1 s')), (V, (I.comp (s, I.shift))), occ)
      | (G, Q, Rl, (Pi (((Dec (_, V1) as D'), I.No), V2), s'), (V, s), occ)
          ->
          let Rl' =
            match getROrder (G, Q, (V1, s'), occ) with
            | NONE -> Rl
            | SOME (O) -> O :: Rl in
          checkRImp (G, Q, Rl', (V2, (I.comp (I.invShift, s'))), (V, s), occ)
      | (G, Q, Rl, ((Root (Const a, S), s) as Vs'), Vs, occ) ->
          checkRGoal (G, Q, Rl, Vs, occ)
      | (G, Q, Rl, ((Root (Def a, S), s) as Vs'), Vs, occ) ->
          raise
            (Error'
               (occ,
                 (((^) ("Reduction checking for defined type families not yet available:\n"
                          ^ "Illegal use of ")
                     N.qidToString (N.constQid a))
                    ^ ".")))
    let rec checkRClause (G, Q, Rl, Vs, occ) =
      checkRClauseW (G, Q, Rl, (Whnf.whnf Vs), occ)
    let rec checkRClauseW =
      function
      | (G, Q, Rl, (Pi ((D, I.Maybe), V), s), occ) ->
          checkRClause
            ((I.Decl (G, (N.decEName (G, (I.decSub (D, s)))))),
              (I.Decl (Q, C.Exist)),
              (C.shiftRCtx Rl (function | s -> I.comp (s, I.shift))),
              (V, (I.dot1 s)), (P.body occ))
      | (G, Q, Rl, (Pi (((Dec (_, V1) as D), I.No), V2), s), occ) ->
          let G' = I.Decl (G, (I.decSub (D, s))) in
          let Q' = I.Decl (Q, C.Exist) in
          let Rl' = C.shiftRCtx Rl (function | s -> I.comp (s, I.shift)) in
          let Rl'' =
            match getROrder (G', Q', (V1, (I.comp (s, I.shift))), occ) with
            | NONE -> Rl'
            | SOME (O) -> O :: Rl' in
          (checkRClause (G', Q', Rl'', (V2, (I.dot1 s)), (P.body occ));
           checkRImp
             (G', Q', Rl'', (V2, (I.dot1 s)), (V1, (I.comp (s, I.shift))),
               (P.label occ)))
      | (G, Q, Rl, ((Root (Const a, S), s) as Vs), occ) ->
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
                          (G, Rl))
                         ^ " ---> ")
                    orderToString (G, RO))
                   ^ " \n")
            else () in
          if C.deduce (G, Q, Rl, RO)
          then ()
          else
            raise
              (Error'
                 (occ,
                   ((^) (((^) "Reduction violation:\n" rlistToString (G, Rl))
                           ^ " ---> ")
                      orderToString (G, RO))))
      | (G, Q, Rl, ((Root (Def a, S), s) as VS), occ) ->
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
      If   . |- c : V   G |- s : G'    G' |- S : V > type
      and  V = {x1:V1} ... {xn:Vn} type.
      then P = U1[s1] .. Un[sn] is parameter select of S[s] according to sel (c)
      and  G |- si : Gi  Gi |- Ui : Vi
      and  G |- Vi[s]  == V[si] : type   forall 1<=i<=n
    *)
    (* selectROrder (c, (S, s)) = P

       select parameters according to reduction order

       Invariant:
       If   . |- c : V   G |- s : G'    G' |- S : V > type
       and  V = {x1:V1} ... {xn:Vn} type.
       then P = U1[s1] .. Un[sn] is parameter select of S[s] according to sel (c)
       and  G |- si : Gi  Gi |- Ui : Vi
       and  G |- Vi[s]  == V[si] : type   forall 1<=i<=n
    *)
    (*--------------------------------------------------------------*)
    (* abstractRO (G, D, RO) = Pi D. RO
       Invariant:

       If  G, D |- RO
       then  G |- Pi D . RO

    *)
    (* getROrder (G, Q, (V, s)) = O
       If G: Q
       and  G |- s : G1    and   G1 |- V : L
       then O is the reduction order associated to V[s]
       and  G |- O

     *)
    (*--------------------------------------------------------------------*)
    (* Termination Checker *)
    (* checkGoal (G0, Q0, Rl, (V, s), (V', s'), occ) = ()

       Invariant:
       If   G0 : Q0
       and  G0 |- s : G1     and   G1 |- V : L     (V, s) in whnf
       and  V[s], V'[s'] does not contain Skolem constants
       and  G0 |- s' : G2    and   G2 |- V' : L'   (V', s') in whnf
       and  V' = a' @ S'
       and  G |- L = L'
       and  V[s] < V'[s']  (< termination ordering)
         then ()
       else Error is raised.
    *)
    (* only if a terminates? *)
    (* always succeeds? -fp *)
    (* always succeeds? -fp *)
    (* checkSubgoals (G0, Q0, Rl, Vs, n, (G, Q), Vs, occ)

      if    G0 |- Q0
       and  G0 |- s : G1    and   G1 |- V : L
       and  V[s] does not contain any skolem constants
       and  Rl is a list of reduction propositions
       and  G0 |- Rl
       and  G0 |- V[s]
       and  G0 = G0', G' where G' <= G
       and  n = |G'| - |G|
       and  G0 |- G[^n]
       and  G |- Q
     and
       V[s] satisfies the associated termination order

     *)
    (* checkClause (GQR as (G0, Q0, Rl), G, Q, Vs, occ)

      if   G0, G |- Q0, Q
       and  G0, G |- s : G1    and   G1 |- V : L
       and  V[s] does not contain any skolem constants
       and  Rl is a list of reduction propositions
       and  G0, G |- Rl
       and  G0, G |- V[s]
     and
       V[s] satisfies the associated termination order
     *)
    (*-------------------------------------------------------------------*)
    (* Reduction Checker *)
    (* checkRGoal (G, Q, Rl, (V1, s1), occ) = Rl''

       Invariant
       If   G : Q
       and  G |- s1 : G1   and   G1 |- V1 : type
       and  V1[s1], V2[s2] does not contain Skolem constants
       and  G |- s2 : G2   and   G2 |- V2 : type
       and occ locates V1 in declaration
       and Rl is a context of reduction predicates
       and  G |- Rl
       and Rl implies that V1[s1] satisfies its associated reduction order

     *)
    (* trivial *)
    (* checkRImp (G, Q, Rl, (V1, s1), (V2, s2), occ) = ()

       Invariant
       If   G : Q
       and  G |- s1 : G1   and   G1 |- V1 : type
       and  V1[s1], V2[s2] does not contain Skolem constants
       and  G |- s2 : G2   and   G2 |- V2 : type
       and occ locates V1 in declaration
       and Rl is a context for derived reduction order assumptions
       and G |- Rl

       then Rl implies that  V2[s2] satisfies its associated reduction order
            with respect to V1[s1]
    *)
    (* checkRClause (G, Q, Rl, (V, s)) = ()

       Invariant:
       If G: Q
       and  G |- s : G1    and   G1 |- V : L
       and  V[s] does not contain any Skolem constants
       and  Rl is a context of reduction predicates
       and  G |- Rl
       then Rl implies that V[s] satifies the reduction order
    *)
    (* N.decEName (G, I.decSub (D, s)) *)
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
