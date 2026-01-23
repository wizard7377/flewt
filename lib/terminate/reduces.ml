module type REDUCES  =
  sig
    exception Error of string 
    val reset : unit -> unit
    val checkFamReduction : IntSyn.cid -> unit
    val checkFam : IntSyn.cid -> unit
  end


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
    let rec error (c, occ, msg) =
      begin match Origins.originLookup c with
      | (fileName, None) -> raise (Error ((fileName ^ ":") ^ msg))
      | (fileName, Some occDec) ->
          raise
            (Error
               (P.wrapLoc'
                  ((P.Loc (fileName, (P.occToRegionDec occDec occ))),
                    (Origins.linesInfoLookup fileName), msg))) end
    let rec concat =
      begin function
      | (g'_, I.Null) -> g'_
      | (g'_, Decl (g_, d_)) -> I.Decl ((concat (g'_, g_)), d_) end
  let rec fmtOrder (g_, o_) =
    let rec fmtOrder' =
      begin function
      | Arg (((u_, s) as us_), ((v_, s') as vs_)) ->
          F.Hbox
            [F.String "("; Print.formatExp (g_, (I.EClo us_)); F.String ")"]
      | Lex (l_) ->
          F.Hbox [F.String "{"; F.HOVbox0 1 0 1 (fmtOrders l_); F.String "}"]
      | Simul (l_) ->
          F.Hbox [F.String "["; F.HOVbox0 1 0 1 (fmtOrders l_); F.String "]"] end
      and fmtOrders =
        begin function
        | [] -> []
        | (o_)::[] -> (fmtOrder' o_) :: []
        | (o_)::l_ -> (::) ((fmtOrder' o_) :: F.Break) fmtOrders l_ end in
  fmtOrder' o_
let rec fmtComparison (g_, o_, comp, o'_) =
  F.HOVbox0 1 0 1
    [fmtOrder (g_, o_); F.Break; F.String comp; F.Break; fmtOrder (g_, o'_)]
let rec fmtPredicate =
  begin function
  | (g_, Less (o_, o'_)) -> fmtComparison (g_, o_, "<", o'_)
  | (g_, Leq (o_, o'_)) -> fmtComparison (g_, o_, "<=", o'_)
  | (g_, Eq (o_, o'_)) -> fmtComparison (g_, o_, "=", o'_)
  | (g_, Pi (d_, p_)) ->
      F.Hbox [F.String "Pi "; fmtPredicate ((I.Decl (g_, d_)), p_)] end
let rec rlistToString' =
  begin function
  | (g_, []) -> ""
  | (g_, (p_)::[]) -> F.makestring_fmt (fmtPredicate (g_, p_))
  | (g_, (p_)::Rl) ->
      (^) ((F.makestring_fmt (fmtPredicate (g_, p_))) ^ " ,") rlistToString'
        (g_, Rl) end
let rec rlistToString (g_, Rl) = rlistToString' ((Names.ctxName g_), Rl)
let rec orderToString (g_, p_) =
  F.makestring_fmt (fmtPredicate ((Names.ctxName g_), p_))
let rec select (c, (s_, s)) =
  let SO = R.selLookup c in
  let Vid = ((I.constType c), I.id) in
  let rec select'' (n, (ss'_, Vs'')) =
    select''W (n, (ss'_, (Whnf.whnf Vs'')))
  and select''W =
    begin function
    | (1, ((App (u'_, s'_), s'), (Pi ((Dec (_, V''), _), _), s''))) ->
        ((u'_, s'), (V'', s''))
    | (n, ((SClo (s'_, s1'), s2'), Vs'')) ->
        select''W (n, ((s'_, (I.comp (s1', s2'))), Vs''))
    | (n, ((App (u'_, s'_), s'), (Pi ((Dec (_, V1''), _), V2''), s''))) ->
        select''
          ((n - 1),
            ((s'_, s'), (V2'', (I.Dot ((I.Exp (I.EClo (u'_, s'))), s''))))) end in
  let rec select' =
    begin function
    | Arg n -> R.Arg (select'' (n, ((s_, s), Vid)))
    | Lex (l_) -> R.Lex (map select' l_)
    | Simul (l_) -> R.Simul (map select' l_) end in
  select' (R.selLookup c)
let rec selectOcc (c, (s_, s), occ) =
  begin try select (c, (s_, s))
  with
  | Error msg ->
      raise
        (Error'
           (occ,
             ((^) "Termination violation: no order assigned for "
                N.qidToString (N.constQid c)))) end
let rec selectROrder (c, (s_, s)) =
  let Vid = ((I.constType c), I.id) in
  let rec select'' (n, (ss'_, Vs'')) =
    select''W (n, (ss'_, (Whnf.whnf Vs'')))
  and select''W =
    begin function
    | (1, ((App (u'_, s'_), s'), (Pi ((Dec (_, V''), _), _), s''))) ->
        ((u'_, s'), (V'', s''))
    | (n, ((SClo (s'_, s1'), s2'), Vs'')) ->
        select''W (n, ((s'_, (I.comp (s1', s2'))), Vs''))
    | (n, ((App (u'_, s'_), s'), (Pi ((Dec (_, V1''), _), V2''), s''))) ->
        select''
          ((n - 1),
            ((s'_, s'), (V2'', (I.Dot ((I.Exp (I.EClo (u'_, s'))), s''))))) end in
  let rec select' =
    begin function
    | Arg n -> R.Arg (select'' (n, ((s_, s), Vid)))
    | Lex (l_) -> R.Lex (map select' l_)
    | Simul (l_) -> R.Simul (map select' l_) end in
  let rec selectP =
    begin function
    | Less (o1_, o2_) -> C.Less ((select' o1_), (select' o2_))
    | Leq (o1_, o2_) -> C.Leq ((select' o1_), (select' o2_))
    | Eq (o1_, o2_) -> C.Eq ((select' o1_), (select' o2_)) end in
  begin try Some (selectP (R.selLookupROrder c)) with | Error s -> None end
let rec abstractRO (g_, d_, o_) = C.Pi (d_, o_)
let rec getROrder (g_, q_, vs_, occ) =
  getROrderW (g_, q_, (Whnf.whnf vs_), occ)
let rec getROrderW =
  begin function
  | (g_, q_, ((Root (Const a, s_), s) as vs_), occ) ->
      let o_ = selectROrder (a, (s_, s)) in
      let _ =
        begin match o_ with
        | None -> ()
        | Some (o_) ->
            if !Global.chatter > 5
            then
              begin print
                      (((^) (((^) "Reduction predicate for " N.qidToString
                                (N.constQid a))
                               ^ " added : ")
                          orderToString (g_, o_))
                         ^ "\n") end
            else begin () end end in
o_
| (g_, q_, (Pi ((d_, I.Maybe), v_), s), occ) ->
    let o_ =
      getROrder
        ((I.Decl (g_, (N.decLUName (g_, (I.decSub (d_, s)))))),
          (I.Decl (q_, C.All)), (v_, (I.dot1 s)), (P.body occ)) in
    (begin match o_ with
     | None -> None
     | Some (o'_) -> Some (abstractRO (g_, (I.decSub (d_, s)), o'_)) end)
| (g_, q_, (Pi (((Dec (_, v1_) as d_), I.No), v2_), s), occ) ->
    let o_ =
      getROrder (g_, q_, (v2_, (I.comp (I.invShift, s))), (P.body occ)) in
    (begin match o_ with | None -> None | Some (o'_) -> Some o'_ end)
| (g_, q_, ((Root (Def a, s_), s) as vs_), occ) ->
    raise
      (Error'
         (occ,
           (((^) ("Reduction checking for defined type families not yet available:\n"
                    ^ "Illegal use of ")
               N.qidToString (N.constQid a))
              ^ "."))) end
let rec checkGoal (g0_, q0_, Rl, vs_, vs'_, occ) =
  checkGoalW (g0_, q0_, Rl, (Whnf.whnf vs_), vs'_, occ)
let rec checkGoalW =
  begin function
  | (g0_, q0_, Rl, (Pi (((Dec (_, v1_) as d_), I.No), v2_), s), vs'_, occ) ->
      (begin checkClause
               ((g0_, q0_, Rl), I.Null, I.Null, (v1_, s), (P.label occ));
       checkGoal
         (g0_, q0_, Rl, (v2_, (I.comp (I.invShift, s))), vs'_, (P.body occ)) end)
  | (g0_, q0_, Rl, (Pi ((d_, I.Maybe), v_), s), (v'_, s'), occ) ->
      checkGoal
        ((I.Decl (g0_, (N.decLUName (g0_, (I.decSub (d_, s)))))),
          (I.Decl (q0_, C.All)),
          (C.shiftRCtx Rl (begin function | s -> I.comp (s, I.shift) end)),
        (v_, (I.dot1 s)), (v'_, (I.comp (s', I.shift))), (P.body occ))
  | (g0_, q0_, Rl, ((Root (Const a, s_), s) as vs_),
     ((Root (Const a', s'_), s') as vs'_), occ) ->
      let rec lookup =
        begin function
        | (R.Empty, f) -> R.Empty
        | ((LE (a, a's') as a's), f) -> if f a then begin a's end
            else begin lookup (a's', f) end
        | ((LT (a, a's') as a's), f) -> if f a then begin a's end
            else begin lookup (a's', f) end end in
let p_ = selectOcc (a, (s_, s), occ) in
let p'_ = select (a', (s'_, s')) in
let a's = Order.mutLookup a in
(((begin match lookup (a's, (begin function | x' -> x' = a' end)) with
| R.Empty -> ()
| LE _ ->
    (begin if !Global.chatter > 4
           then
             begin (begin print "Verifying termination order:\n";
                    print (rlistToString (g0_, Rl));
                    print
                      (((^) " ---> " orderToString (g0_, (C.Leq (p_, p'_))))
                         ^ "\n") end) end
    else begin () end;
if C.deduce (g0_, q0_, Rl, (C.Leq (p_, p'_))) then begin () end
else begin
  raise
    (Error'
       (occ,
         ((^) (((^) "Termination violation:\n" rlistToString (g0_, Rl)) ^
                 " ---> ")
            orderToString (g0_, (C.Leq (p_, p'_)))))) end end)
| LT _ ->
    (begin if !Global.chatter > 4
           then
             begin (begin print "Verifying termination order:\n";
                    print ((rlistToString (g0_, Rl)) ^ " ---> ");
                    print ((orderToString (g0_, (C.Less (p_, p'_)))) ^ "\n") end) end
    else begin () end;
if C.deduce (g0_, q0_, Rl, (C.Less (p_, p'_))) then begin () end
else begin
  raise
    (Error'
       (occ,
         ((^) (((^) "Termination violation:\n" rlistToString (g0_, Rl)) ^
                 " ---> ")
            orderToString (g0_, (C.Less (p_, p'_)))))) end end) end))
(* only if a terminates? *)(* always succeeds? -fp *)
(* always succeeds? -fp *))
| (g0_, q0_, Rl, ((Root (Def a, s_), s) as vs_), vs'_, occ) ->
    raise
      (Error'
         (occ,
           (((^) ("Reduction checking for defined type families not yet available:\n"
                    ^ "Illegal use of ")
               N.qidToString (N.constQid a))
              ^ ".")))
| (g0_, q0_, Rl, vs_, ((Root (Def a', s'_), s') as vs'_), occ) ->
    raise
      (Error'
         (occ,
           (((^) ("Reduction checking for defined type families not yet available:\n"
                    ^ "Illegal use of ")
               N.qidToString (N.constQid a'))
              ^ "."))) end
let rec checkSubgoals =
  begin function
  | (g0_, q0_, Rl, vs_, n,
     (Decl (g_, (Dec (_, v'_) as d_)), Decl (q_, And occ))) ->
      let _ = checkGoal (g0_, q0_, Rl, (v'_, (I.Shift (n + 1))), vs_, occ) in
      let RO = getROrder (g0_, q0_, (v'_, (I.Shift (n + 1))), occ) in
      let Rl' = begin match RO with | None -> Rl | Some (o_) -> o_ :: Rl end in
      checkSubgoals (g0_, q0_, Rl', vs_, (n + 1), (g_, q_))
  | (g0_, q0_, Rl, vs_, n, (Decl (g_, d_), Decl (q_, C.Exist))) ->
      checkSubgoals (g0_, q0_, Rl, vs_, (n + 1), (g_, q_))
  | (g0_, q0_, Rl, vs_, n, (Decl (g_, d_), Decl (q_, C.All))) ->
      checkSubgoals (g0_, q0_, Rl, vs_, (n + 1), (g_, q_))
  | (g0_, q0_, Rl, vs_, n, (I.Null, I.Null)) -> () end
let rec checkClause (GQR, g_, q_, vs_, occ) =
  checkClauseW (GQR, g_, q_, (Whnf.whnf vs_), occ)
let rec checkClauseW =
  begin function
  | (GQR, g_, q_, (Pi ((d_, I.Maybe), v_), s), occ) ->
      checkClause
        (GQR, (I.Decl (g_, (N.decEName (g_, (I.decSub (d_, s)))))),
          (I.Decl (q_, C.Exist)), (v_, (I.dot1 s)), (P.body occ))
  | (GQR, g_, q_, (Pi (((Dec (_, v1_) as d_), I.No), v2_), s), occ) ->
      checkClause
        (GQR, (I.Decl (g_, (I.decSub (d_, s)))),
          (I.Decl (q_, (C.And (P.label occ)))), (v2_, (I.dot1 s)),
          (P.body occ))
  | (((g0_, q0_, Rl) as GQR), g_, q_, ((Root (Const a, s_), s) as vs_), occ)
      ->
      let n = I.ctxLength g_ in
      let Rl' =
        C.shiftRCtx Rl (begin function | s -> I.comp (s, (I.Shift n)) end) in
      checkSubgoals
        ((concat (g0_, g_)), (concat (q0_, q_)), Rl', vs_, 0, (g_, q_))
  | (GQR, g_, q_, (Root (Def a, s_), s), occ) ->
      raise
        (Error'
           (occ,
             (((^) ("Termination checking for defined type families not yet available:\n"
                      ^ "Illegal use of ")
                 N.qidToString (N.constQid a))
                ^ "."))) end
let rec checkClause' (vs_, occ) =
  checkClause ((I.Null, I.Null, []), I.Null, I.Null, vs_, occ)
let rec checkRGoal (g_, q_, Rl, vs_, occ) =
  checkRGoalW (g_, q_, Rl, (Whnf.whnf vs_), occ)
let rec checkRGoalW =
  begin function
  | (g_, q_, Rl, ((Root (Const a, s_), s) as vs_), occ) -> ()
  | (g_, q_, Rl, (Pi ((d_, I.Maybe), v_), s), occ) ->
      checkRGoal
        ((I.Decl (g_, (N.decLUName (g_, (I.decSub (d_, s)))))),
          (I.Decl (q_, C.All)),
          (C.shiftRCtx Rl (begin function | s -> I.comp (s, I.shift) end)),
        (v_, (I.dot1 s)), (P.body occ))
  | (g_, q_, Rl, (Pi (((Dec (_, v1_) as d_), I.No), v2_), s), occ) ->
      (begin checkRClause (g_, q_, Rl, (v1_, s), (P.label occ));
       checkRGoal (g_, q_, Rl, (v2_, (I.comp (I.invShift, s))), (P.body occ)) end)
  | (g_, q_, Rl, (Root (Def a, s_), s), occ) ->
      raise
        (Error'
           (occ,
             (((^) ("Reduction checking for defined type families not yet available:\n"
                      ^ "Illegal use of ")
                 N.qidToString (N.constQid a))
                ^ "."))) end(* trivial *)
let rec checkRImp (g_, q_, Rl, vs_, vs'_, occ) =
  checkRImpW (g_, q_, Rl, (Whnf.whnf vs_), vs'_, occ)
let rec checkRImpW =
  begin function
  | (g_, q_, Rl, (Pi ((d'_, I.Maybe), v'_), s'), (v_, s), occ) ->
      checkRImp
        ((I.Decl (g_, (N.decEName (g_, (I.decSub (d'_, s')))))),
          (I.Decl (q_, C.Exist)),
          (C.shiftRCtx Rl (begin function | s -> I.comp (s, I.shift) end)),
        (v'_, (I.dot1 s')), (v_, (I.comp (s, I.shift))), occ)
  | (g_, q_, Rl, (Pi (((Dec (_, v1_) as d'_), I.No), v2_), s'), (v_, s), occ)
      ->
      let Rl' =
        begin match getROrder (g_, q_, (v1_, s'), occ) with
        | None -> Rl
        | Some (o_) -> o_ :: Rl end in
    checkRImp (g_, q_, Rl', (v2_, (I.comp (I.invShift, s'))), (v_, s), occ)
  | (g_, q_, Rl, ((Root (Const a, s_), s) as vs'_), vs_, occ) ->
      checkRGoal (g_, q_, Rl, vs_, occ)
  | (g_, q_, Rl, ((Root (Def a, s_), s) as vs'_), vs_, occ) ->
      raise
        (Error'
           (occ,
             (((^) ("Reduction checking for defined type families not yet available:\n"
                      ^ "Illegal use of ")
                 N.qidToString (N.constQid a))
                ^ "."))) end
let rec checkRClause (g_, q_, Rl, vs_, occ) =
  checkRClauseW (g_, q_, Rl, (Whnf.whnf vs_), occ)
let rec checkRClauseW =
  begin function
  | (g_, q_, Rl, (Pi ((d_, I.Maybe), v_), s), occ) ->
      checkRClause
        ((I.Decl (g_, (N.decEName (g_, (I.decSub (d_, s)))))),
          (I.Decl (q_, C.Exist)),
          (C.shiftRCtx Rl (begin function | s -> I.comp (s, I.shift) end)),
        (v_, (I.dot1 s)), (P.body occ))
  | (g_, q_, Rl, (Pi (((Dec (_, v1_) as d_), I.No), v2_), s), occ) ->
      let g'_ = I.Decl (g_, (I.decSub (d_, s))) in
      let q'_ = I.Decl (q_, C.Exist) in
      let Rl' =
        C.shiftRCtx Rl (begin function | s -> I.comp (s, I.shift) end) in
      let Rl'' =
        begin match getROrder (g'_, q'_, (v1_, (I.comp (s, I.shift))), occ)
              with
        | None -> Rl'
        | Some (o_) -> o_ :: Rl' end in
      (((begin checkRClause (g'_, q'_, Rl'', (v2_, (I.dot1 s)), (P.body occ));
         checkRImp
           (g'_, q'_, Rl'', (v2_, (I.dot1 s)), (v1_, (I.comp (s, I.shift))),
             (P.label occ)) end))
        (* N.decEName (G, I.decSub (D, s)) *)(* will not be used *))
| (g_, q_, Rl, ((Root (Const a, s_), s) as vs_), occ) ->
    let RO =
      begin match selectROrder (a, (s_, s)) with
      | None ->
          raise
            (Error'
               (occ,
                 (((^) "No reduction order assigned for " N.qidToString
                     (N.constQid a))
                    ^ ".")))
      | Some (o_) -> o_ end in
  let _ =
    if !Global.chatter > 4
    then
      begin print
              (((^) (((^) "Verifying reduction property:\n" rlistToString
                        (g_, Rl))
                       ^ " ---> ")
                  orderToString (g_, RO))
                 ^ " \n") end
    else begin () end in if C.deduce (g_, q_, Rl, RO) then begin () end
else begin
  raise
    (Error'
       (occ,
         (((^) (((^) "Reduction violation:\n" rlistToString (g_, Rl)) ^
                  " ---> ")
             orderToString (g_, RO))(* rename ctx ??? *)))) end
| (g_, q_, Rl, ((Root (Def a, s_), s) as VS), occ) ->
    raise
      (Error'
         (occ,
           (((^) ("Reduction checking for defined type families not yet available:\n"
                    ^ "Illegal use of ")
               N.qidToString (N.constQid a))
              ^ "."))) end
let rec checkFamReduction a =
  let rec checkFam' =
    begin function
    | [] ->
        (begin if !Global.chatter > 3 then begin print "\n" end
         else begin () end;
    () end)
  | (Const b)::bs ->
      (((begin if !Global.chatter > 3
               then begin print ((N.qidToString (N.constQid b)) ^ " ") end
         else begin () end;
  if !Global.chatter > 4
  then begin (begin N.varReset IntSyn.Null; print "\n" end) end
  else begin () end;
(begin try checkRClause (I.Null, I.Null, [], ((I.constType b), I.id), P.top)
 with | Error' (occ, msg) -> error (b, occ, msg)
 | Error msg -> raise (Error msg) end); checkFam' bs end))
(* reuse variable names when tracing *))
| (Def d)::bs ->
    (((begin if !Global.chatter > 3
             then begin print ((N.qidToString (N.constQid d)) ^ " ") end
       else begin () end;
if !Global.chatter > 4
then begin (begin N.varReset IntSyn.Null; print "\n" end) end
else begin () end;
(begin try checkRClause (I.Null, I.Null, [], ((I.constType d), I.id), P.top)
 with | Error' (occ, msg) -> error (d, occ, msg)
 | Error msg -> raise (Error msg) end); checkFam' bs end))
(* reuse variable names when tracing *)) end in
let _ =
if !Global.chatter > 3
then
  begin print
          (((^) "Reduction checking family " N.qidToString (N.constQid a)) ^
             ":\n") end
else begin () end in
checkFam' (Index.lookup a)
let rec checkFam a =
  let rec checkFam' =
    begin function
    | [] ->
        (begin if !Global.chatter > 3 then begin print "\n" end
         else begin () end;
    () end)
  | (Const b)::bs ->
      (((begin if !Global.chatter > 3
               then begin print ((N.qidToString (N.constQid b)) ^ " ") end
         else begin () end;
  if !Global.chatter > 4
  then begin (begin N.varReset IntSyn.Null; print "\n" end) end
  else begin () end;
(begin try checkClause' (((I.constType b), I.id), P.top)
 with | Error' (occ, msg) -> error (b, occ, msg)
 | Error msg -> raise (Error msg) end); checkFam' bs end))
(* reuse variable names when tracing *))
| (Def d)::bs ->
    (((begin if !Global.chatter > 3
             then begin print ((N.qidToString (N.constQid d)) ^ " ") end
       else begin () end;
if !Global.chatter > 4
then begin (begin N.varReset IntSyn.Null; print "\n" end) end
else begin () end;
(begin try checkClause' (((I.constType d), I.id), P.top)
 with | Error' (occ, msg) -> error (d, occ, msg)
 | Error msg -> raise (Error msg) end); checkFam' bs end))
(* reuse variable names when tracing *)) end in
let _ =
if !Global.chatter > 3
then
  begin print
          (((^) "Termination checking family " N.qidToString (N.constQid a))
             ^ "\n") end
else begin () end in
checkFam' (Index.lookup a)
let rec reset () = begin R.reset (); R.resetROrder () end
let reset = reset
let checkFamReduction = checkFamReduction
let checkFam = checkFam end
