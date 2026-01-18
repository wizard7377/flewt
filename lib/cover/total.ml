
(* Total Declarations *)
(* Author: Frank Pfenning *)
module type TOTAL  =
  sig
    (*! structure IntSyn : INTSYN !*)
    exception Error of string 
    val reset : unit -> unit
    val install : IntSyn.cid -> unit
    (* install(a) --- a is total in its input arguments *)
    val uninstall : IntSyn.cid -> bool
    (* true: was known to be total *)
    val checkFam : IntSyn.cid -> unit
  end;;




(* Total Declarations *)
(* Author: Frank Pfenning *)
module Total(Total:sig
                     module Global : GLOBAL
                     module Table : TABLE
                     module Whnf : WHNF
                     module Names : NAMES
                     module ModeTable : MODETABLE
                     module ModeCheck : MODECHECK
                     module Index : INDEX
                     module Subordinate : SUBORDINATE
                     module Order : ORDER
                     module Reduces : REDUCES
                     module Cover : COVER
                     module Origins : ORIGINS
                     (*! structure IntSyn' : INTSYN !*)
                     (*! sharing Whnf.IntSyn = IntSyn' !*)
                     (*! sharing Names.IntSyn = IntSyn' !*)
                     (*! sharing ModeSyn.IntSyn = IntSyn' !*)
                     (*! sharing Index.IntSyn = IntSyn' !*)
                     (*! sharing Subordinate.IntSyn = IntSyn' !*)
                     (*! sharing Order.IntSyn = IntSyn' !*)
                     (*! sharing Reduces.IntSyn = IntSyn' !*)
                     (*! structure Paths : PATHS !*)
                     (*! sharing Origins.Paths = Paths !*)
                     (*! sharing Origins.IntSyn = IntSyn' !*)
                     module Timers : TIMERS
                   end) : TOTAL =
  struct
    (*! structure IntSyn = IntSyn' !*)
    exception Error of string 
    module I = IntSyn
    module P = Paths
    module M = ModeSyn
    module N = Names
    let (totalTable : unit Table.__Table) = Table.new__ 0
    let rec reset () = Table.clear totalTable
    let rec install cid = Table.insert totalTable (cid, ())
    let rec lookup cid = Table.lookup totalTable cid
    let rec uninstall cid = Table.delete totalTable cid
    (* totalTable (a) = Some() iff a is total, otherwise None *)
    let reset = reset
    let install = install
    let uninstall =
      function
      | cid ->
          (match lookup cid with
           | None -> false__
           | Some _ -> (uninstall cid; true__))
    let rec total cid =
      match lookup cid with | None -> false__ | Some _ -> true__(* call only on constants *)
    exception Error' of (P.occ * string) 
    (* copied from terminates/reduces.fun *)
    let rec error (c, occ, msg) =
      match Origins.originLookup c with
      | (fileName, None) -> raise (Error ((fileName ^ ":") ^ msg))
      | (fileName, Some occDec) ->
          raise
            (Error
               (P.wrapLoc'
                  ((P.Loc (fileName, (P.occToRegionDec occDec occ))),
                    (Origins.linesInfoLookup fileName), msg)))
    (* __g is unused here *)
    let rec checkDynOrder =
      function
      | (__g, __Vs, 0, occ) ->
          (if (!Global.chatter) >= 5
           then
             print
               "Output coverage: skipping redundant checking of third-order clause\n"
           else ();
           ())
      | (__g, __Vs, n, occ) -> checkDynOrderW (__g, (Whnf.whnf __Vs), n, occ)
      (* n > 0 *)(* Sun Jan  5 12:17:06 2003 -fp *)
      (* Functional calculus now checks this *)(* raise Error' (occ, "Output coverage for clauses of order >= 3 not yet implemented") *)
    let rec checkDynOrderW =
      function
      | (__g, (Root _, s), n, occ) -> ()
      | (__g, (Pi (((Dec (_, V1)) as D1), I.No), V2), s), n, occ) ->
          (checkDynOrder (__g, (V1, s), (n - 1), (P.label occ));
           checkDynOrder
             ((I.Decl (__g, D1)), (V2, (I.dot1 s)), n, (P.body occ)))
      | (__g, (Pi ((D1, I.Maybe), V2), s), n, occ) ->
          checkDynOrder ((I.Decl (__g, D1)), (V2, (I.dot1 s)), n, (P.body occ))
      (* static (= dependent) assumption --- consider only body *)
      (* dynamic (= non-dependent) assumption --- calculate dynamic order of V1 *)
      (* atomic subgoal *)
    (* checkClause (__g, (__v, s), occ) = ()
       checkGoal (__g, (__v, s), occ) = ()
       iff local output coverage for __v is satisfied
           for clause __v[s] or goal __v[s], respectively.
       Effect: raises Error' (occ, msg) if coverage is not satisfied at occ.

       Invariants: __g |- __v[s] : type
    *)
    let rec checkClause (__g, __Vs, occ) = checkClauseW (__g, (Whnf.whnf __Vs), occ)
    let rec checkClauseW =
      function
      | (__g, (Pi ((D1, I.Maybe), V2), s), occ) ->
          let D1' = N.decEName (__g, (I.decSub (D1, s))) in
          checkClause ((I.Decl (__g, D1')), (V2, (I.dot1 s)), (P.body occ))
      | (__g, (Pi (((Dec (_, V1) as D1), I.No), V2), s), occ) ->
          let _ =
            checkClause ((I.Decl (__g, D1)), (V2, (I.dot1 s)), (P.body occ)) in
          checkGoal (__g, (V1, s), (P.label occ))
      | (__g, (Root _, s), occ) -> ()(* clause head *)
      (* subgoal *)(* quantifier *)
    let rec checkGoal (__g, __Vs, occ) = checkGoalW (__g, (Whnf.whnf __Vs), occ)
    let rec checkGoalW (__g, (__v, s), occ) =
      let a = I.targetFam __v in
      let _ =
        if not (total a)
        then
          raise
            (Error'
               (occ,
                 (((^) "Subgoal " N.qidToString (N.constQid a)) ^
                    " not declared to be total")))
        else () in
      let _ = checkDynOrderW (__g, (__v, s), 2, occ) in
      ((try Cover.checkOut (__g, (__v, s))
        with
        | Error msg ->
            raise
              (Error'
                 (occ, ("Totality: Output of subgoal not covered\n" ^ msg))))
        (* can raise Cover.Error for third-order clauses *))
    (* checkDefinite (a, ms) = ()
       iff every mode in mode spine ms is either input or output
       Effect: raises Error (msg) otherwise
    *)
    let rec checkDefinite =
      function
      | (a, M.Mnil) -> ()
      | (a, Mapp (Marg (M.Plus, _), ms')) -> checkDefinite (a, ms')
      | (a, Mapp (Marg (M.Minus, _), ms')) -> checkDefinite (a, ms')
      | (a, Mapp (Marg (M.Star, xOpt), ms')) ->
          error
            (a, P.top,
              (((((^) "Error: Totality checking " N.qidToString
                    (N.constQid a))
                   ^ ":\n")
                  ^ "All argument modes must be input (+) or output (-)")
                 ^
                 (match xOpt with
                  | None -> ""
                  | Some x -> (" but argument " ^ x) ^ " is indefinite (*)")))
      (* Fri Apr  5 19:25:54 2002 -fp *)(* Note: filename and location are missing in this error message *)
    let rec checkOutCover =
      function
      | nil -> ()
      | (Const c)::cs ->
          (if (!Global.chatter) >= 4
           then print ((N.qidToString (N.constQid c)) ^ " ")
           else ();
           if (!Global.chatter) >= 6 then print "\n" else ();
           (try checkClause (I.Null, ((I.constType c), I.id), P.top)
            with | Error' (occ, msg) -> error (c, occ, msg));
           checkOutCover cs)
      | (Def d)::cs ->
          (if (!Global.chatter) >= 4
           then print ((N.qidToString (N.constQid d)) ^ " ")
           else ();
           if (!Global.chatter) >= 6 then print "\n" else ();
           (try checkClause (I.Null, ((I.constType d), I.id), P.top)
            with | Error' (occ, msg) -> error (d, occ, msg));
           checkOutCover cs)
    (* checkFam (a) = ()
       iff family a is total in its input arguments.
       This requires termination, input coverage, and local output coverage.
       Currently, there is no global output coverage.
       Effect: raises Error (msg) otherwise, where msg has filename and location.
    *)
    let rec checkFam a =
      let _ = Cover.checkNoDef a in
      let _ =
        ((try Subordinate.checkNoDef a
          with
          | Error msg ->
              raise
                (Subordinate.Error
                   ((((^) "Totality checking " N.qidToString (N.constQid a))
                       ^ ":\n")
                      ^ msg)))
        (* a cannot depend on type-level definitions *)) in
      let _ =
        try
          Timers.time Timers.terminate Reduces.checkFam a;
          if (!Global.chatter) >= 4
          then
            print (((^) "Terminates: " N.qidToString (N.constQid a)) ^ "\n")
          else ()
        with | Error msg -> raise (Reduces.Error msg) in
      let Some ms = ModeTable.modeLookup a in
      let _ = checkDefinite (a, ms) in
      let _ =
        try
          Timers.time Timers.coverage Cover.checkCovers (a, ms);
          if (!Global.chatter) >= 4
          then
            print
              (((^) "Covers (input): " N.qidToString (N.constQid a)) ^ "\n")
          else ()
        with | Error msg -> raise (Cover.Error msg) in
      let _ =
        if (!Global.chatter) >= 4
        then
          print
            (((^) "Output coverage checking family " N.qidToString
                (N.constQid a))
               ^ "\n")
        else () in
      let _ = ModeCheck.checkFreeOut (a, ms) in
      let cs = Index.lookup a in
      let _ =
        try
          Timers.time Timers.coverage checkOutCover cs;
          if (!Global.chatter) = 4 then print "\n" else ();
          if (!Global.chatter) >= 4
          then
            print
              (((^) "Covers (output): " N.qidToString (N.constQid a)) ^ "\n")
          else ()
        with | Error msg -> raise (Cover.Error msg) in
      ((())
        (* Ensuring that there is no bad interaction with type-level definitions *)
        (* a cannot be a type-level definition *)(* Checking termination *)
        (* Checking input coverage *)(* by termination invariant, there must be consistent mode for a *)
        (* must be defined and well-moded *)(* all arguments must be either input or output *)
        (* Checking output coverage *)(* all variables in output args must be free *))
  end ;;
