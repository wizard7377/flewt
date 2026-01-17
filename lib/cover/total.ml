
module type TOTAL  =
  sig
    exception Error of
      ((string)(*! structure IntSyn : INTSYN !*)(* Author: Frank Pfenning *)
      (* Total Declarations *)) 
    val reset : unit -> unit
    val install : IntSyn.cid -> unit
    val uninstall :
      IntSyn.cid ->
        ((bool)(* install(a) --- a is total in its input arguments *))
    val checkFam :
      IntSyn.cid ->
        ((unit)(* true: was known to be total *))
  end;;




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
                     module Timers :
                     ((TIMERS)(* Total Declarations *)
                     (* Author: Frank Pfenning *)(*! structure IntSyn' : INTSYN !*)
                     (*! sharing Whnf.IntSyn = IntSyn' !*)
                     (*! sharing Names.IntSyn = IntSyn' !*)
                     (*! sharing ModeSyn.IntSyn = IntSyn' !*)(*! sharing Index.IntSyn = IntSyn' !*)
                     (*! sharing Subordinate.IntSyn = IntSyn' !*)
                     (*! sharing Order.IntSyn = IntSyn' !*)
                     (*! sharing Reduces.IntSyn = IntSyn' !*)(*! structure Paths : PATHS !*)
                     (*! sharing Origins.Paths = Paths !*)
                     (*! sharing Origins.IntSyn = IntSyn' !*))
                   end) : TOTAL =
  struct
    exception Error of
      ((string)(*! structure IntSyn = IntSyn' !*)) 
    module I = IntSyn
    module P = Paths
    module M = ModeSyn
    module N = Names
    let (totalTable : unit Table.__Table) = Table.new__ 0
    let rec reset () = Table.clear totalTable
    let rec install cid = Table.insert totalTable (cid, ())
    let rec lookup cid = Table.lookup totalTable cid
    let rec uninstall cid = Table.delete totalTable cid
    let ((reset)(* totalTable (a) = SOME() iff a is total, otherwise NONE *))
      = reset
    let install = install
    let uninstall =
      function
      | cid ->
          (match lookup cid with
           | NONE -> false__
           | SOME _ -> (uninstall cid; true__))
    let rec total cid =
      match lookup cid with
      | NONE -> ((false__)(* call only on constants *))
      | SOME _ -> true__
    exception Error' of (P.occ * string) 
    let rec error
      (((c)(* copied from terminates/reduces.fun *)), occ,
       msg)
      =
      match Origins.originLookup c with
      | (fileName, NONE) -> raise (Error ((fileName ^ ":") ^ msg))
      | (fileName, SOME occDec) ->
          raise
            (Error
               (P.wrapLoc'
                  ((P.Loc (fileName, (P.occToRegionDec occDec occ))),
                    (Origins.linesInfoLookup fileName), msg)))
    let rec checkDynOrder =
      function
      | (((G)(* G is unused here *)), Vs, 0, occ) ->
          (if (!Global.chatter) >= 5
           then
             print
               "Output coverage: skipping redundant checking of third-order clause\n"
           else ();
           ((())
           (* raise Error' (occ, "Output coverage for clauses of order >= 3 not yet implemented") *)
           (* Functional calculus now checks this *)
           (* Sun Jan  5 12:17:06 2003 -fp *)))
      | (G, Vs, n, occ) ->
          checkDynOrderW
            (((G)(* n > 0 *)), (Whnf.whnf Vs), n, occ)
    let rec checkDynOrderW =
      function
      | (G, (Root _, s), n, occ) -> ()
      | (((G)(* atomic subgoal *)),
         (Pi (((Dec (_, V1) as D1), I.No), V2), s), n, occ) ->
          (checkDynOrder (G, (V1, s), (n - 1), (P.label occ));
           checkDynOrder
             ((I.Decl
                 (((G)
                   (* dynamic (= non-dependent) assumption --- calculate dynamic order of V1 *)),
                   D1)), (V2, (I.dot1 s)), n, (P.body occ)))
      | (G, (Pi ((D1, I.Maybe), V2), s), n, occ) ->
          checkDynOrder
            ((I.Decl
                (((G)
                  (* static (= dependent) assumption --- consider only body *)),
                  D1)), (V2, (I.dot1 s)), n, (P.body occ))
    let rec checkClause
      (((G)(* checkClause (G, (V, s), occ) = ()
       checkGoal (G, (V, s), occ) = ()
       iff local output coverage for V is satisfied
           for clause V[s] or goal V[s], respectively.
       Effect: raises Error' (occ, msg) if coverage is not satisfied at occ.

       Invariants: G |- V[s] : type
    *)),
       Vs, occ)
      = checkClauseW (G, (Whnf.whnf Vs), occ)
    let rec checkClauseW =
      function
      | (G, (Pi ((D1, I.Maybe), V2), s), occ) ->
          let ((D1')(* quantifier *)) =
            N.decEName (G, (I.decSub (D1, s))) in
          checkClause ((I.Decl (G, D1')), (V2, (I.dot1 s)), (P.body occ))
      | (G, (Pi (((Dec (_, V1) as D1), I.No), V2), s), occ) ->
          let ((_)(* subgoal *)) =
            checkClause ((I.Decl (G, D1)), (V2, (I.dot1 s)), (P.body occ)) in
          checkGoal (G, (V1, s), (P.label occ))
      | (G, (Root _, s), occ) -> ((())(* clause head *))
    let rec checkGoal (G, Vs, occ) = checkGoalW (G, (Whnf.whnf Vs), occ)
    let rec checkGoalW (G, (V, s), occ) =
      let a = I.targetFam V in
      let _ =
        if not (total a)
        then
          raise
            (Error'
               (occ,
                 (((^) "Subgoal " N.qidToString (N.constQid a)) ^
                    " not declared to be total")))
        else () in
      let _ = checkDynOrderW (G, (V, s), 2, occ) in
      try Cover.checkOut (G, (V, s))
      with
      | Error msg ->
          raise
            (Error'
               (((occ)
                 (* can raise Cover.Error for third-order clauses *)),
                 ("Totality: Output of subgoal not covered\n" ^ msg)))
    let rec checkDefinite =
      function
      | (((a)(* checkDefinite (a, ms) = ()
       iff every mode in mode spine ms is either input or output
       Effect: raises Error (msg) otherwise
    *)),
         M.Mnil) -> ()
      | (a, Mapp (Marg (M.Plus, _), ms')) -> checkDefinite (a, ms')
      | (a, Mapp (Marg (M.Minus, _), ms')) -> checkDefinite (a, ms')
      | (a, Mapp (Marg (M.Star, xOpt), ms')) ->
          error
            (((a)
              (* Note: filename and location are missing in this error message *)
              (* Fri Apr  5 19:25:54 2002 -fp *)), P.top,
              (((((^) "Error: Totality checking " N.qidToString
                    (N.constQid a))
                   ^ ":\n")
                  ^ "All argument modes must be input (+) or output (-)")
                 ^
                 (match xOpt with
                  | NONE -> ""
                  | SOME x -> (" but argument " ^ x) ^ " is indefinite (*)")))
    let rec checkOutCover =
      function
      | ((nil)(*)"  ))

     checkOutCover [c1,...,cn] = ()
       iff local output coverage for every subgoal in ci:Vi is satisfied.
       Effect: raises Error (msg) otherwise, where msg has filename and location.
    *))
          -> ()
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
    let rec checkFam
      ((a)(* checkFam (a) = ()
       iff family a is total in its input arguments.
       This requires termination, input coverage, and local output coverage.
       Currently, there is no global output coverage.
       Effect: raises Error (msg) otherwise, where msg has filename and location.
    *))
      =
      let ((_)(* Ensuring that there is no bad interaction with type-level definitions *))
        = Cover.checkNoDef a in
      let ((_)(* a cannot be a type-level definition *)) =
        try Subordinate.checkNoDef a
        with
        | Error msg ->
            raise
              (Subordinate.Error
                 ((((^) "Totality checking " ((N.qidToString)
                      (* a cannot depend on type-level definitions *))
                      (N.constQid a))
                     ^ ":\n")
                    ^ msg)) in
      let ((_)(* Checking termination *)) =
        try
          Timers.time Timers.terminate Reduces.checkFam a;
          if (!Global.chatter) >= 4
          then
            print (((^) "Terminates: " N.qidToString (N.constQid a)) ^ "\n")
          else ()
        with | Error msg -> raise (Reduces.Error msg) in
      let SOME
        ((ms)(* Checking input coverage *)(* by termination invariant, there must be consistent mode for a *))
        = ModeTable.modeLookup a in
      let ((_)(* must be defined and well-moded *)) =
        checkDefinite (a, ms) in
      let ((_)(* all arguments must be either input or output *))
        =
        try
          Timers.time Timers.coverage Cover.checkCovers (a, ms);
          if (!Global.chatter) >= 4
          then
            print
              (((^) "Covers (input): " N.qidToString (N.constQid a)) ^ "\n")
          else ()
        with | Error msg -> raise (Cover.Error msg) in
      let ((_)(* Checking output coverage *)) =
        if (!Global.chatter) >= 4
        then
          print
            (((^) "Output coverage checking family " N.qidToString
                (N.constQid a))
               ^ "\n")
        else () in
      let _ = ModeCheck.checkFreeOut (a, ms) in
      let ((cs)(* all variables in output args must be free *))
        = Index.lookup a in
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
      ()
  end ;;
