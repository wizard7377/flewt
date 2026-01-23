module type TOTAL  =
  sig
    exception Error of string 
    val reset : unit -> unit
    val install : IntSyn.cid -> unit
    val uninstall : IntSyn.cid -> bool
    val checkFam : IntSyn.cid -> unit
  end


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
                     module Timers : TIMERS
                   end) : TOTAL =
  struct
    exception Error of string 
    module I = IntSyn
    module P = Paths
    module M = ModeSyn
    module N = Names
    let (totalTable : unit Table.table_) = Table.new_ 0
    let rec reset () = Table.clear totalTable
    let rec install cid = Table.insert totalTable (cid, ())
    let rec lookup cid = Table.lookup totalTable cid
    let rec uninstall cid = Table.delete totalTable cid
    let reset = reset
    let install = install
    let uninstall =
      begin function
      | cid ->
          (begin match lookup cid with
           | None -> false
           | Some _ -> (begin uninstall cid; true end) end) end
let rec total cid =
  begin match lookup cid with | None -> false | Some _ -> true end(* call only on constants *)
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
let rec checkDynOrder =
  begin function
  | (g_, vs_, 0, occ) ->
      (begin if !Global.chatter >= 5
             then
               begin print
                       "Output coverage: skipping redundant checking of third-order clause\n" end
       else begin () end;
  () end)
| (g_, vs_, n, occ) -> checkDynOrderW (g_, (Whnf.whnf vs_), n, occ) end
(* n > 0 *)(* Sun Jan  5 12:17:06 2003 -fp *)(* Functional calculus now checks this *)
(* raise Error' (occ, "Output coverage for clauses of order >= 3 not yet implemented") *)
let rec checkDynOrderW =
  begin function
  | (g_, (Root _, s), n, occ) -> ()
  | (g_, (Pi (((Dec (_, v1_) as d1_), I.No), v2_), s), n, occ) ->
      (begin checkDynOrder (g_, (v1_, s), (n - 1), (P.label occ));
       checkDynOrder ((I.Decl (g_, d1_)), (v2_, (I.dot1 s)), n, (P.body occ)) end)
  | (g_, (Pi ((d1_, I.Maybe), v2_), s), n, occ) ->
      checkDynOrder ((I.Decl (g_, d1_)), (v2_, (I.dot1 s)), n, (P.body occ)) end
(* static (= dependent) assumption --- consider only body *)(* dynamic (= non-dependent) assumption --- calculate dynamic order of V1 *)
(* atomic subgoal *)
let rec checkClause (g_, vs_, occ) = checkClauseW (g_, (Whnf.whnf vs_), occ)
let rec checkClauseW =
  begin function
  | (g_, (Pi ((d1_, I.Maybe), v2_), s), occ) ->
      let D1' = N.decEName (g_, (I.decSub (d1_, s))) in
      checkClause ((I.Decl (g_, D1')), (v2_, (I.dot1 s)), (P.body occ))
  | (g_, (Pi (((Dec (_, v1_) as d1_), I.No), v2_), s), occ) ->
      let _ =
        checkClause ((I.Decl (g_, d1_)), (v2_, (I.dot1 s)), (P.body occ)) in
      checkGoal (g_, (v1_, s), (P.label occ))
  | (g_, (Root _, s), occ) -> () end(* clause head *)
(* subgoal *)(* quantifier *)
let rec checkGoal (g_, vs_, occ) = checkGoalW (g_, (Whnf.whnf vs_), occ)
let rec checkGoalW (g_, (v_, s), occ) =
  let a = I.targetFam v_ in
  let _ =
    if not (total a)
    then
      begin raise
              (Error'
                 (occ,
                   (((^) "Subgoal " N.qidToString (N.constQid a)) ^
                      " not declared to be total"))) end
    else begin () end in
let _ = checkDynOrderW (g_, (v_, s), 2, occ) in
((begin try Cover.checkOut (g_, (v_, s))
  with
  | Error msg ->
      raise
        (Error' (occ, ("Totality: Output of subgoal not covered\n" ^ msg))) end)
  (* can raise Cover.Error for third-order clauses *))
let rec checkDefinite =
  begin function
  | (a, M.Mnil) -> ()
  | (a, Mapp (Marg (M.Plus, _), ms')) -> checkDefinite (a, ms')
  | (a, Mapp (Marg (M.Minus, _), ms')) -> checkDefinite (a, ms')
  | (a, Mapp (Marg (M.Star, xOpt), ms')) ->
      error
        (a, P.top,
          (((((^) "Error: Totality checking " N.qidToString (N.constQid a)) ^
               ":\n")
              ^ "All argument modes must be input (+) or output (-)")
             ^
             (begin match xOpt with
              | None -> ""
              | Some x -> (" but argument " ^ x) ^ " is indefinite (*)" end))) end
(* Fri Apr  5 19:25:54 2002 -fp *)(* Note: filename and location are missing in this error message *)
let rec checkOutCover =
  begin function
  | [] -> ()
  | (Const c)::cs ->
      (begin if !Global.chatter >= 4
             then begin print ((N.qidToString (N.constQid c)) ^ " ") end
       else begin () end;
  if !Global.chatter >= 6 then begin print "\n" end
  else begin () end;
  (begin try checkClause (I.Null, ((I.constType c), I.id), P.top)
   with | Error' (occ, msg) -> error (c, occ, msg) end);
checkOutCover cs end)
| (Def d)::cs ->
    (begin if !Global.chatter >= 4
           then begin print ((N.qidToString (N.constQid d)) ^ " ") end
     else begin () end; if !Global.chatter >= 6 then begin print "\n" end
else begin () end;
(begin try checkClause (I.Null, ((I.constType d), I.id), P.top)
 with | Error' (occ, msg) -> error (d, occ, msg) end);
checkOutCover cs end) end
let rec checkFam a =
  let _ = Cover.checkNoDef a in
  let _ =
    ((begin try Subordinate.checkNoDef a
      with
      | Error msg ->
          raise
            (Subordinate.Error
               ((((^) "Totality checking " N.qidToString (N.constQid a)) ^
                   ":\n")
                  ^ msg)) end)
    (* a cannot depend on type-level definitions *)) in
  let _ =
    begin try
            begin Timers.time Timers.terminate Reduces.checkFam a;
            if !Global.chatter >= 4
            then
              begin print
                      (((^) "Terminates: " N.qidToString (N.constQid a)) ^
                         "\n") end
            else begin () end end
    with | Error msg -> raise (Reduces.Error msg) end in
let Some ms = ModeTable.modeLookup a in
let _ = checkDefinite (a, ms) in
let _ =
begin try
        begin Timers.time Timers.coverage Cover.checkCovers (a, ms);
        if !Global.chatter >= 4
        then
          begin print
                  (((^) "Covers (input): " N.qidToString (N.constQid a)) ^
                     "\n") end
        else begin () end end
with | Error msg -> raise (Cover.Error msg) end in
let _ =
if !Global.chatter >= 4
then
  begin print
          (((^) "Output coverage checking family " N.qidToString
              (N.constQid a))
             ^ "\n") end
else begin () end in
let _ = ModeCheck.checkFreeOut (a, ms) in
let cs = Index.lookup a in
let _ =
begin try
        begin Timers.time Timers.coverage checkOutCover cs;
        if !Global.chatter = 4 then begin print "\n" end
        else begin () end;
if !Global.chatter >= 4
then
  begin print (((^) "Covers (output): " N.qidToString (N.constQid a)) ^ "\n") end
else begin () end end with | Error msg -> raise (Cover.Error msg) end in
((())
(* Ensuring that there is no bad interaction with type-level definitions *)
(* a cannot be a type-level definition *)(* Checking termination *)
(* Checking input coverage *)(* by termination invariant, there must be consistent mode for a *)
(* must be defined and well-moded *)(* all arguments must be either input or output *)
(* Checking output coverage *)(* all variables in output args must be free *))
end
