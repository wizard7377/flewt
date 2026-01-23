module type WORLDSYN  =
  sig
    exception Error of string 
    val reset : unit -> unit
    val install : (IntSyn.cid * Tomega.worlds_) -> unit
    val lookup : IntSyn.cid -> Tomega.worlds_
    val uninstall : IntSyn.cid -> bool
    val worldcheck : Tomega.worlds_ -> IntSyn.cid -> unit
    val ctxToList : IntSyn.dec_ IntSyn.ctx_ -> IntSyn.dec_ list
    val isSubsumed : Tomega.worlds_ -> IntSyn.cid -> unit
    val getWorlds : IntSyn.cid -> Tomega.worlds_
  end


module WorldSyn(WorldSyn:sig
                           module Global : GLOBAL
                           module Whnf : WHNF
                           module Index : INDEX
                           module Names : NAMES
                           module Unify : UNIFY
                           module Abstract : ABSTRACT
                           module Constraints : CONSTRAINTS
                           module Subordinate : SUBORDINATE
                           module Print : PRINT
                           module Table : TABLE
                           module Origins : ORIGINS
                           module Timers : TIMERS
                         end) : WORLDSYN =
  struct
    module I = IntSyn
    module T = Tomega
    module P = Paths
    module F = Print.Formatter
    exception Error of string 
    exception Error' of (P.occ * string) 
    let rec wrapMsg (c, occ, msg) =
      begin match Origins.originLookup c with
      | (fileName, None) -> (fileName ^ ":") ^ msg
      | (fileName, Some occDec) ->
          P.wrapLoc'
            ((P.Loc (fileName, (P.occToRegionDec occDec occ))),
              (Origins.linesInfoLookup fileName),
              ((((^) "While checking constant " Names.qidToString
                   (Names.constQid c))
                  ^ ":\n")
                 ^ msg)) end
    type nonrec dlist = IntSyn.dec_ list
    let (worldsTable : T.worlds_ Table.table_) = Table.new_ 0
    let rec reset () = Table.clear worldsTable
    let rec insert (cid, w_) = Table.insert worldsTable (cid, w_)
    let rec getWorlds b =
      begin match Table.lookup worldsTable b with
      | None ->
          raise
            (Error
               (((^) "Family " Names.qidToString (Names.constQid b)) ^
                  " has no worlds declaration"))
      | Some (Wb) -> Wb end
  let (subsumedTable : unit Table.table_) = Table.new_ 0
  let rec subsumedReset () = Table.clear subsumedTable
  let rec subsumedInsert cid = Table.insert subsumedTable (cid, ())
  let rec subsumedLookup cid =
    begin match Table.lookup subsumedTable cid with
    | None -> false
    | Some _ -> true end
type reg_ =
  | Block of (I.dctx * dlist) 
  | Seq of (dlist * I.sub_) 
  | Star of reg_ 
  | Plus of (reg_ * reg_) 
  | One 
exception Success 
let rec formatReg r =
  ((begin match r with
    | Block (g_, dl) -> Print.formatDecList (g_, dl)
    | Seq (dl, s) -> Print.formatDecList' (I.Null, (dl, s))
    | Star r -> F.Hbox [F.String "("; formatReg r; F.String ")*"]
    | Plus (r1, r2) ->
        F.HVbox
          [F.String "(";
          formatReg r1;
          F.String ")";
          F.Break;
          F.String "|";
          F.Space;
          F.String "(";
          formatReg r2;
          F.String ")"]
    | One -> F.String "1" end)
  (* Is this correct? - gaw *)(* Fixed June 3, 2009 -fp,cs *))
let rec formatSubsump msg (g_, dl, Rb, b) =
  F.HVbox
    (([F.String msg;
      F.Space;
      F.String "for family";
      F.Space;
      F.String ((Names.qidToString (Names.constQid b)) ^ ":");
      F.Break;
      Print.formatDecList (g_, dl);
      F.Break;
      F.String "</:";
      F.Space;
      formatReg Rb])
    (* F.Newline (), *)(* Do not print some-variables; reenable if necessary *)
    (* June 3, 2009 -fp,cs *)(* Print.formatCtx(I.Null, G), F.Break, F.String "|-", F.Space, *))
  (*
            F.HVbox ([F.String ((Names.qidToString (Names.constQid b)) ^ ":")])
        *)
let rec createEVarSub =
  begin function
  | (g_, I.Null) -> I.Shift (I.ctxLength g_)
  | (g_, Decl (g'_, (Dec (_, v_) as d_))) ->
      let s = createEVarSub (g_, g'_) in
      let v'_ = I.EClo (v_, s) in
      let x_ = I.newEVar (g_, v'_) in I.Dot ((I.Exp x_), s) end
let rec collectConstraints =
  begin function
  | [] -> []
  | (EVar (_, _, _, { contents = [] }))::xs_ -> collectConstraints xs_
  | (EVar (_, _, _, { contents = constrs }))::xs_ ->
      (@) (Constraints.simplify constrs) collectConstraints xs_ end(* constrs <> nil *)
let rec collectEVars =
  begin function
  | (g_, Dot (Exp (x_), s), xs_) ->
      collectEVars (g_, s, (Abstract.collectEVars (g_, (x_, I.id), xs_)))
  | (g_, Shift _, xs_) -> xs_ end
let rec noConstraints (g_, s) =
  begin match collectConstraints (collectEVars (g_, s, [])) with
  | [] -> true
  | _ -> false end
let rec formatD (g_, d_) =
  F.Hbox
    (((::) ((::) (F.String "{") Print.formatDec (g_, d_)) F.String "}") :: [])
let rec formatDList =
  begin function
  | (g_, [], t) -> []
  | (g_, (d_)::[], t) ->
      let d'_ = I.decSub (d_, t) in (((formatD (g_, d'_)) :: [])
        (* Names.decUName (G, I.decSub(D, t)) *))
  | (g_, (d_)::l_, t) ->
      let d'_ = I.decSub (d_, t) in
      (((::) ((formatD (g_, d'_)) :: F.Break) formatDList
          ((I.Decl (g_, d'_)), l_, (I.dot1 t)))
        (* Names.decUName (G, I.decSub (D, t)) *)) end
let rec wGoalToString ((g_, l_), Seq (piDecs, t)) =
  F.makestring_fmt
    (F.HVbox
       [F.HVbox (formatDList (g_, l_, I.id));
       F.Break;
       F.String "<|";
       F.Break;
       F.HVbox (formatDList (g_, piDecs, t))])
let rec worldToString (g_, Seq (piDecs, t)) =
  F.makestring_fmt (F.HVbox (formatDList (g_, piDecs, t)))
let rec hypsToString (g_, l_) =
  F.makestring_fmt (F.HVbox (formatDList (g_, l_, I.id)))
let rec mismatchToString (g_, (v1_, s1), (v2_, s2)) =
  F.makestring_fmt
    (F.HVbox
       [Print.formatExp (g_, (I.EClo (v1_, s1)));
       F.Break;
       F.String "<>";
       F.Break;
       Print.formatExp (g_, (I.EClo (v2_, s2)))])
module Trace :
  sig
    val clause : I.cid -> unit
    val constraintsRemain : unit -> unit
    val matchBlock : ((I.dctx * dlist) * reg_) -> unit
    val unmatched : (I.dctx * dlist) -> unit
    val missing : (I.dctx * reg_) -> unit
    val mismatch : (I.dctx * I.eclo * I.eclo) -> unit
    val success : unit -> unit
  end =
  struct
    let rec clause c =
      print
        (((^) "World checking clause " Names.qidToString (Names.constQid c))
           ^ "\n")
    let rec constraintsRemain () =
      if !Global.chatter > 7
      then
        begin print
                "Constraints remain after matching hypotheses against context block\n" end
      else begin () end
  let rec matchBlock (GL, r_) =
    if !Global.chatter > 7
    then begin print (((^) "Matching:\n" wGoalToString (GL, r_)) ^ "\n") end
    else begin () end(* R = (D1,...,Dn)[t] *)
let rec unmatched (GL) =
  if !Global.chatter > 7
  then begin print (((^) "Unmatched hypotheses:\n" hypsToString GL) ^ "\n") end
  else begin () end
let rec missing (g_, r_) =
  if !Global.chatter > 7
  then
    begin print (((^) "Missing hypotheses:\n" worldToString (g_, r_)) ^ "\n") end
  else begin () end(* R = (D1,...,Dn)[t] *)
let rec mismatch (g_, vs1_, vs2_) =
  if !Global.chatter > 7
  then
    begin print
            (((^) "Mismatch:\n" mismatchToString (g_, vs1_, vs2_)) ^ "\n") end
  else begin () end
let rec success () = if !Global.chatter > 7 then begin print "Success\n" end
  else begin () end end

let rec decUName (g_, d_) = I.Decl (g_, (Names.decUName (g_, d_)))
let rec decEName (g_, d_) = I.Decl (g_, (Names.decEName (g_, d_)))
let rec subGoalToDList =
  begin function
  | Pi ((d_, _), v_) -> (::) d_ subGoalToDList v_
  | Root _ -> [] end
let rec worldsToReg =
  begin function | Worlds [] -> One | Worlds cids -> Star (worldsToReg' cids) end
let rec worldsToReg' =
  begin function
  | cid::[] -> Block (I.constBlock cid)
  | cid::cids -> Plus ((Block (I.constBlock cid)), (worldsToReg' cids)) end
let rec init arg__0 arg__1 =
  begin match (arg__0, arg__1) with
  | (b, (_, [])) -> (begin Trace.success (); raise Success end)
  | (b, (g_, ((Dec (_, v1_) as d1_)::l2_ as l_))) ->
      if Subordinate.belowEq ((I.targetFam v1_), b)
      then begin (begin Trace.unmatched (g_, l_); () end) end
  else begin init b ((decUName (g_, d1_)), l2_) end end
let rec accR =
  begin function
  | (GL, One, b, k) -> k GL
  | (((g_, l_) as GL), Block (someDecs, piDecs), b, k) ->
      let t = createEVarSub (g_, someDecs) in
      let _ = Trace.matchBlock (GL, (Seq (piDecs, t))) in
      let k' =
        begin function
        | GL' -> if noConstraints (g_, t) then begin k GL' end
            else begin (begin Trace.constraintsRemain (); () end) end end in
((accR (GL, (Seq (piDecs, t)), b, k'))
  (* G |- t : someDecs *)(* if block matches, check for remaining constraints *))
| ((g_, ((Dec (_, v1_) as d_)::l2_ as l_)),
   (Seq (((Dec (_, V1'))::L2' as b'_), t) as l'_), b, k) ->
    if Unify.unifiable (g_, (v1_, I.id), (V1', t))
    then
      begin accR (((decUName (g_, d_)), l2_), (Seq (L2', (I.dot1 t))), b, k) end
    else begin
      ((if Subordinate.belowEq ((I.targetFam v1_), b)
        then begin (begin Trace.mismatch (g_, (v1_, I.id), (V1', t)); () end) end
    else begin
      accR
        (((decUName (g_, d_)), l2_), (Seq (b'_, (I.comp (t, I.shift)))), b,
          k) end)
(* relevant to family b, fail *)(* not relevant to family b, skip in L *)) end
| (GL, Seq ([], t), b, k) -> k GL
| (((g_, []) as GL), (Seq (l'_, t) as r_), b, k) ->
    (begin Trace.missing (g_, r_); () end)
| (GL, Plus (r1, r2), b, k) ->
    (begin CSManager.trail (begin function | () -> accR (GL, r1, b, k) end);
    accR (GL, r2, b, k) end) | (GL, Star (One), b, k) -> k GL
| (GL, (Star r' as r), b, k) ->
    (begin CSManager.trail (begin function | () -> k GL end);
    accR (GL, r', b, (begin function | GL' -> accR (GL', r, b, k) end)) end) end
(* r' does not accept empty declaration list *)(* only possibility for non-termination in next rule *)
(* L is missing *)(* Mon May 7 2007 -fp *)(* fixed bug in previous line; was: t instead of t o ^ *)
let rec checkSubsumedBlock (g_, l'_, Rb, b) =
  begin try
          begin accR ((g_, l'_), Rb, b, (init b));
          raise
            (Error
               (F.makestring_fmt
                  (formatSubsump "World subsumption failure" (g_, l'_, Rb, b)))) end
  with | Success -> () end
let rec checkSubsumedWorlds =
  begin function
  | ([], Rb, b) -> ()
  | (cid::cids, Rb, b) ->
      let (someDecs, piDecs) = I.constBlock cid in
      (begin checkSubsumedBlock ((Names.ctxName someDecs), piDecs, Rb, b);
       checkSubsumedWorlds (cids, Rb, b) end) end
let rec checkBlocks (Worlds cids) (g_, v_, occ) =
  begin try
          let b = I.targetFam v_ in
          let Wb =
            begin try getWorlds b
            with | Error msg -> raise (Error' (occ, msg)) end in
          let Rb = worldsToReg Wb in
          let _ = if subsumedLookup b then begin () end
            else begin
              (begin try
                       begin checkSubsumedWorlds (cids, Rb, b);
                       subsumedInsert b end
              with | Error msg -> raise (Error' (occ, msg)) end) end in
let l_ = subGoalToDList v_ in
begin accR ((g_, l_), Rb, b, (init b));
raise
  (Error'
     (occ,
       (F.makestring_fmt (formatSubsump "World violation" (g_, l_, Rb, b))))) end
with | Success -> () end
let rec checkClause =
  begin function
  | (g_, Root (a, s_), w_, occ) -> ()
  | (g_, Pi (((Dec (_, v1_) as d_), I.Maybe), v2_), w_, occ) ->
      (begin checkClause ((decEName (g_, d_)), v2_, w_, (P.body occ));
       checkGoal (g_, v1_, w_, (P.label occ)) end)
  | (g_, Pi (((Dec (_, v1_) as d_), I.No), v2_), w_, occ) ->
      (begin checkBlocks w_ (g_, v1_, (P.label occ));
       checkClause ((decEName (g_, d_)), v2_, w_, (P.body occ));
       checkGoal (g_, v1_, w_, (P.label occ)) end) end
let rec checkGoal =
  begin function
  | (g_, Root (a, s_), w_, occ) -> ()
  | (g_, Pi (((Dec (_, v1_) as d_), _), v2_), w_, occ) ->
      (begin checkGoal ((decUName (g_, d_)), v2_, w_, (P.body occ));
       checkClause (g_, v1_, w_, (P.label occ)) end) end
let rec worldcheck (w_) a =
  let _ =
    if !Global.chatter > 3
    then
      begin print
              (((^) "World checking family " Names.qidToString
                  (Names.constQid a))
                 ^ ":\n") end
    else begin () end in
let _ = subsumedReset () in
let rec checkAll =
  begin function
  | [] -> ()
  | (Const c)::clist ->
      (begin if !Global.chatter = 4
             then begin print ((Names.qidToString (Names.constQid c)) ^ " ") end
       else begin () end;
  if !Global.chatter > 4 then begin Trace.clause c end
  else begin () end;
  (begin try checkClause (I.Null, (I.constType c), w_, P.top)
   with | Error' (occ, msg) -> raise (Error (wrapMsg (c, occ, msg))) end);
  checkAll clist end)
| (Def d)::clist ->
    (begin if !Global.chatter = 4
           then begin print ((Names.qidToString (Names.constQid d)) ^ " ") end
     else begin () end; if !Global.chatter > 4 then begin Trace.clause d end
else begin () end;
(begin try checkClause (I.Null, (I.constType d), w_, P.top)
 with | Error' (occ, msg) -> raise (Error (wrapMsg (d, occ, msg))) end);
checkAll clist end) end in
let _ = checkAll (Index.lookup a) in
let _ = if !Global.chatter = 4 then begin print "\n" end else begin () end in
((())
(* initialize table of subsumed families *))
let rec ctxAppend =
  begin function
  | (g_, I.Null) -> g_
  | (g_, Decl (g'_, d_)) -> I.Decl ((ctxAppend (g_, g'_)), d_) end
let rec checkSubordBlock (g_, g'_, l_) =
  checkSubordBlock' ((ctxAppend (g_, g'_)), l_)
let rec checkSubordBlock' =
  begin function
  | (g_, (Dec (_, v_) as d_)::l'_) ->
      (((begin Subordinate.respectsN (g_, v_);
         checkSubordBlock' ((I.Decl (g_, d_)), l'_) end))
  (* is V nf?  Assume here: yes! *)) | (g_, []) -> () end
let rec conDecBlock =
  begin function
  | BlockDec (_, _, Gsome, Lpi) -> (Gsome, Lpi)
  | condec ->
      raise
        (Error
           (((^) "Identifier " I.conDecName condec) ^ " is not a block label")) end
let rec constBlock cid = conDecBlock (I.sgnLookup cid)
let rec checkSubordWorlds =
  begin function
  | [] -> ()
  | cid::cids ->
      let (someDecs, piDecs) = constBlock cid in
      (begin checkSubordBlock (I.Null, someDecs, piDecs);
       checkSubordWorlds cids end) end
let rec install (a, (Worlds cids as w_)) =
  begin (begin try checkSubordWorlds cids
         with | Error msg -> raise (Error msg) end);
  insert (a, w_) end
let rec uninstall a =
  begin match Table.lookup worldsTable a with
  | None -> false
  | Some _ -> (begin Table.delete worldsTable a; true end) end
let rec lookup a = getWorlds a
let rec ctxToList (Gin) =
  let rec ctxToList' =
    begin function
    | (I.Null, g_) -> g_
    | (Decl (g_, d_), g'_) -> ctxToList' (g_, (d_ :: g'_)) end in
ctxToList' (Gin, [])
let rec isSubsumed (Worlds cids) b =
  let Wb = getWorlds b in
  let Rb = worldsToReg Wb in if subsumedLookup b then begin () end
    else begin (begin checkSubsumedWorlds (cids, Rb, b); subsumedInsert b end) end
let reset = reset
let install = install
let lookup = lookup
let uninstall = uninstall
let worldcheck = worldcheck
let ctxToList = ctxToList
let isSubsumed = isSubsumed
let getWorlds = getWorlds end
