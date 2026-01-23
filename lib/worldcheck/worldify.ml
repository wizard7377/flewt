module type WORLDIFY  =
  sig
    exception Error of string 
    val worldify : IntSyn.cid -> IntSyn.conDec_ list
    val worldifyGoal : (IntSyn.dec_ IntSyn.ctx_ * IntSyn.exp_) -> IntSyn.exp_
  end


module Worldify(Worldify:sig
                           module Global : GLOBAL
                           module WorldSyn : WORLDSYN
                           module Whnf : WHNF
                           module Index : INDEX
                           module Names : NAMES
                           module Unify : UNIFY
                           module Abstract : ABSTRACT
                           module Constraints : CONSTRAINTS
                           module CSManager : CS_MANAGER
                           module Subordinate : SUBORDINATE
                           module Print : PRINT
                           module Table : TABLE
                           module MemoTable : TABLE
                           module IntSet : INTSET
                           module Origins : ORIGINS
                         end) : WORLDIFY =
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
              ((((^) "Constant " Names.qidToString (Names.constQid c)) ^ ":")
                 ^ msg)) end
    let rec wrapMsgBlock (c, occ, msg) =
      begin match Origins.originLookup c with
      | (fileName, None) -> (fileName ^ ":") ^ msg
      | (fileName, Some occDec) ->
          P.wrapLoc'
            ((P.Loc (fileName, (P.occToRegionDec occDec occ))),
              (Origins.linesInfoLookup fileName),
              ((((^) "Block " Names.qidToString (Names.constQid c)) ^ ":") ^
                 msg)) end
  type nonrec dlist = IntSyn.dec_ list
  module W = WorldSyn
  type reg_ =
    | Block of (I.cid * (I.dctx * dlist)) 
    | Seq of (int * dlist * I.sub_) 
    | Star of reg_ 
    | Plus of (reg_ * reg_) 
    | One 
  exception Success of I.exp_ 
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
let rec wGoalToString ((g_, l_), Seq (_, piDecs, t)) =
  F.makestring_fmt
    (F.HVbox
       [F.HVbox (formatDList (g_, l_, I.id));
       F.Break;
       F.String "<|";
       F.Break;
       F.HVbox (formatDList (g_, piDecs, t))])
let rec worldToString (g_, Seq (_, piDecs, t)) =
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
let rec equivList =
  begin function
  | (g_, (_, []), []) -> true
  | (g_, (t, (Dec (_, v1_))::l1_), (Dec (_, v2_))::l2_) ->
      (begin try
               begin Unify.unify (g_, (v1_, t), (v2_, I.id));
               equivList (g_, ((I.dot1 t), l1_), l2_) end
      with | Unify _ -> false end)
  | _ -> false end
let rec equivBlock ((g_, l_), l'_) =
  let t = createEVarSub (I.Null, g_) in equivList (I.Null, (t, l_), l'_)
let rec equivBlocks arg__0 arg__1 =
  begin match (arg__0, arg__1) with
  | (w1_, []) -> true
  | ([], l'_) -> false
  | (b::w1_, l'_) ->
      (equivBlock ((I.constBlock b), l'_)) || (equivBlocks w1_ l'_) end
let rec strengthen arg__2 arg__3 =
  begin match (arg__2, arg__3) with
  | (a, (t, [])) -> []
  | (a, (t, (Dec (_, v_) as d_)::l_)) ->
      if Subordinate.below ((I.targetFam v_), a)
      then begin (::) (I.decSub (d_, t)) strengthen a ((I.dot1 t), l_) end
      else begin strengthen a ((I.Dot (I.Undef, t)), l_) end end
let rec subsumedBlock a (w1_) (g_, l_) =
  let t = createEVarSub (I.Null, g_) in
  let l'_ = strengthen a (t, l_) in
  ((if equivBlocks w1_ l'_ then begin () end
    else begin raise (Error "Static world subsumption failed") end)
  (* G |- t : someDecs *))
let rec subsumedBlocks arg__4 arg__5 arg__6 =
  begin match (arg__4, arg__5, arg__6) with
  | (a, w1_, []) -> ()
  | (a, w1_, b::w2_) ->
      (begin subsumedBlock a w1_ (I.constBlock b); subsumedBlocks a w1_ w2_ end) end
let rec subsumedWorld a (Worlds (w1_)) (Worlds (w2_)) =
  subsumedBlocks a w1_ w2_
let rec eqCtx =
  begin function
  | (I.Null, I.Null) -> true
  | (Decl (g1_, d1_), Decl (g2_, d2_)) ->
      (eqCtx (g1_, g2_)) && (Conv.convDec ((d1_, I.id), (d2_, I.id)))
  | _ -> false end
let rec eqList =
  begin function
  | ([], []) -> true
  | ((d1_)::l1_, (d2_)::l2_) ->
      (Conv.convDec ((d1_, I.id), (d2_, I.id))) && (eqList (l1_, l2_))
  | _ -> false end
let rec eqBlock (b1, b2) =
  let (g1_, l1_) = I.constBlock b1 in
  let (g2_, l2_) = I.constBlock b2 in
  (eqCtx (g1_, g2_)) && (eqList (l1_, l2_))
let rec subsumedCtx =
  begin function
  | (I.Null, w_) -> ()
  | (Decl (g_, BDec (_, (b, _))), (Worlds (bs_) as w_)) ->
      (begin if List.exists (begin function | b' -> eqBlock (b, b') end) bs_
       then begin () end
      else begin raise (Error "Dynamic world subsumption failed") end;
  subsumedCtx (g_, w_) end)
| (Decl (g_, _), (Worlds (bs_) as w_)) -> subsumedCtx (g_, w_) end
let rec checkGoal arg__7 arg__8 =
  begin match (arg__7, arg__8) with
  | (w_, (g_, Root (Const a, s_), occ)) ->
      let w'_ = W.getWorlds a in
      (begin subsumedWorld a w'_ w_; subsumedCtx (g_, w_) end)
  | (w_, (g_, Pi ((d_, _), v2_), occ)) ->
      checkGoal w_ ((decUName (g_, d_)), v2_, (P.body occ)) end
let rec checkClause arg__9 arg__10 =
  begin match (arg__9, arg__10) with
  | (w_, (g_, Root (a, s_), occ)) -> ()
  | (w_, (g_, Pi (((Dec (_, v1_) as d_), I.Maybe), v2_), occ)) ->
      checkClause w_ ((decEName (g_, d_)), v2_, (P.body occ))
  | (w_, (g_, Pi (((Dec (_, v1_) as d_), I.No), v2_), occ)) ->
      (begin checkClause w_ ((decEName (g_, d_)), v2_, (P.body occ));
       checkGoal w_ (g_, v1_, (P.label occ)) end) end
let rec checkConDec (w_) (ConDec (s, m, k, status, v_, l_)) =
  checkClause w_ (I.Null, v_, P.top)
let rec subGoalToDList =
  begin function
  | Pi ((d_, _), v_) -> (::) d_ subGoalToDList v_
  | Root _ -> [] end
let rec worldsToReg =
  begin function | Worlds [] -> One | Worlds cids -> Star (worldsToReg' cids) end
let rec worldsToReg' =
  begin function
  | cid::[] -> Block (cid, (I.constBlock cid))
  | cid::cids ->
      Plus ((Block (cid, (I.constBlock cid))), (worldsToReg' cids)) end
let rec init =
  begin function
  | (_, ((Root _, s) as vs_)) ->
      (begin Trace.success (); raise (Success (Whnf.normalize vs_)) end)
  | (g_, ((Pi (((Dec (_, v1_) as d1_), _), v2_) as v_), s)) ->
      (begin Trace.unmatched (g_, (subGoalToDList (Whnf.normalize (v_, s))));
       () end) end
let rec accR =
  begin function
  | (GVs, One, k) -> k GVs
  | (((g_, (v_, s)) as GVs), Block (c, (someDecs, piDecs)), k) ->
      let t = createEVarSub (g_, someDecs) in
      let _ =
        Trace.matchBlock
          ((g_, (subGoalToDList (Whnf.normalize (v_, s)))),
            (Seq (1, piDecs, t))) in
      let k' =
        begin function
        | (g'_, vs'_) ->
            if noConstraints (g_, t) then begin k (g'_, vs'_) end
            else begin (begin Trace.constraintsRemain (); () end) end end in
(((begin try
           accR
             (((decUName (g_, (I.BDec (None, (c, t))))),
                (v_, (I.comp (s, I.shift)))),
               (Seq (1, piDecs, (I.comp (t, I.shift)))), k')
   with
   | Success (v_) ->
       raise
         (Success
            (Whnf.normalize
               ((I.Pi (((I.BDec (None, (c, t))), I.Maybe), v_)), I.id))) end))
  (* G |- t : someDecs *))
| ((g_, ((Pi (((Dec (_, v1_) as d_), _), v2_) as v_), s)),
   (Seq (j, (Dec (_, V1'))::L2', t) as l'_), k) ->
    if Unify.unifiable (g_, (v1_, s), (V1', t))
    then
      begin accR
              ((g_,
                 (v2_,
                   (I.Dot
                      ((I.Exp (I.Root ((I.Proj ((I.Bidx 1), j)), I.Nil))), s)))),
                (Seq
                   ((j + 1), L2',
                     (I.Dot
                        ((I.Exp (I.Root ((I.Proj ((I.Bidx 1), j)), I.Nil))),
                          t)))), k) end
    else begin (begin Trace.mismatch (g_, (v1_, I.id), (V1', t)); () end) end
| (GVs, Seq (_, [], t), k) -> k GVs
| (((g_, (Root _, s)) as GVs), (Seq (_, l'_, t) as r_), k) ->
    (begin Trace.missing (g_, r_); () end)
| (GVs, Plus (r1, r2), k) ->
    (begin CSManager.trail (begin function | () -> accR (GVs, r1, k) end);
    accR (GVs, r2, k) end) | (GVs, Star (One), k) -> k GVs
| (GVs, (Star r' as r), k) ->
    (begin CSManager.trail (begin function | () -> k GVs end);
    accR (GVs, r', (begin function | GVs' -> accR (GVs', r, k) end)) end) end
(* r' does not accept empty declaration list *)(* only possibility for non-termination in next rule *)
(* L is missing *)
let rec worldifyGoal (g_, v_, (Worlds cids as w_), occ) =
  begin try
          let b = I.targetFam v_ in
          let Wb = W.getWorlds b in
          let Rb = worldsToReg Wb in
          begin accR ((g_, (v_, I.id)), Rb, init);
          raise (Error' (occ, "World violation")) end
  with | Success (v'_) -> v'_ end
let rec worldifyClause =
  begin function
  | (g_, (Root (a, s_) as v_), w_, occ) -> v_
  | (g_, Pi (((Dec (x, v1_) as d_), I.Maybe), v2_), w_, occ) ->
      let _ = print "{" in
      let w2_ = worldifyClause ((decEName (g_, d_)), v2_, w_, (P.body occ)) in
      let _ = print "}" in
      ((I.Pi (((I.Dec (((x, v1_))(* W1*))), I.Maybe), w2_))
        (*         val W1 = worldifyGoal (G, V1, W, P.label occ) *))
  | (g_, Pi (((Dec (x, v1_) as d_), I.No), v2_), w_, occ) ->
      let w1_ = worldifyGoal (g_, v1_, w_, (P.label occ)) in
      let w2_ = worldifyClause ((decEName (g_, d_)), v2_, w_, (P.body occ)) in
      I.Pi (((I.Dec (x, w1_)), I.No), w2_) end
let rec worldifyConDec (w_) (c, ConDec (s, m, k, status, v_, l_)) =
  begin if !Global.chatter = 4
        then begin print ((Names.qidToString (Names.constQid c)) ^ " ") end
  else begin () end; if !Global.chatter > 4 then begin Trace.clause c end
  else begin () end;
(begin try
         I.ConDec
           (s, m, k, status, (worldifyClause (I.Null, v_, w_, P.top)), l_)
 with | Error' (occ, msg) -> raise (Error (wrapMsg (c, occ, msg))) end) end
let rec worldifyBlock =
  begin function
  | (g_, []) -> ()
  | (g_, (Dec (_, v_) as d_)::l_) ->
      let a = I.targetFam v_ in
      let w'_ = W.getWorlds a in
      (begin checkClause w'_
               (g_, (worldifyClause (I.Null, v_, w'_, P.top)), P.top);
       worldifyBlock ((decUName (g_, d_)), l_) end) end
let rec worldifyBlocks =
  begin function
  | [] -> ()
  | b::bs_ ->
      let _ = worldifyBlocks bs_ in
      let (Gsome, Lblock) = I.constBlock b in
      let _ = print "|" in
      (begin try worldifyBlock (Gsome, Lblock)
       with
       | Error' (occ, s) ->
           raise
             (Error (wrapMsgBlock (b, occ, "World not hereditarily closed"))) end) end
let rec worldifyWorld (Worlds (bs_)) = worldifyBlocks bs_
let rec worldify a =
  let w_ = W.getWorlds a in
  let _ = print "[?" in
  let w'_ = worldifyWorld w_ in
  let _ = print ";" in
  let _ =
    if !Global.chatter > 3
    then
      begin print
              (((^) "World checking family " Names.qidToString
                  (Names.constQid a))
                 ^ ":\n") end
    else begin () end in
  let condecs =
    map
      (begin function
       | Const c ->
           (begin try worldifyConDec w_ (c, (I.sgnLookup c))
            with | Error' (occ, s) -> raise (Error (wrapMsg (c, occ, s))) end) end)
    (Index.lookup a) in
  let _ =
    map
      (begin function
       | condec -> (begin print "#"; checkConDec w_ condec end) end)
    condecs in
  let _ = print "]" in
  let _ = if !Global.chatter = 4 then begin print "\n" end else begin () end in
  condecs
let worldify = worldify
let worldifyGoal =
  begin function
  | (g_, v_) -> worldifyGoal (g_, v_, (W.getWorlds (I.targetFam v_)), P.top) end
end
