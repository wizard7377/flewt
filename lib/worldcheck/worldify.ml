
module type WORLDIFY  =
  sig
    exception Error of string 
    val worldify : IntSyn.cid -> IntSyn.__ConDec list
    val worldifyGoal :
      IntSyn.__Dec IntSyn.__Ctx -> IntSyn.__Exp -> IntSyn.__Exp
  end;;




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
    let rec wrapMsg c occ msg =
      match Origins.originLookup c with
      | (fileName, NONE) -> (fileName ^ ":") ^ msg
      | (fileName, Some occDec) ->
          P.wrapLoc'
            ((P.Loc (fileName, (P.occToRegionDec occDec occ))),
              (Origins.linesInfoLookup fileName),
              ((((^) "Constant " Names.qidToString (Names.constQid c)) ^ ":")
                 ^ msg))
    let rec wrapMsgBlock c occ msg =
      match Origins.originLookup c with
      | (fileName, NONE) -> (fileName ^ ":") ^ msg
      | (fileName, Some occDec) ->
          P.wrapLoc'
            ((P.Loc (fileName, (P.occToRegionDec occDec occ))),
              (Origins.linesInfoLookup fileName),
              ((((^) "Block " Names.qidToString (Names.constQid c)) ^ ":") ^
                 msg))
    type nonrec dlist = IntSyn.__Dec list
    module W = WorldSyn
    type __Reg =
      | Block of (I.cid * (I.dctx * dlist)) 
      | Seq of (int * dlist * I.__Sub) 
      | Star of __Reg 
      | Plus of (__Reg * __Reg) 
      | One 
    exception Success of I.__Exp 
    let rec createEVarSub __0__ __1__ =
      match (__0__, __1__) with
      | (__G, I.Null) -> I.Shift (I.ctxLength __G)
      | (__G, Decl (__G', (Dec (_, __V) as D))) ->
          let s = createEVarSub (__G, __G') in
          let __V' = I.EClo (__V, s) in
          let __X = I.newEVar (__G, __V') in I.Dot ((I.Exp __X), s)
    let rec collectConstraints =
      function
      | nil -> nil
      | (EVar (_, _, _, { contents = nil }))::__Xs -> collectConstraints __Xs
      | (EVar (_, _, _, { contents = constrs }))::__Xs ->
          (@) (Constraints.simplify constrs) collectConstraints __Xs(* constrs <> nil *)
    let rec collectEVars __2__ __3__ __4__ =
      match (__2__, __3__, __4__) with
      | (__G, Dot (Exp (__X), s), __Xs) ->
          collectEVars
            (__G, s, (Abstract.collectEVars (__G, (__X, I.id), __Xs)))
      | (__G, Shift _, __Xs) -> __Xs
    let rec noConstraints (__G) s =
      match collectConstraints (collectEVars (__G, s, nil)) with
      | nil -> true__
      | _ -> false__
    let rec formatD (__G) (__D) =
      F.Hbox
        (((::) ((::) (F.String "{") Print.formatDec (__G, __D)) F.String "}")
           :: nil)
    let rec formatDList __5__ __6__ __7__ =
      match (__5__, __6__, __7__) with
      | (__G, nil, t) -> nil
      | (__G, (__D)::nil, t) ->
          let __D' = I.decSub (__D, t) in (((formatD (__G, __D')) :: nil)
            (* Names.decUName (G, I.decSub(D, t)) *))
      | (__G, (__D)::__L, t) ->
          let __D' = I.decSub (__D, t) in
          (((::) ((formatD (__G, __D')) :: F.Break) formatDList
              ((I.Decl (__G, __D')), __L, (I.dot1 t)))
            (* Names.decUName (G, I.decSub (D, t)) *))
    let rec wGoalToString (__G, __L) (Seq (_, piDecs, t)) =
      F.makestring_fmt
        (F.HVbox
           [F.HVbox (formatDList (__G, __L, I.id));
           F.Break;
           F.String "<|";
           F.Break;
           F.HVbox (formatDList (__G, piDecs, t))])
    let rec worldToString (__G) (Seq (_, piDecs, t)) =
      F.makestring_fmt (F.HVbox (formatDList (__G, piDecs, t)))
    let rec hypsToString (__G) (__L) =
      F.makestring_fmt (F.HVbox (formatDList (__G, __L, I.id)))
    let rec mismatchToString (__G) (__V1, s1) (__V2, s2) =
      F.makestring_fmt
        (F.HVbox
           [Print.formatExp (__G, (I.EClo (__V1, s1)));
           F.Break;
           F.String "<>";
           F.Break;
           Print.formatExp (__G, (I.EClo (__V2, s2)))])
    module Trace :
      sig
        val clause : I.cid -> unit
        val constraintsRemain : unit -> unit
        val matchBlock : (I.dctx * dlist) -> __Reg -> unit
        val unmatched : I.dctx -> dlist -> unit
        val missing : I.dctx -> __Reg -> unit
        val mismatch : I.dctx -> I.eclo -> I.eclo -> unit
        val success : unit -> unit
      end =
      struct
        let rec clause c =
          print
            (((^) "World checking clause " Names.qidToString
                (Names.constQid c))
               ^ "\n")
        let rec constraintsRemain () =
          if (!Global.chatter) > 7
          then
            print
              "Constraints remain after matching hypotheses against context block\n"
          else ()
        let rec matchBlock (GL) (__R) =
          if (!Global.chatter) > 7
          then print (((^) "Matching:\n" wGoalToString (GL, __R)) ^ "\n")
          else ()(* R = (D1,...,Dn)[t] *)
        let rec unmatched (GL) =
          if (!Global.chatter) > 7
          then print (((^) "Unmatched hypotheses:\n" hypsToString GL) ^ "\n")
          else ()
        let rec missing (__G) (__R) =
          if (!Global.chatter) > 7
          then
            print
              (((^) "Missing hypotheses:\n" worldToString (__G, __R)) ^ "\n")
          else ()(* R = (D1,...,Dn)[t] *)
        let rec mismatch (__G) (__Vs1) (__Vs2) =
          if (!Global.chatter) > 7
          then
            print
              (((^) "Mismatch:\n" mismatchToString (__G, __Vs1, __Vs2)) ^
                 "\n")
          else ()
        let rec success () =
          if (!Global.chatter) > 7 then print "Success\n" else ()
      end 
    let rec decUName (__G) (__D) = I.Decl (__G, (Names.decUName (__G, __D)))
    let rec decEName (__G) (__D) = I.Decl (__G, (Names.decEName (__G, __D)))
    let rec equivList __8__ __9__ __10__ =
      match (__8__, __9__, __10__) with
      | (__G, (_, nil), nil) -> true__
      | (__G, (t, (Dec (_, __V1))::__L1), (Dec (_, __V2))::__L2) ->
          (try
             Unify.unify (__G, (__V1, t), (__V2, I.id));
             equivList (__G, ((I.dot1 t), __L1), __L2)
           with | Unify _ -> false__)
      | _ -> false__
    let rec equivBlock (__G, __L) (__L') =
      let t = createEVarSub (I.Null, __G) in
      equivList (I.Null, (t, __L), __L')
    let rec equivBlocks __11__ __12__ =
      match (__11__, __12__) with
      | (__W1, nil) -> true__
      | (nil, __L') -> false__
      | (b::__W1, __L') ->
          (equivBlock ((I.constBlock b), __L')) || (equivBlocks __W1 __L')
    let rec strengthen __13__ __14__ __15__ =
      match (__13__, __14__, __15__) with
      | (a, t, nil) -> nil
      | (a, t, (Dec (_, __V) as D)::__L) ->
          if Subordinate.below ((I.targetFam __V), a)
          then (::) (I.decSub (__D, t)) strengthen a ((I.dot1 t), __L)
          else strengthen a ((I.Dot (I.Undef, t)), __L)
    let rec subsumedBlock a (__W1) (__G) (__L) =
      let t = createEVarSub (I.Null, __G) in
      let __L' = strengthen a (t, __L) in
      ((if equivBlocks __W1 __L'
        then ()
        else raise (Error "Static world subsumption failed"))
        (* G |- t : someDecs *))
    let rec subsumedBlocks __16__ __17__ __18__ =
      match (__16__, __17__, __18__) with
      | (a, __W1, nil) -> ()
      | (a, __W1, b::__W2) ->
          (subsumedBlock a __W1 (I.constBlock b); subsumedBlocks a __W1 __W2)
    let rec subsumedWorld a (Worlds (__W1)) (Worlds (__W2)) =
      subsumedBlocks a __W1 __W2
    let rec eqCtx __19__ __20__ =
      match (__19__, __20__) with
      | (I.Null, I.Null) -> true__
      | (Decl (__G1, __D1), Decl (__G2, __D2)) ->
          (eqCtx (__G1, __G2)) && (Conv.convDec ((__D1, I.id), (__D2, I.id)))
      | _ -> false__
    let rec eqList __21__ __22__ =
      match (__21__, __22__) with
      | (nil, nil) -> true__
      | ((__D1)::__L1, (__D2)::__L2) ->
          (Conv.convDec ((__D1, I.id), (__D2, I.id))) &&
            (eqList (__L1, __L2))
      | _ -> false__
    let rec eqBlock b1 b2 =
      let (__G1, __L1) = I.constBlock b1 in
      let (__G2, __L2) = I.constBlock b2 in
      (eqCtx (__G1, __G2)) && (eqList (__L1, __L2))
    let rec subsumedCtx __23__ __24__ =
      match (__23__, __24__) with
      | (I.Null, __W) -> ()
      | (Decl (__G, BDec (_, (b, _))), (Worlds (__Bs) as W)) ->
          (if List.exists (fun b' -> eqBlock (b, b')) __Bs
           then ()
           else raise (Error "Dynamic world subsumption failed");
           subsumedCtx (__G, __W))
      | (Decl (__G, _), (Worlds (__Bs) as W)) -> subsumedCtx (__G, __W)
    let rec checkGoal __25__ __26__ __27__ __28__ =
      match (__25__, __26__, __27__, __28__) with
      | (__W, __G, Root (Const a, __S), occ) ->
          let __W' = W.getWorlds a in
          (subsumedWorld a __W' __W; subsumedCtx (__G, __W))
      | (__W, __G, Pi ((__D, _), __V2), occ) ->
          checkGoal __W ((decUName (__G, __D)), __V2, (P.body occ))
    let rec checkClause __29__ __30__ __31__ __32__ =
      match (__29__, __30__, __31__, __32__) with
      | (__W, __G, Root (a, __S), occ) -> ()
      | (__W, __G, Pi (((Dec (_, __V1) as D), I.Maybe), __V2), occ) ->
          checkClause __W ((decEName (__G, __D)), __V2, (P.body occ))
      | (__W, __G, Pi (((Dec (_, __V1) as D), I.No), __V2), occ) ->
          (checkClause __W ((decEName (__G, __D)), __V2, (P.body occ));
           checkGoal __W (__G, __V1, (P.label occ)))
    let rec checkConDec (__W) (ConDec (s, m, k, status, __V, __L)) =
      checkClause __W (I.Null, __V, P.top)
    let rec subGoalToDList =
      function
      | Pi ((__D, _), __V) -> (::) __D subGoalToDList __V
      | Root _ -> nil
    let rec worldsToReg =
      function | Worlds nil -> One | Worlds cids -> Star (worldsToReg' cids)
    let rec worldsToReg' =
      function
      | cid::nil -> Block (cid, (I.constBlock cid))
      | cid::cids ->
          Plus ((Block (cid, (I.constBlock cid))), (worldsToReg' cids))
    let rec init __33__ __34__ =
      match (__33__, __34__) with
      | (_, ((Root _, s) as Vs)) ->
          (Trace.success (); raise (Success (Whnf.normalize __Vs)))
      | (__G, ((Pi (((Dec (_, __V1) as D1), _), __V2) as V), s)) ->
          (Trace.unmatched (__G, (subGoalToDList (Whnf.normalize (__V, s))));
           ())
    let rec accR __35__ __36__ __37__ =
      match (__35__, __36__, __37__) with
      | (GVs, One, k) -> k GVs
      | (((__G, (__V, s)) as GVs), Block (c, (someDecs, piDecs)), k) ->
          let t = createEVarSub (__G, someDecs) in
          let _ =
            Trace.matchBlock
              ((__G, (subGoalToDList (Whnf.normalize (__V, s)))),
                (Seq (1, piDecs, t))) in
          let k' (__G') (__Vs') =
            if noConstraints (__G, t)
            then k (__G', __Vs')
            else (Trace.constraintsRemain (); ()) in
          (((try
               accR
                 (((decUName (__G, (I.BDec (NONE, (c, t))))),
                    (__V, (I.comp (s, I.shift)))),
                   (Seq (1, piDecs, (I.comp (t, I.shift)))), k')
             with
             | Success (__V) ->
                 raise
                   (Success
                      (Whnf.normalize
                         ((I.Pi (((I.BDec (NONE, (c, t))), I.Maybe), __V)),
                           I.id)))))
            (* G |- t : someDecs *))
      | ((__G, ((Pi (((Dec (_, __V1) as D), _), __V2) as V), s)),
         (Seq (j, (Dec (_, V1'))::L2', t) as L'), k) ->
          if Unify.unifiable (__G, (__V1, s), (V1', t))
          then
            accR
              ((__G,
                 (__V2,
                   (I.Dot
                      ((I.Exp (I.Root ((I.Proj ((I.Bidx 1), j)), I.Nil))), s)))),
                (Seq
                   ((j + 1), L2',
                     (I.Dot
                        ((I.Exp (I.Root ((I.Proj ((I.Bidx 1), j)), I.Nil))),
                          t)))), k)
          else (Trace.mismatch (__G, (__V1, I.id), (V1', t)); ())
      | (GVs, Seq (_, nil, t), k) -> k GVs
      | (((__G, (Root _, s)) as GVs), (Seq (_, __L', t) as R), k) ->
          (Trace.missing (__G, __R); ())
      | (GVs, Plus (r1, r2), k) ->
          (CSManager.trail (fun () -> accR (GVs, r1, k)); accR (GVs, r2, k))
      | (GVs, Star (One), k) -> k GVs
      | (GVs, (Star r' as r), k) ->
          (CSManager.trail (fun () -> k GVs);
           accR (GVs, r', (fun (GVs') -> accR (GVs', r, k))))(* r' does not accept empty declaration list *)
      (* only possibility for non-termination in next rule *)(* L is missing *)
    let rec worldifyGoal (__G) (__V) (Worlds cids as W) occ =
      try
        let b = I.targetFam __V in
        let Wb = W.getWorlds b in
        let Rb = worldsToReg Wb in
        accR ((__G, (__V, I.id)), Rb, init);
        raise (Error' (occ, "World violation"))
      with | Success (__V') -> __V'
    let rec worldifyClause __38__ __39__ __40__ __41__ =
      match (__38__, __39__, __40__, __41__) with
      | (__G, (Root (a, __S) as V), __W, occ) -> __V
      | (__G, Pi (((Dec (x, __V1) as D), I.Maybe), __V2), __W, occ) ->
          let _ = print "{" in
          let __W2 =
            worldifyClause ((decEName (__G, __D)), __V2, __W, (P.body occ)) in
          let _ = print "}" in
          ((I.Pi
              (((I.Dec (((x, __V1))(* W1*))), I.Maybe),
                __W2))
            (*         val W1 = worldifyGoal (G, V1, W, P.label occ) *))
      | (__G, Pi (((Dec (x, __V1) as D), I.No), __V2), __W, occ) ->
          let __W1 = worldifyGoal (__G, __V1, __W, (P.label occ)) in
          let __W2 =
            worldifyClause ((decEName (__G, __D)), __V2, __W, (P.body occ)) in
          I.Pi (((I.Dec (x, __W1)), I.No), __W2)
    let rec worldifyConDec (__W) c (ConDec (s, m, k, status, __V, __L)) =
      if (!Global.chatter) = 4
      then print ((Names.qidToString (Names.constQid c)) ^ " ")
      else ();
      if (!Global.chatter) > 4 then Trace.clause c else ();
      (try
         I.ConDec
           (s, m, k, status, (worldifyClause (I.Null, __V, __W, P.top)), __L)
       with | Error' (occ, msg) -> raise (Error (wrapMsg (c, occ, msg))))
    let rec worldifyBlock __42__ __43__ =
      match (__42__, __43__) with
      | (__G, nil) -> ()
      | (__G, (Dec (_, __V) as D)::__L) ->
          let a = I.targetFam __V in
          let __W' = W.getWorlds a in
          (checkClause __W'
             (__G, (worldifyClause (I.Null, __V, __W', P.top)), P.top);
           worldifyBlock ((decUName (__G, __D)), __L))
    let rec worldifyBlocks =
      function
      | nil -> ()
      | b::__Bs ->
          let _ = worldifyBlocks __Bs in
          let (Gsome, Lblock) = I.constBlock b in
          let _ = print "|" in
          (try worldifyBlock (Gsome, Lblock)
           with
           | Error' (occ, s) ->
               raise
                 (Error
                    (wrapMsgBlock (b, occ, "World not hereditarily closed"))))
    let rec worldifyWorld (Worlds (__Bs)) = worldifyBlocks __Bs
    let rec worldify a =
      let __W = W.getWorlds a in
      let _ = print "[?" in
      let __W' = worldifyWorld __W in
      let _ = print ";" in
      let _ =
        if (!Global.chatter) > 3
        then
          print
            (((^) "World checking family " Names.qidToString
                (Names.constQid a))
               ^ ":\n")
        else () in
      let condecs =
        map
          (fun (Const c) ->
             try worldifyConDec __W (c, (I.sgnLookup c))
             with | Error' (occ, s) -> raise (Error (wrapMsg (c, occ, s))))
          (Index.lookup a) in
      let _ = map (fun condec -> print "#"; checkConDec __W condec) condecs in
      let _ = print "]" in
      let _ = if (!Global.chatter) = 4 then print "\n" else () in condecs
    let worldify = worldify
    let worldifyGoal (__G) (__V) =
      worldifyGoal (__G, __V, (W.getWorlds (I.targetFam __V)), P.top)
  end ;;
