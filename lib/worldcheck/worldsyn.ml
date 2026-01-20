
module type WORLDSYN  =
  sig
    exception Error of string 
    val reset : unit -> unit
    val install : IntSyn.cid -> Tomega.__Worlds -> unit
    val lookup : IntSyn.cid -> Tomega.__Worlds
    val uninstall : IntSyn.cid -> bool
    val worldcheck : Tomega.__Worlds -> IntSyn.cid -> unit
    val ctxToList : IntSyn.__Dec IntSyn.__Ctx -> IntSyn.__Dec list
    val isSubsumed : Tomega.__Worlds -> IntSyn.cid -> unit
    val getWorlds : IntSyn.cid -> Tomega.__Worlds
  end;;




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
    let rec wrapMsg c occ msg =
      match Origins.originLookup c with
      | (fileName, None) -> (fileName ^ ":") ^ msg
      | (fileName, Some occDec) ->
          P.wrapLoc'
            ((P.Loc (fileName, (P.occToRegionDec occDec occ))),
              (Origins.linesInfoLookup fileName),
              ((((^) "While checking constant " Names.qidToString
                   (Names.constQid c))
                  ^ ":\n")
                 ^ msg))
    type nonrec dlist = IntSyn.__Dec list
    let (worldsTable : T.__Worlds Table.__Table) = Table.new__ 0
    let rec reset () = Table.clear worldsTable
    let rec insert cid (__W) = Table.insert worldsTable (cid, __W)
    let rec getWorlds b =
      match Table.lookup worldsTable b with
      | None ->
          raise
            (Error
               (((^) "Family " Names.qidToString (Names.constQid b)) ^
                  " has no worlds declaration"))
      | Some (Wb) -> Wb
    let (subsumedTable : unit Table.__Table) = Table.new__ 0
    let rec subsumedReset () = Table.clear subsumedTable
    let rec subsumedInsert cid = Table.insert subsumedTable (cid, ())
    let rec subsumedLookup cid =
      match Table.lookup subsumedTable cid with
      | None -> false
      | Some _ -> true
    type __Reg =
      | Block of (I.dctx * dlist) 
      | Seq of (dlist * I.__Sub) 
      | Star of __Reg 
      | Plus of (__Reg * __Reg) 
      | One 
    exception Success 
    let rec formatReg r =
      ((match r with
        | Block (__G, dl) -> Print.formatDecList (__G, dl)
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
        | One -> F.String "1")
      (* Is this correct? - gaw *)(* Fixed June 3, 2009 -fp,cs *))
    let rec formatSubsump msg (__G) dl (Rb) b =
      F.HVbox
        (([F.String msg;
          F.Space;
          F.String "for family";
          F.Space;
          F.String ((Names.qidToString (Names.constQid b)) ^ ":");
          F.Break;
          Print.formatDecList (__G, dl);
          F.Break;
          F.String "</:";
          F.Space;
          formatReg Rb])
        (* F.Newline (), *)(* Do not print some-variables; reenable if necessary *)
        (* June 3, 2009 -fp,cs *)(* Print.formatCtx(I.Null, G), F.Break, F.String "|-", F.Space, *))
      (*
            F.HVbox ([F.String ((Names.qidToString (Names.constQid b)) ^ ":")])
        *)
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
      | nil -> true
      | _ -> false
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
    let rec wGoalToString (__G, __L) (Seq (piDecs, t)) =
      F.makestring_fmt
        (F.HVbox
           [F.HVbox (formatDList (__G, __L, I.id));
           F.Break;
           F.String "<|";
           F.Break;
           F.HVbox (formatDList (__G, piDecs, t))])
    let rec worldToString (__G) (Seq (piDecs, t)) =
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
    let rec subGoalToDList =
      function
      | Pi ((__D, _), __V) -> (::) __D subGoalToDList __V
      | Root _ -> nil
    let rec worldsToReg =
      function | Worlds nil -> One | Worlds cids -> Star (worldsToReg' cids)
    let rec worldsToReg' =
      function
      | cid::nil -> Block (I.constBlock cid)
      | cid::cids -> Plus ((Block (I.constBlock cid)), (worldsToReg' cids))
    let rec init __8__ __9__ __10__ =
      match (__8__, __9__, __10__) with
      | (b, _, nil) -> (Trace.success (); raise Success)
      | (b, __G, ((Dec (_, __V1) as D1)::__L2 as L)) ->
          if Subordinate.belowEq ((I.targetFam __V1), b)
          then (Trace.unmatched (__G, __L); ())
          else init b ((decUName (__G, __D1)), __L2)
    let rec accR __11__ __12__ __13__ __14__ =
      match (__11__, __12__, __13__, __14__) with
      | (GL, One, b, k) -> k GL
      | (((__G, __L) as GL), Block (someDecs, piDecs), b, k) ->
          let t = createEVarSub (__G, someDecs) in
          let _ = Trace.matchBlock (GL, (Seq (piDecs, t))) in
          let k' (GL') =
            if noConstraints (__G, t)
            then k GL'
            else (Trace.constraintsRemain (); ()) in
          ((accR (GL, (Seq (piDecs, t)), b, k'))
            (* G |- t : someDecs *)(* if block matches, check for remaining constraints *))
      | ((__G, ((Dec (_, __V1) as D)::__L2 as L)),
         (Seq (((Dec (_, V1'))::L2' as B'), t) as L'), b, k) ->
          if Unify.unifiable (__G, (__V1, I.id), (V1', t))
          then
            accR
              (((decUName (__G, __D)), __L2), (Seq (L2', (I.dot1 t))), b, k)
          else
            ((if Subordinate.belowEq ((I.targetFam __V1), b)
              then (Trace.mismatch (__G, (__V1, I.id), (V1', t)); ())
              else
                accR
                  (((decUName (__G, __D)), __L2),
                    (Seq (__B', (I.comp (t, I.shift)))), b, k))
            (* relevant to family b, fail *)(* not relevant to family b, skip in L *))
      | (GL, Seq (nil, t), b, k) -> k GL
      | (((__G, nil) as GL), (Seq (__L', t) as R), b, k) ->
          (Trace.missing (__G, __R); ())
      | (GL, Plus (r1, r2), b, k) ->
          (CSManager.trail (fun () -> accR (GL, r1, b, k));
           accR (GL, r2, b, k))
      | (GL, Star (One), b, k) -> k GL
      | (GL, (Star r' as r), b, k) ->
          (CSManager.trail (fun () -> k GL);
           accR (GL, r', b, (fun (GL') -> accR (GL', r, b, k))))(* r' does not accept empty declaration list *)
      (* only possibility for non-termination in next rule *)(* L is missing *)
      (* Mon May 7 2007 -fp *)(* fixed bug in previous line; was: t instead of t o ^ *)
    let rec checkSubsumedBlock (__G) (__L') (Rb) b =
      try
        accR ((__G, __L'), Rb, b, (init b));
        raise
          (Error
             (F.makestring_fmt
                (formatSubsump "World subsumption failure" (__G, __L', Rb, b))))
      with | Success -> ()
    let rec checkSubsumedWorlds __15__ __16__ __17__ =
      match (__15__, __16__, __17__) with
      | (nil, Rb, b) -> ()
      | (cid::cids, Rb, b) ->
          let (someDecs, piDecs) = I.constBlock cid in
          (checkSubsumedBlock ((Names.ctxName someDecs), piDecs, Rb, b);
           checkSubsumedWorlds (cids, Rb, b))
    let rec checkBlocks (Worlds cids) (__G) (__V) occ =
      try
        let b = I.targetFam __V in
        let Wb =
          try getWorlds b with | Error msg -> raise (Error' (occ, msg)) in
        let Rb = worldsToReg Wb in
        let _ =
          if subsumedLookup b
          then ()
          else
            (try checkSubsumedWorlds (cids, Rb, b); subsumedInsert b
             with | Error msg -> raise (Error' (occ, msg))) in
        let __L = subGoalToDList __V in
        accR ((__G, __L), Rb, b, (init b));
        raise
          (Error'
             (occ,
               (F.makestring_fmt
                  (formatSubsump "World violation" (__G, __L, Rb, b)))))
      with | Success -> ()
    let rec checkClause __18__ __19__ __20__ __21__ =
      match (__18__, __19__, __20__, __21__) with
      | (__G, Root (a, __S), __W, occ) -> ()
      | (__G, Pi (((Dec (_, __V1) as D), I.Maybe), __V2), __W, occ) ->
          (checkClause ((decEName (__G, __D)), __V2, __W, (P.body occ));
           checkGoal (__G, __V1, __W, (P.label occ)))
      | (__G, Pi (((Dec (_, __V1) as D), I.No), __V2), __W, occ) ->
          (checkBlocks __W (__G, __V1, (P.label occ));
           checkClause ((decEName (__G, __D)), __V2, __W, (P.body occ));
           checkGoal (__G, __V1, __W, (P.label occ)))
    let rec checkGoal __22__ __23__ __24__ __25__ =
      match (__22__, __23__, __24__, __25__) with
      | (__G, Root (a, __S), __W, occ) -> ()
      | (__G, Pi (((Dec (_, __V1) as D), _), __V2), __W, occ) ->
          (checkGoal ((decUName (__G, __D)), __V2, __W, (P.body occ));
           checkClause (__G, __V1, __W, (P.label occ)))
    let rec worldcheck (__W) a =
      let _ =
        if (!Global.chatter) > 3
        then
          print
            (((^) "World checking family " Names.qidToString
                (Names.constQid a))
               ^ ":\n")
        else () in
      let _ = subsumedReset () in
      let rec checkAll =
        function
        | nil -> ()
        | (Const c)::clist ->
            (if (!Global.chatter) = 4
             then print ((Names.qidToString (Names.constQid c)) ^ " ")
             else ();
             if (!Global.chatter) > 4 then Trace.clause c else ();
             (try checkClause (I.Null, (I.constType c), __W, P.top)
              with
              | Error' (occ, msg) -> raise (Error (wrapMsg (c, occ, msg))));
             checkAll clist)
        | (Def d)::clist ->
            (if (!Global.chatter) = 4
             then print ((Names.qidToString (Names.constQid d)) ^ " ")
             else ();
             if (!Global.chatter) > 4 then Trace.clause d else ();
             (try checkClause (I.Null, (I.constType d), __W, P.top)
              with
              | Error' (occ, msg) -> raise (Error (wrapMsg (d, occ, msg))));
             checkAll clist) in
      let _ = checkAll (Index.lookup a) in
      let _ = if (!Global.chatter) = 4 then print "\n" else () in ((())
        (* initialize table of subsumed families *))
    let rec ctxAppend __26__ __27__ =
      match (__26__, __27__) with
      | (__G, I.Null) -> __G
      | (__G, Decl (__G', __D)) -> I.Decl ((ctxAppend (__G, __G')), __D)
    let rec checkSubordBlock (__G) (__G') (__L) =
      checkSubordBlock' ((ctxAppend (__G, __G')), __L)
    let rec checkSubordBlock' __28__ __29__ =
      match (__28__, __29__) with
      | (__G, (Dec (_, __V) as D)::__L') ->
          (((Subordinate.respectsN (__G, __V);
             checkSubordBlock' ((I.Decl (__G, __D)), __L')))
          (* is V nf?  Assume here: yes! *))
      | (__G, nil) -> ()
    let rec conDecBlock =
      function
      | BlockDec (_, _, Gsome, Lpi) -> (Gsome, Lpi)
      | condec ->
          raise
            (Error
               (((^) "Identifier " I.conDecName condec) ^
                  " is not a block label"))
    let rec constBlock cid = conDecBlock (I.sgnLookup cid)
    let rec checkSubordWorlds =
      function
      | nil -> ()
      | cid::cids ->
          let (someDecs, piDecs) = constBlock cid in
          (checkSubordBlock (I.Null, someDecs, piDecs);
           checkSubordWorlds cids)
    let rec install a (Worlds cids as W) =
      (try checkSubordWorlds cids with | Error msg -> raise (Error msg));
      insert (a, __W)
    let rec uninstall a =
      match Table.lookup worldsTable a with
      | None -> false
      | Some _ -> (Table.delete worldsTable a; true)
    let rec lookup a = getWorlds a
    let rec ctxToList (Gin) =
      let rec ctxToList' __30__ __31__ =
        match (__30__, __31__) with
        | (I.Null, __G) -> __G
        | (Decl (__G, __D), __G') -> ctxToList' (__G, (__D :: __G')) in
      ctxToList' (Gin, nil)
    let rec isSubsumed (Worlds cids) b =
      let Wb = getWorlds b in
      let Rb = worldsToReg Wb in
      if subsumedLookup b
      then ()
      else (checkSubsumedWorlds (cids, Rb, b); subsumedInsert b)
    let reset = reset
    let install = install
    let lookup = lookup
    let uninstall = uninstall
    let worldcheck = worldcheck
    let ctxToList = ctxToList
    let isSubsumed = isSubsumed
    let getWorlds = getWorlds
  end ;;
