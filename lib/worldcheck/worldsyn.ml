
(* World Checking *)
(* Author: Carsten Schuermann *)
module type WORLDSYN  =
  sig
    exception Error of string 
    val reset : unit -> unit
    val install : (IntSyn.cid * Tomega.__Worlds) -> unit
    val lookup : IntSyn.cid -> Tomega.__Worlds
    (* raises Error if undeclared *)
    val uninstall : IntSyn.cid -> bool
    (* true if declared *)
    val worldcheck : Tomega.__Worlds -> IntSyn.cid -> unit
    val ctxToList : IntSyn.__Dec IntSyn.__Ctx -> IntSyn.__Dec list
    val isSubsumed : Tomega.__Worlds -> IntSyn.cid -> unit
    val getWorlds : IntSyn.cid -> Tomega.__Worlds
  end;;




(* World Checking *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning *)
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
                           (*! sharing Whnf.IntSyn = IntSyn !*)
                           (*! sharing Index.IntSyn = IntSyn !*)
                           (*! sharing Names.IntSyn = IntSyn !*)
                           (*! sharing Unify.IntSyn = IntSyn !*)
                           (*! sharing Abstract.IntSyn = IntSyn !*)
                           (*! sharing Constraints.IntSyn = IntSyn !*)
                           (*! structure CSManager : CS_MANAGER !*)
                           (*! sharing CSManager.IntSyn = IntSyn !*)
                           (*! sharing Subordinate.IntSyn = IntSyn !*)
                           (*! sharing Print.IntSyn = IntSyn !*)
                           (*! structure Paths : PATHS !*)
                           (*! sharing Origins.Paths = Paths !*)
                           (*! sharing Origins.IntSyn = IntSyn !*)
                           module Timers : TIMERS
                         end) : WORLDSYN =
  struct
    module I = IntSyn
    module T = Tomega
    module P = Paths
    module F = Print.Formatter
    exception Error of string 
    exception Error' of (P.occ * string) 
    (* copied from terminates/reduces.fun *)
    let rec wrapMsg (c, occ, msg) =
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
    let rec insert (cid, W) = Table.insert worldsTable (cid, W)
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
      | None -> false__
      | Some _ -> true__
    type __Reg =
      | Block of (I.dctx * dlist) 
      | Seq of (dlist * I.__Sub) 
      | Star of __Reg 
      | Plus of (__Reg * __Reg) 
      | One 
    exception Success 
    let rec formatReg r =
      match r with
      | Block (__g, dl) -> Print.formatDecList (__g, dl)
      | Seq (dl, s) -> Print.formatDecList' (I.Null, (dl, s))
      | Star r -> F.hbox [F.String "("; formatReg r; F.String ")*"]
      | Plus (r1, r2) ->
          F.hVbox
            [F.String "(";
            formatReg r1;
            F.String ")";
            F.Break;
            F.String "|";
            F.space;
            F.String "(";
            formatReg r2;
            F.String ")"]
      | One -> F.String "1"
    let rec formatSubsump msg (__g, dl, Rb, b) =
      F.hVbox
        [F.String msg;
        F.space;
        F.String "for family";
        F.space;
        F.String ((Names.qidToString (Names.constQid b)) ^ ":");
        F.Break;
        Print.formatDecList (__g, dl);
        F.Break;
        F.String "</:";
        F.space;
        formatReg Rb]
    let rec createEVarSub =
      function
      | (__g, I.Null) -> I.Shift (I.ctxLength __g)
      | (__g, Decl (__g', (Dec (_, __v) as __d))) ->
          let s = createEVarSub (__g, __g') in
          let __v' = I.EClo (__v, s) in
          let x = I.newEVar (__g, __v') in I.Dot ((I.Exp x), s)
    let rec collectConstraints =
      function
      | nil -> nil
      | (EVar (_, _, _, ref nil))::__Xs -> collectConstraints __Xs
      | (EVar (_, _, _, ref constrs))::__Xs ->
          (@) (Constraints.simplify constrs) collectConstraints __Xs
    let rec collectEVars =
      function
      | (__g, Dot (Exp (x), s), __Xs) ->
          collectEVars (__g, s, (Abstract.collectEVars (__g, (x, I.id), __Xs)))
      | (__g, Shift _, __Xs) -> __Xs
    let rec noConstraints (__g, s) =
      match collectConstraints (collectEVars (__g, s, nil)) with
      | nil -> true__
      | _ -> false__
    let rec formatD (__g, __d) =
      F.hbox
        (((::) ((::) (F.String "{") Print.formatDec (__g, __d)) F.String "}") ::
           nil)
    let rec formatDList =
      function
      | (__g, nil, t) -> nil
      | (__g, (__d)::nil, t) ->
          let __d' = I.decSub (__d, t) in (formatD (__g, __d')) :: nil
      | (__g, (__d)::__l, t) ->
          let __d' = I.decSub (__d, t) in
          (::) ((formatD (__g, __d')) :: F.Break) formatDList
            ((I.Decl (__g, __d')), __l, (I.dot1 t))
    let rec wGoalToString ((__g, __l), Seq (piDecs, t)) =
      F.makestring_fmt
        (F.hVbox
           [F.hVbox (formatDList (__g, __l, I.id));
           F.Break;
           F.String "<|";
           F.Break;
           F.hVbox (formatDList (__g, piDecs, t))])
    let rec worldToString (__g, Seq (piDecs, t)) =
      F.makestring_fmt (F.hVbox (formatDList (__g, piDecs, t)))
    let rec hypsToString (__g, __l) =
      F.makestring_fmt (F.hVbox (formatDList (__g, __l, I.id)))
    let rec mismatchToString (__g, (V1, s1), (V2, s2)) =
      F.makestring_fmt
        (F.hVbox
           [Print.formatExp (__g, (I.EClo (V1, s1)));
           F.Break;
           F.String "<>";
           F.Break;
           Print.formatExp (__g, (I.EClo (V2, s2)))])
    module Trace :
      sig
        val clause : I.cid -> unit
        val constraintsRemain : unit -> unit
        val matchBlock : ((I.dctx * dlist) * __Reg) -> unit
        val unmatched : (I.dctx * dlist) -> unit
        val missing : (I.dctx * __Reg) -> unit
        val mismatch : (I.dctx * I.eclo * I.eclo) -> unit
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
        let rec matchBlock (GL, R) =
          if (!Global.chatter) > 7
          then print (((^) "Matching:\n" wGoalToString (GL, R)) ^ "\n")
          else ()
        let rec unmatched (GL) =
          if (!Global.chatter) > 7
          then print (((^) "Unmatched hypotheses:\n" hypsToString GL) ^ "\n")
          else ()
        let rec missing (__g, R) =
          if (!Global.chatter) > 7
          then
            print (((^) "Missing hypotheses:\n" worldToString (__g, R)) ^ "\n")
          else ()
        let rec mismatch (__g, Vs1, Vs2) =
          if (!Global.chatter) > 7
          then
            print (((^) "Mismatch:\n" mismatchToString (__g, Vs1, Vs2)) ^ "\n")
          else ()
        let rec success () =
          if (!Global.chatter) > 7 then print "Success\n" else ()
      end 
    let rec decUName (__g, __d) = I.Decl (__g, (Names.decUName (__g, __d)))
    let rec decEName (__g, __d) = I.Decl (__g, (Names.decEName (__g, __d)))
    let rec subGoalToDList =
      function | Pi ((__d, _), __v) -> (::) __d subGoalToDList __v | Root _ -> nil
    let rec worldsToReg =
      function | Worlds nil -> One | Worlds cids -> Star (worldsToReg' cids)
    let rec worldsToReg' =
      function
      | cid::nil -> Block (I.constBlock cid)
      | cid::cids -> Plus ((Block (I.constBlock cid)), (worldsToReg' cids))
    let rec init arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (b, (_, nil)) -> (Trace.success (); raise Success)
      | (b, (__g, ((Dec (_, V1) as D1)::L2 as __l))) ->
          if Subordinate.belowEq ((I.targetFam V1), b)
          then (Trace.unmatched (__g, __l); ())
          else init b ((decUName (__g, D1)), L2)
    let rec accR =
      function
      | (GL, One, b, k) -> k GL
      | (((__g, __l) as GL), Block (someDecs, piDecs), b, k) ->
          let t = createEVarSub (__g, someDecs) in
          let _ = Trace.matchBlock (GL, (Seq (piDecs, t))) in
          let k' =
            function
            | GL' ->
                if noConstraints (__g, t)
                then k GL'
                else (Trace.constraintsRemain (); ()) in
          accR (GL, (Seq (piDecs, t)), b, k')
      | ((__g, ((Dec (_, V1) as __d)::L2 as __l)),
         (Seq (((Dec (_, V1'))::L2' as B'), t) as __l'), b, k) ->
          if Unify.unifiable (__g, (V1, I.id), (V1', t))
          then accR (((decUName (__g, __d)), L2), (Seq (L2', (I.dot1 t))), b, k)
          else
            if Subordinate.belowEq ((I.targetFam V1), b)
            then (Trace.mismatch (__g, (V1, I.id), (V1', t)); ())
            else
              accR
                (((decUName (__g, __d)), L2), (Seq (B', (I.comp (t, I.shift)))),
                  b, k)
      | (GL, Seq (nil, t), b, k) -> k GL
      | (((__g, nil) as GL), (Seq (__l', t) as R), b, k) ->
          (Trace.missing (__g, R); ())
      | (GL, Plus (r1, r2), b, k) ->
          (CSManager.trail (function | () -> accR (GL, r1, b, k));
           accR (GL, r2, b, k))
      | (GL, Star (One), b, k) -> k GL
      | (GL, (Star r' as r), b, k) ->
          (CSManager.trail (function | () -> k GL);
           accR (GL, r', b, (function | GL' -> accR (GL', r, b, k))))
    let rec checkSubsumedBlock (__g, __l', Rb, b) =
      try
        accR ((__g, __l'), Rb, b, (init b));
        raise
          (Error
             (F.makestring_fmt
                (formatSubsump "World subsumption failure" (__g, __l', Rb, b))))
      with | Success -> ()
    let rec checkSubsumedWorlds =
      function
      | (nil, Rb, b) -> ()
      | (cid::cids, Rb, b) ->
          let (someDecs, piDecs) = I.constBlock cid in
          (checkSubsumedBlock ((Names.ctxName someDecs), piDecs, Rb, b);
           checkSubsumedWorlds (cids, Rb, b))
    let rec checkBlocks (Worlds cids) (__g, __v, occ) =
      try
        let b = I.targetFam __v in
        let Wb =
          try getWorlds b with | Error msg -> raise (Error' (occ, msg)) in
        let Rb = worldsToReg Wb in
        let _ =
          if subsumedLookup b
          then ()
          else
            (try checkSubsumedWorlds (cids, Rb, b); subsumedInsert b
             with | Error msg -> raise (Error' (occ, msg))) in
        let __l = subGoalToDList __v in
        accR ((__g, __l), Rb, b, (init b));
        raise
          (Error'
             (occ,
               (F.makestring_fmt
                  (formatSubsump "World violation" (__g, __l, Rb, b)))))
      with | Success -> ()
    let rec checkClause =
      function
      | (__g, Root (a, S), W, occ) -> ()
      | (__g, Pi (((Dec (_, V1) as __d), I.Maybe), V2), W, occ) ->
          (checkClause ((decEName (__g, __d)), V2, W, (P.body occ));
           checkGoal (__g, V1, W, (P.label occ)))
      | (__g, Pi (((Dec (_, V1) as __d), I.No), V2), W, occ) ->
          (checkBlocks W (__g, V1, (P.label occ));
           checkClause ((decEName (__g, __d)), V2, W, (P.body occ));
           checkGoal (__g, V1, W, (P.label occ)))
    let rec checkGoal =
      function
      | (__g, Root (a, S), W, occ) -> ()
      | (__g, Pi (((Dec (_, V1) as __d), _), V2), W, occ) ->
          (checkGoal ((decUName (__g, __d)), V2, W, (P.body occ));
           checkClause (__g, V1, W, (P.label occ)))
    let rec worldcheck (W) a =
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
             (try checkClause (I.Null, (I.constType c), W, P.top)
              with
              | Error' (occ, msg) -> raise (Error (wrapMsg (c, occ, msg))));
             checkAll clist)
        | (Def d)::clist ->
            (if (!Global.chatter) = 4
             then print ((Names.qidToString (Names.constQid d)) ^ " ")
             else ();
             if (!Global.chatter) > 4 then Trace.clause d else ();
             (try checkClause (I.Null, (I.constType d), W, P.top)
              with
              | Error' (occ, msg) -> raise (Error (wrapMsg (d, occ, msg))));
             checkAll clist) in
      let _ = checkAll (Index.lookup a) in
      let _ = if (!Global.chatter) = 4 then print "\n" else () in ()
    let rec ctxAppend =
      function
      | (__g, I.Null) -> __g
      | (__g, Decl (__g', __d)) -> I.Decl ((ctxAppend (__g, __g')), __d)
    let rec checkSubordBlock (__g, __g', __l) =
      checkSubordBlock' ((ctxAppend (__g, __g')), __l)
    let rec checkSubordBlock' =
      function
      | (__g, (Dec (_, __v) as __d)::__l') ->
          (Subordinate.respectsN (__g, __v);
           checkSubordBlock' ((I.Decl (__g, __d)), __l'))
      | (__g, nil) -> ()
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
    let rec install (a, (Worlds cids as W)) =
      (try checkSubordWorlds cids with | Error msg -> raise (Error msg));
      insert (a, W)
    let rec uninstall a =
      match Table.lookup worldsTable a with
      | None -> false__
      | Some _ -> (Table.delete worldsTable a; true__)
    let rec lookup a = getWorlds a
    let rec ctxToList (Gin) =
      let rec ctxToList' =
        function
        | (I.Null, __g) -> __g
        | (Decl (__g, __d), __g') -> ctxToList' (__g, (__d :: __g')) in
      ctxToList' (Gin, nil)
    let rec isSubsumed (Worlds cids) b =
      let Wb = getWorlds b in
      let Rb = worldsToReg Wb in
      if subsumedLookup b
      then ()
      else (checkSubsumedWorlds (cids, Rb, b); subsumedInsert b)
    (* subsumedTable
       For each family a that is world-checked, this
       contains the subordinate families b whose worlds
       subsume that of a modulo subordination
    *)
    (* Regular world expressions R
       Invariants:
       If R = (D1,...,Dn)[s] then __g |- s : __g' and __g' |- D1,...,Dn ctx
       If R = r* then r = 1 or r does not accept the empty world
    *)
    (* Regular world expressions  *)
    (* R ::= LD                   *)
    (*     | (D1,...,Dn)[s]       *)
    (*     | R*                   *)
    (*     | R1 + R2              *)
    (*     | 1                    *)
    (* signals worldcheck success *)
    (* Format a regular world *)
    (* __Is this correct? - gaw *)
    (* Fixed June 3, 2009 -fp,cs *)
    (* Format a subsumption failure judgment
       msg: Prefix for the message
       dl : declaration list
       Rb : regular world
       b : family
       Displays:

         msg for family b:
         __g |- dl </: Rb
     *)
    (*
            F.hVbox ([F.String ((Names.qidToString (Names.constQid b)) ^ ":")])
        *)
    (* F.newline (), *)
    (* Do not print some-variables; reenable if necessary *)
    (* June 3, 2009 -fp,cs *)
    (* Print.formatCtx(I.Null, __g), F.Break, F.String "|-", F.space, *)
    (* createEVarSub __g __g' = s

       Invariant:
       If   __g is a context
       and  __g' is a context
       then __g |- s : __g'
    *)
    (* from cover.fun *)
    (* collectConstraints (__Xs) = constrs
       collect all the constraints that may be attached to EVars in __Xs

       try simplifying away the constraints in case they are "hard"
    *)
    (* constrs <> nil *)
    (* collectEVars (__g, s, __Xs) = __Xs'
       adds all uninstantiated EVars from s to __Xs to obtain __Xs'
       Invariant: s is EVar substitutions
    *)
    (* other cases impossible by invariants since s is EVarSubst *)
    (* noConstraints (__g, s) = true iff there are no remaining constraints in s
       Invariants: s is an EVar substitution X1...Xn.^k
    *)
    (* end from cover.fun *)
    (************)
    (* Printing *)
    (************)
    (* Declarations *)
    (* Declaration lists *)
    (* Names.decUName (__g, I.decSub(__d, t)) *)
    (* Names.decUName (__g, I.decSub (__d, t)) *)
    (*
    fun hypsToDList (I.Root _) = nil
      | hypsToDList (I.Pi ((__d, _), __v)) =
          __d::hypsToDList __v
    *)
    (* Hypotheses and declaration lists *)
    (* Declaration list *)
    (* Hypotheses *)
    (* Mismatch between hypothesis and world declaration *)
    (***********)
    (* Tracing *)
    (***********)
    (* R = (D1,...,Dn)[t] *)
    (* R = (D1,...,Dn)[t] *)
    (**************************************)
    (* Matching hypotheses against worlds *)
    (**************************************)
    (* worldsToReg (Worlds [c1,...,cn]) = R
       W = R, except that R is a regular expression
       with non-empty contextblocks as leaves
    *)
    (* init b (__g, __l) raises Success iff __v is empty
       or none of the remaining declarations are relevant to b
       otherwise fails by returning ()
       Initial continuation for world checker

       Invariant: __g |- __l dlist, __l nf
    *)
    (* accR ((__g, __l), R, k)   raises Success
       iff __l = L1,L2 such that R accepts L1
           and k ((__g, L1), L2) succeeds
       otherwise fails by returning ()
       Invariant: __g |- __l dlist, __l nf
                  R regular world expression
       trails at choice points to undo EVar instantiations during matching
    *)
    (* __g |- t : someDecs *)
    (* if block matches, check for remaining constraints *)
    (* relevant to family b, fail *)
    (* not relevant to family b, skip in __l *)
    (* fixed bug in previous line; was: t instead of t o ^ *)
    (* Mon May 7 2007 -fp *)
    (* __l is missing *)
    (* only possibility for non-termination in next rule *)
    (* r' does not accept empty declaration list *)
    (* checkSubsumedBlock (__g, someDecs, piDecs, Rb, b) = ()
       iff block Some someDecs. PI piDecs is subsumed by Rb
       Effect: raises Error (msg) otherwise

       Invariants: Rb = reg (worlds (b))
    *)
    (* checkSubsumedWorlds (Wa, Rb, b) = ()
       iff Wa is subsumed by Rb
       Effect: raises Error (msg) otherwise

       Invariants: Rb = reg (worlds (b))
    *)
    (* checkBlocks W (__g, __v, occ) = ()
       iff __v = {{__g'}} a @ S and __g' satisfies worlds W
       Effect: raises Error'(occ, msg) otherwise

       Invariants: __g |- __v : type, __v nf
    *)
    (******************************)
    (* Checking clauses and goals *)
    (******************************)
    (* checkClause (__g, __v, W, occ) = ()
       iff all subgoals in __v satisfy world spec W
       Effect: raises Error' (occ', msg) otherwise

       Invariant: __g |- __v : type, __v nf
       occ is occurrence of __v in current clause
     *)
    (* checkGoal (__g, __v, W, occ) = ()
        iff all (embedded) subgoals in __v satisfy world spec W
        Effect: raises Error' (occ', msg) otherwise

        Invariant: __g |- __v : type, __v nf
     *)
    (* Question: should dependent Pi's really be checked recursively? *)
    (* Thu Mar 29 09:38:20 2001 -fp *)
    (* worldcheck W a = ()
       iff all subgoals in all clauses defining a satisfy world spec W
       Effect: raises Error(msg) otherwise, where msg includes location
    *)
    (* initialize table of subsumed families *)
    (**************************)
    (* Checking Subordination *)
    (**************************)
    (*
       At present, worlds declarations must respect the
       current subordination relation in order to guarantee
       soundness.
    *)
    (* checkSubordBlock (__g, __g', __l') = ()
       Effect: raises Error(msg) if subordination is not respected
               in context block Some __g'. PI __l'
       Invariants: __g |- Some __g'. PI __l' block
    *)
    (* is __v nf?  Assume here: yes! *)
    (* conDecBlock (condec) = (Gsome, Lpi)
       if condec is a block declaration
       raise Error (msg) otherwise
    *)
    (* constBlock cid = (someDecs, piDecs)
       if cid is defined as a context block
       Effect: raise Error (msg) otherwise
    *)
    (* checkSubordWorlds (W) = ()
       Effect: raises Error(msg) if subordination is not respected
               in some context block in W
    *)
    (* install (a, W) = ()
       install worlds declaration W for family a

       Effect: raises Error if W does not respect subordination
    *)
    (* lookup (a) = Some W if worlds declared for a, None otherwise *)
    (* ctxToList __g = __l

       Invariant:
       __g = __l  (__g is left associative, __l is right associative)
    *)
    (* isSubsumed (W, b) = ()
       holds if the worlds associated with b are subsumed by W
       Effect: raises Error'(occ, msg) otherwise

       Invariants: __g |- __v : type, __v nf
    *)
    let reset = reset
    let install = install
    let lookup = lookup
    let uninstall = uninstall
    let worldcheck = worldcheck
    let ctxToList = ctxToList
    let isSubsumed = isSubsumed
    let getWorlds = getWorlds
  end ;;
