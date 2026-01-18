
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
      | (fileName, NONE) -> (fileName ^ ":") ^ msg
      | (fileName, SOME occDec) ->
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
      | NONE ->
          raise
            (Error
               (((^) "Family " Names.qidToString (Names.constQid b)) ^
                  " has no worlds declaration"))
      | SOME (Wb) -> Wb
    let (subsumedTable : unit Table.__Table) = Table.new__ 0
    let rec subsumedReset () = Table.clear subsumedTable
    let rec subsumedInsert cid = Table.insert subsumedTable (cid, ())
    let rec subsumedLookup cid =
      match Table.lookup subsumedTable cid with
      | NONE -> false__
      | SOME _ -> true__
    type __Reg =
      | Block of (I.dctx * dlist) 
      | Seq of (dlist * I.__Sub) 
      | Star of __Reg 
      | Plus of (__Reg * __Reg) 
      | One 
    exception Success 
    let rec formatReg r =
      match r with
      | Block (G, dl) -> Print.formatDecList (G, dl)
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
      | One -> F.String "1"
    let rec formatSubsump msg (G, dl, Rb, b) =
      F.HVbox
        [F.String msg;
        F.Space;
        F.String "for family";
        F.Space;
        F.String ((Names.qidToString (Names.constQid b)) ^ ":");
        F.Break;
        Print.formatDecList (G, dl);
        F.Break;
        F.String "</:";
        F.Space;
        formatReg Rb]
    let rec createEVarSub =
      function
      | (G, I.Null) -> I.Shift (I.ctxLength G)
      | (G, Decl (G', (Dec (_, V) as D))) ->
          let s = createEVarSub (G, G') in
          let V' = I.EClo (V, s) in
          let X = I.newEVar (G, V') in I.Dot ((I.Exp X), s)
    let rec collectConstraints =
      function
      | nil -> nil
      | (EVar (_, _, _, ref nil))::Xs -> collectConstraints Xs
      | (EVar (_, _, _, ref constrs))::Xs ->
          (@) (Constraints.simplify constrs) collectConstraints Xs
    let rec collectEVars =
      function
      | (G, Dot (Exp (X), s), Xs) ->
          collectEVars (G, s, (Abstract.collectEVars (G, (X, I.id), Xs)))
      | (G, Shift _, Xs) -> Xs
    let rec noConstraints (G, s) =
      match collectConstraints (collectEVars (G, s, nil)) with
      | nil -> true__
      | _ -> false__
    let rec formatD (G, D) =
      F.Hbox
        (((::) ((::) (F.String "{") Print.formatDec (G, D)) F.String "}") ::
           nil)
    let rec formatDList =
      function
      | (G, nil, t) -> nil
      | (G, (D)::nil, t) ->
          let D' = I.decSub (D, t) in (formatD (G, D')) :: nil
      | (G, (D)::L, t) ->
          let D' = I.decSub (D, t) in
          (::) ((formatD (G, D')) :: F.Break) formatDList
            ((I.Decl (G, D')), L, (I.dot1 t))
    let rec wGoalToString ((G, L), Seq (piDecs, t)) =
      F.makestring_fmt
        (F.HVbox
           [F.HVbox (formatDList (G, L, I.id));
           F.Break;
           F.String "<|";
           F.Break;
           F.HVbox (formatDList (G, piDecs, t))])
    let rec worldToString (G, Seq (piDecs, t)) =
      F.makestring_fmt (F.HVbox (formatDList (G, piDecs, t)))
    let rec hypsToString (G, L) =
      F.makestring_fmt (F.HVbox (formatDList (G, L, I.id)))
    let rec mismatchToString (G, (V1, s1), (V2, s2)) =
      F.makestring_fmt
        (F.HVbox
           [Print.formatExp (G, (I.EClo (V1, s1)));
           F.Break;
           F.String "<>";
           F.Break;
           Print.formatExp (G, (I.EClo (V2, s2)))])
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
        let rec missing (G, R) =
          if (!Global.chatter) > 7
          then
            print (((^) "Missing hypotheses:\n" worldToString (G, R)) ^ "\n")
          else ()
        let rec mismatch (G, Vs1, Vs2) =
          if (!Global.chatter) > 7
          then
            print (((^) "Mismatch:\n" mismatchToString (G, Vs1, Vs2)) ^ "\n")
          else ()
        let rec success () =
          if (!Global.chatter) > 7 then print "Success\n" else ()
      end 
    let rec decUName (G, D) = I.Decl (G, (Names.decUName (G, D)))
    let rec decEName (G, D) = I.Decl (G, (Names.decEName (G, D)))
    let rec subGoalToDList =
      function | Pi ((D, _), V) -> (::) D subGoalToDList V | Root _ -> nil
    let rec worldsToReg =
      function | Worlds nil -> One | Worlds cids -> Star (worldsToReg' cids)
    let rec worldsToReg' =
      function
      | cid::nil -> Block (I.constBlock cid)
      | cid::cids -> Plus ((Block (I.constBlock cid)), (worldsToReg' cids))
    let rec init arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (b, (_, nil)) -> (Trace.success (); raise Success)
      | (b, (G, ((Dec (_, V1) as D1)::L2 as L))) ->
          if Subordinate.belowEq ((I.targetFam V1), b)
          then (Trace.unmatched (G, L); ())
          else init b ((decUName (G, D1)), L2)
    let rec accR =
      function
      | (GL, One, b, k) -> k GL
      | (((G, L) as GL), Block (someDecs, piDecs), b, k) ->
          let t = createEVarSub (G, someDecs) in
          let _ = Trace.matchBlock (GL, (Seq (piDecs, t))) in
          let k' =
            function
            | GL' ->
                if noConstraints (G, t)
                then k GL'
                else (Trace.constraintsRemain (); ()) in
          accR (GL, (Seq (piDecs, t)), b, k')
      | ((G, ((Dec (_, V1) as D)::L2 as L)),
         (Seq (((Dec (_, V1'))::L2' as B'), t) as L'), b, k) ->
          if Unify.unifiable (G, (V1, I.id), (V1', t))
          then accR (((decUName (G, D)), L2), (Seq (L2', (I.dot1 t))), b, k)
          else
            if Subordinate.belowEq ((I.targetFam V1), b)
            then (Trace.mismatch (G, (V1, I.id), (V1', t)); ())
            else
              accR
                (((decUName (G, D)), L2), (Seq (B', (I.comp (t, I.shift)))),
                  b, k)
      | (GL, Seq (nil, t), b, k) -> k GL
      | (((G, nil) as GL), (Seq (L', t) as R), b, k) ->
          (Trace.missing (G, R); ())
      | (GL, Plus (r1, r2), b, k) ->
          (CSManager.trail (function | () -> accR (GL, r1, b, k));
           accR (GL, r2, b, k))
      | (GL, Star (One), b, k) -> k GL
      | (GL, (Star r' as r), b, k) ->
          (CSManager.trail (function | () -> k GL);
           accR (GL, r', b, (function | GL' -> accR (GL', r, b, k))))
    let rec checkSubsumedBlock (G, L', Rb, b) =
      try
        accR ((G, L'), Rb, b, (init b));
        raise
          (Error
             (F.makestring_fmt
                (formatSubsump "World subsumption failure" (G, L', Rb, b))))
      with | Success -> ()
    let rec checkSubsumedWorlds =
      function
      | (nil, Rb, b) -> ()
      | (cid::cids, Rb, b) ->
          let (someDecs, piDecs) = I.constBlock cid in
          (checkSubsumedBlock ((Names.ctxName someDecs), piDecs, Rb, b);
           checkSubsumedWorlds (cids, Rb, b))
    let rec checkBlocks (Worlds cids) (G, V, occ) =
      try
        let b = I.targetFam V in
        let Wb =
          try getWorlds b with | Error msg -> raise (Error' (occ, msg)) in
        let Rb = worldsToReg Wb in
        let _ =
          if subsumedLookup b
          then ()
          else
            (try checkSubsumedWorlds (cids, Rb, b); subsumedInsert b
             with | Error msg -> raise (Error' (occ, msg))) in
        let L = subGoalToDList V in
        accR ((G, L), Rb, b, (init b));
        raise
          (Error'
             (occ,
               (F.makestring_fmt
                  (formatSubsump "World violation" (G, L, Rb, b)))))
      with | Success -> ()
    let rec checkClause =
      function
      | (G, Root (a, S), W, occ) -> ()
      | (G, Pi (((Dec (_, V1) as D), I.Maybe), V2), W, occ) ->
          (checkClause ((decEName (G, D)), V2, W, (P.body occ));
           checkGoal (G, V1, W, (P.label occ)))
      | (G, Pi (((Dec (_, V1) as D), I.No), V2), W, occ) ->
          (checkBlocks W (G, V1, (P.label occ));
           checkClause ((decEName (G, D)), V2, W, (P.body occ));
           checkGoal (G, V1, W, (P.label occ)))
    let rec checkGoal =
      function
      | (G, Root (a, S), W, occ) -> ()
      | (G, Pi (((Dec (_, V1) as D), _), V2), W, occ) ->
          (checkGoal ((decUName (G, D)), V2, W, (P.body occ));
           checkClause (G, V1, W, (P.label occ)))
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
      | (G, I.Null) -> G
      | (G, Decl (G', D)) -> I.Decl ((ctxAppend (G, G')), D)
    let rec checkSubordBlock (G, G', L) =
      checkSubordBlock' ((ctxAppend (G, G')), L)
    let rec checkSubordBlock' =
      function
      | (G, (Dec (_, V) as D)::L') ->
          (Subordinate.respectsN (G, V);
           checkSubordBlock' ((I.Decl (G, D)), L'))
      | (G, nil) -> ()
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
      | NONE -> false__
      | SOME _ -> (Table.delete worldsTable a; true__)
    let rec lookup a = getWorlds a
    let rec ctxToList (Gin) =
      let rec ctxToList' =
        function
        | (I.Null, G) -> G
        | (Decl (G, D), G') -> ctxToList' (G, (D :: G')) in
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
       If R = (D1,...,Dn)[s] then G |- s : G' and G' |- D1,...,Dn ctx
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
    (* Is this correct? - gaw *)
    (* Fixed June 3, 2009 -fp,cs *)
    (* Format a subsumption failure judgment
       msg: Prefix for the message
       dl : declaration list
       Rb : regular world
       b : family
       Displays:

         msg for family b:
         G |- dl </: Rb
     *)
    (*
            F.HVbox ([F.String ((Names.qidToString (Names.constQid b)) ^ ":")])
        *)
    (* F.Newline (), *)
    (* Do not print some-variables; reenable if necessary *)
    (* June 3, 2009 -fp,cs *)
    (* Print.formatCtx(I.Null, G), F.Break, F.String "|-", F.Space, *)
    (* createEVarSub G G' = s

       Invariant:
       If   G is a context
       and  G' is a context
       then G |- s : G'
    *)
    (* from cover.fun *)
    (* collectConstraints (Xs) = constrs
       collect all the constraints that may be attached to EVars in Xs

       try simplifying away the constraints in case they are "hard"
    *)
    (* constrs <> nil *)
    (* collectEVars (G, s, Xs) = Xs'
       adds all uninstantiated EVars from s to Xs to obtain Xs'
       Invariant: s is EVar substitutions
    *)
    (* other cases impossible by invariants since s is EVarSubst *)
    (* noConstraints (G, s) = true iff there are no remaining constraints in s
       Invariants: s is an EVar substitution X1...Xn.^k
    *)
    (* end from cover.fun *)
    (************)
    (* Printing *)
    (************)
    (* Declarations *)
    (* Declaration lists *)
    (* Names.decUName (G, I.decSub(D, t)) *)
    (* Names.decUName (G, I.decSub (D, t)) *)
    (*
    fun hypsToDList (I.Root _) = nil
      | hypsToDList (I.Pi ((D, _), V)) =
          D::hypsToDList V
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
    (* init b (G, L) raises Success iff V is empty
       or none of the remaining declarations are relevant to b
       otherwise fails by returning ()
       Initial continuation for world checker

       Invariant: G |- L dlist, L nf
    *)
    (* accR ((G, L), R, k)   raises Success
       iff L = L1,L2 such that R accepts L1
           and k ((G, L1), L2) succeeds
       otherwise fails by returning ()
       Invariant: G |- L dlist, L nf
                  R regular world expression
       trails at choice points to undo EVar instantiations during matching
    *)
    (* G |- t : someDecs *)
    (* if block matches, check for remaining constraints *)
    (* relevant to family b, fail *)
    (* not relevant to family b, skip in L *)
    (* fixed bug in previous line; was: t instead of t o ^ *)
    (* Mon May 7 2007 -fp *)
    (* L is missing *)
    (* only possibility for non-termination in next rule *)
    (* r' does not accept empty declaration list *)
    (* checkSubsumedBlock (G, someDecs, piDecs, Rb, b) = ()
       iff block SOME someDecs. PI piDecs is subsumed by Rb
       Effect: raises Error (msg) otherwise

       Invariants: Rb = reg (worlds (b))
    *)
    (* checkSubsumedWorlds (Wa, Rb, b) = ()
       iff Wa is subsumed by Rb
       Effect: raises Error (msg) otherwise

       Invariants: Rb = reg (worlds (b))
    *)
    (* checkBlocks W (G, V, occ) = ()
       iff V = {{G'}} a @ S and G' satisfies worlds W
       Effect: raises Error'(occ, msg) otherwise

       Invariants: G |- V : type, V nf
    *)
    (******************************)
    (* Checking clauses and goals *)
    (******************************)
    (* checkClause (G, V, W, occ) = ()
       iff all subgoals in V satisfy world spec W
       Effect: raises Error' (occ', msg) otherwise

       Invariant: G |- V : type, V nf
       occ is occurrence of V in current clause
     *)
    (* checkGoal (G, V, W, occ) = ()
        iff all (embedded) subgoals in V satisfy world spec W
        Effect: raises Error' (occ', msg) otherwise

        Invariant: G |- V : type, V nf
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
    (* checkSubordBlock (G, G', L') = ()
       Effect: raises Error(msg) if subordination is not respected
               in context block SOME G'. PI L'
       Invariants: G |- SOME G'. PI L' block
    *)
    (* is V nf?  Assume here: yes! *)
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
    (* lookup (a) = SOME W if worlds declared for a, NONE otherwise *)
    (* ctxToList G = L

       Invariant:
       G = L  (G is left associative, L is right associative)
    *)
    (* isSubsumed (W, b) = ()
       holds if the worlds associated with b are subsumed by W
       Effect: raises Error'(occ, msg) otherwise

       Invariants: G |- V : type, V nf
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
