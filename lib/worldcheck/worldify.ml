
module type WORLDIFY  =
  sig
    exception Error of
      ((string)(*! structure Tomega : TOMEGA !*)(*! structure IntSyn : INTSYN !*)
      (* Author: Carsten Schuermann *)(* Worldify *)) 
    val worldify : IntSyn.cid -> IntSyn.__ConDec list
    val worldifyGoal :
      (IntSyn.__Dec IntSyn.__Ctx * IntSyn.__Exp) -> IntSyn.__Exp
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
                           module Origins :
                           ((ORIGINS)(* Worldification and World-checking *)
                           (* Author: Carsten Schuermann *)
                           (* Modified: Frank Pfenning *)
                           (*! structure IntSyn : INTSYN !*)
                           (*! structure Tomega : TOMEGA !*)
                           (*! sharing Tomega.IntSyn = IntSyn !*)
                           (*! sharing WorldSyn.IntSyn = IntSyn !*)
                           (*! sharing WorldSyn.Tomega = Tomega !*)
                           (*! sharing Whnf.IntSyn = IntSyn !*)(*! sharing Index.IntSyn = IntSyn !*)
                           (*! sharing Names.IntSyn = IntSyn !*)
                           (*! sharing Unify.IntSyn = IntSyn !*)
                           (*! sharing Abstract.IntSyn = IntSyn !*)
                           (*! sharing Constraints.IntSyn = IntSyn !*)
                           (*! sharing CSManager.IntSyn = IntSyn !*)
                           (*! sharing Subordinate.IntSyn = IntSyn !*)
                           (*! sharing Print.IntSyn = IntSyn !*)
                           (*! structure Paths : PATHS !*))
                         end) : WORLDIFY =
  struct
    module I =
      ((IntSyn)(*! sharing Origins.Paths = Paths !*)
      (*! sharing Origins.IntSyn = IntSyn !*)(*! structure IntSyn = IntSyn !*)
      (*! structure Tomega = Tomega !*))
    module T = Tomega
    module P = Paths
    module F = Print.Formatter
    exception Error of string 
    exception Error' of (P.occ * string) 
    let rec wrapMsg
      (((c)(* copied from terminates/reduces.fun *)), occ,
       msg)
      =
      match Origins.originLookup c with
      | (fileName, NONE) -> (fileName ^ ":") ^ msg
      | (fileName, SOME occDec) ->
          P.wrapLoc'
            ((P.Loc (fileName, (P.occToRegionDec occDec occ))),
              (Origins.linesInfoLookup fileName),
              ((((^) "Constant " Names.qidToString (Names.constQid c)) ^ ":")
                 ^ msg))
    let rec wrapMsgBlock (c, occ, msg) =
      match Origins.originLookup c with
      | (fileName, NONE) -> (fileName ^ ":") ^ msg
      | (fileName, SOME occDec) ->
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
    let rec wGoalToString ((G, L), Seq (_, piDecs, t)) =
      F.makestring_fmt
        (F.HVbox
           [F.HVbox (formatDList (G, L, I.id));
           F.Break;
           F.String "<|";
           F.Break;
           F.HVbox (formatDList (G, piDecs, t))])
    let rec worldToString (G, Seq (_, piDecs, t)) =
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
    let rec equivList =
      function
      | (G, (_, nil), nil) -> true__
      | (G, (t, (Dec (_, V1))::L1), (Dec (_, V2))::L2) ->
          (try
             Unify.unify (G, (V1, t), (V2, I.id));
             equivList (G, ((I.dot1 t), L1), L2)
           with | Unify _ -> false__)
      | _ -> false__
    let rec equivBlock ((G, L), L') =
      let t = createEVarSub (I.Null, G) in equivList (I.Null, (t, L), L')
    let rec equivBlocks arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (W1, nil) -> true__
      | (nil, L') -> false__
      | (b::W1, L') ->
          (equivBlock ((I.constBlock b), L')) || (equivBlocks W1 L')
    let rec strengthen arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (a, (t, nil)) -> nil
      | (a, (t, (Dec (_, V) as D)::L)) ->
          if Subordinate.below ((I.targetFam V), a)
          then (::) (I.decSub (D, t)) strengthen a ((I.dot1 t), L)
          else strengthen a ((I.Dot (I.Undef, t)), L)
    let rec subsumedBlock a (W1) (G, L) =
      let t = createEVarSub (I.Null, G) in
      let L' = strengthen a (t, L) in
      if equivBlocks W1 L'
      then ()
      else raise (Error "Static world subsumption failed")
    let rec subsumedBlocks arg__0 arg__1 arg__2 =
      match (arg__0, arg__1, arg__2) with
      | (a, W1, nil) -> ()
      | (a, W1, b::W2) ->
          (subsumedBlock a W1 (I.constBlock b); subsumedBlocks a W1 W2)
    let rec subsumedWorld a (Worlds (W1)) (Worlds (W2)) =
      subsumedBlocks a W1 W2
    let rec eqCtx =
      function
      | (I.Null, I.Null) -> true__
      | (Decl (G1, D1), Decl (G2, D2)) ->
          (eqCtx (G1, G2)) && (Conv.convDec ((D1, I.id), (D2, I.id)))
      | _ -> false__
    let rec eqList =
      function
      | (nil, nil) -> true__
      | ((D1)::L1, (D2)::L2) ->
          (Conv.convDec ((D1, I.id), (D2, I.id))) && (eqList (L1, L2))
      | _ -> false__
    let rec eqBlock (b1, b2) =
      let (G1, L1) = I.constBlock b1 in
      let (G2, L2) = I.constBlock b2 in (eqCtx (G1, G2)) && (eqList (L1, L2))
    let rec subsumedCtx =
      function
      | (I.Null, W) -> ()
      | (Decl (G, BDec (_, (b, _))), (Worlds (Bs) as W)) ->
          (if List.exists (function | b' -> eqBlock (b, b')) Bs
           then ()
           else raise (Error "Dynamic world subsumption failed");
           subsumedCtx (G, W))
      | (Decl (G, _), (Worlds (Bs) as W)) -> subsumedCtx (G, W)
    let rec checkGoal arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (W, (G, Root (Const a, S), occ)) ->
          let W' = W.getWorlds a in
          (subsumedWorld a W' W; subsumedCtx (G, W))
      | (W, (G, Pi ((D, _), V2), occ)) ->
          checkGoal W ((decUName (G, D)), V2, (P.body occ))
    let rec checkClause arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (W, (G, Root (a, S), occ)) -> ()
      | (W, (G, Pi (((Dec (_, V1) as D), I.Maybe), V2), occ)) ->
          checkClause W ((decEName (G, D)), V2, (P.body occ))
      | (W, (G, Pi (((Dec (_, V1) as D), I.No), V2), occ)) ->
          (checkClause W ((decEName (G, D)), V2, (P.body occ));
           checkGoal W (G, V1, (P.label occ)))
    let rec checkConDec (W) (ConDec (s, m, k, status, V, L)) =
      checkClause W (I.Null, V, P.top)
    let rec subGoalToDList =
      function | Pi ((D, _), V) -> (::) D subGoalToDList V | Root _ -> nil
    let rec worldsToReg =
      function | Worlds nil -> One | Worlds cids -> Star (worldsToReg' cids)
    let rec worldsToReg' =
      function
      | cid::nil -> Block (cid, (I.constBlock cid))
      | cid::cids ->
          Plus ((Block (cid, (I.constBlock cid))), (worldsToReg' cids))
    let rec init =
      function
      | (_, ((Root _, s) as Vs)) ->
          (Trace.success (); raise (Success (Whnf.normalize Vs)))
      | (G, ((Pi (((Dec (_, V1) as D1), _), V2) as V), s)) ->
          (Trace.unmatched (G, (subGoalToDList (Whnf.normalize (V, s)))); ())
    let rec accR =
      function
      | (GVs, One, k) -> k GVs
      | (((G, (V, s)) as GVs), Block (c, (someDecs, piDecs)), k) ->
          let t = createEVarSub (G, someDecs) in
          let _ =
            Trace.matchBlock
              ((G, (subGoalToDList (Whnf.normalize (V, s)))),
                (Seq (1, piDecs, t))) in
          let k' =
            function
            | (G', Vs') ->
                if noConstraints (G, t)
                then k (G', Vs')
                else (Trace.constraintsRemain (); ()) in
          (try
             accR
               (((decUName (G, (I.BDec (NONE, (c, t))))),
                  (V, (I.comp (s, I.shift)))),
                 (Seq (1, piDecs, (I.comp (t, I.shift)))), k')
           with
           | Success (V) ->
               raise
                 (Success
                    (Whnf.normalize
                       ((I.Pi (((I.BDec (NONE, (c, t))), I.Maybe), V)), I.id))))
      | ((G, ((Pi (((Dec (_, V1) as D), _), V2) as V), s)),
         (Seq (j, (Dec (_, V1'))::L2', t) as L'), k) ->
          if Unify.unifiable (G, (V1, s), (V1', t))
          then
            accR
              ((G,
                 (V2,
                   (I.Dot
                      ((I.Exp (I.Root ((I.Proj ((I.Bidx 1), j)), I.Nil))), s)))),
                (Seq
                   ((j + 1), L2',
                     (I.Dot
                        ((I.Exp (I.Root ((I.Proj ((I.Bidx 1), j)), I.Nil))),
                          t)))), k)
          else (Trace.mismatch (G, (V1, I.id), (V1', t)); ())
      | (GVs, Seq (_, nil, t), k) -> k GVs
      | (((G, (Root _, s)) as GVs), (Seq (_, L', t) as R), k) ->
          (Trace.missing (G, R); ())
      | (GVs, Plus (r1, r2), k) ->
          (CSManager.trail (function | () -> accR (GVs, r1, k));
           accR (GVs, r2, k))
      | (GVs, Star (One), k) -> k GVs
      | (GVs, (Star r' as r), k) ->
          (CSManager.trail (function | () -> k GVs);
           accR (GVs, r', (function | GVs' -> accR (GVs', r, k))))
    let rec worldifyGoal (G, V, (Worlds cids as W), occ) =
      try
        let b = I.targetFam V in
        let Wb = W.getWorlds b in
        let Rb = worldsToReg Wb in
        accR ((G, (V, I.id)), Rb, init);
        raise (Error' (occ, "World violation"))
      with | Success (V') -> V'
    let rec worldifyClause =
      function
      | (G, (Root (a, S) as V), W, occ) -> V
      | (G, Pi (((Dec (x, V1) as D), I.Maybe), V2), W, occ) ->
          let _ = print "{" in
          let W2 = worldifyClause ((decEName (G, D)), V2, W, (P.body occ)) in
          let _ = print "}" in I.Pi (((I.Dec (x, V1)), I.Maybe), W2)
      | (G, Pi (((Dec (x, V1) as D), I.No), V2), W, occ) ->
          let W1 = worldifyGoal (G, V1, W, (P.label occ)) in
          let W2 = worldifyClause ((decEName (G, D)), V2, W, (P.body occ)) in
          I.Pi (((I.Dec (x, W1)), I.No), W2)
    let rec worldifyConDec (W) (c, ConDec (s, m, k, status, V, L)) =
      if (!Global.chatter) = 4
      then print ((Names.qidToString (Names.constQid c)) ^ " ")
      else ();
      if (!Global.chatter) > 4 then Trace.clause c else ();
      (try
         I.ConDec
           (s, m, k, status, (worldifyClause (I.Null, V, W, P.top)), L)
       with | Error' (occ, msg) -> raise (Error (wrapMsg (c, occ, msg))))
    let rec worldifyBlock =
      function
      | (G, nil) -> ()
      | (G, (Dec (_, V) as D)::L) ->
          let a = I.targetFam V in
          let W' = W.getWorlds a in
          (checkClause W' (G, (worldifyClause (I.Null, V, W', P.top)), P.top);
           worldifyBlock ((decUName (G, D)), L))
    let rec worldifyBlocks =
      function
      | nil -> ()
      | b::Bs ->
          let _ = worldifyBlocks Bs in
          let (Gsome, Lblock) = I.constBlock b in
          let _ = print "|" in
          (try worldifyBlock (Gsome, Lblock)
           with
           | Error' (occ, s) ->
               raise
                 (Error
                    (wrapMsgBlock (b, occ, "World not hereditarily closed"))))
    let rec worldifyWorld (Worlds (Bs)) = worldifyBlocks Bs
    let rec worldify a =
      let W = W.getWorlds a in
      let _ = print "[?" in
      let W' = worldifyWorld W in
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
          (function
           | Const c ->
               (try worldifyConDec W (c, (I.sgnLookup c))
                with | Error' (occ, s) -> raise (Error (wrapMsg (c, occ, s)))))
          (Index.lookup a) in
      let _ =
        map (function | condec -> (print "#"; checkConDec W condec)) condecs in
      let _ = print "]" in
      let _ = if (!Global.chatter) = 4 then print "\n" else () in condecs
    let ((worldify)(* Regular world expressions R
       Invariants:
       If R = (D1,...,Dn)[s] then G |- s : G' and G' |- D1,...,Dn ctx
       If R = r* then r = 1 or r does not accept the empty world
    *)
      (* Regular world expressions  *)(* R ::= LD                   *)
      (*     | (Di,...,Dn)[s]       *)(*     | R*                   *)
      (*     | R1 + R2              *)(*     | 1                    *)
      (* signals worldcheck success *)(* createEVarSub G G' = s

       Invariant:
       If   G is a context
       and  G' is a context
       then G |- s : G'
    *)
      (* from cover.fun *)(* collectConstraints (Xs) = constrs
       collect all the constraints that may be attached to EVars in Xs

       try simplifying away the constraints in case they are "hard"
    *)
      (* constrs <> nil *)(* collectEVars (G, s, Xs) = Xs'
       adds all uninstantiated EVars from s to Xs to obtain Xs'
       Invariant: s is EVar substitutions
    *)
      (* other cases impossible by invariants since s is EVarSubst *)
      (* noConstraints (G, s) = true iff there are no remaining constraints in s
       Invariants: s is an EVar substitution X1...Xn.^k
    *)
      (************)(* Printing *)(************)
      (* Declarations *)(* Declaration lists *)
      (* Names.decUName (G, I.decSub(D, t)) *)(* Names.decUName (G, I.decSub (D, t)) *)
      (*
    fun hypsToDList (I.Root _) = nil
      | hypsToDList (I.Pi ((D, _), V)) =
          D::hypsToDList V
    *)
      (* Hypotheses and declaration lists *)(* Declaration list *)
      (* Hypotheses *)(* Mismatch between hypothesis and world declaration *)
      (***********)(* Tracing *)(***********)
      (* R = (D1,...,Dn)[t] *)(* R = (D1,...,Dn)[t] *)
      (* ******************** *)(* World Subsumption    *)
      (* The STATIC part      *)(* ******************** *)
      (* equivList (G, (t, L), L')

        Invariant:
        If  . |- t : G
        and G |- L block
        then  B = true if  L [t] unifies with L'
              B = false otherwise
     *)
      (* equivBlock ((G, L), L') = B

        Invariant:
        If   G |- L block
        then B = true if there exists a substitution . |- t : G, s.t. L[t] = L'
             B = false otherwise
     *)
      (* equivBlocks W L = B

        Invariant:
        Let W be a world and L be a block.
        B = true if exists L' in W such that L = L'
        B = false otherwise
     *)
      (* strengthen a (t, L) = L'

        Invariant:
        If   a is a type family,
        and  . |- t : G
        and  G |- L block
        then . |- L' block
        where V \in L and not V < a then V \in L'
        and   V \in L and V < a then not V \in L'
     *)
      (* subsumedBlock a W1 (G, L) = ()

        Invariant:
        If   a is a type family
        and  W1 the world in which the callee is defined
        and (G, L) one block in the world of the caller
        Then the function returns () if (G, L) is subsumed by W1
        otherwise Error is raised
     *)
      (* G |- t : someDecs *)(* subsumedBlocks a W1 W2 = ()

        Invariant:
        Let W1 be the world in which the callee is defined
        Let W2 be the world in which the caller is defined
        Then the function returns () if W2 is subsumed by W1
        otherwise Error is raised
     *)
      (* subsumedWorld a W1 W2 = ()

        Invariant:
        Let W1 be the world in which the callee is defined
        Let W2 be the world in which the caller is defined
        Then the function returns () if W2 is subsumed by W1
        otherwise Error is raised
     *)
      (* ******************** *)(* World Subsumption    *)
      (* The DYNAMIC part     *)(* ******************** *)
      (* eqCtx (G1, G2) = B

        Invariant:
        Let  G1, G2 constexts of declarations (as the occur in the some part
                    of a block).
        B = true if G1 and G2 are equal (modulo renaming of variables)
        B = false otherwise
     *)
      (* eqList (L1, L2) = B

        Invariant:
        Let  L1, L2 lists of declarations (as the occur in a block).
        B = true if L1 and L2 are equal (modulo renaming of variables)
        B = false otherwise
     *)
      (* eqBlock (b1, b2) = B

        Invariant:
        Let  b1, b2 blocks.
        B = true if b1 and b2 are equal (modulo renaming of variables)
        B = false otherwise
     *)
      (* sumbsumedCtx (G, W) = ()

        Invariant:
        Let G be a context of blocks
        and W a world
        Then the function returns () if every block in G
        is listed in W
        otherwise Error is raised
     *)
      (******************************)(* Checking clauses and goals *)
      (******************************)(* checkGoal W (G, V, occ) = ()
        iff all (embedded) subgoals in V satisfy world spec W
        Effect: raises Error' (occ', msg) otherwise

        Invariant: G |- V : type, V nf
     *)
      (* checkClause (G, V, W, occ) = ()
       iff all subgoals in V satisfy world spec W
       Effect: raises Error' (occ', msg) otherwise

       Invariant: G |- V : type, V nf
       occ is occurrence of V in current clause
     *)
      (**************************************)(* Matching hypotheses against worlds *)
      (**************************************)(* worldsToReg (Worlds [c1,...,cn]) = R
       W = R, except that R is a regular expression
       with non-empty contextblocks as leaves
    *)
      (* init b (G, L) raises Success iff V is empty
       or none of the remaining declarations are relevant to b
       otherwise fails by returning ()
       Initial continuation for world checker

       Invariant: G |- L dlist, L nf
    *)
      (* accR ((G, (V, s)), R, k)   raises Success
       iff V[s] = {L1}{L2} P  such that R accepts L1
           and k ((G, L1), L2) succeeds
       otherwise fails by returning ()
       Invariant: G |- (V s) type, L nf
                  R regular world expression
       trails at choice points to undo EVar instantiations during matching
    *)
      (* G |- t : someDecs *)(* L is missing *)
      (* only possibility for non-termination in next rule *)(* r' does not accept empty declaration list *)
      (******************************)(* Worldifying clauses and goals *)
      (******************************)(* worldifyGoal (G, V, W, occ) = ()
       iff V = {{G'}} a @ S and G' satisfies worlds W
       Effect: raises Error' (occ', msg) otherwise

       Invariant: G |- V : type, V nf
    *)
      (* worldifyClause (G, V, W, occ) = ()
       iff all subgoals in V satisfy world spec W
       Effect: raises Error' (occ', msg) otherwise

       Invariant: G |- V : type, V nf
       occ is occurrence of V in current clause
     *)
      (*         val W1 = worldifyGoal (G, V1, W, P.label occ) *)
      (* W1*)(* worldcheck W a = ()
       iff all subgoals in all clauses defining a satisfy world spec W
       Effect: raises Error(msg) otherwise, where msg includes location
     *)
      (* by invariant, other cases cannot apply *)) =
      worldify
    let worldifyGoal =
      function
      | (G, V) -> worldifyGoal (G, V, (W.getWorlds (I.targetFam V)), P.top)
  end ;;
