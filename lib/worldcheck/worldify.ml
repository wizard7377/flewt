
(* Worldify *)
(* Author: Carsten Schuermann *)
module type WORLDIFY  =
  sig
    (*! structure IntSyn : INTSYN !*)
    (*! structure Tomega : TOMEGA !*)
    exception Error of string 
    val worldify : IntSyn.cid -> IntSyn.__ConDec list
    val worldifyGoal :
      (IntSyn.__Dec IntSyn.__Ctx * IntSyn.__Exp) -> IntSyn.__Exp
  end;;




(* Worldification and World-checking *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning *)
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
                           (*! structure IntSyn : INTSYN !*)
                           (*! structure Tomega : TOMEGA !*)
                           (*! sharing Tomega.IntSyn = IntSyn !*)
                           (*! sharing WorldSyn.IntSyn = IntSyn !*)
                           (*! sharing WorldSyn.Tomega = Tomega !*)
                           (*! sharing Whnf.IntSyn = IntSyn !*)
                           (*! sharing Index.IntSyn = IntSyn !*)
                           (*! sharing Names.IntSyn = IntSyn !*)
                           (*! sharing Unify.IntSyn = IntSyn !*)
                           (*! sharing Abstract.IntSyn = IntSyn !*)
                           (*! sharing Constraints.IntSyn = IntSyn !*)
                           (*! sharing CSManager.IntSyn = IntSyn !*)
                           (*! sharing Subordinate.IntSyn = IntSyn !*)
                           (*! sharing Print.IntSyn = IntSyn !*)
                           (*! structure Paths : PATHS !*)
                           module Origins : ORIGINS
                         end) : WORLDIFY =
  struct
    (*! sharing Origins.Paths = Paths !*)
    (*! sharing Origins.IntSyn = IntSyn !*)
    (*! structure IntSyn = IntSyn !*)
    (*! structure Tomega = Tomega !*)
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
              ((((^) "Constant " Names.qidToString (Names.constQid c)) ^ ":")
                 ^ msg))
    let rec wrapMsgBlock (c, occ, msg) =
      match Origins.originLookup c with
      | (fileName, None) -> (fileName ^ ":") ^ msg
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
    let rec wGoalToString ((__g, __l), Seq (_, piDecs, t)) =
      F.makestring_fmt
        (F.hVbox
           [F.hVbox (formatDList (__g, __l, I.id));
           F.Break;
           F.String "<|";
           F.Break;
           F.hVbox (formatDList (__g, piDecs, t))])
    let rec worldToString (__g, Seq (_, piDecs, t)) =
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
    let rec equivList =
      function
      | (__g, (_, nil), nil) -> true__
      | (__g, (t, (Dec (_, V1))::L1), (Dec (_, V2))::L2) ->
          (try
             Unify.unify (__g, (V1, t), (V2, I.id));
             equivList (__g, ((I.dot1 t), L1), L2)
           with | Unify _ -> false__)
      | _ -> false__
    let rec equivBlock ((__g, __l), __l') =
      let t = createEVarSub (I.Null, __g) in equivList (I.Null, (t, __l), __l')
    let rec equivBlocks arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (W1, nil) -> true__
      | (nil, __l') -> false__
      | (b::W1, __l') ->
          (equivBlock ((I.constBlock b), __l')) || (equivBlocks W1 __l')
    let rec strengthen arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (a, (t, nil)) -> nil
      | (a, (t, (Dec (_, __v) as __d)::__l)) ->
          if Subordinate.below ((I.targetFam __v), a)
          then (::) (I.decSub (__d, t)) strengthen a ((I.dot1 t), __l)
          else strengthen a ((I.Dot (I.Undef, t)), __l)
    let rec subsumedBlock a (W1) (__g, __l) =
      let t = createEVarSub (I.Null, __g) in
      let __l' = strengthen a (t, __l) in
      if equivBlocks W1 __l'
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
      | (Decl (__g, BDec (_, (b, _))), (Worlds (__Bs) as W)) ->
          (if List.exists (function | b' -> eqBlock (b, b')) __Bs
           then ()
           else raise (Error "Dynamic world subsumption failed");
           subsumedCtx (__g, W))
      | (Decl (__g, _), (Worlds (__Bs) as W)) -> subsumedCtx (__g, W)
    let rec checkGoal arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (W, (__g, Root (Const a, S), occ)) ->
          let W' = W.getWorlds a in
          (subsumedWorld a W' W; subsumedCtx (__g, W))
      | (W, (__g, Pi ((__d, _), V2), occ)) ->
          checkGoal W ((decUName (__g, __d)), V2, (P.body occ))
    let rec checkClause arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (W, (__g, Root (a, S), occ)) -> ()
      | (W, (__g, Pi (((Dec (_, V1) as __d), I.Maybe), V2), occ)) ->
          checkClause W ((decEName (__g, __d)), V2, (P.body occ))
      | (W, (__g, Pi (((Dec (_, V1) as __d), I.No), V2), occ)) ->
          (checkClause W ((decEName (__g, __d)), V2, (P.body occ));
           checkGoal W (__g, V1, (P.label occ)))
    let rec checkConDec (W) (ConDec (s, m, k, status, __v, __l)) =
      checkClause W (I.Null, __v, P.top)
    let rec subGoalToDList =
      function | Pi ((__d, _), __v) -> (::) __d subGoalToDList __v | Root _ -> nil
    let rec worldsToReg =
      function | Worlds nil -> One | Worlds cids -> Star (worldsToReg' cids)
    let rec worldsToReg' =
      function
      | cid::nil -> Block (cid, (I.constBlock cid))
      | cid::cids ->
          Plus ((Block (cid, (I.constBlock cid))), (worldsToReg' cids))
    let rec init =
      function
      | (_, ((Root _, s) as __Vs)) ->
          (Trace.success (); raise (Success (Whnf.normalize __Vs)))
      | (__g, ((Pi (((Dec (_, V1) as D1), _), V2) as __v), s)) ->
          (Trace.unmatched (__g, (subGoalToDList (Whnf.normalize (__v, s)))); ())
    let rec accR =
      function
      | (GVs, One, k) -> k GVs
      | (((__g, (__v, s)) as GVs), Block (c, (someDecs, piDecs)), k) ->
          let t = createEVarSub (__g, someDecs) in
          let _ =
            Trace.matchBlock
              ((__g, (subGoalToDList (Whnf.normalize (__v, s)))),
                (Seq (1, piDecs, t))) in
          let k' =
            function
            | (__g', __Vs') ->
                if noConstraints (__g, t)
                then k (__g', __Vs')
                else (Trace.constraintsRemain (); ()) in
          (try
             accR
               (((decUName (__g, (I.BDec (None, (c, t))))),
                  (__v, (I.comp (s, I.shift)))),
                 (Seq (1, piDecs, (I.comp (t, I.shift)))), k')
           with
           | Success (__v) ->
               raise
                 (Success
                    (Whnf.normalize
                       ((I.Pi (((I.BDec (None, (c, t))), I.Maybe), __v)), I.id))))
      | ((__g, ((Pi (((Dec (_, V1) as __d), _), V2) as __v), s)),
         (Seq (j, (Dec (_, V1'))::L2', t) as __l'), k) ->
          if Unify.unifiable (__g, (V1, s), (V1', t))
          then
            accR
              ((__g,
                 (V2,
                   (I.Dot
                      ((I.Exp (I.Root ((I.Proj ((I.Bidx 1), j)), I.Nil))), s)))),
                (Seq
                   ((j + 1), L2',
                     (I.Dot
                        ((I.Exp (I.Root ((I.Proj ((I.Bidx 1), j)), I.Nil))),
                          t)))), k)
          else (Trace.mismatch (__g, (V1, I.id), (V1', t)); ())
      | (GVs, Seq (_, nil, t), k) -> k GVs
      | (((__g, (Root _, s)) as GVs), (Seq (_, __l', t) as R), k) ->
          (Trace.missing (__g, R); ())
      | (GVs, Plus (r1, r2), k) ->
          (CSManager.trail (function | () -> accR (GVs, r1, k));
           accR (GVs, r2, k))
      | (GVs, Star (One), k) -> k GVs
      | (GVs, (Star r' as r), k) ->
          (CSManager.trail (function | () -> k GVs);
           accR (GVs, r', (function | GVs' -> accR (GVs', r, k))))
    let rec worldifyGoal (__g, __v, (Worlds cids as W), occ) =
      try
        let b = I.targetFam __v in
        let Wb = W.getWorlds b in
        let Rb = worldsToReg Wb in
        accR ((__g, (__v, I.id)), Rb, init);
        raise (Error' (occ, "World violation"))
      with | Success (__v') -> __v'
    let rec worldifyClause =
      function
      | (__g, (Root (a, S) as __v), W, occ) -> __v
      | (__g, Pi (((Dec (x, V1) as __d), I.Maybe), V2), W, occ) ->
          let _ = print "{" in
          let W2 = worldifyClause ((decEName (__g, __d)), V2, W, (P.body occ)) in
          let _ = print "}" in I.Pi (((I.Dec (x, V1)), I.Maybe), W2)
      | (__g, Pi (((Dec (x, V1) as __d), I.No), V2), W, occ) ->
          let W1 = worldifyGoal (__g, V1, W, (P.label occ)) in
          let W2 = worldifyClause ((decEName (__g, __d)), V2, W, (P.body occ)) in
          I.Pi (((I.Dec (x, W1)), I.No), W2)
    let rec worldifyConDec (W) (c, ConDec (s, m, k, status, __v, __l)) =
      if (!Global.chatter) = 4
      then print ((Names.qidToString (Names.constQid c)) ^ " ")
      else ();
      if (!Global.chatter) > 4 then Trace.clause c else ();
      (try
         I.ConDec
           (s, m, k, status, (worldifyClause (I.Null, __v, W, P.top)), __l)
       with | Error' (occ, msg) -> raise (Error (wrapMsg (c, occ, msg))))
    let rec worldifyBlock =
      function
      | (__g, nil) -> ()
      | (__g, (Dec (_, __v) as __d)::__l) ->
          let a = I.targetFam __v in
          let W' = W.getWorlds a in
          (checkClause W' (__g, (worldifyClause (I.Null, __v, W', P.top)), P.top);
           worldifyBlock ((decUName (__g, __d)), __l))
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
    (* Regular world expressions R
       Invariants:
       If R = (D1,...,Dn)[s] then __g |- s : __g' and __g' |- D1,...,Dn ctx
       If R = r* then r = 1 or r does not accept the empty world
    *)
    (* Regular world expressions  *)
    (* R ::= LD                   *)
    (*     | (Di,...,Dn)[s]       *)
    (*     | R*                   *)
    (*     | R1 + R2              *)
    (*     | 1                    *)
    (* signals worldcheck success *)
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
    (* ******************** *)
    (* World Subsumption    *)
    (* The STATIC part      *)
    (* ******************** *)
    (* equivList (__g, (t, __l), __l')

        Invariant:
        If  . |- t : __g
        and __g |- __l block
        then  B = true if  __l [t] unifies with __l'
              B = false otherwise
     *)
    (* equivBlock ((__g, __l), __l') = B

        Invariant:
        If   __g |- __l block
        then B = true if there exists a substitution . |- t : __g, s.t. __l[t] = __l'
             B = false otherwise
     *)
    (* equivBlocks W __l = B

        Invariant:
        Let W be a world and __l be a block.
        B = true if exists __l' in W such that __l = __l'
        B = false otherwise
     *)
    (* strengthen a (t, __l) = __l'

        Invariant:
        If   a is a type family,
        and  . |- t : __g
        and  __g |- __l block
        then . |- __l' block
        where __v \in __l and not __v < a then __v \in __l'
        and   __v \in __l and __v < a then not __v \in __l'
     *)
    (* subsumedBlock a W1 (__g, __l) = ()

        Invariant:
        If   a is a type family
        and  W1 the world in which the callee is defined
        and (__g, __l) one block in the world of the caller
        Then the function returns () if (__g, __l) is subsumed by W1
        otherwise Error is raised
     *)
    (* __g |- t : someDecs *)
    (* subsumedBlocks a W1 W2 = ()

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
    (* ******************** *)
    (* World Subsumption    *)
    (* The DYNAMIC part     *)
    (* ******************** *)
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
    (* sumbsumedCtx (__g, W) = ()

        Invariant:
        Let __g be a context of blocks
        and W a world
        Then the function returns () if every block in __g
        is listed in W
        otherwise Error is raised
     *)
    (******************************)
    (* Checking clauses and goals *)
    (******************************)
    (* checkGoal W (__g, __v, occ) = ()
        iff all (embedded) subgoals in __v satisfy world spec W
        Effect: raises Error' (occ', msg) otherwise

        Invariant: __g |- __v : type, __v nf
     *)
    (* checkClause (__g, __v, W, occ) = ()
       iff all subgoals in __v satisfy world spec W
       Effect: raises Error' (occ', msg) otherwise

       Invariant: __g |- __v : type, __v nf
       occ is occurrence of __v in current clause
     *)
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
    (* accR ((__g, (__v, s)), R, k)   raises Success
       iff __v[s] = {L1}{L2} P  such that R accepts L1
           and k ((__g, L1), L2) succeeds
       otherwise fails by returning ()
       Invariant: __g |- (__v s) type, __l nf
                  R regular world expression
       trails at choice points to undo EVar instantiations during matching
    *)
    (* __g |- t : someDecs *)
    (* __l is missing *)
    (* only possibility for non-termination in next rule *)
    (* r' does not accept empty declaration list *)
    (******************************)
    (* Worldifying clauses and goals *)
    (******************************)
    (* worldifyGoal (__g, __v, W, occ) = ()
       iff __v = {{__g'}} a @ S and __g' satisfies worlds W
       Effect: raises Error' (occ', msg) otherwise

       Invariant: __g |- __v : type, __v nf
    *)
    (* worldifyClause (__g, __v, W, occ) = ()
       iff all subgoals in __v satisfy world spec W
       Effect: raises Error' (occ', msg) otherwise

       Invariant: __g |- __v : type, __v nf
       occ is occurrence of __v in current clause
     *)
    (*         val W1 = worldifyGoal (__g, V1, W, P.label occ) *)
    (* W1*)
    (* worldcheck W a = ()
       iff all subgoals in all clauses defining a satisfy world spec W
       Effect: raises Error(msg) otherwise, where msg includes location
     *)
    (* by invariant, other cases cannot apply *)
    let worldify = worldify
    let worldifyGoal =
      function
      | (__g, __v) -> worldifyGoal (__g, __v, (W.getWorlds (I.targetFam __v)), P.top)
  end ;;
