
module type ABSMACHINESBT  =
  sig
    val solve :
      ((CompSyn.__Goal * IntSyn.__Sub) * CompSyn.__DProg *
        (CompSyn.__Flatterm list -> unit)) ->
        ((unit)(*! structure CompSyn : COMPSYN !*)(*! structure IntSyn  : INTSYN !*)
        (* Modified: Frank Pfenning *)(* Modified: Jeff Polakow *)
        (* Author: Iliano Cervesato *)(* Abstract Machine *))
  end;;




module AbsMachineSbt(AbsMachineSbt:sig
                                     module Unify : UNIFY
                                     module SubTree : SUBTREE
                                     module Assign : ASSIGN
                                     module Index : INDEX
                                     module CPrint : CPRINT
                                     module Print : PRINT
                                     module Names :
                                     ((NAMES)(* Abstract Machine using substitution trees *)
                                     (* Author: Iliano Cervesato *)
                                     (* Modified: Jeff Polakow, Frank Pfenning, Larry Greenfield, Roberto Virga *)
                                     (*! structure IntSyn' : INTSYN !*)
                                     (*! structure CompSyn' : COMPSYN !*)
                                     (*! sharing CompSyn'.IntSyn = IntSyn' !*)
                                     (*! sharing Unify.IntSyn = IntSyn' !*)
                                     (*! sharing SubTree.IntSyn = IntSyn' !*)
                                     (*! sharing SubTree.CompSyn = CompSyn' !*)
                                     (*! sharing Assign.IntSyn = IntSyn' !*)
                                     (*! sharing Index.IntSyn = IntSyn' !*)
                                     (* CPrint currently unused *)
                                     (*! sharing CPrint.IntSyn = IntSyn' !*)
                                     (*! sharing CPrint.CompSyn = CompSyn' !*)
                                     (*! sharing Print.IntSyn = IntSyn' !*))
                                   end) : ABSMACHINESBT =
  struct
    module I = IntSyn
    module C = CompSyn
    let (mSig :
      (((IntSyn.__Exp * IntSyn.__Sub) * CompSyn.__DProg *
         (CompSyn.__Flatterm list -> unit)) -> unit)
        ref)
      = ref (function | (ps, dp, sc) -> ())
    let rec cidFromHead = function | Const a -> a | Def a -> a
    let rec eqHead =
      function
      | (Const a, Const a') -> a = a'
      | (Def a, Def a') -> a = a'
      | _ -> false__
    let rec compose' =
      function
      | (IntSyn.Null, G) -> G
      | (Decl (G, D), G') -> IntSyn.Decl ((compose' (G, G')), D)
    let rec shift =
      function
      | (IntSyn.Null, s) -> s
      | (Decl (G, D), s) -> I.dot1 (shift (G, s))
    let rec invShiftN (n, s) =
      if n = 0
      then I.comp (I.invShift, s)
      else I.comp (I.invShift, (invShiftN ((n - 1), s)))
    let rec raiseType =
      function
      | (I.Null, V) -> V
      | (Decl (G, D), V) -> raiseType (G, (I.Pi ((D, I.Maybe), V)))
    let rec printSub =
      function
      | Shift n -> print (((^) "Shift " Int.toString n) ^ "\n")
      | Dot (Idx n, s) ->
          (print (((^) "Idx " Int.toString n) ^ " . "); printSub s)
      | Dot (Exp (EVar (_, _, _, _)), s) ->
          (print "Exp (EVar _ ). "; printSub s)
      | Dot (Exp (AVar _), s) -> (print "Exp (AVar _ ). "; printSub s)
      | Dot (Exp (EClo (AVar _, _)), s) ->
          (print "Exp (AVar _ ). "; printSub s)
      | Dot (Exp (EClo (_, _)), s) -> (print "Exp (EClo _ ). "; printSub s)
      | Dot (Exp _, s) -> (print "Exp (_ ). "; printSub s)
      | Dot (IntSyn.Undef, s) -> (print "Undef . "; printSub s)
    let rec ctxToEVarSub =
      function
      | (Gglobal, I.Null, s) -> s
      | (Gglobal, Decl (G, Dec (_, A)), s) ->
          let s' = ctxToEVarSub (Gglobal, G, s) in
          let X = I.newEVar (Gglobal, (I.EClo (A, s'))) in
          I.Dot ((I.Exp X), s')
      | (Gglobal, Decl (G, ADec (_, d)), s) ->
          let X = I.newAVar () in
          I.Dot
            ((I.Exp (I.EClo (X, (I.Shift (~ d))))),
              (ctxToEVarSub (Gglobal, G, s)))
    let rec solve' =
      function
      | ((Atom p, s), (DProg (G, dpool) as dp), sc) ->
          matchAtom ((p, s), dp, sc)
      | ((Impl (r, A, Ha, g), s), DProg (G, dPool), sc) ->
          let D' = I.Dec (NONE, (I.EClo (A, s))) in
          solve'
            ((g, (I.dot1 s)),
              (C.DProg
                 ((I.Decl (G, D')), (I.Decl (dPool, (C.Dec (r, s, Ha)))))),
              sc)
      | ((All (D, g), s), DProg (G, dPool), sc) ->
          let D' = Names.decLUName (G, (I.decSub (D, s))) in
          solve'
            ((g, (I.dot1 s)),
              (C.DProg ((I.Decl (G, D')), (I.Decl (dPool, C.Parameter)))),
              sc)
    let rec rSolve =
      function
      | (ps', (Eq (Q), s), DProg (G, dPool), sc) ->
          if Unify.unifiable (G, ps', (Q, s)) then sc nil else ()
      | (ps', (Assign (Q, eqns), s), (DProg (G, dPool) as dp), sc) ->
          (match Assign.assignable (G, ps', (Q, s)) with
           | SOME cnstr ->
               aSolve ((eqns, s), dp, cnstr, (function | () -> sc nil))
           | NONE -> ())
      | (ps', (And (r, A, g), s), (DProg (G, dPool) as dp), sc) ->
          let X = I.newEVar (G, (I.EClo (A, s))) in
          rSolve
            (ps', (r, (I.Dot ((I.Exp X), s))), dp,
              (function
               | skel1 ->
                   solve'
                     ((g, s), dp, (function | skel2 -> sc (skel1 @ skel2)))))
      | (ps', (Exists (Dec (_, A), r), s), (DProg (G, dPool) as dp), sc) ->
          let X = I.newEVar (G, (I.EClo (A, s))) in
          rSolve (ps', (r, (I.Dot ((I.Exp X), s))), dp, sc)
      | (ps', (Axists (ADec (_, d), r), s), (DProg (G, dPool) as dp), sc) ->
          let X' = I.newAVar () in
          rSolve
            (ps', (r, (I.Dot ((I.Exp (I.EClo (X', (I.Shift (~ d))))), s))),
              dp, sc)
    let rec aSolve =
      function
      | ((C.Trivial, s), dp, cnstr, sc) ->
          if Assign.solveCnstr cnstr then sc () else ()
      | ((UnifyEq (G', e1, N, eqns), s), (DProg (G, dPool) as dp), cnstr, sc)
          ->
          let G'' = compose' (G', G) in
          let s' = shift (G', s) in
          if Assign.unifiable (G'', (N, s'), (e1, s'))
          then aSolve ((eqns, s), dp, cnstr, sc)
          else ()
    let rec sSolve =
      function
      | ((C.True, s), dp, sc) -> sc nil
      | ((Conjunct (g, A, Sgoals), s), (DProg (G, dPool) as dp), sc) ->
          solve'
            ((g, s), dp,
              (function
               | skel1 ->
                   sSolve
                     ((Sgoals, s), dp,
                       (function | skel2 -> sc (skel1 @ skel2)))))
    let rec matchSig
      (((Root (Ha, S), s) as ps'), (DProg (G, dPool) as dp), sc) =
      let mSig =
        function
        | nil -> ()
        | (Const c as Hc)::sgn' ->
            let SClause r = C.sProgLookup (cidFromHead Hc) in
            (CSManager.trail
               (function
                | () ->
                    rSolve
                      (ps', (r, I.id), dp,
                        (function | S -> sc ((C.Pc c) :: S))));
             mSig sgn') in
      mSig (Index.lookup (cidFromHead Ha))
    let rec matchIndexSig
      (((Root (Ha, S), s) as ps'), (DProg (G, dPool) as dp), sc) =
      SubTree.matchSig
        ((cidFromHead Ha), G, ps',
          (function
           | ((ConjGoals, s), clauseName) ->
               sSolve
                 ((ConjGoals, s), dp,
                   (function | S -> sc ((C.Pc clauseName) :: S)))))
    let rec matchAtom
      (((Root (Ha, S), s) as ps'), (DProg (G, dPool) as dp), sc) =
      let matchDProg =
        function
        | (I.Null, _) -> (!) mSig (ps', dp, sc)
        | (Decl (dPool', Dec (r, s, Ha')), k) ->
            if eqHead (Ha, Ha')
            then
              (CSManager.trail
                 (function
                  | () ->
                      rSolve
                        (ps', (r, (I.comp (s, (I.Shift k)))), dp,
                          (function | S -> sc ((C.Dc k) :: S))));
               matchDProg (dPool', (k + 1)))
            else matchDProg (dPool', (k + 1))
        | (Decl (dPool', C.Parameter), k) -> matchDProg (dPool', (k + 1)) in
      let matchConstraint (solve, try__) =
        let succeeded =
          CSManager.trail
            (function
             | () ->
                 (match solve (G, (I.SClo (S, s)), try__) with
                  | SOME (U) -> (sc [C.Csolver U]; true__)
                  | NONE -> false__)) in
        if succeeded then matchConstraint (solve, (try__ + 1)) else () in
      match I.constStatus (cidFromHead Ha) with
      | Constraint (cs, solve) -> matchConstraint (solve, 0)
      | _ -> matchDProg (dPool, 1)
    let rec solve
      ((args)(*! sharing Names.IntSyn = IntSyn' !*)(*! structure CSManager : CS_MANAGER !*)
      (*! sharing CSManager.IntSyn = IntSyn'!*)(*! structure IntSyn = IntSyn' !*)
      (*! structure CompSyn = CompSyn' !*)(* We write
       G |- M : g
     if M is a canonical proof term for goal g which could be found
     following the operational semantics.  In general, the
     success continuation sc may be applied to such M's in the order
     they are found.  Backtracking is modeled by the return of
     the success continuation.

     Similarly, we write
       G |- S : r
     if S is a canonical proof spine for residual goal r which could
     be found following the operational semantics.  A success continuation
     sc may be applies to such S's in the order they are found and
     return to indicate backtracking.
  *)
      (* Wed Mar 13 10:27:00 2002 -bp  *)(* should probably go to intsyn.fun *)
      (* ctxToEVarSub D = s*)(* solve' ((g, s), dp, sc) = res
     Invariants:
       dp = (G, dPool) where  G ~ dPool  (context G matches dPool)
       G |- s : G'
       G' |- g  goal
       if  G |- M : g[s]
       then  sc M  is evaluated with return value res
       else Fail
     Effects: instantiation of EVars in g, s, and dp
              any effect  sc M  might have
  *)
      (* rSolve ((p,s'), (r,s), dp, sc) = res
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       G' |- r  resgoal
       G |- s' : G''
       G'' |- p : H @ S' (mod whnf)
       if G |- S : r[s]
       then sc S is evaluated with return value res
       else Fail
     Effects: instantiation of EVars in p[s'], r[s], and dp
              any effect  sc S  might have
  *)
      (* effect: instantiate EVars *)(* call success continuation *)
      (* fail *)(* is this EVar redundant? -fp *)
      (* we don't increase the proof term here! *)(* aSolve ((ag, s), dp, sc) = res
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       if G |- ag[s] auxgoal
       then sc () is evaluated with return value res
       else Fail
     Effects: instantiation of EVars in ag[s], dp and sc () *)
      (* Fail *)(* Fail *)(* solve subgoals of static program clauses *)
      (* sSolve ((sg, s) , dp , sc =
 if  dp = (G, dPool) where G ~ dPool
     G |- s : G'
     sg = g1 and g2 ...and gk
     for every subgoal gi, G' |- gi
                           G  | gi[s]
   then
      sc () is evaluated
   else Fail

   Effects: instantiation of EVars in gi[s], dp, sc
*)
      (* match signature *)(* return on failure *)
      (* trail to undo EVar instantiations *)(* matchatom ((p, s), dp, sc) => res
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       G' |- p : type, p = H @ S mod whnf
       if G |- M :: p[s]
       then sc M is evaluated with return value res
       else Fail
     Effects: instantiation of EVars in p[s] and dp
              any effect  sc M  might have

     This first tries the local assumptions in dp then
     the static signature.
  *)
      (* matchDProg (dPool, k) = ()
           where k is the index of dPool in global dPool from call to matchAtom.
           Try each local assumption for solving atomic goal ps', starting
           with the most recent one.
        *)
      (* dynamic program exhausted, try signature
               there is a choice depending on how we compiled signature
             *)
      (* trail to undo EVar instantiations *)) =
      match !CompSyn.optimize with
      | CompSyn.No -> (mSig := matchSig; solve' args)
      | CompSyn.LinearHeads -> (mSig := matchSig; solve' args)
      | CompSyn.Indexing -> (mSig := matchIndexSig; solve' args)
  end ;;
