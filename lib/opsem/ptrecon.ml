
module type PTRECON  =
  sig
    exception Error of
      ((string)(*! structure CompSyn : COMPSYN !*)(*! structure IntSyn : INTSYN !*)
      (* Proof term reconstruction by proof skeleton *)
      (* Modified: Frank Pfenning *)(* Modified: Jeff Polakow *)
      (* Author: Brigitte Pientks *)(* Abstract Machine guided by proof skeleton *))
      
    val solve :
      (CompSyn.pskeleton * (CompSyn.__Goal * IntSyn.__Sub) * CompSyn.__DProg
        * ((CompSyn.pskeleton * IntSyn.__Exp) -> unit)) -> unit
  end;;




module PtRecon(PtRecon:sig
                         module Unify : UNIFY
                         module Assign : ASSIGN
                         module MemoTable : MEMOTABLE
                         module Index : INDEX
                         module CPrint : CPRINT
                         module Names :
                         ((NAMES)(* Abstract Machine execution guided by proof skeleton *)
                         (* Author: Brigitte Pientka *)
                         (* Modified: Jeff Polakow, Frank Pfenning, Larry Greenfield, Roberto Virga, Brigitte Pientka *)
                         (* Proof term reconstruction from proof skeleton *)
                         (*! structure IntSyn' : INTSYN !*)
                         (*! structure CompSyn' : COMPSYN !*)(*! sharing CompSyn'.IntSyn = IntSyn' !*)
                         (*! sharing Unify.IntSyn = IntSyn' !*)(*! sharing Assign.IntSyn = IntSyn' !*)
                         (*! structure TableParam : TABLEPARAM !*)
                         (*! sharing MemoTable.TableParam = TableParam !*)
                         (*! sharing Index.IntSyn = IntSyn' !*)(* CPrint currently unused *)
                         (*! sharing CPrint.IntSyn = IntSyn' !*)
                         (*! sharing CPrint.CompSyn = CompSyn' !*))
                       end) : PTRECON =
  struct
    module I = IntSyn
    module C = CompSyn
    module MT = MemoTable
    exception Error of
      ((string)(*! structure TableParam = TableParam !*)
      (*! structure CompSyn = CompSyn' !*)(*! structure IntSyn = IntSyn' !*)
      (*! sharing CSManager.IntSyn = IntSyn' !*)(*! structure CSManager : CS_MANAGER !*)
      (*! sharing Names.IntSyn = IntSyn' !*)) 
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
    let rec solve' =
      function
      | (((O)(* We write
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

     Non-determinism within the rules is resolved by oracle
  *)
         (* solve' (o, (g, s), dp, sc) => ()
     Invariants:
       o = oracle
       dp = (G, dPool) where  G ~ dPool  (context G matches dPool)
       G |- s : G'
       G' |- g  goal
       if  G |- M : g[s]
       then  sc M  is evaluated
     Effects: instantiation of EVars in g, s, and dp
              any effect  sc M  might have
  *)),
         (Atom p, s), (DProg (G, dPool) as dp), sc) ->
          matchAtom (O, (p, s), dp, sc)
      | (O, (Impl (r, A, Ha, g), s), DProg (G, dPool), sc) ->
          let D' = I.Dec (NONE, (I.EClo (A, s))) in
          ((if !TableParam.strengthen
            then
              (match MT.memberCtx ((G, (I.EClo (A, s))), G) with
               | SOME (D) ->
                   let X = I.newEVar (G, (I.EClo (A, s))) in
                   solve'
                     (O, (g, (I.Dot ((I.Exp X), s))), (C.DProg (G, dPool)),
                       (function | (O, M) -> sc (O, (I.Lam (D', M)))))
               | NONE ->
                   solve'
                     (O, (g, (I.dot1 s)),
                       (C.DProg
                          ((I.Decl (G, D')),
                            (I.Decl (dPool, (C.Dec (r, s, Ha)))))),
                       (function | (O, M) -> sc (O, (I.Lam (D', M))))))
            else
              solve'
                (((O)
                  (* need to reuse label for this assumption .... *)),
                  (g, (I.dot1 s)),
                  (C.DProg
                     ((I.Decl (G, D')), (I.Decl (dPool, (C.Dec (r, s, Ha)))))),
                  (function | (O, M) -> sc (O, (I.Lam (D', M))))))
            (*      solve' (O, (g, I.dot1 s), C.DProg (I.Decl(G, D'), I.Decl (dPool, C.Dec (r, s, Ha))),
               (fn (O,M) => sc (O, (I.Lam (D', M)))))*))
      | (O, (All (D, g), s), DProg (G, dPool), sc) ->
          let D' = Names.decLUName (G, (I.decSub (D, s))) in
          solve'
            (((O)(* val D' = I.decSub (D, s) *)),
              (g, (I.dot1 s)),
              (C.DProg ((I.Decl (G, D')), (I.Decl (dPool, C.Parameter)))),
              (function | (O, M) -> sc (O, (I.Lam (D', M)))))
    let rec rSolve =
      function
      | (((O)(* rsolve (O, (p,s'), (r,s), dp, sc) = ()
     Invariants:
       O = oracle
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       G' |- r  resgoal
       G |- s' : G''
       G'' |- p : H @ S' (mod whnf)
       if G |- S : r[s]
       then sc S is evaluated
     Effects: instantiation of EVars in p[s'], r[s], and dp
              any effect  sc S  might have
  *)),
         ps', (Eq (Q), s), DProg (G, dPool), sc) ->
          if Unify.unifiable (G, (Q, s), ps')
          then sc (O, I.Nil)
          else
            (let ((_)(* effect: instantiate EVars *)
               (* call success continuation *)) =
               print "Unification Failed -- SHOULD NEVER HAPPEN!\n";
               print ((Print.expToString (G, (I.EClo ps'))) ^ " unify ");
               print ((Print.expToString (G, (I.EClo (Q, s)))) ^ "\n") in
             ())
      | (((O)(* fail *)), ps', (Assign (Q, eqns), s),
         (DProg (G, dPool) as dp), sc) ->
          (match Assign.assignable (G, ps', (Q, s)) with
           | SOME cnstr ->
               if aSolve ((eqns, s), dp, cnstr)
               then sc (O, I.Nil)
               else
                 print "aSolve cnstr not solvable -- SHOULD NEVER HAPPEN\n"
           | NONE ->
               print "Clause Head not assignable -- SHOULD NEVER HAPPEN\n")
      | (O, ps', (And (r, A, g), s), (DProg (G, dPool) as dp), sc) ->
          let ((X)(* is this EVar redundant? -fp *)) =
            I.newEVar (G, (I.EClo (A, s))) in
          rSolve
            (O, ps', (r, (I.Dot ((I.Exp X), s))), dp,
              (function
               | (O, S) ->
                   solve'
                     (O, (g, s), dp,
                       (function | (O, M) -> sc (O, (I.App (M, S)))))))
      | (O, ps', (Exists (Dec (_, A), r), s), (DProg (G, dPool) as dp), sc)
          ->
          let X = I.newEVar (G, (I.EClo (A, s))) in
          rSolve
            (O, ps', (r, (I.Dot ((I.Exp X), s))), dp,
              (function | (O, S) -> sc (O, (I.App (X, S)))))
      | (O, ps', (Axists (ADec (SOME (X), d), r), s),
         (DProg (G, dPool) as dp), sc) ->
          let X' = I.newAVar () in
          ((rSolve
              (O, ps',
                (r, (I.Dot ((I.Exp (I.EClo (X', (I.Shift (~ d))))), s))), dp,
                sc))
            (* we don't increase the proof term here! *))
    let rec aSolve =
      function
      | ((((C.Trivial)(* aSolve ((ag, s), dp, sc) = res
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       if G |- ag[s] auxgoal
       then sc () is evaluated with return value res
       else res = Fail
     Effects: instantiation of EVars in ag[s], dp and sc () *)),
          s),
         dp, cnstr) -> Assign.solveCnstr cnstr
      | ((UnifyEq (G', e1, N, eqns), s), (DProg (G, dPool) as dp), cnstr) ->
          let G'' = compose' (G', G) in
          let s' = shift (G', s) in
          (Assign.unifiable (G'', (N, s'), (e1, s'))) &&
            (aSolve ((eqns, s), dp, cnstr))
    let rec matchAtom
      (((Ho)(* matchatom (O, (p, s), dp, sc) => ()
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       G' |- p : type, p = H @ S mod whnf
       if G |- M :: p[s]
       then sc M is evaluated
     Effects: instantiation of EVars in p[s] and dp
              any effect  sc M  might have

     This first tries the local assumptions in dp then
     the static signature.
  *))::O,
       ((Root (Ha, S), s) as ps'), (DProg (G, dPool) as dp), sc)
      =
      let matchSig =
        function
        | (((nil)(* matchSig [c1,...,cn] = ()
           try each constant ci in turn for solving atomic goal ps', starting
           with c1.
        *)),
           k) -> raise (Error " \noracle #Pc does not exist \n")
        | ((Const ((c)(* should not happen *)) as Hc)::sgn',
           k) ->
            if c = k
            then
              let SClause r = C.sProgLookup (cidFromHead Hc) in
              rSolve
                (O, ps', (r, I.id), dp,
                  (function | (O, S) -> sc (O, (I.Root (Hc, S)))))
            else matchSig (sgn', k)
        | ((Def d as Hc)::sgn', k) ->
            if d = k
            then
              let SClause r = C.sProgLookup (cidFromHead Hc) in
              rSolve
                (O, ps', (r, I.id), dp,
                  (function | (O, S) -> sc (O, (I.Root (Hc, S)))))
            else matchSig (sgn', k) in
      let matchDProg =
        function
        | (((I.Null)(* matchDProg (dPool, k) = ()
           where k is the index of dPool in global dPool from call to matchAtom.
           Try each local assumption for solving atomic goal ps', starting
           with the most recent one.
        *)),
           i, k) ->
            raise
              (Error
                 (("\n selected dynamic clause number does not exist in current dynamic clause pool!\n")
                 (* dynamic program exhausted -- shouldn't happen *)))
        | (Decl (dPool', Dec (r, s, Ha')), 1, k) ->
            if eqHead (Ha, Ha')
            then
              rSolve
                (O, ps', (r, (I.comp (s, (I.Shift k)))), dp,
                  (function | (O, S) -> sc (O, (I.Root ((I.BVar k), S)))))
            else
              raise
                (Error
                   (("\n selected dynamic clause does not match current goal!\n")
                   (* shouldn't happen *)))
        | (Decl (dPool', dc), i, k) -> matchDProg (dPool', (i - 1), k) in
      match Ho with
      | Pc i -> matchSig ((Index.lookup (cidFromHead Ha)), i)
      | Dc i -> matchDProg (dPool, i, i)
      | Csolver (U) -> sc (O, U)
    let rec solve (O, (g, s), (DProg (G, dPool) as dp), sc) =
      try solve' (O, (g, s), dp, sc) with | Error msg -> print msg
  end ;;
