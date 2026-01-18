
(* Abstract Machine guided by proof skeleton *)
(* Author: Brigitte Pientks *)
(* Modified: Jeff Polakow *)
(* Modified: Frank Pfenning *)
(* Proof term reconstruction by proof skeleton *)
module type PTRECON  =
  sig
    (*! structure IntSyn : INTSYN !*)
    (*! structure CompSyn : COMPSYN !*)
    exception Error of string 
    val solve :
      (CompSyn.pskeleton * (CompSyn.__Goal * IntSyn.__Sub) * CompSyn.__DProg
        * ((CompSyn.pskeleton * IntSyn.__Exp) -> unit)) -> unit
  end;;




(* Abstract Machine execution guided by proof skeleton *)
(* Author: Brigitte Pientka *)
(* Modified: Jeff Polakow, Frank Pfenning, Larry Greenfield, Roberto Virga, Brigitte Pientka *)
(* Proof term reconstruction from proof skeleton *)
module PtRecon(PtRecon:sig
                         (*! structure IntSyn' : INTSYN !*)
                         (*! structure CompSyn' : COMPSYN !*)
                         (*! sharing CompSyn'.IntSyn = IntSyn' !*)
                         module Unify : UNIFY
                         module Assign : ASSIGN
                         module MemoTable : MEMOTABLE
                         module Index : INDEX
                         module CPrint : CPRINT
                         (*! sharing Unify.IntSyn = IntSyn' !*)
                         (*! sharing Assign.IntSyn = IntSyn' !*)
                         (*! structure TableParam : TABLEPARAM !*)
                         (*! sharing MemoTable.TableParam = TableParam !*)
                         (*! sharing Index.IntSyn = IntSyn' !*)
                         (* CPrint currently unused *)
                         (*! sharing CPrint.IntSyn = IntSyn' !*)
                         (*! sharing CPrint.CompSyn = CompSyn' !*)
                         module Names : NAMES
                       end) : PTRECON =
  struct
    (*! sharing Names.IntSyn = IntSyn' !*)
    (*! structure CSManager : CS_MANAGER !*)
    (*! sharing CSManager.IntSyn = IntSyn' !*)
    (*! structure IntSyn = IntSyn' !*)
    (*! structure CompSyn = CompSyn' !*)
    (*! structure TableParam = TableParam !*)
    module I = IntSyn
    module C = CompSyn
    module MT = MemoTable
    exception Error of string 
    let rec cidFromHead = function | Const a -> a | Def a -> a
    let rec eqHead =
      function
      | (Const a, Const a') -> a = a'
      | (Def a, Def a') -> a = a'
      | _ -> false__
    let rec compose' =
      function
      | (IntSyn.Null, __g) -> __g
      | (Decl (__g, __d), __g') -> IntSyn.Decl ((compose' (__g, __g')), __d)
    let rec shift =
      function
      | (IntSyn.Null, s) -> s
      | (Decl (__g, __d), s) -> I.dot1 (shift (__g, s))
    (* We write
       __g |- M : g
     if M is a canonical proof term for goal g which could be found
     following the operational semantics.  In general, the
     success continuation sc may be applied to such M's in the order
     they are found.  Backtracking is modeled by the return of
     the success continuation.

     Similarly, we write
       __g |- S : r
     if S is a canonical proof spine for residual goal r which could
     be found following the operational semantics.  A success continuation
     sc may be applies to such S's in the order they are found and
     return to indicate backtracking.

     Non-determinism within the rules is resolved by oracle
  *)
    (* solve' (o, (g, s), dp, sc) => ()
     Invariants:
       o = oracle
       dp = (__g, dPool) where  __g ~ dPool  (context __g matches dPool)
       __g |- s : __g'
       __g' |- g  goal
       if  __g |- M : g[s]
       then  sc M  is evaluated
     Effects: instantiation of EVars in g, s, and dp
              any effect  sc M  might have
  *)
    let rec solve' =
      function
      | (O, (Atom p, s), (DProg (__g, dPool) as dp), sc) ->
          matchAtom (O, (p, s), dp, sc)
      | (O, (Impl (r, A, Ha, g), s), DProg (__g, dPool), sc) ->
          let __d' = I.Dec (None, (I.EClo (A, s))) in
          ((if !TableParam.strengthen
            then
              (match MT.memberCtx ((__g, (I.EClo (A, s))), __g) with
               | Some (__d) ->
                   let x = I.newEVar (__g, (I.EClo (A, s))) in
                   ((solve'
                       (O, (g, (I.Dot ((I.Exp x), s))), (C.DProg (__g, dPool)),
                         (function | (O, M) -> sc (O, (I.Lam (__d', M))))))
                     (* need to reuse label for this assumption .... *))
               | None ->
                   solve'
                     (O, (g, (I.dot1 s)),
                       (C.DProg
                          ((I.Decl (__g, __d')),
                            (I.Decl (dPool, (C.Dec (r, s, Ha)))))),
                       (function | (O, M) -> sc (O, (I.Lam (__d', M))))))
            else
              solve'
                (O, (g, (I.dot1 s)),
                  (C.DProg
                     ((I.Decl (__g, __d')), (I.Decl (dPool, (C.Dec (r, s, Ha)))))),
                  (function | (O, M) -> sc (O, (I.Lam (__d', M))))))
            (*      solve' (O, (g, I.dot1 s), C.DProg (I.Decl(__g, __d'), I.Decl (dPool, C.Dec (r, s, Ha))),
               (fn (O,M) => sc (O, (I.Lam (__d', M)))))*))
      | (O, (All (__d, g), s), DProg (__g, dPool), sc) ->
          let __d' = Names.decLUName (__g, (I.decSub (__d, s))) in
          ((solve'
              (O, (g, (I.dot1 s)),
                (C.DProg ((I.Decl (__g, __d')), (I.Decl (dPool, C.Parameter)))),
                (function | (O, M) -> sc (O, (I.Lam (__d', M))))))
            (* val __d' = I.decSub (__d, s) *))
    let rec rSolve =
      function
      | (O, ps', (Eq (Q), s), DProg (__g, dPool), sc) ->
          ((if Unify.unifiable (__g, (Q, s), ps')
            then sc (O, I.Nil)
            else
              (let _ =
                 print "Unification Failed -- SHOULD NEVER HAPPEN!\n";
                 print ((Print.expToString (__g, (I.EClo ps'))) ^ " unify ");
                 print ((Print.expToString (__g, (I.EClo (Q, s)))) ^ "\n") in
               ()))
          (* effect: instantiate EVars *)(* call success continuation *))
      | (O, ps', (Assign (Q, eqns), s), (DProg (__g, dPool) as dp), sc) ->
          (match Assign.assignable (__g, ps', (Q, s)) with
           | Some cnstr ->
               if aSolve ((eqns, s), dp, cnstr)
               then sc (O, I.Nil)
               else
                 print "aSolve cnstr not solvable -- SHOULD NEVER HAPPEN\n"
           | None ->
               print "Clause Head not assignable -- SHOULD NEVER HAPPEN\n")
      | (O, ps', (And (r, A, g), s), (DProg (__g, dPool) as dp), sc) ->
          let x = I.newEVar (__g, (I.EClo (A, s))) in
          ((rSolve
              (O, ps', (r, (I.Dot ((I.Exp x), s))), dp,
                (function
                 | (O, S) ->
                     solve'
                       (O, (g, s), dp,
                         (function | (O, M) -> sc (O, (I.App (M, S))))))))
            (* is this EVar redundant? -fp *))
      | (O, ps', (Exists (Dec (_, A), r), s), (DProg (__g, dPool) as dp), sc)
          ->
          let x = I.newEVar (__g, (I.EClo (A, s))) in
          rSolve
            (O, ps', (r, (I.Dot ((I.Exp x), s))), dp,
              (function | (O, S) -> sc (O, (I.App (x, S)))))
      | (O, ps', (Axists (ADec (Some (x), d), r), s),
         (DProg (__g, dPool) as dp), sc) ->
          let x' = I.newAVar () in
          ((rSolve
              (O, ps',
                (r, (I.Dot ((I.Exp (I.EClo (x', (I.Shift (~- d))))), s))), dp,
                sc))
            (* we don't increase the proof term here! *))
      (* fail *)
    let rec aSolve =
      function
      | ((C.Trivial, s), dp, cnstr) -> Assign.solveCnstr cnstr
      | ((UnifyEq (__g', e1, N, eqns), s), (DProg (__g, dPool) as dp), cnstr) ->
          let __g'' = compose' (__g', __g) in
          let s' = shift (__g', s) in
          (Assign.unifiable (__g'', (N, s'), (e1, s'))) &&
            (aSolve ((eqns, s), dp, cnstr))
    let rec matchAtom
      ((Ho)::O, ((Root (Ha, S), s) as ps'), (DProg (__g, dPool) as dp), sc) =
      let rec matchSig =
        function
        | (nil, k) -> raise (Error " \noracle #Pc does not exist \n")
        | ((Const c as Hc)::sgn', k) ->
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
            else matchSig (sgn', k)(* should not happen *) in
      let rec matchDProg =
        function
        | (I.Null, i, k) ->
            raise
              (Error
                 "\n selected dynamic clause number does not exist in current dynamic clause pool!\n")
        | (Decl (dPool', Dec (r, s, Ha')), 1, k) ->
            ((if eqHead (Ha, Ha')
              then
                rSolve
                  (O, ps', (r, (I.comp (s, (I.Shift k)))), dp,
                    (function | (O, S) -> sc (O, (I.Root ((I.BVar k), S)))))
              else
                raise
                  (Error
                     "\n selected dynamic clause does not match current goal!\n"))
            (* shouldn't happen *))
        | (Decl (dPool', dc), i, k) -> matchDProg (dPool', (i - 1), k)
        (* dynamic program exhausted -- shouldn't happen *) in
      ((match Ho with
        | Pc i -> matchSig ((Index.lookup (cidFromHead Ha)), i)
        | Dc i -> matchDProg (dPool, i, i)
        | Csolver (__u) -> sc (O, __u))
        (* matchSig [c1,...,cn] = ()
           try each constant ci in turn for solving atomic goal ps', starting
           with c1.
        *)
        (* matchDProg (dPool, k) = ()
           where k is the index of dPool in global dPool from call to matchAtom.
           Try each local assumption for solving atomic goal ps', starting
           with the most recent one.
        *))
    let rec solve (O, (g, s), (DProg (__g, dPool) as dp), sc) =
      try solve' (O, (g, s), dp, sc) with | Error msg -> print msg
  end ;;
