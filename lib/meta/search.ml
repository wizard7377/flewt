
module type MTPSEARCH  =
  sig
    module StateSyn :
    ((STATESYN)(* Basic search engine: Version 1.3*)
    (* Author: Carsten Schuermann *))
    exception Error of string 
    val searchEx :
      (int * IntSyn.__Exp list * (int -> unit)) ->
        ((unit)(*      * (IntSyn.Exp * IntSyn.Sub) *))
  end;;




module MTPSearch(MTPSearch:sig
                             module Global : GLOBAL
                             module Abstract : ABSTRACT
                             module MTPGlobal : MTPGLOBAL
                             module StateSyn' : STATESYN
                             module Whnf : WHNF
                             module Unify : UNIFY
                             module Assign : ASSIGN
                             module Index : INDEX
                             module Compile : COMPILE
                             module CPrint : CPRINT
                             module Print : PRINT
                             module Names :
                             ((NAMES)(* Search (based on abstract machine ) : Version 1.3 *)
                             (* Author: Carsten Schuermann *)(*! structure IntSyn' : INTSYN !*)
                             (*! sharing Abstract.IntSyn = IntSyn' !*)
                             (*! sharing StateSyn'.FunSyn.IntSyn = IntSyn' !*)
                             (*! structure CompSyn' : COMPSYN !*)
                             (*! sharing CompSyn'.IntSyn = IntSyn' !*)
                             (*! sharing Whnf.IntSyn = IntSyn' !*)
                             (*! sharing Unify.IntSyn = IntSyn'              !*)
                             (*! sharing Assign.IntSyn = IntSyn'   !*)
                             (*! sharing Index.IntSyn = IntSyn' !*)
                             (*! sharing Compile.IntSyn = IntSyn' !*)
                             (*! sharing Compile.CompSyn = CompSyn' !*)
                             (*! sharing CPrint.IntSyn = IntSyn' !*)
                             (*! sharing CPrint.CompSyn = CompSyn' !*)
                             (*! sharing Print.IntSyn = IntSyn' !*))
                           end) : MTPSEARCH =
  struct
    module StateSyn =
      ((StateSyn')(*! sharing Names.IntSyn = IntSyn' !*)
      (*! structure CSManager : CS_MANAGER !*)(*! sharing CSManager.IntSyn = IntSyn' !*)
      (*! structure IntSyn = IntSyn' !*))
    exception Error of
      ((string)(*! structure CompSyn = CompSyn' !*)) 
    module I = IntSyn
    module C = CompSyn
    let rec isInstantiated =
      function
      | Root (Const cid, _) -> true__
      | Pi (_, V) -> isInstantiated V
      | Root (Def cid, _) -> true__
      | Redex (V, S) -> isInstantiated V
      | Lam (_, V) -> isInstantiated V
      | EVar (ref (SOME (V)), _, _, _) -> isInstantiated V
      | EClo (V, s) -> isInstantiated V
      | _ -> false__
    let rec compose' =
      function
      | (IntSyn.Null, g) -> g
      | (Decl (g, D), g') -> IntSyn.Decl ((compose' (g, g')), D)
    let rec shift =
      function
      | (IntSyn.Null, s) -> s
      | (Decl (g, D), s) -> I.dot1 (shift (g, s))
    let rec raiseType =
      function
      | (I.Null, V) -> V
      | (Decl (g, D), V) -> raiseType (g, (I.Pi ((D, I.Maybe), V)))
    let rec exists (P) (K) =
      let exists' =
        function | I.Null -> false__ | Decl (K', Y) -> (P Y) || (exists' K') in
      exists' K
    let rec occursInExp (r, Vs) = occursInExpW (r, (Whnf.whnf Vs))
    let rec occursInExpW =
      function
      | (r, (Uni _, _)) -> false__
      | (r, (Pi ((D, _), V), s)) ->
          (occursInDec (r, (D, s))) || (occursInExp (r, (V, (I.dot1 s))))
      | (r, (Root (_, S), s)) -> occursInSpine (r, (S, s))
      | (r, (Lam (D, V), s)) ->
          (occursInDec (r, (D, s))) || (occursInExp (r, (V, (I.dot1 s))))
      | (r, (EVar (r', _, V', _), s)) ->
          (r = r') || (occursInExp (r, (V', s)))
      | (r, (FgnExp csfe, s)) ->
          I.FgnExpStd.fold csfe
            (function | (U, B) -> B || (occursInExp (r, (U, s)))) false__
    let rec occursInSpine =
      function
      | (_, (I.Nil, _)) -> false__
      | (r, (SClo (S, s'), s)) -> occursInSpine (r, (S, (I.comp (s', s))))
      | (r, (App (U, S), s)) ->
          (occursInExp (r, (U, s))) || (occursInSpine (r, (S, s)))
    let rec occursInDec (r, (Dec (_, V), s)) = occursInExp (r, (V, s))
    let rec nonIndex =
      function
      | (_, nil) -> true__
      | (r, (EVar (_, _, V, _))::GE) ->
          (not (occursInExp (r, (V, I.id)))) && (nonIndex (r, GE))
    let rec selectEVar =
      function
      | nil -> nil
      | (EVar (r, _, _, ref nil) as X)::GE ->
          let Xs = selectEVar GE in if nonIndex (r, Xs) then Xs @ [X] else Xs
      | (EVar (r, _, _, cnstrs) as X)::GE ->
          let Xs = selectEVar GE in if nonIndex (r, Xs) then X :: Xs else Xs
    let rec pruneCtx =
      function | (g, 0) -> g | (Decl (g, _), n) -> pruneCtx (g, (n - 1))
    let rec cidFromHead =
      function | Const a -> a | Def a -> a | Skonst a -> a
    let rec eqHead =
      function
      | (Const a, Const a') -> a = a'
      | (Def a, Def a') -> a = a'
      | _ -> false__
    let rec solve =
      function
      | (max, depth, (Atom p, s), (DProg (g, dPool) as dp), sc) ->
          matchAtom (max, depth, (p, s), dp, sc)
      | (max, depth, (Impl (r, A, Ha, g), s), DProg (g, dPool), sc) ->
          let D' = I.Dec (NONE, (I.EClo (A, s))) in
          solve
            (max, (depth + 1), (g, (I.dot1 s)),
              (C.DProg
                 ((I.Decl (g, D')), (I.Decl (dPool, (C.Dec (r, s, Ha)))))),
              (function | M -> sc (I.Lam (D', M))))
      | (max, depth, (All (D, g), s), DProg (g, dPool), sc) ->
          let D' = I.decSub (D, s) in
          solve
            (max, (depth + 1), (g, (I.dot1 s)),
              (C.DProg ((I.Decl (g, D')), (I.Decl (dPool, C.Parameter)))),
              (function | M -> sc (I.Lam (D', M))))
    let rec rSolve =
      function
      | (max, depth, ps', (Eq (Q), s), DProg (g, dPool), sc) ->
          if Unify.unifiable (g, ps', (Q, s)) then sc I.Nil else ()
      | (max, depth, ps', (Assign (Q, eqns), s), (DProg (g, dPool) as dp),
         sc) ->
          (match Assign.assignable (g, ps', (Q, s)) with
           | SOME cnstr ->
               aSolve ((eqns, s), dp, cnstr, (function | () -> sc I.Nil))
           | NONE -> ())
      | (max, depth, ps', (And (r, A, g), s), (DProg (g, dPool) as dp), sc)
          ->
          let X = I.newEVar (g, (I.EClo (A, s))) in
          rSolve
            (max, depth, ps', (r, (I.Dot ((I.Exp X), s))), dp,
              (function
               | S ->
                   solve
                     (max, depth, (g, s), dp,
                       (function | M -> sc (I.App (M, S))))))
      | (max, depth, ps', (In (r, A, g), s), (DProg (g, dPool) as dp), sc) ->
          let G0 = pruneCtx (g, depth) in
          let dPool0 = pruneCtx (dPool, depth) in
          let w = I.Shift depth in
          let iw = Whnf.invert w in
          let s' = I.comp (s, iw) in
          let X = I.newEVar (G0, (I.EClo (A, s'))) in
          let X' = I.EClo (X, w) in
          rSolve
            (max, depth, ps', (r, (I.Dot ((I.Exp X'), s))), dp,
              (function
               | S ->
                   if isInstantiated X
                   then sc (I.App (X', S))
                   else
                     solve
                       (max, 0, (g, s'), (C.DProg (G0, dPool0)),
                         (function
                          | M ->
                              (try
                                 Unify.unify (G0, (X, I.id), (M, I.id));
                                 sc (I.App ((I.EClo (M, w)), S))
                               with | Unify _ -> ())))))
      | (max, depth, ps', (Exists (Dec (_, A), r), s),
         (DProg (g, dPool) as dp), sc) ->
          let X = I.newEVar (g, (I.EClo (A, s))) in
          rSolve
            (max, depth, ps', (r, (I.Dot ((I.Exp X), s))), dp,
              (function | S -> sc (I.App (X, S))))
      | (max, depth, ps', (Axists (ADec (SOME (X), d), r), s),
         (DProg (g, dPool) as dp), sc) ->
          let X' = I.newAVar () in
          rSolve
            (max, depth, ps',
              (r, (I.Dot ((I.Exp (I.EClo (X', (I.Shift (~ d))))), s))), dp,
              sc)
    let rec aSolve =
      function
      | ((C.Trivial, s), dp, cnstr, sc) ->
          if Assign.solveCnstr cnstr then sc () else ()
      | ((UnifyEq (g', e1, N, eqns), s), (DProg (g, dPool) as dp), cnstr, sc)
          ->
          let g'' = compose' (g', g) in
          let s' = shift (g', s) in
          if Assign.unifiable (g'', (N, s'), (e1, s'))
          then aSolve ((eqns, s), dp, cnstr, sc)
          else ()
    let rec matchAtom =
      function
      | (0, _, _, _, _) -> ()
      | (max, depth, ((Root (Ha, _), _) as ps'), (DProg (g, dPool) as dp),
         sc) ->
          let matchSig' =
            function
            | nil -> ()
            | (Hc)::sgn' ->
                let SClause r = C.sProgLookup (cidFromHead Hc) in
                let _ =
                  CSManager.trail
                    (function
                     | () ->
                         rSolve
                           ((max - 1), depth, ps', (r, I.id), dp,
                             (function | S -> sc (I.Root (Hc, S))))) in
                matchSig' sgn' in
          let matchDProg =
            function
            | (I.Null, _) -> matchSig' (Index.lookup (cidFromHead Ha))
            | (Decl (dPool', Dec (r, s, Ha')), n) ->
                if eqHead (Ha, Ha')
                then
                  let _ =
                    CSManager.trail
                      (function
                       | () ->
                           rSolve
                             ((max - 1), depth, ps',
                               (r, (I.comp (s, (I.Shift n)))), dp,
                               (function | S -> sc (I.Root ((I.BVar n), S))))) in
                  matchDProg (dPool', (n + 1))
                else matchDProg (dPool', (n + 1))
            | (Decl (dPool', C.Parameter), n) -> matchDProg (dPool', (n + 1)) in
          matchDProg (dPool, 1)
    let rec searchEx' arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (max, (nil, sc)) -> sc max
      | (max, ((EVar (r, g, V, _) as X)::GE, sc)) ->
          solve
            (max, 0, ((Compile.compileGoal (g, V)), I.id),
              (Compile.compileCtx false__ g),
              (function
               | U' ->
                   (try
                      Unify.unify (g, (X, I.id), (U', I.id));
                      searchEx' max (GE, sc)
                    with | Unify _ -> ())))
    let rec deepen depth f (P) =
      let deepen' level =
        if level > depth
        then ()
        else
          (if (!Global.chatter) > 5 then print "#" else ();
           f level P;
           deepen' (level + 1)) in
      deepen' 1
    let rec searchEx (it, depth) (GE, sc) =
      if (!Global.chatter) > 5 then print "[Search: " else ();
      deepen depth searchEx'
        ((selectEVar GE),
          (function
           | max ->
               (if (!Global.chatter) > 5 then print "OK]\n" else ();
                (let GE' =
                   foldr
                     (function
                      | ((EVar (_, g, _, _) as X), L) ->
                          Abstract.collectEVars (g, (X, I.id), L)) nil GE in
                 let gE' = List.length GE' in
                 if gE' > 0
                 then
                   (if it > 0 then searchEx ((it - 1), 1) (GE', sc) else ())
                 else sc max))));
      if (!Global.chatter) > 5 then print "FAIL]\n" else ();
      ()
    let rec search (maxFill, GE, sc) = searchEx (1, maxFill) (GE, sc)
    let ((searchEx)(* isInstantiated (V) = SOME(cid) or NONE
       where cid is the type family of the atomic target type of V,
       NONE if V is a kind or object or have variable type.
    *)
      (* raiseType (g, V) = {{g}} V

       Invariant:
       If g |- V : L
       then  . |- {{g}} V : L

       All abstractions are potentially dependent.
    *)
      (* exists P K = B
       where B iff K = K1, Y, K2  s.t. P Y  holds
    *)
      (* occursInExp (r, (U, s)) = B,

       Invariant:
       If    g |- s : G1   G1 |- U : V
       then  B holds iff r occurs in (the normal form of) U
    *)
      (* hack - should consult cs  -rv *)(* nonIndex (r, GE) = B

       Invariant:
       B hold iff
        r does not occur in any type of EVars in GE
    *)
      (* select (GE, (V, s), acc) = acc'

       Invariant:
    *)
      (* Efficiency: repeated whnf for every subterm in Vs!!! *)
      (* Constraint case *)(* pruneCtx (g, n) = g'

       Invariant:
       If   |- g ctx
       and  g = G0, G1
       and  |G1| = n
       then |- g' = G0 ctx
    *)
      (* only used for type families of compiled clauses *)
      (* solve ((g,s), (g,dPool), sc, (acc, k)) => ()
     Invariants:
       g |- s : g'
       g' |- g :: goal
       g ~ dPool  (context g matches dPool)
       acc is the accumulator of results
       and k is the max search depth limit
           (used in the existential case for iterative deepening,
            used in the universal case for max search depth)
       if  g |- M :: g[s] then g |- sc :: g[s] => Answer, Answer closed
  *)
      (* rsolve (max, depth, (p,s'), (r,s), (g,dPool), sc, (acc, k)) = ()
     Invariants:
       g |- s : g'
       g' |- r :: resgoal
       g |- s' : g''
       g'' |- p :: atom
       g ~ dPool
       acc is the accumulator of results
       and k is the max search depth limit
           (used in the existential case for iterative deepening,
            used in the universal case for max search depth)
       if g |- S :: r[s] then g |- sc : (r >> p[s']) => Answer
  *)
      (* replaced below by above.  -fp Mon Aug 17 10:41:09 1998
        ((Unify.unify (ps', (Q, s)); sc (I.Nil, acck)) handle Unify.Unify _ => acc) *)
      (* is this EVar redundant? -fp *)(* g |- g goal *)
      (* g |- A : type *)(* g, A |- r resgoal *)
      (* G0, Gl  |- s : g *)(* G0, Gl  |- w : G0 *)
      (* G0 |- iw : G0, Gl *)(* G0 |- w : g *)(* G0 |- X : A[s'] *)
      (* G0, Gl |- X' : A[s'][w] = A[s] *)(* we don't increase the proof term here! *)
      (* aSolve ((ag, s), dp, sc) = res
     Invariants:
       dp = (g, dPool) where g ~ dPool
       g |- s : g'
       if g |- ag[s] auxgoal
       then sc () is evaluated with return value res
       else res = Fail
     Effects: instantiation of EVars in ag[s], dp and sc () *)
      (* matchatom ((p, s), (g, dPool), sc, (acc, k)) => ()
     g |- s : g'
     g' |- p :: atom
     g ~ dPool
     acc is the accumulator of results
     and k is the max search depth limit
         (used in the existential case for iterative deepening,
          used in the universal case for max search depth)
     if g |- M :: p[s] then g |- sc :: p[s] => Answer
  *)
      (* searchEx' max (GE, sc) = acc'

       Invariant:
       If   GE is a list of EVars to be instantiated
       and  max is the maximal number of constructors
       then if an instantiation of EVars in GE is found Success is raised
            otherwise searchEx' terminates with []
    *)
      (* contexts of EVars are recompiled for each search depth *)
      (* Possible optimization:
           Check if there are still variables left over
        *)
      (* deepen (f, P) = R'

       Invariant:
       If   f function expecting parameters P
         checking the variable MTPGlobal.maxLevel
       then R' is the result of applying f to P and
         traversing all possible numbers up to MTPGlobal.maxLevel
    *)
      (* searchEx (g, GE, (V, s), sc) = acc'
       Invariant:
       If   g |- s : g'   g' |- V : level
       and  GE is a list of EVars contained in V[s]
         where g |- X : VX
       and  sc is a function to be executed after all non-index variables have
         been instantiated
       then acc' is a list containing the one result from executing the success continuation
         All EVar's got instantiated with the smallest possible terms.
    *)
      (* warning: iterative deepening depth is not propably updated.
                                             possible that it runs into an endless loop ? *)
      (* search (GE, sc) = ()

       Invariant:
       GE is a list of uninstantiated EVars
       and sc is a success continuation : int -> unit

       Side effect:
       success continuation will raise exception
    *)
      (* Shared contexts of EVars in GE may recompiled many times *))
      = search
  end ;;
