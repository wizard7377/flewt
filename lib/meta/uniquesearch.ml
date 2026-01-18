
(* Basic search engine: Version 1.3*)
(* Author: Carsten Schuermann *)
module type UNIQUESEARCH  =
  sig
    (*! structure IntSyn : INTSYN !*)
    (*! structure FunSyn : FUNSYN !*)
    module StateSyn : STATESYN
    exception Error of string 
    type nonrec acctype = IntSyn.__Exp
    val searchEx :
      (int * IntSyn.__Exp list * (acctype list -> acctype list)) ->
        acctype list
  end;;




(* Search (based on abstract machine ) : Version 1.3 *)
(* Author: Carsten Schuermann *)
module UniqueSearch(UniqueSearch:sig
                                   module Global : GLOBAL
                                   module StateSyn' : STATESYN
                                   module Abstract : ABSTRACT
                                   module MTPGlobal : MTPGLOBAL
                                   module Whnf : WHNF
                                   module Unify : UNIFY
                                   module Assign : ASSIGN
                                   module Index : INDEX
                                   module Compile : COMPILE
                                   module CPrint : CPRINT
                                   module Print : PRINT
                                   (*! structure IntSyn' : INTSYN !*)
                                   (*! structure FunSyn' : FUNSYN !*)
                                   (*! sharing FunSyn'.IntSyn = IntSyn' !*)
                                   (*! sharing StateSyn'.IntSyn = IntSyn' !*)
                                   (*! sharing StateSyn'.FunSyn = FunSyn' !*)
                                   (*! sharing Abstract.IntSyn = IntSyn' !*)
                                   (*! structure CompSyn' : COMPSYN !*)
                                   (*! sharing CompSyn'.IntSyn = IntSyn' !*)
                                   (*! sharing Whnf.IntSyn = IntSyn' !*)
                                   (*! sharing Unify.IntSyn = IntSyn' !*)
                                   (*! sharing Assign.IntSyn = IntSyn'                         !*)
                                   (*! sharing Index.IntSyn = IntSyn' !*)
                                   (*! sharing Compile.IntSyn = IntSyn' !*)
                                   (*! sharing Compile.CompSyn = CompSyn' !*)
                                   (*! sharing CPrint.IntSyn = IntSyn' !*)
                                   (*! sharing CPrint.CompSyn = CompSyn' !*)
                                   (*! sharing Print.IntSyn = IntSyn' !*)
                                   module Names : NAMES
                                 end) : UNIQUESEARCH =
  struct
    (*! sharing Names.IntSyn = IntSyn' !*)
    (*! structure CSManager : CS_MANAGER !*)
    (*! sharing CSManager.IntSyn = IntSyn' !*)
    (*! structure IntSyn = IntSyn' !*)
    (*! structure FunSyn = FunSyn' !*)
    module StateSyn = StateSyn'
    (*! structure CompSyn = CompSyn' !*)
    exception Error of string 
    type nonrec acctype = IntSyn.__Exp
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
      | (IntSyn.Null, G) -> G
      | (Decl (G, D), G') -> IntSyn.Decl ((compose' (G, G')), D)
    let rec shift =
      function
      | (IntSyn.Null, s) -> s
      | (Decl (G, D), s) -> I.dot1 (shift (G, s))
    let rec exists (P) (K) =
      let rec exists' =
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
      function | (G, 0) -> G | (Decl (G, _), n) -> pruneCtx (G, (n - 1))
    let rec cidFromHead =
      function | Const a -> a | Def a -> a | Skonst a -> a
    let rec eqHead =
      function
      | (Const a, Const a') -> a = a'
      | (Def a, Def a') -> a = a'
      | _ -> false__
    let rec solve =
      function
      | (max, depth, (Atom p, s), dp, sc, acc) ->
          matchAtom (max, depth, (p, s), dp, sc, acc)
      | (max, depth, (Impl (r, A, H, g), s), DProg (G, dPool), sc, acc) ->
          let D' = I.Dec (NONE, (I.EClo (A, s))) in
          solve
            (max, (depth + 1), (g, (I.dot1 s)),
              (C.DProg
                 ((I.Decl (G, D')), (I.Decl (dPool, (C.Dec (r, s, H)))))),
              (function | (M, acc') -> sc ((I.Lam (D', M)), acc')), acc)
      | (max, depth, (All (D, g), s), DProg (G, dPool), sc, acc) ->
          let D' = I.decSub (D, s) in
          solve
            (max, (depth + 1), (g, (I.dot1 s)),
              (C.DProg ((I.Decl (G, D')), (I.Decl (dPool, C.Parameter)))),
              (function | (M, acc') -> sc ((I.Lam (D', M)), acc')), acc)
    let rec rSolve =
      function
      | (max, depth, ps', (Eq (Q), s), DProg (G, dPool), sc, acc) ->
          if Unify.unifiable (G, ps', (Q, s)) then sc (I.Nil, acc) else acc
      | (max, depth, ps', (Assign (Q, eqns), s), (DProg (G, dPool) as dp),
         sc, acc) ->
          (match Assign.assignable (G, ps', (Q, s)) with
           | SOME cnstr ->
               aSolve
                 ((eqns, s), dp, cnstr, (function | () -> sc (I.Nil, acc)),
                   acc)
           | NONE -> acc)
      | (max, depth, ps', (And (r, A, g), s), (DProg (G, dPool) as dp), sc,
         acc) ->
          let X = I.newEVar (G, (I.EClo (A, s))) in
          rSolve
            (max, depth, ps', (r, (I.Dot ((I.Exp X), s))), dp,
              (function
               | (S, acc') ->
                   solve
                     (max, depth, (g, s), dp,
                       (function | (M, acc'') -> sc ((I.App (M, S)), acc'')),
                       acc')), acc)
      | (max, depth, ps', (In (r, A, g), s), (DProg (G, dPool) as dp), sc,
         acc) ->
          let G0 = pruneCtx (G, depth) in
          let dPool0 = pruneCtx (dPool, depth) in
          let w = I.Shift depth in
          let iw = Whnf.invert w in
          let s' = I.comp (s, iw) in
          let X = I.newEVar (G0, (I.EClo (A, s'))) in
          let X' = I.EClo (X, w) in
          rSolve
            (max, depth, ps', (r, (I.Dot ((I.Exp X'), s))), dp,
              (function
               | (S, acc') ->
                   if isInstantiated X
                   then sc ((I.App (X', S)), acc')
                   else
                     solve
                       (max, 0, (g, s'), (C.DProg (G0, dPool0)),
                         (function
                          | (M, acc'') ->
                              (try
                                 Unify.unify (G0, (X, I.id), (M, I.id));
                                 sc ((I.App ((I.EClo (M, w)), S)), acc'')
                               with | Unify _ -> acc'')), acc')), acc)
      | (max, depth, ps', (Exists (Dec (_, A), r), s),
         (DProg (G, dPool) as dp), sc, acc) ->
          let X = I.newEVar (G, (I.EClo (A, s))) in
          rSolve
            (max, depth, ps', (r, (I.Dot ((I.Exp X), s))), dp,
              (function | (S, acc') -> sc ((I.App (X, S)), acc')), acc)
      | (max, depth, ps', (Axists (ADec (SOME (X), d), r), s),
         (DProg (G, dPool) as dp), sc, acc) ->
          let X' = I.newAVar () in
          rSolve
            (max, depth, ps',
              (r, (I.Dot ((I.Exp (I.EClo (X', (I.Shift (~ d))))), s))), dp,
              sc, acc)
    let rec aSolve =
      function
      | ((C.Trivial, s), dp, cnstr, sc, acc) ->
          if Assign.solveCnstr cnstr then sc () else acc
      | ((UnifyEq (G', e1, N, eqns), s), (DProg (G, dPool) as dp), cnstr, sc,
         acc) ->
          let G'' = compose' (G', G) in
          let s' = shift (G', s) in
          if Assign.unifiable (G'', (N, s'), (e1, s'))
          then aSolve ((eqns, s), dp, cnstr, sc, acc)
          else acc
    let rec matchAtom =
      function
      | (0, _, _, _, _, acc) -> acc
      | (max, depth, ((Root (Ha, _), _) as ps'), (DProg (G, dPool) as dp),
         sc, acc) ->
          let rec matchSig' =
            function
            | (nil, acc') -> acc'
            | ((Hc)::sgn', acc') ->
                let SClause r = C.sProgLookup (cidFromHead Hc) in
                let acc''' =
                  CSManager.trail
                    (function
                     | () ->
                         rSolve
                           ((max - 1), depth, ps', (r, I.id), dp,
                             (function
                              | (S, acc'') -> sc ((I.Root (Hc, S)), acc'')),
                             acc')) in
                matchSig' (sgn', acc''') in
          let rec matchDProg =
            function
            | (I.Null, _, acc') ->
                matchSig' ((Index.lookup (cidFromHead Ha)), acc')
            | (Decl (dPool', Dec (r, s, Ha')), n, acc') ->
                if eqHead (Ha, Ha')
                then
                  let acc''' =
                    CSManager.trail
                      (function
                       | () ->
                           rSolve
                             ((max - 1), depth, ps',
                               (r, (I.comp (s, (I.Shift n)))), dp,
                               (function
                                | (S, acc'') ->
                                    sc ((I.Root ((I.BVar n), S)), acc'')),
                               acc')) in
                  matchDProg (dPool', (n + 1), acc''')
                else matchDProg (dPool', (n + 1), acc')
            | (Decl (dPool', C.Parameter), n, acc') ->
                matchDProg (dPool', (n + 1), acc') in
          matchDProg (dPool, 1, acc)
    let rec searchEx' arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (max, (nil, sc, acc)) -> sc acc
      | (max, ((EVar (r, G, V, _) as X)::GE, sc, acc)) ->
          solve
            (max, 0, ((Compile.compileGoal (G, V)), I.id),
              (Compile.compileCtx false__ G),
              (function
               | (U', acc') ->
                   (try
                      Unify.unify (G, (X, I.id), (U', I.id));
                      searchEx' max (GE, sc, acc')
                    with | Unify _ -> acc')), acc)
    let rec searchEx (it, depth) (GE, sc, acc) =
      if (!Global.chatter) > 5 then print "[Search: " else ();
      searchEx' depth
        ((selectEVar GE),
          (function
           | acc' ->
               (if (!Global.chatter) > 5 then print "OK]\n" else ();
                (let GE' =
                   foldr
                     (function
                      | ((EVar (_, G, _, _) as X), L) ->
                          Abstract.collectEVars (G, (X, I.id), L)) nil GE in
                 let gE' = List.length GE' in
                 if gE' > 0
                 then
                   (if it > 0
                    then searchEx ((it - 1), depth) (GE', sc, acc')
                    else raise (Error "not found"))
                 else sc acc'))), acc)
    let rec search (maxFill, GE, sc) = searchEx (1, maxFill) (GE, sc, nil)
    (* isInstantiated (V) = SOME(cid) or NONE
       where cid is the type family of the atomic target type of V,
       NONE if V is a kind or object or have variable type.
    *)
    (* exists P K = B
       where B iff K = K1, Y, K2  s.t. P Y  holds
    *)
    (* occursInExp (r, (U, s)) = B,

       Invariant:
       If    G |- s : G1   G1 |- U : V
       then  B holds iff r occurs in (the normal form of) U
    *)
    (* hack - should consult cs  -rv *)
    (* nonIndex (r, GE) = B

       Invariant:
       B hold iff
        r does not occur in any type of EVars in GE
    *)
    (* select (GE, (V, s), acc) = acc'

       Invariant:
    *)
    (* Efficiency: repeated whnf for every subterm in Vs!!! *)
    (* Constraint case *)
    (* pruneCtx (G, n) = G'

       Invariant:
       If   |- G ctx
       and  G = G0, G1
       and  |G1| = n
       then |- G' = G0 ctx
    *)
    (* only used for type families of compiled clauses *)
    (* solve ((g,s), (G,dPool), sc, (acc, k)) => ()
     Invariants:
       G |- s : G'
       G' |- g :: goal
       G ~ dPool  (context G matches dPool)
       acc is the accumulator of results
       and k is the max search depth limit
           (used in the existential case for iterative deepening,
            used in the universal case for max search depth)
       if  G |- M :: g[s] then G |- sc :: g[s] => Answer, Answer closed
  *)
    (* rsolve (max, depth, (p,s'), (r,s), (G,dPool), sc, (acc, k)) = ()
     Invariants:
       G |- s : G'
       G' |- r :: resgoal
       G |- s' : G''
       G'' |- p :: atom
       G ~ dPool
       acc is the accumulator of results
       and k is the max search depth limit
           (used in the existential case for iterative deepening,
            used in the universal case for max search depth)
       if G |- S :: r[s] then G |- sc : (r >> p[s']) => Answer
  *)
    (* replaced below by above.  -fp Mon Aug 17 10:41:09 1998
        ((Unify.unify (ps', (Q, s)); sc (I.Nil, acck)) handle Unify.Unify _ => acc) *)
    (* is this EVar redundant? -fp *)
    (* G |- g goal *)
    (* G |- A : type *)
    (* G, A |- r resgoal *)
    (* G0, Gl  |- s : G *)
    (* G0, Gl  |- w : G0 *)
    (* G0 |- iw : G0, Gl *)
    (* G0 |- w : G *)
    (* G0 |- X : A[s'] *)
    (* G0, Gl |- X' : A[s'][w] = A[s] *)
    (* we don't increase the proof term here! *)
    (* aSolve ((ag, s), dp, sc) = res
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       if G |- ag[s] auxgoal
       then sc () is evaluated with return value res
       else res = Fail
     Effects: instantiation of EVars in ag[s], dp and sc () *)
    (* matchatom ((p, s), (G, dPool), sc, (acc, k)) => ()
     G |- s : G'
     G' |- p :: atom
     G ~ dPool
     acc is the accumulator of results
     and k is the max search depth limit
         (used in the existential case for iterative deepening,
          used in the universal case for max search depth)
     if G |- M :: p[s] then G |- sc :: p[s] => Answer
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
    (* searchEx (G, GE, (V, s), sc) = acc'
       Invariant:
       If   G |- s : G'   G' |- V : level
       and  GE is a list of EVars contained in V[s]
         where G |- X : VX
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
    (* Shared contexts of EVars in GE may recompiled many times *)
    let searchEx = search
  end ;;
