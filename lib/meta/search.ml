
(* Basic search engine: Version 1.3*)
(* Author: Carsten Schuermann *)
module type MTPSEARCH  =
  sig
    module StateSyn : STATESYN
    exception Error of string 
    val searchEx : (int * IntSyn.__Exp list * (int -> unit)) -> unit
    (*      * (IntSyn.Exp * IntSyn.Sub) *)
  end;;




(* Search (based on abstract machine ) : Version 1.3 *)
(* Author: Carsten Schuermann *)
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
                             (*! structure IntSyn' : INTSYN !*)
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
                             (*! sharing Print.IntSyn = IntSyn' !*)
                             module Names : NAMES
                           end) : MTPSEARCH =
  struct
    (*! sharing Names.IntSyn = IntSyn' !*)
    (*! structure CSManager : CS_MANAGER !*)
    (*! sharing CSManager.IntSyn = IntSyn' !*)
    (*! structure IntSyn = IntSyn' !*)
    module StateSyn = StateSyn'
    (*! structure CompSyn = CompSyn' !*)
    exception Error of string 
    module I = IntSyn
    module C = CompSyn
    let rec isInstantiated =
      function
      | Root (Const cid, _) -> true__
      | Pi (_, __v) -> isInstantiated __v
      | Root (Def cid, _) -> true__
      | Redex (__v, S) -> isInstantiated __v
      | Lam (_, __v) -> isInstantiated __v
      | EVar (ref (Some (__v)), _, _, _) -> isInstantiated __v
      | EClo (__v, s) -> isInstantiated __v
      | _ -> false__
    let rec compose' =
      function
      | (IntSyn.Null, __g) -> __g
      | (Decl (__g, __d), __g') -> IntSyn.Decl ((compose' (__g, __g')), __d)
    let rec shift =
      function
      | (IntSyn.Null, s) -> s
      | (Decl (__g, __d), s) -> I.dot1 (shift (__g, s))
    let rec raiseType =
      function
      | (I.Null, __v) -> __v
      | (Decl (__g, __d), __v) -> raiseType (__g, (I.Pi ((__d, I.Maybe), __v)))
    let rec exists (P) (K) =
      let rec exists' =
        function | I.Null -> false__ | Decl (K', y) -> (P y) || (exists' K') in
      exists' K
    let rec occursInExp (r, __Vs) = occursInExpW (r, (Whnf.whnf __Vs))
    let rec occursInExpW =
      function
      | (r, (Uni _, _)) -> false__
      | (r, (Pi ((__d, _), __v), s)) ->
          (occursInDec (r, (__d, s))) || (occursInExp (r, (__v, (I.dot1 s))))
      | (r, (Root (_, S), s)) -> occursInSpine (r, (S, s))
      | (r, (Lam (__d, __v), s)) ->
          (occursInDec (r, (__d, s))) || (occursInExp (r, (__v, (I.dot1 s))))
      | (r, (EVar (r', _, __v', _), s)) ->
          (r = r') || (occursInExp (r, (__v', s)))
      | (r, (FgnExp csfe, s)) ->
          I.FgnExpStd.fold csfe
            (function | (__u, B) -> B || (occursInExp (r, (__u, s)))) false__
    let rec occursInSpine =
      function
      | (_, (I.Nil, _)) -> false__
      | (r, (SClo (S, s'), s)) -> occursInSpine (r, (S, (I.comp (s', s))))
      | (r, (App (__u, S), s)) ->
          (occursInExp (r, (__u, s))) || (occursInSpine (r, (S, s)))
    let rec occursInDec (r, (Dec (_, __v), s)) = occursInExp (r, (__v, s))
    let rec nonIndex =
      function
      | (_, nil) -> true__
      | (r, (EVar (_, _, __v, _))::GE) ->
          (not (occursInExp (r, (__v, I.id)))) && (nonIndex (r, GE))
    let rec selectEVar =
      function
      | nil -> nil
      | (EVar (r, _, _, ref nil) as x)::GE ->
          let __Xs = selectEVar GE in if nonIndex (r, __Xs) then __Xs @ [x] else __Xs
      | (EVar (r, _, _, cnstrs) as x)::GE ->
          let __Xs = selectEVar GE in if nonIndex (r, __Xs) then x :: __Xs else __Xs
    let rec pruneCtx =
      function | (__g, 0) -> __g | (Decl (__g, _), n) -> pruneCtx (__g, (n - 1))
    let rec cidFromHead =
      function | Const a -> a | Def a -> a | Skonst a -> a
    let rec eqHead =
      function
      | (Const a, Const a') -> a = a'
      | (Def a, Def a') -> a = a'
      | _ -> false__
    let rec solve =
      function
      | (max, depth, (Atom p, s), (DProg (__g, dPool) as dp), sc) ->
          matchAtom (max, depth, (p, s), dp, sc)
      | (max, depth, (Impl (r, A, Ha, g), s), DProg (__g, dPool), sc) ->
          let __d' = I.Dec (None, (I.EClo (A, s))) in
          solve
            (max, (depth + 1), (g, (I.dot1 s)),
              (C.DProg
                 ((I.Decl (__g, __d')), (I.Decl (dPool, (C.Dec (r, s, Ha)))))),
              (function | M -> sc (I.Lam (__d', M))))
      | (max, depth, (All (__d, g), s), DProg (__g, dPool), sc) ->
          let __d' = I.decSub (__d, s) in
          solve
            (max, (depth + 1), (g, (I.dot1 s)),
              (C.DProg ((I.Decl (__g, __d')), (I.Decl (dPool, C.Parameter)))),
              (function | M -> sc (I.Lam (__d', M))))
    let rec rSolve =
      function
      | (max, depth, ps', (Eq (Q), s), DProg (__g, dPool), sc) ->
          if Unify.unifiable (__g, ps', (Q, s)) then sc I.Nil else ()
      | (max, depth, ps', (Assign (Q, eqns), s), (DProg (__g, dPool) as dp),
         sc) ->
          (match Assign.assignable (__g, ps', (Q, s)) with
           | Some cnstr ->
               aSolve ((eqns, s), dp, cnstr, (function | () -> sc I.Nil))
           | None -> ())
      | (max, depth, ps', (And (r, A, g), s), (DProg (__g, dPool) as dp), sc)
          ->
          let x = I.newEVar (__g, (I.EClo (A, s))) in
          rSolve
            (max, depth, ps', (r, (I.Dot ((I.Exp x), s))), dp,
              (function
               | S ->
                   solve
                     (max, depth, (g, s), dp,
                       (function | M -> sc (I.App (M, S))))))
      | (max, depth, ps', (In (r, A, g), s), (DProg (__g, dPool) as dp), sc) ->
          let G0 = pruneCtx (__g, depth) in
          let dPool0 = pruneCtx (dPool, depth) in
          let w = I.Shift depth in
          let iw = Whnf.invert w in
          let s' = I.comp (s, iw) in
          let x = I.newEVar (G0, (I.EClo (A, s'))) in
          let x' = I.EClo (x, w) in
          rSolve
            (max, depth, ps', (r, (I.Dot ((I.Exp x'), s))), dp,
              (function
               | S ->
                   if isInstantiated x
                   then sc (I.App (x', S))
                   else
                     solve
                       (max, 0, (g, s'), (C.DProg (G0, dPool0)),
                         (function
                          | M ->
                              (try
                                 Unify.unify (G0, (x, I.id), (M, I.id));
                                 sc (I.App ((I.EClo (M, w)), S))
                               with | Unify _ -> ())))))
      | (max, depth, ps', (Exists (Dec (_, A), r), s),
         (DProg (__g, dPool) as dp), sc) ->
          let x = I.newEVar (__g, (I.EClo (A, s))) in
          rSolve
            (max, depth, ps', (r, (I.Dot ((I.Exp x), s))), dp,
              (function | S -> sc (I.App (x, S))))
      | (max, depth, ps', (Axists (ADec (Some (x), d), r), s),
         (DProg (__g, dPool) as dp), sc) ->
          let x' = I.newAVar () in
          rSolve
            (max, depth, ps',
              (r, (I.Dot ((I.Exp (I.EClo (x', (I.Shift (~- d))))), s))), dp,
              sc)
    let rec aSolve =
      function
      | ((C.Trivial, s), dp, cnstr, sc) ->
          if Assign.solveCnstr cnstr then sc () else ()
      | ((UnifyEq (__g', e1, N, eqns), s), (DProg (__g, dPool) as dp), cnstr, sc)
          ->
          let __g'' = compose' (__g', __g) in
          let s' = shift (__g', s) in
          if Assign.unifiable (__g'', (N, s'), (e1, s'))
          then aSolve ((eqns, s), dp, cnstr, sc)
          else ()
    let rec matchAtom =
      function
      | (0, _, _, _, _) -> ()
      | (max, depth, ((Root (Ha, _), _) as ps'), (DProg (__g, dPool) as dp),
         sc) ->
          let rec matchSig' =
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
          let rec matchDProg =
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
      | (max, ((EVar (r, __g, __v, _) as x)::GE, sc)) ->
          solve
            (max, 0, ((Compile.compileGoal (__g, __v)), I.id),
              (Compile.compileCtx false__ __g),
              (function
               | __u' ->
                   (try
                      Unify.unify (__g, (x, I.id), (__u', I.id));
                      searchEx' max (GE, sc)
                    with | Unify _ -> ())))
    let rec deepen depth f (P) =
      let rec deepen' level =
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
                      | ((EVar (_, __g, _, _) as x), __l) ->
                          Abstract.collectEVars (__g, (x, I.id), __l)) nil GE in
                 let gE' = List.length GE' in
                 if gE' > 0
                 then
                   (if it > 0 then searchEx ((it - 1), 1) (GE', sc) else ())
                 else sc max))));
      if (!Global.chatter) > 5 then print "FAIL]\n" else ();
      ()
    let rec search (maxFill, GE, sc) = searchEx (1, maxFill) (GE, sc)
    (* isInstantiated (__v) = Some(cid) or None
       where cid is the type family of the atomic target type of __v,
       None if __v is a kind or object or have variable type.
    *)
    (* raiseType (__g, __v) = {{__g}} __v

       Invariant:
       If __g |- __v : __l
       then  . |- {{__g}} __v : __l

       All abstractions are potentially dependent.
    *)
    (* exists P K = B
       where B iff K = K1, y, K2  s.t. P y  holds
    *)
    (* occursInExp (r, (__u, s)) = B,

       Invariant:
       If    __g |- s : G1   G1 |- __u : __v
       then  B holds iff r occurs in (the normal form of) __u
    *)
    (* hack - should consult cs  -rv *)
    (* nonIndex (r, GE) = B

       Invariant:
       B hold iff
        r does not occur in any type of EVars in GE
    *)
    (* select (GE, (__v, s), acc) = acc'

       Invariant:
    *)
    (* Efficiency: repeated whnf for every subterm in __Vs!!! *)
    (* Constraint case *)
    (* pruneCtx (__g, n) = __g'

       Invariant:
       If   |- __g ctx
       and  __g = G0, G1
       and  |G1| = n
       then |- __g' = G0 ctx
    *)
    (* only used for type families of compiled clauses *)
    (* solve ((g,s), (__g,dPool), sc, (acc, k)) => ()
     Invariants:
       __g |- s : __g'
       __g' |- g :: goal
       __g ~ dPool  (context __g matches dPool)
       acc is the accumulator of results
       and k is the max search depth limit
           (used in the existential case for iterative deepening,
            used in the universal case for max search depth)
       if  __g |- M :: g[s] then __g |- sc :: g[s] => Answer, Answer closed
  *)
    (* rsolve (max, depth, (p,s'), (r,s), (__g,dPool), sc, (acc, k)) = ()
     Invariants:
       __g |- s : __g'
       __g' |- r :: resgoal
       __g |- s' : __g''
       __g'' |- p :: atom
       __g ~ dPool
       acc is the accumulator of results
       and k is the max search depth limit
           (used in the existential case for iterative deepening,
            used in the universal case for max search depth)
       if __g |- S :: r[s] then __g |- sc : (r >> p[s']) => Answer
  *)
    (* replaced below by above.  -fp Mon Aug 17 10:41:09 1998
        ((Unify.unify (ps', (Q, s)); sc (I.Nil, acck)) handle Unify.Unify _ => acc) *)
    (* is this EVar redundant? -fp *)
    (* __g |- g goal *)
    (* __g |- A : type *)
    (* __g, A |- r resgoal *)
    (* G0, Gl  |- s : __g *)
    (* G0, Gl  |- w : G0 *)
    (* G0 |- iw : G0, Gl *)
    (* G0 |- w : __g *)
    (* G0 |- x : A[s'] *)
    (* G0, Gl |- x' : A[s'][w] = A[s] *)
    (* we don't increase the proof term here! *)
    (* aSolve ((ag, s), dp, sc) = res
     Invariants:
       dp = (__g, dPool) where __g ~ dPool
       __g |- s : __g'
       if __g |- ag[s] auxgoal
       then sc () is evaluated with return value res
       else res = Fail
     Effects: instantiation of EVars in ag[s], dp and sc () *)
    (* matchatom ((p, s), (__g, dPool), sc, (acc, k)) => ()
     __g |- s : __g'
     __g' |- p :: atom
     __g ~ dPool
     acc is the accumulator of results
     and k is the max search depth limit
         (used in the existential case for iterative deepening,
          used in the universal case for max search depth)
     if __g |- M :: p[s] then __g |- sc :: p[s] => Answer
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
    (* searchEx (__g, GE, (__v, s), sc) = acc'
       Invariant:
       If   __g |- s : __g'   __g' |- __v : level
       and  GE is a list of EVars contained in __v[s]
         where __g |- x : VX
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
