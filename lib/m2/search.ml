
(* Basic search engine *)
(* Author: Carsten Schuermann *)
module type OLDSEARCH  =
  sig
    module MetaSyn : METASYN
    exception Error of string 
    val searchEx :
      (IntSyn.dctx * IntSyn.__Exp list * (IntSyn.__Exp * IntSyn.__Sub) *
        (unit -> unit)) -> MetaSyn.__State list
    val searchAll :
      (IntSyn.dctx * IntSyn.__Exp list * (IntSyn.__Exp * IntSyn.__Sub) *
        (MetaSyn.__State list -> MetaSyn.__State list)) ->
        MetaSyn.__State list
  end;;




(* Search (based on abstract machine ) *)
(* Author: Carsten Schuermann *)
module OLDSearch(OLDSearch:sig
                             (*! structure IntSyn' : INTSYN !*)
                             module MetaGlobal : METAGLOBAL
                             module MetaSyn' : METASYN
                             module Whnf : WHNF
                             module Unify : UNIFY
                             module Index : INDEX
                             module Compile : COMPILE
                             module CPrint : CPRINT
                             module Print : PRINT
                             (*! sharing MetaSyn'.IntSyn = IntSyn' !*)
                             (*! structure CompSyn' : COMPSYN !*)
                             (*! sharing CompSyn'.IntSyn = IntSyn' !*)
                             (*! sharing Whnf.IntSyn = IntSyn' !*)
                             (*! sharing Unify.IntSyn = IntSyn' !*)
                             (*
                structure Assign : ASSIGN
                sharing Assign.IntSyn = IntSyn'
                *)
                             (*! sharing Index.IntSyn = IntSyn' !*)
                             (*! sharing Compile.IntSyn = IntSyn' !*)
                             (*! sharing Compile.CompSyn = CompSyn' !*)
                             (*! sharing CPrint.IntSyn = IntSyn' !*)
                             (*! sharing CPrint.CompSyn = CompSyn' !*)
                             (*! sharing Print.IntSyn = IntSyn' !*)
                             module Names : NAMES
                           end) : OLDSEARCH =
  struct
    (*! sharing Names.IntSyn = IntSyn' !*)
    (*! structure CSManager : CS_MANAGER !*)
    (*! sharing CSManager.IntSyn = IntSyn' !*)
    (*! structure IntSyn = IntSyn' !*)
    module MetaSyn = MetaSyn'
    (*! structure CompSyn = CompSyn' !*)
    exception Error of string 
    module I = IntSyn
    module M = MetaSyn
    module C = CompSyn
    let rec cidFromHead =
      function | Const a -> a | Def a -> a | Skonst a -> a
    let rec eqHead =
      function
      | (Const a, Const a') -> a = a'
      | (Def a, Def a') -> a = a'
      | _ -> false__
    let rec solve =
      function
      | ((Atom p, s), dp, sc, acck) -> matchAtom ((p, s), dp, sc, acck)
      | ((Impl (r, A, H, g), s), DProg (__g, dPool), sc, acck) ->
          let __d' = I.Dec (None, (I.EClo (A, s))) in
          solve
            ((g, (I.dot1 s)),
              (C.DProg
                 ((I.Decl (__g, __d')), (I.Decl (dPool, (C.Dec (r, s, H)))))),
              (function | (M, acck') -> sc ((I.Lam (__d', M)), acck')), acck)
      | ((All (__d, g), s), DProg (__g, dPool), sc, acck) ->
          let __d' = I.decSub (__d, s) in
          solve
            ((g, (I.dot1 s)),
              (C.DProg ((I.Decl (__g, __d')), (I.Decl (dPool, C.Parameter)))),
              (function | (M, acck') -> sc ((I.Lam (__d', M)), acck')), acck)
    let rec rSolve =
      function
      | (ps', (Eq (Q), s), DProg (__g, dPool), sc, ((acc, k) as acck)) ->
          if Unify.unifiable (__g, ps', (Q, s)) then sc (I.Nil, acck) else acc
      | (ps', (And (r, A, g), s), (DProg (__g, dPool) as dp), sc, acck) ->
          let x = I.newEVar (__g, (I.EClo (A, s))) in
          rSolve
            (ps', (r, (I.Dot ((I.Exp x), s))), dp,
              (function
               | (S, acck') ->
                   solve
                     ((g, s), dp,
                       (function
                        | (M, acck'') ->
                            (try
                               Unify.unify (__g, (x, I.id), (M, I.id));
                               sc ((I.App (M, S)), acck'')
                             with | Unify _ -> [])), acck')), acck)
      | (ps', (Exists (Dec (_, A), r), s), (DProg (__g, dPool) as dp), sc,
         acck) ->
          let x = I.newEVar (__g, (I.EClo (A, s))) in
          rSolve
            (ps', (r, (I.Dot ((I.Exp x), s))), dp,
              (function | (S, acck') -> sc ((I.App (x, S)), acck')), acck)
    let rec aSolve ((C.Trivial, s), dp, sc, acc) = sc ()
    let rec matchAtom
      (((Root (Ha, _), _) as ps'), (DProg (__g, dPool) as dp), sc, (acc, k)) =
      let rec matchSig acc' =
        let rec matchSig' =
          function
          | (nil, acc'') -> acc''
          | ((Hc)::sgn', acc'') ->
              let SClause r = C.sProgLookup (cidFromHead Hc) in
              let acc''' =
                CSManager.trail
                  (function
                   | () ->
                       rSolve
                         (ps', (r, I.id), dp,
                           (function
                            | (S, acck') -> sc ((I.Root (Hc, S)), acck')),
                           (acc'', (k - 1)))) in
              matchSig' (sgn', acc''') in
        matchSig' ((Index.lookup (cidFromHead Ha)), acc') in
      let rec matchDProg =
        function
        | (I.Null, _, acc') -> matchSig acc'
        | (Decl (dPool', Dec (r, s, Ha')), n, acc') ->
            if eqHead (Ha, Ha')
            then
              let acc'' =
                CSManager.trail
                  (function
                   | () ->
                       rSolve
                         (ps', (r, (I.comp (s, (I.Shift n)))), dp,
                           (function
                            | (S, acck') ->
                                sc ((I.Root ((I.BVar n), S)), acck')),
                           (acc', (k - 1)))) in
              matchDProg (dPool', (n + 1), acc'')
            else matchDProg (dPool', (n + 1), acc')
        | (Decl (dPool', C.Parameter), n, acc') ->
            matchDProg (dPool', (n + 1), acc') in
      if k < 0 then acc else matchDProg (dPool, 1, acc)
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
      | (nil, _, acc) -> acc
      | ((EVar (r, _, _, _) as x)::GE, __Vs, acc) ->
          if (occursInExp (r, __Vs)) && (nonIndex (r, acc))
          then selectEVar (GE, __Vs, (x :: acc))
          else selectEVar (GE, __Vs, acc)
    let rec searchEx' arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (max, (nil, sc)) -> [sc ()]
      | (max, ((EVar (r, __g, __v, _))::GE, sc)) ->
          solve
            (((Compile.compileGoal (__g, __v)), I.id),
              (Compile.compileCtx false__ __g),
              (function
               | (__u', (acc', _)) ->
                   (Unify.instantiateEVar (r, __u', nil);
                    searchEx' max (GE, sc))), (nil, max))
    let rec deepen f (P) =
      let rec deepen' (level, acc) =
        if level > (!MetaGlobal.maxFill)
        then acc
        else
          (if (!Global.chatter) > 5 then print "#" else ();
           deepen' ((level + 1), (f level P))) in
      deepen' (1, nil)
    let rec searchEx (__g, GE, __Vs, sc) =
      if (!Global.chatter) > 5 then print "[Search: " else ();
      deepen searchEx'
        ((selectEVar (GE, __Vs, nil)),
          (function
           | Params ->
               (if (!Global.chatter) > 5 then print "OK]\n" else ();
                sc Params)));
      if (!Global.chatter) > 5 then print "FAIL]\n" else ();
      raise (Error "No object found")
    let rec searchAll' =
      function
      | (nil, acc, sc) -> sc acc
      | ((EVar (r, __g, __v, _))::GE, acc, sc) ->
          solve
            (((Compile.compileGoal (__g, __v)), I.id),
              (Compile.compileCtx false__ __g),
              (function
               | (__u', (acc', _)) ->
                   (Unify.instantiateEVar (r, __u', nil);
                    searchAll' (GE, acc', sc))),
              (acc, (!MetaGlobal.maxFill)))
    let rec searchAll (__g, GE, __Vs, sc) =
      searchAll' ((selectEVar (GE, __Vs, nil)), nil, sc)
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
    (* rsolve ((p,s'), (r,s), (__g,dPool), sc, (acc, k)) = ()
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
    (*
    | rSolve (ps', (C.Assign (Q, ag), s), dp, sc, acck as (acc, k)) =
        ((Assign.assign (ps', (Q, s));
          aSolve ((ag, s), dp, (fn () => sc (I.Nil, acck)) , acc))
          handle Unify.Unify _ => acc
               | Assign.Assign _ => acc)
    *)
    (* why doesn't it always succeed?
                                                                --cs *)
    (*    | rSolve (ps', (C.Axists (I.Dec (_, A), r), s), dp as C.DProg (__g, dPool), sc, acck) =
        let
          val x = I.newEVar (__g, I.EClo (A, s))
        in
          rSolve (ps', (r, I.Dot (I.Exp (x), s)), dp,
                  (fn (S, acck') => sc (S, acck')), acck)
        end
*)
    (* aSolve ... *)
    (* Fri Jan 15 16:04:39 1999 -fp,cs
    | aSolve ((C.Unify(I.Eqn(e1, e2), ag), s), dp, sc, acc) =
      ((Unify.unify ((e1, s), (e2, s));
        aSolve ((ag, s), dp, sc, acc))
       handle Unify.Unify _ => acc)
     *)
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
    (* occursInExp (r, (__u, s)) = B,

       Invariant:
       If    __g |- s : G1   G1 |- __u : __v
       then  B holds iff r occurs in (the normal form of) __u
    *)
    (* nonIndex (r, GE) = B

       Invariant:
       B hold iff
        r does not occur in any type of EVars in GE
    *)
    (* select (GE, (__v, s), acc) = acc'

       Invariant:
       If   GE is a list of Evars
       and  __g |- s : __g'   __g' |- __v : __l
       then acc' is a list of EVars (__g', x') s.t.
         (0) it extends acc'
         (1) (__g', x') occurs in __v[s]
         (2) (__g', x') is not an index Variable to any (__g, x) in acc'.
    *)
    (* Efficiency: repeated whnf for every subterm in __Vs!!! *)
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
         checking the variable MetaGlobal.maxLevel
       then R' is the result of applying f to P and
         traversing all possible numbers up to MetaGlobal.maxLevel
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
    (* searchAll' (GE, acc, sc) = acc'

       Invariant:
       If   GE is a list of EVars to be instantiated
       and  acc is list of already collected results of the success continuation
       then acc' is an extension of acc', containing the results of sc
         after trying all combinations of instantiations of EVars in GE
    *)
    (* Shared contexts of EVars in GE may recompiled many times *)
    (* searchAll (__g, GE, (__v, s), sc) = acc'

       Invariant:
       If   __g |- s : __g'   __g' |- __v : level
       and  GE is a list of EVars contained in __v[s]
         where __g |- x : VX
       and  sc is a function to be executed after all non-index variables have
         been instantiated
       then acc' is a list of results from executing the success continuation
    *)
    let searchEx = searchEx
    let searchAll = searchAll
  end ;;
