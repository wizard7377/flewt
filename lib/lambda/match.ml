
module type MATCH  =
  sig
    exception Match of
      ((string)(* matching *)(*! structure IntSyn : INTSYN !*)
      (* Author: Frank Pfenning, Carsten Schuermann *)
      (* Matching *)) 
    val match__ : (IntSyn.dctx * IntSyn.eclo * IntSyn.eclo) -> unit
    val matchW :
      (IntSyn.dctx * IntSyn.eclo * IntSyn.eclo) ->
        ((unit)(* raises Unify *))
    val matchBlock :
      (IntSyn.dctx * IntSyn.__Block * IntSyn.__Block) ->
        ((unit)(* raises Unify *))
    val matchSub :
      (IntSyn.dctx * IntSyn.__Sub * IntSyn.__Sub) ->
        ((unit)(* raises Unify *))
    val instance :
      (IntSyn.dctx * IntSyn.eclo * IntSyn.eclo) ->
        ((bool)(* instance (g, Us,Us') will instantiate EVars as an effect 
     checks if Us' is an instance of Us *)
        (* raises Unify *))
    val instance' :
      (IntSyn.dctx * IntSyn.eclo * IntSyn.eclo) ->
        ((string)(* instance' (g, Us,Us') is like instance, but returns NONE for
     success and SOME(msg) for failure *))
          option
  end;;




module Match(Match:sig
                     module Whnf : WHNF
                     module Unify : UNIFY
                     module Trail :
                     ((TRAIL)(* Matching *)(* Unification modified to Matching *)
                     (* Author: Frank Pfenning, Carsten Schuermann *)
                     (* Modified: Roberto Virga, Brigitte Pientka *)
                     (*! structure IntSyn' : INTSYN !*)
                     (*! sharing Whnf.IntSyn = IntSyn' !*))
                   end) : MATCH =
  struct
    exception Match of
      ((string)(*! structure IntSyn = IntSyn' !*)) 
    exception NotInvertible 
    open IntSyn
    let delayExp = Unify.delay
    let rec weakenSub =
      function
      | (g, Shift n, ss) ->
          if (<) n ctxLength g
          then weakenSub (g, (Dot ((Idx (n + 1)), (Shift (n + 1)))), ss)
          else id
      | (g, Dot (Idx n, s'), ss) ->
          (match bvarSub (n, ss) with
           | Undef -> comp ((weakenSub (g, s', ss)), shift)
           | Idx _ -> dot1 (weakenSub (g, s', ss)))
      | (g, Dot (Undef, s'), ss) -> comp ((weakenSub (g, s', ss)), shift)
    let rec pruneExp (g, Us, ss, rOccur) =
      pruneExpW (g, (Whnf.whnf Us), ss, rOccur)
    let rec pruneExpW =
      function
      | (g, ((Uni _ as U), s), _, _) -> U
      | (g, (Pi ((D, P), V), s), ss, rOccur) ->
          Pi
            (((pruneDec (g, (D, s), ss, rOccur)), P),
              (pruneExp
                 ((Decl (g, (decSub (D, s)))), (V, (dot1 s)), (dot1 ss),
                   rOccur)))
      | (g, (Lam (D, V), s), ss, rOccur) ->
          Lam
            ((pruneDec (g, (D, s), ss, rOccur)),
              (pruneExp
                 ((Decl (g, (decSub (D, s)))), (V, (dot1 s)), (dot1 ss),
                   rOccur)))
      | (g, (Root (H, S), s), ss, rOccur) ->
          Root
            ((pruneHead (g, H, ss, rOccur)),
              (pruneSpine (g, (S, s), ss, rOccur)))
      | (g, ((EVar (r, GX, V, cnstrs) as X), s), ss, rOccur) ->
          if rOccur = r
          then raise (Match "Variable occurrence")
          else
            if Whnf.isPatSub s
            then
              (let w = weakenSub (g, s, ss) in
               if Whnf.isId w
               then EClo (X, (comp (s, ss)))
               else
                 raise
                   (Match
                      "Invertible Substitution does not necessarily exist\n"))
            else
              (try EClo (X, (Unify.invertSub (g, s, ss, rOccur)))
               with
               | NotInvertible ->
                   let GY = pruneCtx (ss, g, rOccur) in
                   let V' = pruneExp (g, (V, s), ss, rOccur) in
                   let Y = newEVar (GY, V') in
                   let _ =
                     Unify.addConstraint
                       (cnstrs,
                         (ref
                            (Eqn
                               (g, (EClo (X, s)),
                                 (EClo (Y, (Whnf.invert ss))))))) in
                   Y)
      | (g, (FgnExp csfe, s), ss, rOccur) ->
          FgnExpStd.Map.apply csfe
            (function | U -> pruneExp (g, (U, s), ss, rOccur))
      | (g, ((AVar _ as X), s), ss, rOccur) -> raise (Match "Left-over AVar")
    let rec pruneDec =
      function
      | (g, (Dec (name, V), s), ss, rOccur) ->
          Dec (name, (pruneExp (g, (V, s), ss, rOccur)))
      | (g, (NDec x, _), _, _) -> NDec x
    let rec pruneSpine =
      function
      | (g, (Nil, s), ss, rOccur) -> Nil
      | (g, (App (U, S), s), ss, rOccur) ->
          App
            ((pruneExp (g, (U, s), ss, rOccur)),
              (pruneSpine (g, (S, s), ss, rOccur)))
      | (g, (SClo (S, s'), s), ss, rOccur) ->
          pruneSpine (g, (S, (comp (s', s))), ss, rOccur)
    let rec pruneHead =
      function
      | (g, BVar k, ss, rOccur) ->
          (match bvarSub (k, ss) with
           | Undef -> raise (Match "Parameter dependency")
           | Idx k' -> BVar k')
      | (g, (Const _ as H), ss, rOccur) -> H
      | (g, Proj ((Bidx k as B), i), ss, rOccur) ->
          (match blockSub (B, ss) with | Bidx k' -> Proj ((Bidx k'), i))
      | (g, (Proj (LVar (r, sk, (l, t)), i) as H), ss, rOccur) ->
          (pruneSub (g, t, id, rOccur); H)
      | (g, (Skonst _ as H), ss, rOccur) -> H
      | (g, (Def _ as H), ss, rOccur) -> H
      | (g, FVar (x, V, s'), ss, rOccur) ->
          (pruneExp (g, (V, id), id, rOccur); FVar (x, V, (comp (s', ss))))
      | (g, (FgnConst _ as H), ss, rOccur) -> H
    let rec pruneSub =
      function
      | (g, (Shift n as s), ss, rOccur) ->
          if (<) n ctxLength g
          then
            pruneSub (g, (Dot ((Idx (n + 1)), (Shift (n + 1)))), ss, rOccur)
          else comp (s, ss)
      | (g, Dot (Idx n, s'), ss, rOccur) ->
          (match bvarSub (n, ss) with
           | Undef -> raise (Match "Not prunable")
           | Ft -> Dot (Ft, (pruneSub (g, s', ss, rOccur))))
      | (g, Dot (Exp (U), s'), ss, rOccur) ->
          Dot
            ((Exp (pruneExp (g, (U, id), ss, rOccur))),
              (pruneSub (g, s', ss, rOccur)))
    let rec pruneCtx =
      function
      | (Shift n, Null, rOccur) -> Null
      | (Dot (Idx k, t), Decl (g, D), rOccur) ->
          let t' = comp (t, invShift) in
          let D' = pruneDec (g, (D, id), t', rOccur) in
          Decl ((pruneCtx (t', g, rOccur)), D')
      | (Dot (Undef, t), Decl (g, d), rOccur) -> pruneCtx (t, g, rOccur)
      | (Shift n, g, rOccur) ->
          pruneCtx ((Dot ((Idx (n + 1)), (Shift (n + 1)))), g, rOccur)
    let rec matchExpW =
      function
      | (g, ((FgnExp csfe1, _) as us1), us2) ->
          (match FgnExpStd.UnifyWith.apply csfe1 (g, (EClo us2)) with
           | Succeed residualL ->
               let execResidual =
                 function
                 | Assign (g, EVar (r, _, _, cnstrs), W, ss) ->
                     let W' = pruneExp (g, (W, id), ss, r) in
                     Unify.instantiateEVar (r, W', (!cnstrs))
                 | Delay (U, cnstr) -> delayExp ((U, id), cnstr) in
               List.app execResidual residualL
           | Fail -> raise (Match "Foreign Expression Mismatch"))
      | (g, us1, ((FgnExp csfe2, _) as us2)) ->
          (match FgnExpStd.UnifyWith.apply csfe2 (g, (EClo us1)) with
           | Succeed opL ->
               let execOp =
                 function
                 | Assign (g, EVar (r, _, _, cnstrs), W, ss) ->
                     let W' = pruneExp (g, (W, id), ss, r) in
                     Unify.instantiateEVar (r, W', (!cnstrs))
                 | Delay (U, cnstr) -> delayExp ((U, id), cnstr) in
               List.app execOp opL
           | Fail -> raise (Match "Foreign Expression Mismatch"))
      | (g, (Uni (L1), _), (Uni (L2), _)) -> ()
      | (g, ((Root (H1, s1), s1) as us1), ((Root (H2, s2), s2) as us2)) ->
          (match (H1, H2) with
           | (BVar k1, BVar k2) ->
               if k1 = k2
               then matchSpine (g, (s1, s1), (s2, s2))
               else raise (Match "Bound variable clash")
           | (Const c1, Const c2) ->
               if c1 = c2
               then matchSpine (g, (s1, s1), (s2, s2))
               else raise (Match "Constant clash")
           | (Proj (b1, i1), Proj (b2, i2)) ->
               if i1 = i2
               then
                 (matchBlock (g, b1, b2); matchSpine (g, (s1, s1), (s2, s2)))
               else raise (Match "Global parameter clash")
           | (Skonst c1, Skonst c2) ->
               if c1 = c2
               then matchSpine (g, (s1, s1), (s2, s2))
               else raise (Match "Skolem constant clash")
           | (FVar (n1, _, _), FVar (n2, _, _)) ->
               if n1 = n2
               then matchSpine (g, (s1, s1), (s2, s2))
               else raise (Match "Free variable clash")
           | (Def d1, Def d2) ->
               if d1 = d2
               then matchSpine (g, (s1, s1), (s2, s2))
               else matchDefDefW (g, us1, us2)
           | (Def d1, Const c2) ->
               (match defAncestor d1 with
                | Anc (_, _, NONE) ->
                    matchExpW (g, (Whnf.expandDef us1), us2)
                | Anc (_, _, SOME c1) ->
                    if c1 = c2
                    then matchExpW (g, (Whnf.expandDef us1), us2)
                    else raise (Match "Constant clash"))
           | (Const c1, Def d2) ->
               (match defAncestor d2 with
                | Anc (_, _, NONE) ->
                    matchExpW (g, us1, (Whnf.expandDef us2))
                | Anc (_, _, SOME c2) ->
                    if c1 = c2
                    then matchExpW (g, us1, (Whnf.expandDef us2))
                    else raise (Match "Constant clash"))
           | (Def d1, BVar k2) -> raise (Match "Head mismatch")
           | (BVar k1, Def d2) -> raise (Match "Head mismatch")
           | (Def d1, _) -> matchExpW (g, (Whnf.expandDef us1), us2)
           | (_, Def d2) -> matchExpW (g, us1, (Whnf.expandDef us2))
           | (FgnConst (cs1, ConDec (n1, _, _, _, _, _)), FgnConst
              (cs2, ConDec (n2, _, _, _, _, _))) ->
               if (cs1 = cs2) && (n1 = n2)
               then ()
               else raise (Match "Foreign Constant clash")
           | (FgnConst (cs1, ConDef (n1, _, _, W1, _, _, _)), FgnConst
              (cs2, ConDef (n2, _, _, V, W2, _, _))) ->
               if (cs1 = cs2) && (n1 = n2)
               then ()
               else matchExp (g, (W1, s1), (W2, s2))
           | (FgnConst (_, ConDef (_, _, _, W1, _, _, _)), _) ->
               matchExp (g, (W1, s1), us2)
           | (_, FgnConst (_, ConDef (_, _, _, W2, _, _, _))) ->
               matchExp (g, us1, (W2, s2))
           | _ -> raise (Match "Head mismatch"))
      | (g, (Pi ((D1, _), u1), s1), (Pi ((D2, _), u2), s2)) ->
          (matchDec (g, (D1, s1), (D2, s2));
           matchExp
             ((Decl (g, (decSub (D1, s1)))), (u1, (dot1 s1)),
               (u2, (dot1 s2))))
      | (g, ((Pi (_, _), _) as us1), ((Root (Def _, _), _) as us2)) ->
          matchExpW (g, us1, (Whnf.expandDef us2))
      | (g, ((Root (Def _, _), _) as us1), ((Pi (_, _), _) as us2)) ->
          matchExpW (g, (Whnf.expandDef us1), us2)
      | (g, (Lam (D1, u1), s1), (Lam (D2, u2), s2)) ->
          matchExp
            ((Decl (g, (decSub (D1, s1)))), (u1, (dot1 s1)), (u2, (dot1 s2)))
      | (g, (Lam (D1, u1), s1), (u2, s2)) ->
          matchExp
            ((Decl (g, (decSub (D1, s1)))), (u1, (dot1 s1)),
              ((Redex
                  ((EClo (u2, shift)), (App ((Root ((BVar 1), Nil)), Nil)))),
                (dot1 s2)))
      | (g, (u1, s1), (Lam (D2, u2), s2)) ->
          matchExp
            ((Decl (g, (decSub (D2, s2)))),
              ((Redex
                  ((EClo (u1, shift)), (App ((Root ((BVar 1), Nil)), Nil)))),
                (dot1 s1)), (u2, (dot1 s2)))
      | (g, ((EVar (r, GX, V, cnstrs), s) as us1), ((u2, s2) as us2)) ->
          if Whnf.isPatSub s
          then
            let ss = Whnf.invert s in
            let u2' = pruneExp (g, us2, ss, r) in
            Unify.instantiateEVar (r, u2', (!cnstrs))
          else
            Unify.addConstraint
              (cnstrs, (ref (Eqn (g, (EClo us1), (EClo us2)))))
      | (g, us1, us2) -> raise (Match "Expression clash")
    let rec matchExp (g, ((E1, s1) as us1), ((E2, s2) as us2)) =
      matchExpW (g, (Whnf.whnf us1), (Whnf.whnf us2))
    let rec matchDefDefW
      (g, ((Root (Def d1, s1), s1) as us1), ((Root (Def d2, s2), s2) as us2))
      =
      let Anc (_, h1, c1Opt) = defAncestor d1 in
      let Anc (_, h2, c2Opt) = defAncestor d2 in
      let _ =
        match (c1Opt, c2Opt) with
        | (SOME c1, SOME c2) ->
            if c1 <> c2
            then raise (Match "Irreconcilable defined constant clash")
            else ()
        | _ -> () in
      match Int.compare (h1, h2) with
      | EQUAL -> matchExpW (g, (Whnf.expandDef us1), (Whnf.expandDef us2))
      | LESS -> matchExpW (g, us1, (Whnf.expandDef us2))
      | GREATER -> matchExpW (g, (Whnf.expandDef us1), us2)
    let rec matchSpine =
      function
      | (g, (Nil, _), (Nil, _)) -> ()
      | (g, (SClo (s1, s1'), s1), Ss) ->
          matchSpine (g, (s1, (comp (s1', s1))), Ss)
      | (g, Ss, (SClo (s2, s2'), s2)) ->
          matchSpine (g, Ss, (s2, (comp (s2', s2))))
      | (g, (App (u1, s1), s1), (App (u2, s2), s2)) ->
          (matchExp (g, (u1, s1), (u2, s2));
           matchSpine (g, (s1, s1), (s2, s2)))
    let rec matchDec (g, (Dec (_, V1), s1), (Dec (_, V2), s2)) =
      matchExp (g, (V1, s1), (V2, s2))
    let rec matchSub =
      function
      | (g, Shift n1, Shift n2) -> ()
      | (g, Shift n, (Dot _ as s2)) ->
          matchSub (g, (Dot ((Idx (n + 1)), (Shift (n + 1)))), s2)
      | (g, (Dot _ as s1), Shift m) ->
          matchSub (g, s1, (Dot ((Idx (m + 1)), (Shift (m + 1)))))
      | (g, Dot (Ft1, s1), Dot (Ft2, s2)) ->
          ((match (Ft1, Ft2) with
            | (Idx n1, Idx n2) ->
                if n1 <> n2
                then raise (Error "SOME variables mismatch")
                else ()
            | (Exp (u1), Exp (u2)) -> matchExp (g, (u1, id), (u2, id))
            | (Exp (u1), Idx n2) ->
                matchExp (g, (u1, id), ((Root ((BVar n2), Nil)), id))
            | (Idx n1, Exp (u2)) ->
                matchExp (g, ((Root ((BVar n1), Nil)), id), (u2, id)));
           matchSub (g, s1, s2))
    let rec matchBlock =
      function
      | (g, LVar (ref (SOME (B1)), s, _), B2) ->
          matchBlock (g, (blockSub (B1, s)), B2)
      | (g, B1, LVar (ref (SOME (B2)), s, _)) ->
          matchBlock (g, B1, (blockSub (B2, s)))
      | (g, B1, B2) -> matchBlockW (g, B1, B2)
    let rec matchBlockW =
      function
      | (g, LVar (r1, Shift k1, (l1, t1)), LVar (r2, Shift k2, (l2, t2))) ->
          if l1 <> l2
          then raise (Match "Label clash")
          else
            if r1 = r2
            then ()
            else
              (matchSub (g, t1, t2);
               if k1 <> k2 then raise Bind else ();
               (let ss = Whnf.invert (Shift k1) in
                let t2' = pruneSub (g, t2, ss, (ref NONE)) in
                Unify.instantiateLVar (r1, (LVar (r2, (Shift 0), (l2, t2'))))))
      | (g, LVar (r1, s1, (l1, t1)), B2) ->
          ((:=) r1 SOME (blockSub (B2, (Whnf.invert s1))); ())
      | (g, B1, LVar (r2, s2, (l2, t2))) ->
          ((:=) r2 SOME (blockSub (B1, (Whnf.invert s2))); ())
      | (g, Bidx n1, Bidx n2) ->
          if n1 <> n2 then raise (Match "Block index clash") else ()
    let rec match1W (g, us1, us2) =
      matchExpW (g, us1, us2); awakeCnstr (Unify.nextCnstr ())
    let rec match1 (g, us1, us2) =
      matchExp (g, us1, us2); awakeCnstr (Unify.nextCnstr ())
    let rec awakeCnstr =
      function
      | NONE -> ()
      | SOME (ref (Solved)) -> awakeCnstr (Unify.nextCnstr ())
      | SOME (ref (Eqn (g, u1, u2)) as cnstr) ->
          (Unify.solveConstraint cnstr; match1 (g, (u1, id), (u2, id)))
      | SOME (ref (FgnCnstr csfc)) ->
          if FgnCnstrStd.Awake.apply csfc ()
          then ()
          else raise (Match "Foreign constraint violated")
    let rec matchW (g, us1, us2) =
      Unify.resetAwakenCnstrs (); match1W (g, us1, us2)
    let rec match__ (g, us1, us2) =
      Unify.resetAwakenCnstrs (); match1 (g, us1, us2)
    let ((matchW)(* weakenSub (G1, s, ss) = w'

       Invariant:
       If    g |- s : G1        s patsub *)
      (* ss strsub *)(* w' weaksub *)
      (* no other cases, ss is strsub *)(* prune (g, (U, s), ss, rOccur) = U[s][ss]

       !!! looks wrong to me -kw
       g |- U : V    g' |- s : g  (g' |- U[s] : V[s])
       g'' |- ss : g'

       !!! i would say
       g |- s : g'   g' |- U : V  (g  |- U[s] : V[s])
       g'' |- ss : g

       Effect: prunes EVars in U[s] according to ss
               raises Match if U[s][ss] does not exist, or rOccur occurs in U[s]
    *)
      (* = id *)(* let
                     val wi = Whnf.invert w
                      val V' = EClo (V, wi) *)
      (* val GY = Whnf.strengthen (wi, GX) *)(* shortcut on GY possible by invariant on GX and V[s]? -fp *)
      (* could optimize by checking for identity subst *)
      (* s not patsub *)(* -bp not sure what to do in the non-pattern case *)
      (* val GY = Whnf.strengthen (ss, g) *)(* shortcuts possible by invariants on g? *)
      (* prune or invert??? *)(* val V' = EClo (V, comp (s, ss)) *)
      (* prune or invert??? *)(* this case should never happen! *)
      (* other cases impossible since (U,s1) whnf *)
      (* Added for the meta level -cs Tue Aug 17 17:09:27 2004 *)
      (* blockSub (B, ss) should always be defined *)
      (* Fri Dec 28 10:03:12 2001 -fp !!! *)(* claim: LVar does not need to be pruned since . |- t : Gsome *)
      (* so we perform only the occurs-check here as for FVars *)
      (* Sat Dec  8 13:39:41 2001 -fp !!! *)(* this is not true any more, Sun Dec  1 11:28:47 2002 -cs  *)
      (* Changed from Null to g Sat Dec  7 21:58:00 2002 -fp *)(* V does not to be pruned, since . |- V : type and s' = ^k *)
      (* perform occurs-check for r only *)(* why g here? -fp !!! *)
      (* pruneSub never allows pruning OUTDATED *)(* in the presence of block variables, this invariant
       doesn't hold any more, because substitutions do not
       only occur in EVars any more but also in LVars!
       and there pruning is allowed!   Tue May 29 21:50:17 EDT 2001 -cs *)
      (* must be defined *)(* below my raise Match *)
      (* pruneSub (g, Dot (Undef, s), ss, rOccur) is impossible *)
      (* By invariant, all EVars X[s] are such that s is defined everywhere *)
      (* Pruning establishes and maintains this invariant *)
      (* matchExpW (g, (u1, s1), (u2, s2)) = ()

       Invariant:
       If   g |- s1 : G1   G1 |- u1 : V1    (u1,s1) in whnf
       and  g |- s2 : G2   G2 |- u2 : V2    (u2,s2) in whnf
       and  g |- V1 [s1] = V2 [s2]  : L    (for some level L)
        ***** or V1 = V2 = kind  (needed to check type definitions)
        ***** added by kw Apr 5 2002
       and  s1, u1, s2, u2 do not contain any blockvariable indices Bidx
       then if   there is an instantiation I :
                 s.t. g |- u1 [s1] <I> == u2 [s2] <I>
            then instantiation is applied as effect, () returned
            else exception Match is raised
       Other effects: EVars may be lowered
                      constraints may be added for non-patterns
    *)
      (* L1 = L2 = type, by invariant *)(* matchUni (L1, L2) - removed Mon Aug 24 12:18:24 1998 -fp *)
      (* s1 = s2 = id by whnf *)(* order of calls critical to establish matchSpine invariant *)
      (* because of strict *)(*  matchExpW (g, Whnf.expandDef (us1), Whnf.expandDef (us2)) *)
      (* four new cases for defined constants *)(* conservative *)
      (* conservative *)(* due to strictness! *)
      (* due to strictness! *)(* next two cases for def/fgn, fgn/def *)
      (* we require unique string representation of external constants *)
      (* D1[s1] = D2[s2]  by invariant *)(* ETA: can't occur if eta expanded *)
      (* for rhs:  (u2[s2])[^] 1 = u2 [s2 o ^] 1 = u2 [^ o (1. s2 o ^)] 1
                        = (u2 [^] 1) [1.s2 o ^] *)
      (* Cannot occur if expressions are eta expanded *)
      (* same reasoning holds as above *)(*      | matchExpW (g, us1 as (u1 as EVar(r1, G1, V1, cnstrs1), s1),
                   us2 as (u2 as EVar(r2, G2, V2, cnstrs2), s2)) =
           postpone, if s1 or s2 are not patsub *)
      (* compute ss' directly? *)(* without the next optimization, bugs/hangs/sources.cfg
                     would gets into an apparent infinite loop
                     Fri Sep  5 20:23:27 2003 -fp
                  *)
      (* added for definitions Mon Sep  1 19:53:13 2003 -fp *)(* X[s] = X[s] *)
      (* invertExp ((V1, id), s', ref NONE) *)(* Unify.instantiateEVar (r1, EClo (u2, comp(s2, ss1)), !cnstrs1) *)
      (* invertExpW (us2, s1, ref NONE) *)(* instantiateEVar (r2, EClo (u1, comp(s1, ss2)), !cnstr2) *)
      (* invertExpW (us1, s2, ref NONE) *)(* instantiateEVar (r, EClo (u2, comp(s2, ss)), !cnstrs) *)
      (* invertExpW (us2, s, r) *)(*      | matchExpW (g, us1 as (u1,s1), us2 as (EVar (r, GX, V, cnstrs), s)) =
        if Whnf.isPatSub(s) then
          let
            val ss = Whnf.invert s
            val u1' = pruneExp (g, us1, ss, r)
          in
             instantiateEVar (r, EClo (u1, comp(s1, ss)), !cnstrs) *)
      (* invertExpW (us1, s, r) *)(* covers most remaining cases *)
      (* the cases for EClo or Redex should not occur because of whnf invariant *)
      (* matchExp (g, (u1, s1), (u2, s2)) = ()
       as in matchExpW, except that arguments may not be in whnf
    *)
      (*  matchExpW (g, Whnf.expandDef (us1), Whnf.expandDef (us2)) *)
      (* conservative *)(* matchSpine (g, (s1, s1), (s2, s2)) = ()

       Invariant:
       If   g |- s1 : G1   G1 |- s1 : V1 > W1
       and  g |- s2 : G2   G2 |- s2 : V2 > W2
       and  g |- V1 [s1] = V2 [s2]  : L    (for some level L)
       and  g |- W1 [s1] = W2 [s2]
       then if   there is an instantiation I :
                 s.t. g |- s1 [s1] <I> == s2 [s2] <I>
            then instantiation is applied as effect, () returned
            else exception Match is raised
       Other effects: EVars may be lowered,
                      constraints may be added for non-patterns
    *)
      (* Nil/App or App/Nil cannot occur by typing invariants *)
      (* matchSub (g, s1, s2) = ()

       Invariant:
       If   g |- s1 : g'
       and  g |- s2 : g'
       then matchSub (g, s1, s2) terminates with ()
            iff there exists an instantiation I, such that
            s1 [I] = s2 [I]

       Remark:  matchSub is used only to match the instantiation of SOME variables
    *)
      (* conjecture: g == Null at all times *)(* Thu Dec  6 21:01:09 2001 -fp *)
      (* by invariant *)(*         | (Undef, Undef) =>
           | _ => false *)
      (* not possible because of invariant? -cs *)(* substitutions s1 and s2 were redundant here --- removed *)
      (* Sat Dec  8 11:47:12 2001 -fp !!! *)(* Sat Dec  7 22:04:31 2002 -fp *)
      (* invariant? always k1 = k2? *)(* prune t2? Sat Dec  7 22:09:53 2002 *)
      (*
              if k1 < k2 then instantiateLVar (r1, LVar(r2, Shift(k2-k1), (l2, t2)))
                else Unify.instantiateLVar (r2, LVar(r1, Shift (k1-k2), (l1, t1)))
              *)
      (* hack! *)(* 0 = k2-k1 *)(* -- ABP *)
      (* -- ABP *)(*      | matchBlockW (g, LVar (r1, Shift(k1), (l1, t1)), Bidx i2) =
            (r1 := SOME (Bidx (i2 -k1)) ; ())  -- ABP *)
      (* -- ABP *)(* How can the next case arise? *)
      (* Sat Dec  8 11:49:16 2001 -fp !!! *)(*
      | matchBlock (LVar (r1, _, _), B as Bidx _) = instantiate (r1, B)
      | matchBlock (B as Bidx _, LVar (r2, _, _)) =

      This is still difficult --- B must make sense in the context of the LVar
      Shall we use the inverse of a pattern substitution? Or postpone as
      a constraint if pattern substitution does not exist?
      Sun Dec  1 11:33:13 2002 -cs

*))
      = matchW
    let match__ = match__
    let matchSub = matchSub
    let matchBlock = matchBlock
    let rec instance (g, us1, us2) =
      try match__ (g, us1, us2); true__ with | Match msg -> false__
    let rec instance' (g, us1, us2) =
      try match__ (g, us1, us2); NONE with | Match msg -> SOME msg
  end ;;
