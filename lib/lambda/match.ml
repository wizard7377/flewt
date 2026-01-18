
(* Matching *)
(* Author: Frank Pfenning, Carsten Schuermann *)
module type MATCH  =
  sig
    (*! structure IntSyn : INTSYN !*)
    (* matching *)
    exception Match of string 
    val match__ : (IntSyn.dctx * IntSyn.eclo * IntSyn.eclo) -> unit
    (* raises Unify *)
    val matchW : (IntSyn.dctx * IntSyn.eclo * IntSyn.eclo) -> unit
    (* raises Unify *)
    val matchBlock : (IntSyn.dctx * IntSyn.__Block * IntSyn.__Block) -> unit
    (* raises Unify *)
    val matchSub : (IntSyn.dctx * IntSyn.__Sub * IntSyn.__Sub) -> unit
    (* raises Unify *)
    (* instance (G, Us,Us') will instantiate EVars as an effect 
     checks if Us' is an instance of Us *)
    val instance : (IntSyn.dctx * IntSyn.eclo * IntSyn.eclo) -> bool
    (* instance' (G, Us,Us') is like instance, but returns NONE for
     success and SOME(msg) for failure *)
    val instance' :
      (IntSyn.dctx * IntSyn.eclo * IntSyn.eclo) -> string option
  end;;




(* Matching *)
(* Unification modified to Matching *)
(* Author: Frank Pfenning, Carsten Schuermann *)
(* Modified: Roberto Virga, Brigitte Pientka *)
module Match(Match:sig
                     (*! structure IntSyn' : INTSYN !*)
                     module Whnf : WHNF
                     module Unify : UNIFY
                     (*! sharing Whnf.IntSyn = IntSyn' !*)
                     module Trail : TRAIL
                   end) : MATCH =
  struct
    (*! structure IntSyn = IntSyn' !*)
    exception Match of string 
    exception NotInvertible 
    open IntSyn
    let delayExp = Unify.delay
    let rec weakenSub =
      function
      | (G, Shift n, ss) ->
          if (<) n ctxLength G
          then weakenSub (G, (Dot ((Idx (n + 1)), (Shift (n + 1)))), ss)
          else id
      | (G, Dot (Idx n, s'), ss) ->
          (match bvarSub (n, ss) with
           | Undef -> comp ((weakenSub (G, s', ss)), shift)
           | Idx _ -> dot1 (weakenSub (G, s', ss)))
      | (G, Dot (Undef, s'), ss) -> comp ((weakenSub (G, s', ss)), shift)
    let rec pruneExp (G, Us, ss, rOccur) =
      pruneExpW (G, (Whnf.whnf Us), ss, rOccur)
    let rec pruneExpW =
      function
      | (G, ((Uni _ as U), s), _, _) -> U
      | (G, (Pi ((D, P), V), s), ss, rOccur) ->
          Pi
            (((pruneDec (G, (D, s), ss, rOccur)), P),
              (pruneExp
                 ((Decl (G, (decSub (D, s)))), (V, (dot1 s)), (dot1 ss),
                   rOccur)))
      | (G, (Lam (D, V), s), ss, rOccur) ->
          Lam
            ((pruneDec (G, (D, s), ss, rOccur)),
              (pruneExp
                 ((Decl (G, (decSub (D, s)))), (V, (dot1 s)), (dot1 ss),
                   rOccur)))
      | (G, (Root (H, S), s), ss, rOccur) ->
          Root
            ((pruneHead (G, H, ss, rOccur)),
              (pruneSpine (G, (S, s), ss, rOccur)))
      | (G, ((EVar (r, GX, V, cnstrs) as X), s), ss, rOccur) ->
          if rOccur = r
          then raise (Match "Variable occurrence")
          else
            if Whnf.isPatSub s
            then
              (let w = weakenSub (G, s, ss) in
               if Whnf.isId w
               then EClo (X, (comp (s, ss)))
               else
                 raise
                   (Match
                      "Invertible Substitution does not necessarily exist\n"))
            else
              (try EClo (X, (Unify.invertSub (G, s, ss, rOccur)))
               with
               | NotInvertible ->
                   let GY = pruneCtx (ss, G, rOccur) in
                   let V' = pruneExp (G, (V, s), ss, rOccur) in
                   let Y = newEVar (GY, V') in
                   let _ =
                     Unify.addConstraint
                       (cnstrs,
                         (ref
                            (Eqn
                               (G, (EClo (X, s)),
                                 (EClo (Y, (Whnf.invert ss))))))) in
                   Y)
      | (G, (FgnExp csfe, s), ss, rOccur) ->
          FgnExpStd.Map.apply csfe
            (function | U -> pruneExp (G, (U, s), ss, rOccur))
      | (G, ((AVar _ as X), s), ss, rOccur) -> raise (Match "Left-over AVar")
    let rec pruneDec =
      function
      | (G, (Dec (name, V), s), ss, rOccur) ->
          Dec (name, (pruneExp (G, (V, s), ss, rOccur)))
      | (G, (NDec x, _), _, _) -> NDec x
    let rec pruneSpine =
      function
      | (G, (Nil, s), ss, rOccur) -> Nil
      | (G, (App (U, S), s), ss, rOccur) ->
          App
            ((pruneExp (G, (U, s), ss, rOccur)),
              (pruneSpine (G, (S, s), ss, rOccur)))
      | (G, (SClo (S, s'), s), ss, rOccur) ->
          pruneSpine (G, (S, (comp (s', s))), ss, rOccur)
    let rec pruneHead =
      function
      | (G, BVar k, ss, rOccur) ->
          (match bvarSub (k, ss) with
           | Undef -> raise (Match "Parameter dependency")
           | Idx k' -> BVar k')
      | (G, (Const _ as H), ss, rOccur) -> H
      | (G, Proj ((Bidx k as B), i), ss, rOccur) ->
          (match blockSub (B, ss) with | Bidx k' -> Proj ((Bidx k'), i))
      | (G, (Proj (LVar (r, sk, (l, t)), i) as H), ss, rOccur) ->
          (pruneSub (G, t, id, rOccur); H)
      | (G, (Skonst _ as H), ss, rOccur) -> H
      | (G, (Def _ as H), ss, rOccur) -> H
      | (G, FVar (x, V, s'), ss, rOccur) ->
          (pruneExp (G, (V, id), id, rOccur); FVar (x, V, (comp (s', ss))))
      | (G, (FgnConst _ as H), ss, rOccur) -> H
    let rec pruneSub =
      function
      | (G, (Shift n as s), ss, rOccur) ->
          if (<) n ctxLength G
          then
            pruneSub (G, (Dot ((Idx (n + 1)), (Shift (n + 1)))), ss, rOccur)
          else comp (s, ss)
      | (G, Dot (Idx n, s'), ss, rOccur) ->
          (match bvarSub (n, ss) with
           | Undef -> raise (Match "Not prunable")
           | Ft -> Dot (Ft, (pruneSub (G, s', ss, rOccur))))
      | (G, Dot (Exp (U), s'), ss, rOccur) ->
          Dot
            ((Exp (pruneExp (G, (U, id), ss, rOccur))),
              (pruneSub (G, s', ss, rOccur)))
    let rec pruneCtx =
      function
      | (Shift n, Null, rOccur) -> Null
      | (Dot (Idx k, t), Decl (G, D), rOccur) ->
          let t' = comp (t, invShift) in
          let D' = pruneDec (G, (D, id), t', rOccur) in
          Decl ((pruneCtx (t', G, rOccur)), D')
      | (Dot (Undef, t), Decl (G, d), rOccur) -> pruneCtx (t, G, rOccur)
      | (Shift n, G, rOccur) ->
          pruneCtx ((Dot ((Idx (n + 1)), (Shift (n + 1)))), G, rOccur)
    let rec matchExpW =
      function
      | (G, ((FgnExp csfe1, _) as Us1), Us2) ->
          (match FgnExpStd.UnifyWith.apply csfe1 (G, (EClo Us2)) with
           | Succeed residualL ->
               let rec execResidual =
                 function
                 | Assign (G, EVar (r, _, _, cnstrs), W, ss) ->
                     let W' = pruneExp (G, (W, id), ss, r) in
                     Unify.instantiateEVar (r, W', (!cnstrs))
                 | Delay (U, cnstr) -> delayExp ((U, id), cnstr) in
               List.app execResidual residualL
           | Fail -> raise (Match "Foreign Expression Mismatch"))
      | (G, Us1, ((FgnExp csfe2, _) as Us2)) ->
          (match FgnExpStd.UnifyWith.apply csfe2 (G, (EClo Us1)) with
           | Succeed opL ->
               let rec execOp =
                 function
                 | Assign (G, EVar (r, _, _, cnstrs), W, ss) ->
                     let W' = pruneExp (G, (W, id), ss, r) in
                     Unify.instantiateEVar (r, W', (!cnstrs))
                 | Delay (U, cnstr) -> delayExp ((U, id), cnstr) in
               List.app execOp opL
           | Fail -> raise (Match "Foreign Expression Mismatch"))
      | (G, (Uni (L1), _), (Uni (L2), _)) -> ()
      | (G, ((Root (H1, S1), s1) as Us1), ((Root (H2, S2), s2) as Us2)) ->
          (match (H1, H2) with
           | (BVar k1, BVar k2) ->
               if k1 = k2
               then matchSpine (G, (S1, s1), (S2, s2))
               else raise (Match "Bound variable clash")
           | (Const c1, Const c2) ->
               if c1 = c2
               then matchSpine (G, (S1, s1), (S2, s2))
               else raise (Match "Constant clash")
           | (Proj (b1, i1), Proj (b2, i2)) ->
               if i1 = i2
               then
                 (matchBlock (G, b1, b2); matchSpine (G, (S1, s1), (S2, s2)))
               else raise (Match "Global parameter clash")
           | (Skonst c1, Skonst c2) ->
               if c1 = c2
               then matchSpine (G, (S1, s1), (S2, s2))
               else raise (Match "Skolem constant clash")
           | (FVar (n1, _, _), FVar (n2, _, _)) ->
               if n1 = n2
               then matchSpine (G, (S1, s1), (S2, s2))
               else raise (Match "Free variable clash")
           | (Def d1, Def d2) ->
               if d1 = d2
               then matchSpine (G, (S1, s1), (S2, s2))
               else matchDefDefW (G, Us1, Us2)
           | (Def d1, Const c2) ->
               (match defAncestor d1 with
                | Anc (_, _, NONE) ->
                    matchExpW (G, (Whnf.expandDef Us1), Us2)
                | Anc (_, _, SOME c1) ->
                    if c1 = c2
                    then matchExpW (G, (Whnf.expandDef Us1), Us2)
                    else raise (Match "Constant clash"))
           | (Const c1, Def d2) ->
               (match defAncestor d2 with
                | Anc (_, _, NONE) ->
                    matchExpW (G, Us1, (Whnf.expandDef Us2))
                | Anc (_, _, SOME c2) ->
                    if c1 = c2
                    then matchExpW (G, Us1, (Whnf.expandDef Us2))
                    else raise (Match "Constant clash"))
           | (Def d1, BVar k2) -> raise (Match "Head mismatch")
           | (BVar k1, Def d2) -> raise (Match "Head mismatch")
           | (Def d1, _) -> matchExpW (G, (Whnf.expandDef Us1), Us2)
           | (_, Def d2) -> matchExpW (G, Us1, (Whnf.expandDef Us2))
           | (FgnConst (cs1, ConDec (n1, _, _, _, _, _)), FgnConst
              (cs2, ConDec (n2, _, _, _, _, _))) ->
               if (cs1 = cs2) && (n1 = n2)
               then ()
               else raise (Match "Foreign Constant clash")
           | (FgnConst (cs1, ConDef (n1, _, _, W1, _, _, _)), FgnConst
              (cs2, ConDef (n2, _, _, V, W2, _, _))) ->
               if (cs1 = cs2) && (n1 = n2)
               then ()
               else matchExp (G, (W1, s1), (W2, s2))
           | (FgnConst (_, ConDef (_, _, _, W1, _, _, _)), _) ->
               matchExp (G, (W1, s1), Us2)
           | (_, FgnConst (_, ConDef (_, _, _, W2, _, _, _))) ->
               matchExp (G, Us1, (W2, s2))
           | _ -> raise (Match "Head mismatch"))
      | (G, (Pi ((D1, _), U1), s1), (Pi ((D2, _), U2), s2)) ->
          (matchDec (G, (D1, s1), (D2, s2));
           matchExp
             ((Decl (G, (decSub (D1, s1)))), (U1, (dot1 s1)),
               (U2, (dot1 s2))))
      | (G, ((Pi (_, _), _) as Us1), ((Root (Def _, _), _) as Us2)) ->
          matchExpW (G, Us1, (Whnf.expandDef Us2))
      | (G, ((Root (Def _, _), _) as Us1), ((Pi (_, _), _) as Us2)) ->
          matchExpW (G, (Whnf.expandDef Us1), Us2)
      | (G, (Lam (D1, U1), s1), (Lam (D2, U2), s2)) ->
          matchExp
            ((Decl (G, (decSub (D1, s1)))), (U1, (dot1 s1)), (U2, (dot1 s2)))
      | (G, (Lam (D1, U1), s1), (U2, s2)) ->
          matchExp
            ((Decl (G, (decSub (D1, s1)))), (U1, (dot1 s1)),
              ((Redex
                  ((EClo (U2, shift)), (App ((Root ((BVar 1), Nil)), Nil)))),
                (dot1 s2)))
      | (G, (U1, s1), (Lam (D2, U2), s2)) ->
          matchExp
            ((Decl (G, (decSub (D2, s2)))),
              ((Redex
                  ((EClo (U1, shift)), (App ((Root ((BVar 1), Nil)), Nil)))),
                (dot1 s1)), (U2, (dot1 s2)))
      | (G, ((EVar (r, GX, V, cnstrs), s) as Us1), ((U2, s2) as Us2)) ->
          if Whnf.isPatSub s
          then
            let ss = Whnf.invert s in
            let U2' = pruneExp (G, Us2, ss, r) in
            Unify.instantiateEVar (r, U2', (!cnstrs))
          else
            Unify.addConstraint
              (cnstrs, (ref (Eqn (G, (EClo Us1), (EClo Us2)))))
      | (G, Us1, Us2) -> raise (Match "Expression clash")
    let rec matchExp (G, ((E1, s1) as Us1), ((E2, s2) as Us2)) =
      matchExpW (G, (Whnf.whnf Us1), (Whnf.whnf Us2))
    let rec matchDefDefW
      (G, ((Root (Def d1, S1), s1) as Us1), ((Root (Def d2, S2), s2) as Us2))
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
      | EQUAL -> matchExpW (G, (Whnf.expandDef Us1), (Whnf.expandDef Us2))
      | LESS -> matchExpW (G, Us1, (Whnf.expandDef Us2))
      | GREATER -> matchExpW (G, (Whnf.expandDef Us1), Us2)
    let rec matchSpine =
      function
      | (G, (Nil, _), (Nil, _)) -> ()
      | (G, (SClo (S1, s1'), s1), Ss) ->
          matchSpine (G, (S1, (comp (s1', s1))), Ss)
      | (G, Ss, (SClo (S2, s2'), s2)) ->
          matchSpine (G, Ss, (S2, (comp (s2', s2))))
      | (G, (App (U1, S1), s1), (App (U2, S2), s2)) ->
          (matchExp (G, (U1, s1), (U2, s2));
           matchSpine (G, (S1, s1), (S2, s2)))
    let rec matchDec (G, (Dec (_, V1), s1), (Dec (_, V2), s2)) =
      matchExp (G, (V1, s1), (V2, s2))
    let rec matchSub =
      function
      | (G, Shift n1, Shift n2) -> ()
      | (G, Shift n, (Dot _ as s2)) ->
          matchSub (G, (Dot ((Idx (n + 1)), (Shift (n + 1)))), s2)
      | (G, (Dot _ as s1), Shift m) ->
          matchSub (G, s1, (Dot ((Idx (m + 1)), (Shift (m + 1)))))
      | (G, Dot (Ft1, s1), Dot (Ft2, s2)) ->
          ((match (Ft1, Ft2) with
            | (Idx n1, Idx n2) ->
                if n1 <> n2
                then raise (Error "SOME variables mismatch")
                else ()
            | (Exp (U1), Exp (U2)) -> matchExp (G, (U1, id), (U2, id))
            | (Exp (U1), Idx n2) ->
                matchExp (G, (U1, id), ((Root ((BVar n2), Nil)), id))
            | (Idx n1, Exp (U2)) ->
                matchExp (G, ((Root ((BVar n1), Nil)), id), (U2, id)));
           matchSub (G, s1, s2))
    let rec matchBlock =
      function
      | (G, LVar (ref (SOME (B1)), s, _), B2) ->
          matchBlock (G, (blockSub (B1, s)), B2)
      | (G, B1, LVar (ref (SOME (B2)), s, _)) ->
          matchBlock (G, B1, (blockSub (B2, s)))
      | (G, B1, B2) -> matchBlockW (G, B1, B2)
    let rec matchBlockW =
      function
      | (G, LVar (r1, Shift k1, (l1, t1)), LVar (r2, Shift k2, (l2, t2))) ->
          if l1 <> l2
          then raise (Match "Label clash")
          else
            if r1 = r2
            then ()
            else
              (matchSub (G, t1, t2);
               if k1 <> k2 then raise Bind else ();
               (let ss = Whnf.invert (Shift k1) in
                let t2' = pruneSub (G, t2, ss, (ref NONE)) in
                Unify.instantiateLVar (r1, (LVar (r2, (Shift 0), (l2, t2'))))))
      | (G, LVar (r1, s1, (l1, t1)), B2) ->
          ((:=) r1 SOME (blockSub (B2, (Whnf.invert s1))); ())
      | (G, B1, LVar (r2, s2, (l2, t2))) ->
          ((:=) r2 SOME (blockSub (B1, (Whnf.invert s2))); ())
      | (G, Bidx n1, Bidx n2) ->
          if n1 <> n2 then raise (Match "Block index clash") else ()
    let rec match1W (G, Us1, Us2) =
      matchExpW (G, Us1, Us2); awakeCnstr (Unify.nextCnstr ())
    let rec match1 (G, Us1, Us2) =
      matchExp (G, Us1, Us2); awakeCnstr (Unify.nextCnstr ())
    let rec awakeCnstr =
      function
      | NONE -> ()
      | SOME (ref (Solved)) -> awakeCnstr (Unify.nextCnstr ())
      | SOME (ref (Eqn (G, U1, U2)) as cnstr) ->
          (Unify.solveConstraint cnstr; match1 (G, (U1, id), (U2, id)))
      | SOME (ref (FgnCnstr csfc)) ->
          if FgnCnstrStd.Awake.apply csfc ()
          then ()
          else raise (Match "Foreign constraint violated")
    let rec matchW (G, Us1, Us2) =
      Unify.resetAwakenCnstrs (); match1W (G, Us1, Us2)
    let rec match__ (G, Us1, Us2) =
      Unify.resetAwakenCnstrs (); match1 (G, Us1, Us2)
    (* weakenSub (G1, s, ss) = w'

       Invariant:
       If    G |- s : G1        s patsub *)
    (* ss strsub *)
    (* w' weaksub *)
    (* no other cases, ss is strsub *)
    (* prune (G, (U, s), ss, rOccur) = U[s][ss]

       !!! looks wrong to me -kw
       G |- U : V    G' |- s : G  (G' |- U[s] : V[s])
       G'' |- ss : G'

       !!! i would say
       G |- s : G'   G' |- U : V  (G  |- U[s] : V[s])
       G'' |- ss : G

       Effect: prunes EVars in U[s] according to ss
               raises Match if U[s][ss] does not exist, or rOccur occurs in U[s]
    *)
    (* = id *)
    (* let
                     val wi = Whnf.invert w
                      val V' = EClo (V, wi) *)
    (* val GY = Whnf.strengthen (wi, GX) *)
    (* shortcut on GY possible by invariant on GX and V[s]? -fp *)
    (* could optimize by checking for identity subst *)
    (* s not patsub *)
    (* -bp not sure what to do in the non-pattern case *)
    (* val GY = Whnf.strengthen (ss, G) *)
    (* shortcuts possible by invariants on G? *)
    (* prune or invert??? *)
    (* val V' = EClo (V, comp (s, ss)) *)
    (* prune or invert??? *)
    (* this case should never happen! *)
    (* other cases impossible since (U,s1) whnf *)
    (* Added for the meta level -cs Tue Aug 17 17:09:27 2004 *)
    (* blockSub (B, ss) should always be defined *)
    (* Fri Dec 28 10:03:12 2001 -fp !!! *)
    (* claim: LVar does not need to be pruned since . |- t : Gsome *)
    (* so we perform only the occurs-check here as for FVars *)
    (* Sat Dec  8 13:39:41 2001 -fp !!! *)
    (* this is not true any more, Sun Dec  1 11:28:47 2002 -cs  *)
    (* Changed from Null to G Sat Dec  7 21:58:00 2002 -fp *)
    (* V does not to be pruned, since . |- V : type and s' = ^k *)
    (* perform occurs-check for r only *)
    (* why G here? -fp !!! *)
    (* pruneSub never allows pruning OUTDATED *)
    (* in the presence of block variables, this invariant
       doesn't hold any more, because substitutions do not
       only occur in EVars any more but also in LVars!
       and there pruning is allowed!   Tue May 29 21:50:17 EDT 2001 -cs *)
    (* must be defined *)
    (* below my raise Match *)
    (* pruneSub (G, Dot (Undef, s), ss, rOccur) is impossible *)
    (* By invariant, all EVars X[s] are such that s is defined everywhere *)
    (* Pruning establishes and maintains this invariant *)
    (* matchExpW (G, (U1, s1), (U2, s2)) = ()

       Invariant:
       If   G |- s1 : G1   G1 |- U1 : V1    (U1,s1) in whnf
       and  G |- s2 : G2   G2 |- U2 : V2    (U2,s2) in whnf
       and  G |- V1 [s1] = V2 [s2]  : L    (for some level L)
        ***** or V1 = V2 = kind  (needed to check type definitions)
        ***** added by kw Apr 5 2002
       and  s1, U1, s2, U2 do not contain any blockvariable indices Bidx
       then if   there is an instantiation I :
                 s.t. G |- U1 [s1] <I> == U2 [s2] <I>
            then instantiation is applied as effect, () returned
            else exception Match is raised
       Other effects: EVars may be lowered
                      constraints may be added for non-patterns
    *)
    (* L1 = L2 = type, by invariant *)
    (* matchUni (L1, L2) - removed Mon Aug 24 12:18:24 1998 -fp *)
    (* s1 = s2 = id by whnf *)
    (* order of calls critical to establish matchSpine invariant *)
    (* because of strict *)
    (*  matchExpW (G, Whnf.expandDef (Us1), Whnf.expandDef (Us2)) *)
    (* four new cases for defined constants *)
    (* conservative *)
    (* conservative *)
    (* due to strictness! *)
    (* due to strictness! *)
    (* next two cases for def/fgn, fgn/def *)
    (* we require unique string representation of external constants *)
    (* D1[s1] = D2[s2]  by invariant *)
    (* ETA: can't occur if eta expanded *)
    (* for rhs:  (U2[s2])[^] 1 = U2 [s2 o ^] 1 = U2 [^ o (1. s2 o ^)] 1
                        = (U2 [^] 1) [1.s2 o ^] *)
    (* Cannot occur if expressions are eta expanded *)
    (* same reasoning holds as above *)
    (*      | matchExpW (G, Us1 as (U1 as EVar(r1, G1, V1, cnstrs1), s1),
                   Us2 as (U2 as EVar(r2, G2, V2, cnstrs2), s2)) =
           postpone, if s1 or s2 are not patsub *)
    (* compute ss' directly? *)
    (* without the next optimization, bugs/hangs/sources.cfg
                     would gets into an apparent infinite loop
                     Fri Sep  5 20:23:27 2003 -fp
                  *)
    (* added for definitions Mon Sep  1 19:53:13 2003 -fp *)
    (* X[s] = X[s] *)
    (* invertExp ((V1, id), s', ref NONE) *)
    (* Unify.instantiateEVar (r1, EClo (U2, comp(s2, ss1)), !cnstrs1) *)
    (* invertExpW (Us2, s1, ref NONE) *)
    (* instantiateEVar (r2, EClo (U1, comp(s1, ss2)), !cnstr2) *)
    (* invertExpW (Us1, s2, ref NONE) *)
    (* instantiateEVar (r, EClo (U2, comp(s2, ss)), !cnstrs) *)
    (* invertExpW (Us2, s, r) *)
    (*      | matchExpW (G, Us1 as (U1,s1), Us2 as (EVar (r, GX, V, cnstrs), s)) =
        if Whnf.isPatSub(s) then
          let
            val ss = Whnf.invert s
            val U1' = pruneExp (G, Us1, ss, r)
          in
             instantiateEVar (r, EClo (U1, comp(s1, ss)), !cnstrs) *)
    (* invertExpW (Us1, s, r) *)
    (* covers most remaining cases *)
    (* the cases for EClo or Redex should not occur because of whnf invariant *)
    (* matchExp (G, (U1, s1), (U2, s2)) = ()
       as in matchExpW, except that arguments may not be in whnf
    *)
    (*  matchExpW (G, Whnf.expandDef (Us1), Whnf.expandDef (Us2)) *)
    (* conservative *)
    (* matchSpine (G, (S1, s1), (S2, s2)) = ()

       Invariant:
       If   G |- s1 : G1   G1 |- S1 : V1 > W1
       and  G |- s2 : G2   G2 |- S2 : V2 > W2
       and  G |- V1 [s1] = V2 [s2]  : L    (for some level L)
       and  G |- W1 [s1] = W2 [s2]
       then if   there is an instantiation I :
                 s.t. G |- S1 [s1] <I> == S2 [s2] <I>
            then instantiation is applied as effect, () returned
            else exception Match is raised
       Other effects: EVars may be lowered,
                      constraints may be added for non-patterns
    *)
    (* Nil/App or App/Nil cannot occur by typing invariants *)
    (* matchSub (G, s1, s2) = ()

       Invariant:
       If   G |- s1 : G'
       and  G |- s2 : G'
       then matchSub (G, s1, s2) terminates with ()
            iff there exists an instantiation I, such that
            s1 [I] = s2 [I]

       Remark:  matchSub is used only to match the instantiation of SOME variables
    *)
    (* conjecture: G == Null at all times *)
    (* Thu Dec  6 21:01:09 2001 -fp *)
    (* by invariant *)
    (*         | (Undef, Undef) =>
           | _ => false *)
    (* not possible because of invariant? -cs *)
    (* substitutions s1 and s2 were redundant here --- removed *)
    (* Sat Dec  8 11:47:12 2001 -fp !!! *)
    (* Sat Dec  7 22:04:31 2002 -fp *)
    (* invariant? always k1 = k2? *)
    (* prune t2? Sat Dec  7 22:09:53 2002 *)
    (*
              if k1 < k2 then instantiateLVar (r1, LVar(r2, Shift(k2-k1), (l2, t2)))
                else Unify.instantiateLVar (r2, LVar(r1, Shift (k1-k2), (l1, t1)))
              *)
    (* hack! *)
    (* 0 = k2-k1 *)
    (* -- ABP *)
    (* -- ABP *)
    (*      | matchBlockW (G, LVar (r1, Shift(k1), (l1, t1)), Bidx i2) =
            (r1 := SOME (Bidx (i2 -k1)) ; ())  -- ABP *)
    (* -- ABP *)
    (* How can the next case arise? *)
    (* Sat Dec  8 11:49:16 2001 -fp !!! *)
    (*
      | matchBlock (LVar (r1, _, _), B as Bidx _) = instantiate (r1, B)
      | matchBlock (B as Bidx _, LVar (r2, _, _)) =

      This is still difficult --- B must make sense in the context of the LVar
      Shall we use the inverse of a pattern substitution? Or postpone as
      a constraint if pattern substitution does not exist?
      Sun Dec  1 11:33:13 2002 -cs

*)
    let matchW = matchW
    let match__ = match__
    let matchSub = matchSub
    let matchBlock = matchBlock
    let rec instance (G, Us1, Us2) =
      try match__ (G, Us1, Us2); true__ with | Match msg -> false__
    let rec instance' (G, Us1, Us2) =
      try match__ (G, Us1, Us2); NONE with | Match msg -> SOME msg
  end ;;
