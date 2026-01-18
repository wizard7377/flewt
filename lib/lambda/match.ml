
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
    (* instance (__g, __Us,__Us') will instantiate EVars as an effect 
     checks if __Us' is an instance of __Us *)
    val instance : (IntSyn.dctx * IntSyn.eclo * IntSyn.eclo) -> bool
    (* instance' (__g, __Us,__Us') is like instance, but returns None for
     success and Some(msg) for failure *)
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
      | (__g, Shift n, ss) ->
          if (<) n ctxLength __g
          then weakenSub (__g, (Dot ((Idx (n + 1)), (Shift (n + 1)))), ss)
          else id
      | (__g, Dot (Idx n, s'), ss) ->
          (match bvarSub (n, ss) with
           | Undef -> comp ((weakenSub (__g, s', ss)), shift)
           | Idx _ -> dot1 (weakenSub (__g, s', ss)))
      | (__g, Dot (Undef, s'), ss) -> comp ((weakenSub (__g, s', ss)), shift)
    let rec pruneExp (__g, __Us, ss, rOccur) =
      pruneExpW (__g, (Whnf.whnf __Us), ss, rOccur)
    let rec pruneExpW =
      function
      | (__g, ((Uni _ as __u), s), _, _) -> __u
      | (__g, (Pi ((__d, P), __v), s), ss, rOccur) ->
          Pi
            (((pruneDec (__g, (__d, s), ss, rOccur)), P),
              (pruneExp
                 ((Decl (__g, (decSub (__d, s)))), (__v, (dot1 s)), (dot1 ss),
                   rOccur)))
      | (__g, (Lam (__d, __v), s), ss, rOccur) ->
          Lam
            ((pruneDec (__g, (__d, s), ss, rOccur)),
              (pruneExp
                 ((Decl (__g, (decSub (__d, s)))), (__v, (dot1 s)), (dot1 ss),
                   rOccur)))
      | (__g, (Root (H, S), s), ss, rOccur) ->
          Root
            ((pruneHead (__g, H, ss, rOccur)),
              (pruneSpine (__g, (S, s), ss, rOccur)))
      | (__g, ((EVar (r, GX, __v, cnstrs) as x), s), ss, rOccur) ->
          if rOccur = r
          then raise (Match "Variable occurrence")
          else
            if Whnf.isPatSub s
            then
              (let w = weakenSub (__g, s, ss) in
               if Whnf.isId w
               then EClo (x, (comp (s, ss)))
               else
                 raise
                   (Match
                      "Invertible Substitution does not necessarily exist\n"))
            else
              (try EClo (x, (Unify.invertSub (__g, s, ss, rOccur)))
               with
               | NotInvertible ->
                   let GY = pruneCtx (ss, __g, rOccur) in
                   let __v' = pruneExp (__g, (__v, s), ss, rOccur) in
                   let y = newEVar (GY, __v') in
                   let _ =
                     Unify.addConstraint
                       (cnstrs,
                         (ref
                            (Eqn
                               (__g, (EClo (x, s)),
                                 (EClo (y, (Whnf.invert ss))))))) in
                   y)
      | (__g, (FgnExp csfe, s), ss, rOccur) ->
          FgnExpStd.Map.apply csfe
            (function | __u -> pruneExp (__g, (__u, s), ss, rOccur))
      | (__g, ((AVar _ as x), s), ss, rOccur) -> raise (Match "Left-over AVar")
    let rec pruneDec =
      function
      | (__g, (Dec (name, __v), s), ss, rOccur) ->
          Dec (name, (pruneExp (__g, (__v, s), ss, rOccur)))
      | (__g, (NDec x, _), _, _) -> NDec x
    let rec pruneSpine =
      function
      | (__g, (Nil, s), ss, rOccur) -> Nil
      | (__g, (App (__u, S), s), ss, rOccur) ->
          App
            ((pruneExp (__g, (__u, s), ss, rOccur)),
              (pruneSpine (__g, (S, s), ss, rOccur)))
      | (__g, (SClo (S, s'), s), ss, rOccur) ->
          pruneSpine (__g, (S, (comp (s', s))), ss, rOccur)
    let rec pruneHead =
      function
      | (__g, BVar k, ss, rOccur) ->
          (match bvarSub (k, ss) with
           | Undef -> raise (Match "Parameter dependency")
           | Idx k' -> BVar k')
      | (__g, (Const _ as H), ss, rOccur) -> H
      | (__g, Proj ((Bidx k as B), i), ss, rOccur) ->
          (match blockSub (B, ss) with | Bidx k' -> Proj ((Bidx k'), i))
      | (__g, (Proj (LVar (r, sk, (l, t)), i) as H), ss, rOccur) ->
          (pruneSub (__g, t, id, rOccur); H)
      | (__g, (Skonst _ as H), ss, rOccur) -> H
      | (__g, (Def _ as H), ss, rOccur) -> H
      | (__g, FVar (x, __v, s'), ss, rOccur) ->
          (pruneExp (__g, (__v, id), id, rOccur); FVar (x, __v, (comp (s', ss))))
      | (__g, (FgnConst _ as H), ss, rOccur) -> H
    let rec pruneSub =
      function
      | (__g, (Shift n as s), ss, rOccur) ->
          if (<) n ctxLength __g
          then
            pruneSub (__g, (Dot ((Idx (n + 1)), (Shift (n + 1)))), ss, rOccur)
          else comp (s, ss)
      | (__g, Dot (Idx n, s'), ss, rOccur) ->
          (match bvarSub (n, ss) with
           | Undef -> raise (Match "Not prunable")
           | Ft -> Dot (Ft, (pruneSub (__g, s', ss, rOccur))))
      | (__g, Dot (Exp (__u), s'), ss, rOccur) ->
          Dot
            ((Exp (pruneExp (__g, (__u, id), ss, rOccur))),
              (pruneSub (__g, s', ss, rOccur)))
    let rec pruneCtx =
      function
      | (Shift n, Null, rOccur) -> Null
      | (Dot (Idx k, t), Decl (__g, __d), rOccur) ->
          let t' = comp (t, invShift) in
          let __d' = pruneDec (__g, (__d, id), t', rOccur) in
          Decl ((pruneCtx (t', __g, rOccur)), __d')
      | (Dot (Undef, t), Decl (__g, d), rOccur) -> pruneCtx (t, __g, rOccur)
      | (Shift n, __g, rOccur) ->
          pruneCtx ((Dot ((Idx (n + 1)), (Shift (n + 1)))), __g, rOccur)
    let rec matchExpW =
      function
      | (__g, ((FgnExp csfe1, _) as us1), us2) ->
          (match FgnExpStd.UnifyWith.apply csfe1 (__g, (EClo us2)) with
           | Succeed residualL ->
               let rec execResidual =
                 function
                 | Assign (__g, EVar (r, _, _, cnstrs), W, ss) ->
                     let W' = pruneExp (__g, (W, id), ss, r) in
                     Unify.instantiateEVar (r, W', (!cnstrs))
                 | Delay (__u, cnstr) -> delayExp ((__u, id), cnstr) in
               List.app execResidual residualL
           | Fail -> raise (Match "Foreign Expression Mismatch"))
      | (__g, us1, ((FgnExp csfe2, _) as us2)) ->
          (match FgnExpStd.UnifyWith.apply csfe2 (__g, (EClo us1)) with
           | Succeed opL ->
               let rec execOp =
                 function
                 | Assign (__g, EVar (r, _, _, cnstrs), W, ss) ->
                     let W' = pruneExp (__g, (W, id), ss, r) in
                     Unify.instantiateEVar (r, W', (!cnstrs))
                 | Delay (__u, cnstr) -> delayExp ((__u, id), cnstr) in
               List.app execOp opL
           | Fail -> raise (Match "Foreign Expression Mismatch"))
      | (__g, (Uni (L1), _), (Uni (L2), _)) -> ()
      | (__g, ((Root (H1, S1), s1) as us1), ((Root (H2, S2), s2) as us2)) ->
          (match (H1, H2) with
           | (BVar k1, BVar k2) ->
               if k1 = k2
               then matchSpine (__g, (S1, s1), (S2, s2))
               else raise (Match "Bound variable clash")
           | (Const c1, Const c2) ->
               if c1 = c2
               then matchSpine (__g, (S1, s1), (S2, s2))
               else raise (Match "Constant clash")
           | (Proj (b1, i1), Proj (b2, i2)) ->
               if i1 = i2
               then
                 (matchBlock (__g, b1, b2); matchSpine (__g, (S1, s1), (S2, s2)))
               else raise (Match "Global parameter clash")
           | (Skonst c1, Skonst c2) ->
               if c1 = c2
               then matchSpine (__g, (S1, s1), (S2, s2))
               else raise (Match "Skolem constant clash")
           | (FVar (n1, _, _), FVar (n2, _, _)) ->
               if n1 = n2
               then matchSpine (__g, (S1, s1), (S2, s2))
               else raise (Match "Free variable clash")
           | (Def d1, Def d2) ->
               if d1 = d2
               then matchSpine (__g, (S1, s1), (S2, s2))
               else matchDefDefW (__g, us1, us2)
           | (Def d1, Const c2) ->
               (match defAncestor d1 with
                | Anc (_, _, None) ->
                    matchExpW (__g, (Whnf.expandDef us1), us2)
                | Anc (_, _, Some c1) ->
                    if c1 = c2
                    then matchExpW (__g, (Whnf.expandDef us1), us2)
                    else raise (Match "Constant clash"))
           | (Const c1, Def d2) ->
               (match defAncestor d2 with
                | Anc (_, _, None) ->
                    matchExpW (__g, us1, (Whnf.expandDef us2))
                | Anc (_, _, Some c2) ->
                    if c1 = c2
                    then matchExpW (__g, us1, (Whnf.expandDef us2))
                    else raise (Match "Constant clash"))
           | (Def d1, BVar k2) -> raise (Match "Head mismatch")
           | (BVar k1, Def d2) -> raise (Match "Head mismatch")
           | (Def d1, _) -> matchExpW (__g, (Whnf.expandDef us1), us2)
           | (_, Def d2) -> matchExpW (__g, us1, (Whnf.expandDef us2))
           | (FgnConst (cs1, ConDec (n1, _, _, _, _, _)), FgnConst
              (cs2, ConDec (n2, _, _, _, _, _))) ->
               if (cs1 = cs2) && (n1 = n2)
               then ()
               else raise (Match "Foreign Constant clash")
           | (FgnConst (cs1, ConDef (n1, _, _, W1, _, _, _)), FgnConst
              (cs2, ConDef (n2, _, _, __v, W2, _, _))) ->
               if (cs1 = cs2) && (n1 = n2)
               then ()
               else matchExp (__g, (W1, s1), (W2, s2))
           | (FgnConst (_, ConDef (_, _, _, W1, _, _, _)), _) ->
               matchExp (__g, (W1, s1), us2)
           | (_, FgnConst (_, ConDef (_, _, _, W2, _, _, _))) ->
               matchExp (__g, us1, (W2, s2))
           | _ -> raise (Match "Head mismatch"))
      | (__g, (Pi ((D1, _), __U1), s1), (Pi ((D2, _), __U2), s2)) ->
          (matchDec (__g, (D1, s1), (D2, s2));
           matchExp
             ((Decl (__g, (decSub (D1, s1)))), (__U1, (dot1 s1)),
               (__U2, (dot1 s2))))
      | (__g, ((Pi (_, _), _) as us1), ((Root (Def _, _), _) as us2)) ->
          matchExpW (__g, us1, (Whnf.expandDef us2))
      | (__g, ((Root (Def _, _), _) as us1), ((Pi (_, _), _) as us2)) ->
          matchExpW (__g, (Whnf.expandDef us1), us2)
      | (__g, (Lam (D1, __U1), s1), (Lam (D2, __U2), s2)) ->
          matchExp
            ((Decl (__g, (decSub (D1, s1)))), (__U1, (dot1 s1)), (__U2, (dot1 s2)))
      | (__g, (Lam (D1, __U1), s1), (__U2, s2)) ->
          matchExp
            ((Decl (__g, (decSub (D1, s1)))), (__U1, (dot1 s1)),
              ((Redex
                  ((EClo (__U2, shift)), (App ((Root ((BVar 1), Nil)), Nil)))),
                (dot1 s2)))
      | (__g, (__U1, s1), (Lam (D2, __U2), s2)) ->
          matchExp
            ((Decl (__g, (decSub (D2, s2)))),
              ((Redex
                  ((EClo (__U1, shift)), (App ((Root ((BVar 1), Nil)), Nil)))),
                (dot1 s1)), (__U2, (dot1 s2)))
      | (__g, ((EVar (r, GX, __v, cnstrs), s) as us1), ((__U2, s2) as us2)) ->
          if Whnf.isPatSub s
          then
            let ss = Whnf.invert s in
            let __U2' = pruneExp (__g, us2, ss, r) in
            Unify.instantiateEVar (r, __U2', (!cnstrs))
          else
            Unify.addConstraint
              (cnstrs, (ref (Eqn (__g, (EClo us1), (EClo us2)))))
      | (__g, us1, us2) -> raise (Match "Expression clash")
    let rec matchExp (__g, ((E1, s1) as us1), ((E2, s2) as us2)) =
      matchExpW (__g, (Whnf.whnf us1), (Whnf.whnf us2))
    let rec matchDefDefW
      (__g, ((Root (Def d1, S1), s1) as us1), ((Root (Def d2, S2), s2) as us2))
      =
      let Anc (_, h1, c1Opt) = defAncestor d1 in
      let Anc (_, h2, c2Opt) = defAncestor d2 in
      let _ =
        match (c1Opt, c2Opt) with
        | (Some c1, Some c2) ->
            if c1 <> c2
            then raise (Match "Irreconcilable defined constant clash")
            else ()
        | _ -> () in
      match Int.compare (h1, h2) with
      | EQUAL -> matchExpW (__g, (Whnf.expandDef us1), (Whnf.expandDef us2))
      | LESS -> matchExpW (__g, us1, (Whnf.expandDef us2))
      | GREATER -> matchExpW (__g, (Whnf.expandDef us1), us2)
    let rec matchSpine =
      function
      | (__g, (Nil, _), (Nil, _)) -> ()
      | (__g, (SClo (S1, s1'), s1), __Ss) ->
          matchSpine (__g, (S1, (comp (s1', s1))), __Ss)
      | (__g, __Ss, (SClo (S2, s2'), s2)) ->
          matchSpine (__g, __Ss, (S2, (comp (s2', s2))))
      | (__g, (App (__U1, S1), s1), (App (__U2, S2), s2)) ->
          (matchExp (__g, (__U1, s1), (__U2, s2));
           matchSpine (__g, (S1, s1), (S2, s2)))
    let rec matchDec (__g, (Dec (_, V1), s1), (Dec (_, V2), s2)) =
      matchExp (__g, (V1, s1), (V2, s2))
    let rec matchSub =
      function
      | (__g, Shift n1, Shift n2) -> ()
      | (__g, Shift n, (Dot _ as s2)) ->
          matchSub (__g, (Dot ((Idx (n + 1)), (Shift (n + 1)))), s2)
      | (__g, (Dot _ as s1), Shift m) ->
          matchSub (__g, s1, (Dot ((Idx (m + 1)), (Shift (m + 1)))))
      | (__g, Dot (Ft1, s1), Dot (Ft2, s2)) ->
          ((match (Ft1, Ft2) with
            | (Idx n1, Idx n2) ->
                if n1 <> n2
                then raise (Error "Some variables mismatch")
                else ()
            | (Exp (__U1), Exp (__U2)) -> matchExp (__g, (__U1, id), (__U2, id))
            | (Exp (__U1), Idx n2) ->
                matchExp (__g, (__U1, id), ((Root ((BVar n2), Nil)), id))
            | (Idx n1, Exp (__U2)) ->
                matchExp (__g, ((Root ((BVar n1), Nil)), id), (__U2, id)));
           matchSub (__g, s1, s2))
    let rec matchBlock =
      function
      | (__g, LVar (ref (Some (B1)), s, _), B2) ->
          matchBlock (__g, (blockSub (B1, s)), B2)
      | (__g, B1, LVar (ref (Some (B2)), s, _)) ->
          matchBlock (__g, B1, (blockSub (B2, s)))
      | (__g, B1, B2) -> matchBlockW (__g, B1, B2)
    let rec matchBlockW =
      function
      | (__g, LVar (r1, Shift k1, (l1, t1)), LVar (r2, Shift k2, (l2, t2))) ->
          if l1 <> l2
          then raise (Match "Label clash")
          else
            if r1 = r2
            then ()
            else
              (matchSub (__g, t1, t2);
               if k1 <> k2 then raise Bind else ();
               (let ss = Whnf.invert (Shift k1) in
                let t2' = pruneSub (__g, t2, ss, (ref None)) in
                Unify.instantiateLVar (r1, (LVar (r2, (Shift 0), (l2, t2'))))))
      | (__g, LVar (r1, s1, (l1, t1)), B2) ->
          ((:=) r1 Some (blockSub (B2, (Whnf.invert s1))); ())
      | (__g, B1, LVar (r2, s2, (l2, t2))) ->
          ((:=) r2 Some (blockSub (B1, (Whnf.invert s2))); ())
      | (__g, Bidx n1, Bidx n2) ->
          if n1 <> n2 then raise (Match "Block index clash") else ()
    let rec match1W (__g, us1, us2) =
      matchExpW (__g, us1, us2); awakeCnstr (Unify.nextCnstr ())
    let rec match1 (__g, us1, us2) =
      matchExp (__g, us1, us2); awakeCnstr (Unify.nextCnstr ())
    let rec awakeCnstr =
      function
      | None -> ()
      | Some (ref (Solved)) -> awakeCnstr (Unify.nextCnstr ())
      | Some (ref (Eqn (__g, __U1, __U2)) as cnstr) ->
          (Unify.solveConstraint cnstr; match1 (__g, (__U1, id), (__U2, id)))
      | Some (ref (FgnCnstr csfc)) ->
          if FgnCnstrStd.Awake.apply csfc ()
          then ()
          else raise (Match "Foreign constraint violated")
    let rec matchW (__g, us1, us2) =
      Unify.resetAwakenCnstrs (); match1W (__g, us1, us2)
    let rec match__ (__g, us1, us2) =
      Unify.resetAwakenCnstrs (); match1 (__g, us1, us2)
    (* weakenSub (G1, s, ss) = w'

       Invariant:
       If    __g |- s : G1        s patsub *)
    (* ss strsub *)
    (* w' weaksub *)
    (* no other cases, ss is strsub *)
    (* prune (__g, (__u, s), ss, rOccur) = __u[s][ss]

       !!! looks wrong to me -kw
       __g |- __u : __v    __g' |- s : __g  (__g' |- __u[s] : __v[s])
       __g'' |- ss : __g'

       !!! i would say
       __g |- s : __g'   __g' |- __u : __v  (__g  |- __u[s] : __v[s])
       __g'' |- ss : __g

       Effect: prunes EVars in __u[s] according to ss
               raises Match if __u[s][ss] does not exist, or rOccur occurs in __u[s]
    *)
    (* = id *)
    (* let
                     val wi = Whnf.invert w
                      val __v' = EClo (__v, wi) *)
    (* val GY = Whnf.strengthen (wi, GX) *)
    (* shortcut on GY possible by invariant on GX and __v[s]? -fp *)
    (* could optimize by checking for identity subst *)
    (* s not patsub *)
    (* -bp not sure what to do in the non-pattern case *)
    (* val GY = Whnf.strengthen (ss, __g) *)
    (* shortcuts possible by invariants on __g? *)
    (* prune or invert??? *)
    (* val __v' = EClo (__v, comp (s, ss)) *)
    (* prune or invert??? *)
    (* this case should never happen! *)
    (* other cases impossible since (__u,s1) whnf *)
    (* Added for the meta level -cs Tue Aug 17 17:09:27 2004 *)
    (* blockSub (B, ss) should always be defined *)
    (* Fri Dec 28 10:03:12 2001 -fp !!! *)
    (* claim: LVar does not need to be pruned since . |- t : Gsome *)
    (* so we perform only the occurs-check here as for FVars *)
    (* Sat Dec  8 13:39:41 2001 -fp !!! *)
    (* this is not true any more, Sun Dec  1 11:28:47 2002 -cs  *)
    (* Changed from Null to __g Sat Dec  7 21:58:00 2002 -fp *)
    (* __v does not to be pruned, since . |- __v : type and s' = ^k *)
    (* perform occurs-check for r only *)
    (* why __g here? -fp !!! *)
    (* pruneSub never allows pruning OUTDATED *)
    (* in the presence of block variables, this invariant
       doesn't hold any more, because substitutions do not
       only occur in EVars any more but also in LVars!
       and there pruning is allowed!   Tue May 29 21:50:17 EDT 2001 -cs *)
    (* must be defined *)
    (* below my raise Match *)
    (* pruneSub (__g, Dot (Undef, s), ss, rOccur) is impossible *)
    (* By invariant, all EVars x[s] are such that s is defined everywhere *)
    (* Pruning establishes and maintains this invariant *)
    (* matchExpW (__g, (__U1, s1), (__U2, s2)) = ()

       Invariant:
       If   __g |- s1 : G1   G1 |- __U1 : V1    (__U1,s1) in whnf
       and  __g |- s2 : G2   G2 |- __U2 : V2    (__U2,s2) in whnf
       and  __g |- V1 [s1] = V2 [s2]  : __l    (for some level __l)
        ***** or V1 = V2 = kind  (needed to check type definitions)
        ***** added by kw Apr 5 2002
       and  s1, __U1, s2, __U2 do not contain any blockvariable indices Bidx
       then if   there is an instantiation I :
                 s.t. __g |- __U1 [s1] <I> == __U2 [s2] <I>
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
    (*  matchExpW (__g, Whnf.expandDef (us1), Whnf.expandDef (us2)) *)
    (* four new cases for defined constants *)
    (* conservative *)
    (* conservative *)
    (* due to strictness! *)
    (* due to strictness! *)
    (* next two cases for def/fgn, fgn/def *)
    (* we require unique string representation of external constants *)
    (* D1[s1] = D2[s2]  by invariant *)
    (* ETA: can't occur if eta expanded *)
    (* for rhs:  (__U2[s2])[^] 1 = __U2 [s2 o ^] 1 = __U2 [^ o (1. s2 o ^)] 1
                        = (__U2 [^] 1) [1.s2 o ^] *)
    (* Cannot occur if expressions are eta expanded *)
    (* same reasoning holds as above *)
    (*      | matchExpW (__g, us1 as (__U1 as EVar(r1, G1, V1, cnstrs1), s1),
                   us2 as (__U2 as EVar(r2, G2, V2, cnstrs2), s2)) =
           postpone, if s1 or s2 are not patsub *)
    (* compute ss' directly? *)
    (* without the next optimization, bugs/hangs/sources.cfg
                     would gets into an apparent infinite loop
                     Fri Sep  5 20:23:27 2003 -fp
                  *)
    (* added for definitions Mon Sep  1 19:53:13 2003 -fp *)
    (* x[s] = x[s] *)
    (* invertExp ((V1, id), s', ref None) *)
    (* Unify.instantiateEVar (r1, EClo (__U2, comp(s2, ss1)), !cnstrs1) *)
    (* invertExpW (us2, s1, ref None) *)
    (* instantiateEVar (r2, EClo (__U1, comp(s1, ss2)), !cnstr2) *)
    (* invertExpW (us1, s2, ref None) *)
    (* instantiateEVar (r, EClo (__U2, comp(s2, ss)), !cnstrs) *)
    (* invertExpW (us2, s, r) *)
    (*      | matchExpW (__g, us1 as (__U1,s1), us2 as (EVar (r, GX, __v, cnstrs), s)) =
        if Whnf.isPatSub(s) then
          let
            val ss = Whnf.invert s
            val __U1' = pruneExp (__g, us1, ss, r)
          in
             instantiateEVar (r, EClo (__U1, comp(s1, ss)), !cnstrs) *)
    (* invertExpW (us1, s, r) *)
    (* covers most remaining cases *)
    (* the cases for EClo or Redex should not occur because of whnf invariant *)
    (* matchExp (__g, (__U1, s1), (__U2, s2)) = ()
       as in matchExpW, except that arguments may not be in whnf
    *)
    (*  matchExpW (__g, Whnf.expandDef (us1), Whnf.expandDef (us2)) *)
    (* conservative *)
    (* matchSpine (__g, (S1, s1), (S2, s2)) = ()

       Invariant:
       If   __g |- s1 : G1   G1 |- S1 : V1 > W1
       and  __g |- s2 : G2   G2 |- S2 : V2 > W2
       and  __g |- V1 [s1] = V2 [s2]  : __l    (for some level __l)
       and  __g |- W1 [s1] = W2 [s2]
       then if   there is an instantiation I :
                 s.t. __g |- S1 [s1] <I> == S2 [s2] <I>
            then instantiation is applied as effect, () returned
            else exception Match is raised
       Other effects: EVars may be lowered,
                      constraints may be added for non-patterns
    *)
    (* Nil/App or App/Nil cannot occur by typing invariants *)
    (* matchSub (__g, s1, s2) = ()

       Invariant:
       If   __g |- s1 : __g'
       and  __g |- s2 : __g'
       then matchSub (__g, s1, s2) terminates with ()
            iff there exists an instantiation I, such that
            s1 [I] = s2 [I]

       Remark:  matchSub is used only to match the instantiation of Some variables
    *)
    (* conjecture: __g == Null at all times *)
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
    (*      | matchBlockW (__g, LVar (r1, Shift(k1), (l1, t1)), Bidx i2) =
            (r1 := Some (Bidx (i2 -k1)) ; ())  -- ABP *)
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
    let rec instance (__g, us1, us2) =
      try match__ (__g, us1, us2); true__ with | Match msg -> false__
    let rec instance' (__g, us1, us2) =
      try match__ (__g, us1, us2); None with | Match msg -> Some msg
  end ;;
