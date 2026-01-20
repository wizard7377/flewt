
module type MATCH  =
  sig
    exception Match of string 
    val match__ : IntSyn.dctx -> IntSyn.eclo -> IntSyn.eclo -> unit
    val matchW : IntSyn.dctx -> IntSyn.eclo -> IntSyn.eclo -> unit
    val matchBlock : IntSyn.dctx -> IntSyn.__Block -> IntSyn.__Block -> unit
    val matchSub : IntSyn.dctx -> IntSyn.__Sub -> IntSyn.__Sub -> unit
    val instance : IntSyn.dctx -> IntSyn.eclo -> IntSyn.eclo -> bool
    val instance' :
      IntSyn.dctx -> IntSyn.eclo -> IntSyn.eclo -> string option
  end;;




module Match(Match:sig
                     module Whnf : WHNF
                     module Unify : UNIFY
                     module Trail : TRAIL
                   end) : MATCH =
  struct
    exception Match of string 
    exception NotInvertible 
    open IntSyn
    let delayExp = Unify.delay
    let rec weakenSub __0__ __1__ __2__ =
      match (__0__, __1__, __2__) with
      | (__G, Shift n, ss) ->
          if (<) n ctxLength __G
          then weakenSub (__G, (Dot ((Idx (n + 1)), (Shift (n + 1)))), ss)
          else id
      | (__G, Dot (Idx n, s'), ss) ->
          (match bvarSub (n, ss) with
           | Undef -> comp ((weakenSub (__G, s', ss)), shift)
           | Idx _ -> dot1 (weakenSub (__G, s', ss)))
      | (__G, Dot (Undef, s'), ss) -> comp ((weakenSub (__G, s', ss)), shift)
      (* no other cases, ss is strsub *)
    let rec pruneExp (__G) (__Us) ss rOccur =
      pruneExpW (__G, (Whnf.whnf __Us), ss, rOccur)
    let rec pruneExpW __3__ __4__ __5__ __6__ =
      match (__3__, __4__, __5__, __6__) with
      | (__G, ((Uni _ as U), s), _, _) -> __U
      | (__G, (Pi ((__D, __P), __V), s), ss, rOccur) ->
          Pi
            (((pruneDec (__G, (__D, s), ss, rOccur)), __P),
              (pruneExp
                 ((Decl (__G, (decSub (__D, s)))), (__V, (dot1 s)),
                   (dot1 ss), rOccur)))
      | (__G, (Lam (__D, __V), s), ss, rOccur) ->
          Lam
            ((pruneDec (__G, (__D, s), ss, rOccur)),
              (pruneExp
                 ((Decl (__G, (decSub (__D, s)))), (__V, (dot1 s)),
                   (dot1 ss), rOccur)))
      | (__G, (((Root (__H, __S), s))(* = id *)), ss,
         rOccur) ->
          Root
            ((pruneHead (__G, __H, ss, rOccur)),
              (pruneSpine (__G, (__S, s), ss, rOccur)))
      | (__G, ((EVar (r, GX, __V, cnstrs) as X), s), ss, rOccur) ->
          if rOccur = r
          then raise (Match "Variable occurrence")
          else
            ((if Whnf.isPatSub s
              then
                (let w = weakenSub (__G, s, ss) in
                 ((if Whnf.isId w
                   then EClo (__X, (comp (s, ss)))
                   else
                     raise
                       (Match
                          "Invertible Substitution does not necessarily exist\n"))
                   (* let
                     val wi = Whnf.invert w
                      val V' = EClo (V, wi) *)
                   (* val GY = Whnf.strengthen (wi, GX) *)
                   (* shortcut on GY possible by invariant on GX and V[s]? -fp *)
                   (* could optimize by checking for identity subst *)))
              else
                (try EClo (__X, (Unify.invertSub (__G, s, ss, rOccur)))
                 with
                 | NotInvertible ->
                     let GY = pruneCtx (ss, __G, rOccur) in
                     let __V' = pruneExp (__G, (__V, s), ss, rOccur) in
                     let __Y = newEVar (GY, __V') in
                     let _ =
                       Unify.addConstraint
                         (cnstrs,
                           (ref
                              (Eqn
                                 (__G, (EClo (__X, s)),
                                   (EClo (__Y, (Whnf.invert ss))))))) in
                     ((__Y)
                       (* val GY = Whnf.strengthen (ss, G) *)(* shortcuts possible by invariants on G? *)
                       (* prune or invert??? *)(* val V' = EClo (V, comp (s, ss)) *)
                       (* prune or invert??? *))))
            (* s not patsub *)(* -bp not sure what to do in the non-pattern case *))
      | (__G, (FgnExp csfe, s), ss, rOccur) ->
          FgnExpStd.Map.apply csfe
            (fun (__U) -> pruneExp (__G, (__U, s), ss, rOccur))
      | (__G, ((AVar _ as X), s), ss, rOccur) ->
          raise (Match "Left-over AVar")(* this case should never happen! *)
    let rec pruneDec __7__ __8__ __9__ __10__ =
      match (__7__, __8__, __9__, __10__) with
      | (__G, (Dec (name, __V), s), ss, rOccur) ->
          Dec (name, (pruneExp (__G, (__V, s), ss, rOccur)))
      | (__G, (NDec x, _), _, _) -> NDec x
    let rec pruneSpine __11__ __12__ __13__ __14__ =
      match (__11__, __12__, __13__, __14__) with
      | (__G, (Nil, s), ss, rOccur) -> Nil
      | (__G, (App (__U, __S), s), ss, rOccur) ->
          App
            ((pruneExp (__G, (__U, s), ss, rOccur)),
              (pruneSpine (__G, (__S, s), ss, rOccur)))
      | (__G, (SClo (__S, s'), s), ss, rOccur) ->
          pruneSpine (__G, (__S, (comp (s', s))), ss, rOccur)
    let rec pruneHead __15__ __16__ __17__ __18__ =
      match (__15__, __16__, __17__, __18__) with
      | (__G, BVar k, ss, rOccur) ->
          (match bvarSub (k, ss) with
           | Undef -> raise (Match "Parameter dependency")
           | Idx k' -> BVar k')
      | (__G, (Const _ as H), ss, rOccur) -> __H
      | (__G, Proj ((Bidx k as B), i), ss, rOccur) ->
          (match blockSub (__B, ss) with | Bidx k' -> Proj ((Bidx k'), i))
      | (__G, (Proj (LVar (r, sk, (l, t)), i) as H), ss, rOccur) ->
          (pruneSub (__G, t, id, rOccur); __H)
      | (__G, (Skonst _ as H), ss, rOccur) -> __H
      | (__G, (Def _ as H), ss, rOccur) -> __H
      | (__G, FVar (x, __V, s'), ss, rOccur) ->
          (((pruneExp (__G, (__V, id), id, rOccur);
             FVar (x, __V, (comp (s', ss)))))
          (* why G here? -fp !!! *))
      | (__G, (FgnConst _ as H), ss, rOccur) -> __H(* perform occurs-check for r only *)
      (* V does not to be pruned, since . |- V : type and s' = ^k *)
      (* Changed from Null to G Sat Dec  7 21:58:00 2002 -fp *)(* this is not true any more, Sun Dec  1 11:28:47 2002 -cs  *)
      (* Sat Dec  8 13:39:41 2001 -fp !!! *)(* so we perform only the occurs-check here as for FVars *)
      (* claim: LVar does not need to be pruned since . |- t : Gsome *)
      (* Fri Dec 28 10:03:12 2001 -fp !!! *)(* blockSub (B, ss) should always be defined *)
    let rec pruneSub __19__ __20__ __21__ __22__ =
      match (__19__, __20__, __21__, __22__) with
      | (__G, (Shift n as s), ss, rOccur) ->
          if (<) n ctxLength __G
          then
            pruneSub
              (__G, (Dot ((Idx (n + 1)), (Shift (n + 1)))), ss, rOccur)
          else comp (s, ss)
      | (__G, Dot (Idx n, s'), ss, rOccur) ->
          (match bvarSub (n, ss) with
           | Undef -> raise (Match "Not prunable")
           | Ft -> Dot (Ft, (pruneSub (__G, s', ss, rOccur))))
      | (__G, Dot (Exp (__U), s'), ss, rOccur) ->
          Dot
            ((Exp (pruneExp (__G, (__U, id), ss, rOccur))),
              (pruneSub (__G, s', ss, rOccur)))(* below my raise Match *)
      (* must be defined *)
    let rec pruneCtx __23__ __24__ __25__ =
      match (__23__, __24__, __25__) with
      | (Shift n, Null, rOccur) -> Null
      | (Dot (Idx k, t), Decl (__G, __D), rOccur) ->
          let t' = comp (t, invShift) in
          let __D' = pruneDec (__G, (__D, id), t', rOccur) in
          Decl ((pruneCtx (t', __G, rOccur)), __D')
      | (Dot (Undef, t), Decl (__G, d), rOccur) -> pruneCtx (t, __G, rOccur)
      | (Shift n, __G, rOccur) ->
          pruneCtx ((Dot ((Idx (n + 1)), (Shift (n + 1)))), __G, rOccur)
    let rec matchExpW __26__ __27__ __28__ =
      match (__26__, __27__, __28__) with
      | (__G, ((FgnExp csfe1, _) as Us1), __Us2) ->
          (match FgnExpStd.UnifyWith.apply csfe1 (__G, (EClo __Us2)) with
           | Succeed residualL ->
               let rec execResidual =
                 function
                 | Assign (__G, EVar (r, _, _, cnstrs), __W, ss) ->
                     let __W' = pruneExp (__G, (__W, id), ss, r) in
                     Unify.instantiateEVar (r, __W', (!cnstrs))
                 | Delay (__U, cnstr) -> delayExp ((__U, id), cnstr) in
               List.app execResidual residualL
           | Fail -> raise (Match "Foreign Expression Mismatch"))
      | (__G, __Us1, ((FgnExp csfe2, _) as Us2)) ->
          (match FgnExpStd.UnifyWith.apply csfe2 (__G, (EClo __Us1)) with
           | Succeed opL ->
               let rec execOp =
                 function
                 | Assign (__G, EVar (r, _, _, cnstrs), __W, ss) ->
                     let __W' = pruneExp (__G, (__W, id), ss, r) in
                     Unify.instantiateEVar (r, __W', (!cnstrs))
                 | Delay (__U, cnstr) -> delayExp ((__U, id), cnstr) in
               List.app execOp opL
           | Fail -> raise (Match "Foreign Expression Mismatch"))
      | (__G, (Uni (__L1), _), (Uni (__L2), _)) -> ()
      | (__G, ((Root (__H1, __S1), s1) as Us1),
         ((Root (__H2, __S2), s2) as Us2)) ->
          (((match (__H1, __H2) with
             | (BVar k1, BVar k2) ->
                 if k1 = k2
                 then matchSpine (__G, (__S1, s1), (__S2, s2))
                 else raise (Match "Bound variable clash")
             | (Const c1, Const c2) ->
                 if c1 = c2
                 then matchSpine (__G, (__S1, s1), (__S2, s2))
                 else raise (Match "Constant clash")
             | (Proj (b1, i1), Proj (b2, i2)) ->
                 if i1 = i2
                 then
                   (matchBlock (__G, b1, b2);
                    matchSpine (__G, (__S1, s1), (__S2, s2)))
                 else raise (Match "Global parameter clash")
             | (Skonst c1, Skonst c2) ->
                 if c1 = c2
                 then matchSpine (__G, (__S1, s1), (__S2, s2))
                 else raise (Match "Skolem constant clash")
             | (FVar (n1, _, _), FVar (n2, _, _)) ->
                 if n1 = n2
                 then matchSpine (__G, (__S1, s1), (__S2, s2))
                 else raise (Match "Free variable clash")
             | (Def d1, Def d2) ->
                 ((if d1 = d2
                   then matchSpine (__G, (__S1, s1), (__S2, s2))
                   else matchDefDefW (__G, __Us1, __Us2))
                 (* because of strict *)(*  matchExpW (G, Whnf.expandDef (Us1), Whnf.expandDef (Us2)) *))
             | (Def d1, Const c2) ->
                 (((match defAncestor d1 with
                    | Anc (_, _, None) ->
                        matchExpW (__G, (Whnf.expandDef __Us1), __Us2)
                    | Anc (_, _, Some c1) ->
                        if c1 = c2
                        then matchExpW (__G, (Whnf.expandDef __Us1), __Us2)
                        else raise (Match "Constant clash")))
                 (* conservative *))
             | (Const c1, Def d2) ->
                 (((match defAncestor d2 with
                    | Anc (_, _, None) ->
                        matchExpW (__G, __Us1, (Whnf.expandDef __Us2))
                    | Anc (_, _, Some c2) ->
                        if c1 = c2
                        then matchExpW (__G, __Us1, (Whnf.expandDef __Us2))
                        else raise (Match "Constant clash")))
                 (* conservative *))
             | (Def d1, BVar k2) -> raise (Match "Head mismatch")
             | (BVar k1, Def d2) -> raise (Match "Head mismatch")
             | (Def d1, _) -> matchExpW (__G, (Whnf.expandDef __Us1), __Us2)
             | (_, Def d2) -> matchExpW (__G, __Us1, (Whnf.expandDef __Us2))
             | (FgnConst (cs1, ConDec (n1, _, _, _, _, _)), FgnConst
                (cs2, ConDec (n2, _, _, _, _, _))) ->
                 if (cs1 = cs2) && (n1 = n2)
                 then ()
                 else raise (Match "Foreign Constant clash")
             | (FgnConst (cs1, ConDef (n1, _, _, __W1, _, _, _)), FgnConst
                (cs2, ConDef (n2, _, _, __V, __W2, _, _))) ->
                 if (cs1 = cs2) && (n1 = n2)
                 then ()
                 else matchExp (__G, (__W1, s1), (__W2, s2))
             | (FgnConst (_, ConDef (_, _, _, __W1, _, _, _)), _) ->
                 matchExp (__G, (__W1, s1), __Us2)
             | (_, FgnConst (_, ConDef (_, _, _, __W2, _, _, _))) ->
                 matchExp (__G, __Us1, (__W2, s2))
             | _ -> raise (Match "Head mismatch")))
          (* four new cases for defined constants *)
          (* due to strictness! *)(* due to strictness! *)
          (* next two cases for def/fgn, fgn/def *)(* we require unique string representation of external constants *))
      | (__G, (Pi ((__D1, _), __U1), s1), (Pi ((__D2, _), __U2), s2)) ->
          (matchDec (__G, (__D1, s1), (__D2, s2));
           matchExp
             ((Decl (__G, (decSub (__D1, s1)))), (__U1, (dot1 s1)),
               (__U2, (dot1 s2))))
      | (__G, ((Pi (_, _), _) as Us1), ((Root (Def _, _), _) as Us2)) ->
          matchExpW (__G, __Us1, (Whnf.expandDef __Us2))
      | (__G, ((Root (Def _, _), _) as Us1), ((Pi (_, _), _) as Us2)) ->
          matchExpW (__G, (Whnf.expandDef __Us1), __Us2)
      | (__G, (Lam (__D1, __U1), s1), (Lam (__D2, __U2), s2)) ->
          matchExp
            ((Decl (__G, (decSub (__D1, s1)))), (__U1, (dot1 s1)),
              (__U2, (dot1 s2)))
      | (__G, (Lam (__D1, __U1), s1), (__U2, s2)) ->
          matchExp
            ((Decl (__G, (decSub (__D1, s1)))), (__U1, (dot1 s1)),
              ((Redex
                  ((EClo (__U2, shift)), (App ((Root ((BVar 1), Nil)), Nil)))),
                (dot1 s2)))
      | (__G, (__U1, s1), (Lam (__D2, __U2), s2)) ->
          matchExp
            ((Decl (__G, (decSub (__D2, s2)))),
              ((Redex
                  ((EClo (__U1, shift)), (App ((Root ((BVar 1), Nil)), Nil)))),
                (dot1 s1)), (__U2, (dot1 s2)))
      | (__G, ((EVar (r, GX, __V, cnstrs), s) as Us1), ((__U2, s2) as Us2))
          ->
          if Whnf.isPatSub s
          then
            let ss = Whnf.invert s in
            let U2' = pruneExp (__G, __Us2, ss, r) in
            ((Unify.instantiateEVar (r, U2', (!cnstrs)))
              (* instantiateEVar (r, EClo (U2, comp(s2, ss)), !cnstrs) *)
              (* invertExpW (Us2, s, r) *))
          else
            Unify.addConstraint
              (cnstrs, (ref (Eqn (__G, (EClo __Us1), (EClo __Us2)))))
      | (__G, __Us1, __Us2) -> raise (Match "Expression clash")(* invertExpW (Us1, s, r) *)
      (*      | matchExpW (G, Us1 as (U1,s1), Us2 as (EVar (r, GX, V, cnstrs), s)) =
        if Whnf.isPatSub(s) then
          let
            val ss = Whnf.invert s
            val U1' = pruneExp (G, Us1, ss, r)
          in
             instantiateEVar (r, EClo (U1, comp(s1, ss)), !cnstrs) *)
      (* invertExpW (Us1, s2, ref None) *)(* instantiateEVar (r2, EClo (U1, comp(s1, ss2)), !cnstr2) *)
      (* invertExpW (Us2, s1, ref None) *)(* Unify.instantiateEVar (r1, EClo (U2, comp(s2, ss1)), !cnstrs1) *)
      (* invertExp ((V1, id), s', ref None) *)(* X[s] = X[s] *)
      (* added for definitions Mon Sep  1 19:53:13 2003 -fp *)(* without the next optimization, bugs/hangs/sources.cfg
                     would gets into an apparent infinite loop
                     Fri Sep  5 20:23:27 2003 -fp
                  *)
      (* compute ss' directly? *)(*      | matchExpW (G, Us1 as (U1 as EVar(r1, G1, V1, cnstrs1), s1),
                   Us2 as (U2 as EVar(r2, G2, V2, cnstrs2), s2)) =
           postpone, if s1 or s2 are not patsub *)
      (* same reasoning holds as above *)(* Cannot occur if expressions are eta expanded *)
      (* for rhs:  (U2[s2])[^] 1 = U2 [s2 o ^] 1 = U2 [^ o (1. s2 o ^)] 1
                        = (U2 [^] 1) [1.s2 o ^] *)
      (* ETA: can't occur if eta expanded *)(* D1[s1] = D2[s2]  by invariant *)
      (* order of calls critical to establish matchSpine invariant *)
      (* s1 = s2 = id by whnf *)(* matchUni (L1, L2) - removed Mon Aug 24 12:18:24 1998 -fp *)
      (* L1 = L2 = type, by invariant *)
    let rec matchExp (__G) ((__E1, s1) as Us1) ((__E2, s2) as Us2) =
      matchExpW (__G, (Whnf.whnf __Us1), (Whnf.whnf __Us2))
    let rec matchDefDefW (__G) ((Root (Def d1, __S1), s1) as Us1)
      ((Root (Def d2, __S2), s2) as Us2) =
      let Anc (_, h1, c1Opt) = defAncestor d1 in
      let Anc (_, h2, c2Opt) = defAncestor d2 in
      let _ =
        match (c1Opt, c2Opt) with
        | (Some c1, Some c2) ->
            if c1 <> c2
            then raise (Match "Irreconcilable defined constant clash")
            else ()
        | _ -> () in
      ((match Int.compare (h1, h2) with
        | EQUAL ->
            matchExpW (__G, (Whnf.expandDef __Us1), (Whnf.expandDef __Us2))
        | LESS -> matchExpW (__G, __Us1, (Whnf.expandDef __Us2))
        | GREATER -> matchExpW (__G, (Whnf.expandDef __Us1), __Us2))
        (* conservative *))(*  matchExpW (G, Whnf.expandDef (Us1), Whnf.expandDef (Us2)) *)
    let rec matchSpine __29__ __30__ __31__ =
      match (__29__, __30__, __31__) with
      | (__G, (Nil, _), (Nil, _)) -> ()
      | (__G, (SClo (__S1, s1'), s1), __Ss) ->
          matchSpine (__G, (__S1, (comp (s1', s1))), __Ss)
      | (__G, __Ss, (SClo (__S2, s2'), s2)) ->
          matchSpine (__G, __Ss, (__S2, (comp (s2', s2))))
      | (__G, (App (__U1, __S1), s1), (App (__U2, __S2), s2)) ->
          (matchExp (__G, (__U1, s1), (__U2, s2));
           matchSpine (__G, (__S1, s1), (__S2, s2)))
    let rec matchDec (__G) (Dec (_, __V1), s1) (Dec (_, __V2), s2) =
      matchExp (__G, (__V1, s1), (__V2, s2))
    let rec matchSub __32__ __33__ __34__ =
      match (__32__, __33__, __34__) with
      | (__G, Shift n1, Shift n2) -> ()
      | (__G, Shift n, (Dot _ as s2)) ->
          matchSub (__G, (Dot ((Idx (n + 1)), (Shift (n + 1)))), s2)
      | (__G, (Dot _ as s1), Shift m) ->
          matchSub (__G, s1, (Dot ((Idx (m + 1)), (Shift (m + 1)))))
      | (__G, Dot (Ft1, s1), Dot (Ft2, s2)) ->
          ((((match (Ft1, Ft2) with
              | (Idx n1, Idx n2) ->
                  if n1 <> n2
                  then raise (Error "Some variables mismatch")
                  else ()
              | (Exp (__U1), Exp (__U2)) ->
                  matchExp (__G, (__U1, id), (__U2, id))
              | (Exp (__U1), Idx n2) ->
                  matchExp (__G, (__U1, id), ((Root ((BVar n2), Nil)), id))
              | (Idx n1, Exp (__U2)) ->
                  matchExp (__G, ((Root ((BVar n1), Nil)), id), (__U2, id)));
             matchSub (__G, s1, s2)))
          (*         | (Undef, Undef) =>
           | _ => false *)
          (* not possible because of invariant? -cs *))
      (* by invariant *)
    let rec matchBlock __35__ __36__ __37__ =
      match (__35__, __36__, __37__) with
      | (__G, LVar ({ contents = Some (__B1) }, s, _), __B2) ->
          matchBlock (__G, (blockSub (__B1, s)), __B2)
      | (__G, __B1, LVar ({ contents = Some (__B2) }, s, _)) ->
          matchBlock (__G, __B1, (blockSub (__B2, s)))
      | (__G, __B1, __B2) -> matchBlockW (__G, __B1, __B2)
    let rec matchBlockW __38__ __39__ __40__ =
      match (__38__, __39__, __40__) with
      | (__G, LVar (r1, Shift k1, (l1, t1)), LVar (r2, Shift k2, (l2, t2)))
          ->
          if l1 <> l2
          then raise (Match "Label clash")
          else
            if r1 = r2
            then ()
            else
              (((matchSub (__G, t1, t2);
                 if k1 <> k2 then raise Bind else ();
                 (let ss = Whnf.invert (Shift k1) in
                  let t2' = pruneSub (__G, t2, ss, (ref None)) in
                  ((Unify.instantiateLVar
                      (r1, (LVar (r2, (Shift 0), (l2, t2')))))
                    (* hack! *)(* 0 = k2-k1 *)))))
              (* Sat Dec  7 22:04:31 2002 -fp *)(* invariant? always k1 = k2? *)
              (* prune t2? Sat Dec  7 22:09:53 2002 *)
              (*
              if k1 < k2 then instantiateLVar (r1, LVar(r2, Shift(k2-k1), (l2, t2)))
                else Unify.instantiateLVar (r2, LVar(r1, Shift (k1-k2), (l1, t1)))
              *))
      | (__G, LVar (r1, s1, (l1, t1)), __B2) ->
          ((:=) r1 Some (blockSub (__B2, (Whnf.invert s1))); ())
      | (__G, __B1, LVar (r2, s2, (l2, t2))) ->
          ((:=) r2 Some (blockSub (__B1, (Whnf.invert s2))); ())
      | (__G, Bidx n1, Bidx n2) ->
          if n1 <> n2 then raise (Match "Block index clash") else ()(* Sat Dec  8 11:49:16 2001 -fp !!! *)
      (* How can the next case arise? *)(* -- ABP *)
      (*      | matchBlockW (G, LVar (r1, Shift(k1), (l1, t1)), Bidx i2) =
            (r1 := Some (Bidx (i2 -k1)) ; ())  -- ABP *)
      (* -- ABP *)(* -- ABP *)
    let rec match1W (__G) (__Us1) (__Us2) =
      matchExpW (__G, __Us1, __Us2); awakeCnstr (Unify.nextCnstr ())
    let rec match1 (__G) (__Us1) (__Us2) =
      matchExp (__G, __Us1, __Us2); awakeCnstr (Unify.nextCnstr ())
    let rec awakeCnstr =
      function
      | None -> ()
      | Some { contents = Solved } -> awakeCnstr (Unify.nextCnstr ())
      | Some ({ contents = Eqn (__G, __U1, __U2) } as cnstr) ->
          (Unify.solveConstraint cnstr; match1 (__G, (__U1, id), (__U2, id)))
      | Some { contents = FgnCnstr csfc } ->
          if FgnCnstrStd.Awake.apply csfc ()
          then ()
          else raise (Match "Foreign constraint violated")
    let rec matchW (__G) (__Us1) (__Us2) =
      Unify.resetAwakenCnstrs (); match1W (__G, __Us1, __Us2)
    let rec match__ (__G) (__Us1) (__Us2) =
      Unify.resetAwakenCnstrs (); match1 (__G, __Us1, __Us2)
    let matchW = matchW
    let match__ = match__
    let matchSub = matchSub
    let matchBlock = matchBlock
    let rec instance (__G) (__Us1) (__Us2) =
      try match__ (__G, __Us1, __Us2); true with | Match msg -> false
    let rec instance' (__G) (__Us1) (__Us2) =
      try match__ (__G, __Us1, __Us2); None with | Match msg -> Some msg
  end ;;
