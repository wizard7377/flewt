
(* Weak Head-Normal Forms *)
(* Authors: Frank Pfenning, Carsten Schuermann *)
module type WHNF  =
  sig
    (*! structure IntSyn : INTSYN !*)
    (* Patterns *)
    val isPatSub : IntSyn.__Sub -> bool
    val makePatSub : IntSyn.__Sub -> IntSyn.__Sub option
    val dotEta : (IntSyn.__Front * IntSyn.__Sub) -> IntSyn.__Sub
    exception Eta 
    val etaContract : IntSyn.__Exp -> int
    (* can raise Eta *)
    (* Weak head normalization *)
    val whnf : IntSyn.eclo -> IntSyn.eclo
    val expandDef : IntSyn.eclo -> IntSyn.eclo
    val whnfExpandDef : IntSyn.eclo -> IntSyn.eclo
    val etaExpandRoot : IntSyn.__Exp -> IntSyn.__Exp
    val whnfEta : (IntSyn.eclo * IntSyn.eclo) -> (IntSyn.eclo * IntSyn.eclo)
    val lowerEVar : IntSyn.__Exp -> IntSyn.__Exp
    val newLoweredEVar : (IntSyn.dctx * IntSyn.eclo) -> IntSyn.__Exp
    val newSpineVar : (IntSyn.dctx * IntSyn.eclo) -> IntSyn.__Spine
    val spineToSub : (IntSyn.__Spine * IntSyn.__Sub) -> IntSyn.__Sub
    (* Full normalization *)
    val normalize : IntSyn.eclo -> IntSyn.__Exp
    val normalizeDec : (IntSyn.__Dec * IntSyn.__Sub) -> IntSyn.__Dec
    val normalizeCtx : IntSyn.dctx -> IntSyn.dctx
    (* Inverting substitutions *)
    val invert : IntSyn.__Sub -> IntSyn.__Sub
    val strengthen : (IntSyn.__Sub * IntSyn.dctx) -> IntSyn.dctx
    val isId : IntSyn.__Sub -> bool
    val cloInv : (IntSyn.__Exp * IntSyn.__Sub) -> IntSyn.__Exp
    val compInv : (IntSyn.__Sub * IntSyn.__Sub) -> IntSyn.__Sub
  end;;




(* Weak Head-Normal Forms *)
(* Author: Frank Pfenning, Carsten Schuermann *)
(* Modified: Roberto Virga *)
module Whnf() : WHNF =
  struct
    (*! structure IntSyn' : INTSYN !*)
    (*! structure IntSyn = IntSyn' !*)
    (*
     Weak Head-Normal Form (whnf)

     whnf ::= (__l, s) | (Pi DP. __u, s) | (Root (#k(b), S))
            | (Root(n,S), id) | (Root(c,S), id) | (Root(d,S), id) | (Root(F[s'], S), id)
            | (Root(fgnC,S), id) where fgnC is a foreign constant
            | (Lam D. __u, s) | (x, s) where x is uninstantiated, x of base type
                                     during type reconstruction, x might have variable type
            | (FgnExp, id) where FgnExp is a foreign expression

     Normal Form (nf)

        UA ::= __l | Pi (DA,P). UA
             | Root(n,SA) | Root(c,SA) | Root(d,SA) | Root(fgnC,SA) | Root (#k(b), S)
             | Lam DA. UA | FgnExp
        DA ::= x:UA
        SA ::= Nil | App (UA, SA)

     Existential Normal Form (enf)

     Existential normal forms are like normal forms, but also allows
     x[s] where x is uninstantiated with no particular restriction on s
     or type of X.

     An existential normal form is a hereditary weak head-normal form.
  *)
    open IntSyn
    exception Eta 
    let rec etaContract =
      function
      | (Root (BVar k, S), s, n) ->
          (match bvarSub (k, s) with
           | Idx k' ->
               if k' > n then (etaContract' (S, s, n); k' - n) else raise Eta
           | _ -> raise Eta)
      | (Lam (__d, __u), s, n) -> etaContract (__u, (dot1 s), (n + 1))
      | (EClo (__u, s'), s, n) -> etaContract (__u, (comp (s', s)), n)
      | (EVar ({ contents = Some (__u) }, _, _, _), s, n) -> etaContract (__u, s, n)
      | (AVar ({ contents = Some (__u) }), s, n) -> etaContract (__u, s, n)
      | _ -> raise Eta
    let rec etaContract' =
      function
      | (Nil, s, 0) -> ()
      | (App (__u, S), s, n) ->
          if (etaContract (__u, s, 0)) = n
          then etaContract' (S, s, (n - 1))
          else raise Eta
      | (SClo (S, s'), s, n) -> etaContract' (S, (comp (s', s)), n)
      | _ -> raise Eta
    let rec dotEta =
      function
      | ((Idx _ as Ft), s) -> Dot (Ft, s)
      | ((Exp (__u) as Ft), s) ->
          let Ft' = try Idx (etaContract (__u, id, 0)) with | Eta -> Ft in
          Dot (Ft', s)
      | ((Undef as Ft), s) -> Dot (Ft, s)
    let rec appendSpine =
      function
      | ((Nil, s1), Ss2) -> SClo Ss2
      | ((App (__U1, S1), s1), Ss2) ->
          App ((EClo (__U1, s1)), (appendSpine ((S1, s1), Ss2)))
      | ((SClo (S1, s1'), s1), Ss2) ->
          appendSpine ((S1, (comp (s1', s1))), Ss2)
    let rec whnfRedex =
      function
      | (__Us, (SClo (S, s2'), s2)) -> whnfRedex (__Us, (S, (comp (s2', s2))))
      | (((Root (R), s1) as __Us), (Nil, s2)) -> __Us
      | ((Root (H1, S1), s1), (S2, s2)) ->
          ((Root (H1, (appendSpine ((S1, s1), (S2, s2))))), id)
      | ((Lam (_, __U1), s1), (App (__U2, S), s2)) ->
          whnfRedex
            ((whnf (__U1, (dotEta ((frontSub ((Exp __U2), s2)), s1)))), (S, s2))
      | (((Lam _, s1) as __Us), _) -> __Us
      | (((EVar _, s1) as __Us), (Nil, s2)) -> __Us
      | ((((EVar _ as x), s1) as __Us), Ss2) ->
          (lowerEVar x; whnfRedex ((whnf __Us), Ss2))
      | (((AVar (ref (Some (__u))), s1) as __Us), Ss2) ->
          whnfRedex ((__u, s1), Ss2)
      | (((AVar (ref (None)), s1) as __Us), Ss2) -> __Us
      | (((FgnExp _, _) as __Us), _) -> __Us
      | (((Uni _, s1) as __Us), _) -> __Us
      | (((Pi _, s1) as __Us), _) -> __Us
    let rec lowerEVar' =
      function
      | (__g, (Pi ((__d', _), __v'), s')) ->
          let __d'' = decSub (__d', s') in
          let (x', __u) =
            lowerEVar' ((Decl (__g, __d'')), (whnfExpandDef (__v', (dot1 s')))) in
          (x', (Lam (__d'', __u)))
      | (__g, __Vs') -> let x' = newEVar (__g, (EClo __Vs')) in (x', x')
    let rec lowerEVar1 =
      function
      | (EVar (r, __g, _, _), ((Pi _, _) as __Vs)) ->
          let (x', __u) = lowerEVar' (__g, __Vs) in let _ = (:=) r Some __u in x'
      | (x, _) -> x
    let rec lowerEVar =
      function
      | EVar (r, __g, __v, ref nil) as x ->
          lowerEVar1 (x, (whnfExpandDef (__v, id)))
      | EVar _ ->
          raise
            (Error
               "Typing ambiguous -- constraint of functional type cannot be simplified")
    let rec whnfRoot =
      function
      | ((BVar k, S), s) ->
          (match bvarSub (k, s) with
           | Idx k -> ((Root ((BVar k), (SClo (S, s)))), id)
           | Exp (__u) -> whnfRedex ((whnf (__u, id)), (S, s)))
      | ((Proj ((Bidx _ as B), i), S), s) ->
          (match blockSub (B, s) with
           | Bidx k as B' -> ((Root ((Proj (B', i)), (SClo (S, s)))), id)
           | LVar _ as B' -> whnfRoot (((Proj (B', i)), (SClo (S, s))), id)
           | Inst (__l) ->
               whnfRedex ((whnf ((List.nth (__l, (i - 1))), id)), (S, s)))
      | ((Proj (LVar (ref (Some (B)), sk, (l, t)), i), S), s) ->
          whnfRoot
            (((Proj ((blockSub (B, (comp (sk, s)))), i)), (SClo (S, s))), id)
      | ((Proj ((LVar (r, sk, (l, t)) as __l), i), S), s) ->
          ((Root
              ((Proj ((LVar (r, (comp (sk, s)), (l, t))), i)), (SClo (S, s)))),
            id)
      | ((FVar (name, __v, s'), S), s) ->
          ((Root ((FVar (name, __v, (comp (s', s)))), (SClo (S, s)))), id)
      | ((NSDef d, S), s) ->
          whnfRedex ((whnf ((IntSyn.constDef d), id)), (S, s))
      | ((H, S), s) -> ((Root (H, (SClo (S, s)))), id)
    let rec whnf =
      function
      | ((Uni _ as __u), s) -> (__u, s)
      | ((Pi _ as __u), s) -> (__u, s)
      | (Root (R), s) -> whnfRoot (R, s)
      | (Redex (__u, S), s) -> whnfRedex ((whnf (__u, s)), (S, s))
      | (Lam _, s) as __Us -> __Us
      | (AVar (ref (Some (__u))), s) -> whnf (__u, s)
      | (AVar _, s) as __Us -> __Us
      | (EVar (ref (Some (__u)), _, _, _), s) -> whnf (__u, s)
      | (EVar (r, _, Root _, _), s) as __Us -> __Us
      | (EVar (r, _, Uni _, _), s) as __Us -> __Us
      | ((EVar (r, _, __v, _) as x), s) as __Us ->
          (match whnf (__v, id) with
           | (Pi _, _) -> (lowerEVar x; whnf __Us)
           | _ -> __Us)
      | (EClo (__u, s'), s) -> whnf (__u, (comp (s', s)))
      | (FgnExp _, Shift 0) as __Us -> __Us
      | (FgnExp csfe, s) as __Us ->
          ((FgnExpStd.Map.apply csfe (function | __u -> EClo (__u, s))), id)
    let rec expandDef (Root (Def d, S), s) =
      whnfRedex ((whnf ((constDef d), id)), (S, s))
    let rec whnfExpandDefW =
      function
      | (Root (Def _, _), _) as __Us -> whnfExpandDefW (expandDef __Us)
      | __Us -> __Us
    let rec whnfExpandDef (__Us) = whnfExpandDefW (whnf __Us)
    let rec newLoweredEVarW =
      function
      | (__g, (Pi ((__d, _), __v), s)) ->
          let __d' = decSub (__d, s) in
          Lam (__d', (newLoweredEVar ((Decl (__g, __d')), (__v, (dot1 s)))))
      | (__g, __Vs) -> newEVar (__g, (EClo __Vs))
    let rec newLoweredEVar (__g, __Vs) = newLoweredEVarW (__g, (whnfExpandDef __Vs))
    let rec newSpineVarW =
      function
      | (__g, (Pi ((Dec (_, Va), _), Vr), s)) ->
          let x = newLoweredEVar (__g, (Va, s)) in
          App (x, (newSpineVar (__g, (Vr, (dotEta ((Exp x), s))))))
      | (__g, _) -> Nil
    let rec newSpineVar (__g, __Vs) = newSpineVarW (__g, (whnfExpandDef __Vs))
    let rec spineToSub =
      function
      | (Nil, s) -> s
      | (App (__u, S), s) -> spineToSub (S, (dotEta ((Exp __u), s)))
    let rec inferSpine =
      function
      | ((Nil, _), __Vs) -> __Vs
      | ((SClo (S, s'), s), __Vs) -> inferSpine ((S, (comp (s', s))), __Vs)
      | ((App (__u, S), s1), (Pi (_, V2), s2)) ->
          inferSpine
            ((S, s1), (whnfExpandDef (V2, (Dot ((Exp (EClo (__u, s1))), s2)))))
    let rec inferCon =
      function
      | Const cid -> constType cid
      | Skonst cid -> constType cid
      | Def cid -> constType cid
    let rec etaExpand' =
      function
      | (__u, (Root _, s)) -> __u
      | (__u, (Pi ((__d, _), __v), s)) ->
          Lam
            ((decSub (__d, s)),
              (etaExpand'
                 ((Redex
                     ((EClo (__u, shift)), (App ((Root ((BVar 1), Nil)), Nil)))),
                   (whnfExpandDef (__v, (dot1 s))))))
    let rec etaExpandRoot (Root (H, S) as __u) =
      etaExpand' (__u, (inferSpine ((S, id), ((inferCon H), id))))
    let rec whnfEta (__Us, __Vs) = whnfEtaW ((whnf __Us), (whnf __Vs))
    let rec whnfEtaW =
      function
      | (_, (Root _, _)) as UsVs -> UsVs
      | ((Lam _, _), (Pi _, _)) as UsVs -> UsVs
      | ((__u, s1), ((Pi ((__d, P), __v), s2) as Vs2)) ->
          (((Lam
               ((decSub (__d, s2)),
                 (Redex
                    ((EClo (__u, (comp (s1, shift)))),
                      (App ((Root ((BVar 1), Nil)), Nil)))))), id), Vs2)
    let rec normalizeExp (__Us) = normalizeExpW (whnf __Us)
    let rec normalizeExpW =
      function
      | ((Uni (__l) as __u), s) -> __u
      | (Pi (DP, __u), s) ->
          Pi ((normalizeDecP (DP, s)), (normalizeExp (__u, (dot1 s))))
      | ((Root (H, S) as __u), s) -> Root (H, (normalizeSpine (S, s)))
      | (Lam (__d, __u), s) ->
          Lam ((normalizeDec (__d, s)), (normalizeExp (__u, (dot1 s))))
      | (EVar _, s) as __Us -> EClo __Us
      | (FgnExp csfe, s) ->
          FgnExpStd.Map.apply csfe (function | __u -> normalizeExp (__u, s))
      | (AVar (ref (Some (__u))), s) as __Us -> normalizeExpW (__u, s)
      | (AVar _, s) as __Us -> (print "Normalize  AVAR\n"; raise (Error ""))
    let rec normalizeSpine =
      function
      | (Nil, s) -> Nil
      | (App (__u, S), s) ->
          App ((normalizeExp (__u, s)), (normalizeSpine (S, s)))
      | (SClo (S, s'), s) -> normalizeSpine (S, (comp (s', s)))
    let rec normalizeDec =
      function
      | (Dec (xOpt, __v), s) -> Dec (xOpt, (normalizeExp (__v, s)))
      | (BDec (xOpt, (c, t)), s) ->
          BDec (xOpt, (c, (normalizeSub (comp (t, s)))))
    let rec normalizeDecP ((__d, P), s) = ((normalizeDec (__d, s)), P)
    let rec normalizeSub =
      function
      | Shift _ as s -> s
      | Dot ((Idx _ as Ft), s) -> Dot (Ft, (normalizeSub s))
      | Dot (Exp (__u), s) ->
          dotEta ((Exp (normalizeExp (__u, id))), (normalizeSub s))
    let rec normalizeCtx =
      function
      | Null -> Null
      | Decl (__g, __d) -> Decl ((normalizeCtx __g), (normalizeDec (__d, id)))
    let rec invert s =
      let rec lookup =
        function
        | (n, Shift _, p) -> None
        | (n, Dot (Undef, s'), p) -> lookup ((n + 1), s', p)
        | (n, Dot (Idx k, s'), p) ->
            if k = p then Some n else lookup ((n + 1), s', p) in
      let rec invert'' =
        function
        | (0, si) -> si
        | (p, si) ->
            (match lookup (1, s, p) with
             | Some k -> invert'' ((p - 1), (Dot ((Idx k), si)))
             | None -> invert'' ((p - 1), (Dot (Undef, si)))) in
      let rec invert' =
        function
        | (n, Shift p) -> invert'' (p, (Shift n))
        | (n, Dot (_, s')) -> invert' ((n + 1), s') in
      invert' (0, s)
    let rec strengthen =
      function
      | (Shift n, Null) -> Null
      | (Dot (Idx k, t), Decl (__g, __d)) ->
          let t' = comp (t, invShift) in
          Decl ((strengthen (t', __g)), (decSub (__d, t')))
      | (Dot (Undef, t), Decl (__g, __d)) -> strengthen (t, __g)
      | (Shift n, __g) ->
          strengthen ((Dot ((Idx (n + 1)), (Shift (n + 1)))), __g)
    let rec isId' =
      function
      | (Shift k, k') -> k = k'
      | (Dot (Idx n, s'), k') -> (n = k') && (isId' (s', (k' + 1)))
      | _ -> false__
    let rec isId s = isId' (s, 0)
    let rec cloInv (__u, w) = EClo (__u, (invert w))
    let rec compInv (s, w) = comp (s, (invert w))
    let rec isPatSub =
      function
      | Shift k -> true__
      | Dot (Idx n, s) ->
          let rec checkBVar =
            function
            | Shift k -> n <= k
            | Dot (Idx n', s) -> (n <> n') && (checkBVar s)
            | Dot (Undef, s) -> checkBVar s
            | _ -> false__ in
          (checkBVar s) && (isPatSub s)
      | Dot (Undef, s) -> isPatSub s
      | _ -> false__
    let rec mkPatSub =
      function
      | Shift k as s -> s
      | Dot (Idx n, s) ->
          let s' = mkPatSub s in
          let rec checkBVar =
            function
            | Shift k -> n <= k
            | Dot (Idx n', s') -> (n <> n') && (checkBVar s')
            | Dot (Undef, s') -> checkBVar s' in
          let _ = checkBVar s' in Dot ((Idx n), s')
      | Dot (Undef, s) -> Dot (Undef, (mkPatSub s))
      | Dot (Exp (__u), s) ->
          let (__u', t') = whnf (__u, id) in
          let k = etaContract (__u', t', 0) in Dot ((Idx k), (mkPatSub s))
      | _ -> raise Eta
    let rec makePatSub s = try Some (mkPatSub s) with | Eta -> None
    (* exception Undefined *)
    (* etaContract (__u, s, n) = k'

       Invariant:
       if   __g, V1, .., Vn |- s : G1  and  G1 |- __u : __v
       then if   lam V1...lam Vn. __u[s] =eta*=> k
            then k' = k
            and  __g |- k' : Pi V1...Pi Vn. __v [s]
            else Eta is raised
              (even if __u[s] might be eta-reducible to some other expressions).
    *)
    (* optimization(?): quick check w/o substitution first *)
    (* Should fail: (c@S), (d@S), (F@S), x *)
    (* Not treated (fails): __u@S *)
    (* Could weak head-normalize for more thorough checks *)
    (* Impossible: __l, Pi D.V *)
    (* etaContract' (S, s, n) = R'

       Invariant:
       If  __g |- s : G1    and  G1 |- S : __v > W
       then if   S[s] =eta*=> n ; n-1 ; ... ; 1 ; Nil
            then ()
       else Eta is raised
    *)
    (* dotEta (Ft, s) = s'

       Invariant:
       If   __g |- s : G1, __v  and __g |- Ft : __v [s]
       then Ft  =eta*=>  Ft1
       and  s' = Ft1 . s
       and  __g |- s' : G1, __v
    *)
    (* appendSpine ((S1, s1), (S2, s2)) = S'

       Invariant:
       If    __g |- s1 : G1   G1 |- S1 : V1' > V1
       and   __g |- s2 : G2   G2 |- S2 : V2  > V2'
       and   __g |- V1 [s1] == V2 [s2]
       then  __g |- S' : V1' [s1] > V2' [s2]
    *)
    (* whnfRedex ((__u, s1), (S, s2)) = (__u', s')

       Invariant:
       If    __g |- s1 : G1   G1 |- __u : V1,   (__u,s1) whnf
             __g |- s2 : G2   G2 |- S : V2 > W2
             __g |- V1 [s1] == V2 [s2] == __v : __l
       then  __g |- s' : __g',  __g' |- __u' : W'
       and   __g |- W'[s'] == W2[s2] == W : __l
       and   __g |- __u'[s'] == (__u[s1] @ S[s2]) : W
       and   (__u',s') whnf

       Effects: EVars may be lowered to base type.
    *)
    (* S2 = App _, only possible if term is not eta-expanded *)
    (* S2[s2] = Nil *)
    (* Ss2 must be App, since prior cases do not apply *)
    (* lowerEVar x results in redex, optimize by unfolding call to whnfRedex *)
    (* Uni and Pi can arise after instantiation of EVar x : K *)
    (* S2[s2] = Nil *)
    (* S2[s2] = Nil *)
    (* Other cases impossible since (__u,s1) whnf *)
    (* lowerEVar' (__g, __v[s]) = (x', __u), see lowerEVar *)
    (* lowerEVar1 (x, __v[s]), __v[s] in whnf, see lowerEVar *)
    (* lowerEVar (x) = x'

       Invariant:
       If   __g |- x : {{__g'}} P
            x not subject to any constraints
       then __g, __g' |- x' : P

       Effect: x is instantiated to [[__g']] x' if __g' is empty
               otherwise x = x' and no effect occurs.
    *)
    (* It is not clear if this case can happen *)
    (* pre-Twelf 1.2 code walk, Fri May  8 11:05:08 1998 *)
    (* whnfRoot ((H, S), s) = (__u', s')

       Invariant:
       If    __g |- s : G1      G1 |- H : __v
                              G1 |- S : __v > W
       then  __g |- s' : __g'     __g' |- __u' : W'
       and   __g |- W [s] = W' [s'] : __l

       Effects: EVars may be instantiated when lowered
    *)
    (* Undef should be impossible *)
    (* could blockSub (B, s) return instantiated LVar ? *)
    (* Sat Dec  8 13:43:17 2001 -fp !!! *)
    (* yes Thu Dec 13 21:48:10 2001 -fp !!! *)
    (* was: (Root (Proj (blockSub (B, s), i), SClo (S, s)), id) *)
    (* r = ref None *)
    (* scary: why is comp(sk, s) = ^n ?? -fp July 22, 2010, -fp -cs *)
    (* was:
         (Root (Proj (LVar (r, comp (sk, s), (l, comp(t, s))), i), SClo (S, s)), id)
         Jul 22, 2010 -fp -cs
         *)
    (* do not compose with t due to globality invariant *)
    (* Thu Dec  6 20:34:30 2001 -fp !!! *)
    (* was: (Root (Proj (__l, i), SClo (S, s)), id) *)
    (* going back to first version, because globality invariant *)
    (* no longer satisfied Wed Nov 27 09:49:58 2002 -fp *)
    (* Undef and Exp should be impossible by definition of substitution -cs *)
    (* whnf (__u, s) = (__u', s')

       Invariant:
       If    __g |- s : __g'    __g' |- __u : __v
       then  __g |- s': __g''   __g''|- __u' : __v'
       and   __g |- __v [s] == __v' [s'] == __v'' : __l
       and   __g |- __u [s] == __u' [s'] : __v''
       and   (__u', s') whnf
    *)
    (*
       Possible optimization :
         Define whnf of Root as (Root (n , S [s]), id)
         Fails currently because appendSpine does not necessairly return a closure  -cs
         Advantage: in unify, abstract... the spine needn't be treated under id, but under s
    *)
    (* simple optimization (C@S)[id] = C@S[id] *)
    (* applied in Twelf 1.1 *)
    (* Sat Feb 14 20:53:08 1998 -fp *)
    (*      | whnf (__Us as (Root _, Shift (0))) = __Us*)
    (* commented out, because non-strict definitions slip
         Mon May 24 09:50:22 EDT 1999 -cs  *)
    (* | whnf (__Us as (EVar _, s)) = __Us *)
    (* next two avoid calls to whnf (__v, id), where __v is type of x *)
    (* possible opt: call lowerEVar1 *)
    (* expandDef (Root (Def (d), S), s) = (__u' ,s')

       Invariant:
       If    __g |- s : G1     G1 |- S : __v > W            ((d @ S), s) in whnf
                             .  |- d = __u : __v'
       then  __g |- s' : __g'    __g' |- __u' : W'
       and   __g |- __v' == __v [s] : __l
       and   __g |- W' [s'] == W [s] == W'' : __l
       and   __g |- (__u @ S) [s] == __u' [s'] : W'
       and   (__u', s') in whnf
    *)
    (* why the call to whnf?  isn't constDef (d) in nf? -kw *)
    (* inferSpine ((S, s1), (__v, s2)) = (__v', s')

       Invariant:
       If  __g |- s1 : G1  and  G1 |- S : V1 > V1'
       and __g |- s2 : G2  and  G2 |- __v : __l,  (__v, s2) in whnf
       and __g |- S[s1] : __v[s2] > W  (so V1[s1] == __v[s2] and V1[s1] == W)
       then __g |- __v'[s'] = W
    *)
    (* FIX: this is almost certainly mis-design -kw *)
    (* inferCon (C) = __v  if C = c or C = d or C = sk and |- C : __v *)
    (* FIX: this is almost certainly mis-design -kw *)
    (* etaExpand' (__u, (__v,s)) = __u'

       Invariant :
       If    __g |- __u : __v [s]   (__v,s) in whnf
       then  __g |- __u' : __v [s]
       and   __g |- __u == __u' : __v[s]
       and   (__u', id) in whnf and __u' in head-eta-long form
    *)
    (* quite inefficient -cs *)
    (* FIX: this is almost certainly mis-design -kw *)
    (* etaExpandRoot (Root(H, S)) = __u' where H = c or H = d

       Invariant:
       If   __g |- H @ S : __v  where H = c or H = d
       then __g |- __u' : __v
       and  __g |- H @ S == __u'
       and (__u',id) in whnf and __u' in head-eta-long form
    *)
    (* FIX: this is almost certainly mis-design -kw *)
    (* whnfEta ((__u, s1), (__v, s2)) = ((__u', s1'), (__v', s2)')

       Invariant:
       If   __g |- s1 : G1  G1 |- __u : V1
       and  __g |- s2 : G2  G2 |- __v : __l
       and  __g |- V1[s1] == __v[s2] : __l

       then __g |- s1' : G1'  G1' |- __u' : V1'
       and  __g |- s2' : G2'  G2' |- __v' : __l'
       and  __g |- V1'[s1'] == __v'[s2'] : __l
       and (__u', s1') is in whnf
       and (__v', s2') is in whnf
       and (__u', s1') == Lam x.U'' if __v[s2] == Pi x.V''

       Similar to etaExpand', but without recursive expansion
    *)
    (* FIX: this is almost certainly mis-design -kw *)
    (* Invariant:

       normalizeExp (__u, s) = __u'
       If   __g |- s : __g' and __g' |- __u : __v
       then __u [s] = __u'
       and  __u' in existential normal form

       If (__u, s) contain no existential variables,
       then __u' in normal formal
    *)
    (* s = id *)
    (* dead code -fp *)
    (* pre-Twelf 1.2 code walk Fri May  8 11:37:18 1998 *)
    (* not any more --cs Wed Jun 19 13:59:56 EDT 2002 *)
    (* changed to obtain pattern substitution if possible *)
    (* Sat Dec  7 16:58:09 2002 -fp *)
    (* Dot (Exp (normalizeExp (__u, id)), normalizeSub s) *)
    (* invert s = s'

       Invariant:
       If   __g |- s : __g'    (and s patsub)
       then __g' |- s' : __g
       s.t. s o s' = id
    *)
    (* strengthen (t, __g) = __g'

       Invariant:
       If   __g'' |- t : __g     and t strsub *)
    (* = 0 *)
    (* k = 1 *)
    (* __g |- __d dec *)
    (* __g' |- t' : __g *)
    (* __g' |- __d[t'] dec *)
    (* isId s = B

       Invariant:
       If   __g |- s: __g', s weakensub
       then B holds
            iff s = id, __g' = __g
    *)
    (* cloInv (__u, w) = __u[w^-1]

       Invariant:
       If __g |- __u : __v
          __g |- w : __g'  w weakening subst
          __u[w^-1] defined (without pruning or constraints)

       then __g' |- __u[w^-1] : __v[w^-1]
       Effects: None
    *)
    (* cloInv (s, w) = s o w^-1

       Invariant:
       If __g |- s : G1
          __g |- w : G2  s weakening subst
          s o w^-1 defined (without pruning or constraints)

       then G2 |- s o w^-1 : G1
       Effects: None
    *)
    (* functions previously in the Pattern functor *)
    (* eventually, they may need to be mutually recursive with whnf *)
    (* isPatSub s = B

       Invariant:
       If    __g |- s : __g'
       and   s = n1 .. nm ^k
       then  B iff  n1, .., nm pairwise distinct
               and  ni <= k or ni = _ for all 1 <= i <= m
    *)
    (* Try harder, due to bug somewhere *)
    (* Sat Dec  7 17:05:02 2002 -fp *)
    (* false *)
    (* below does not work, because the patSub is lost *)
    (*
          let val (__u', s') = whnf (__u, id)
          in
            isPatSub (Dot (Idx (etaContract (__u', s', 0)), s))
            handle Eta => false
          end
      | isPatSub _ = false
      *)
    (* makePatSub s = Some(s') if s is convertible to a patSub
                      None otherwise

       Invariant:
       If    __g |- s : __g'
       and   s = n1 .. nm ^k
       then  B iff  n1, .., nm pairwise distinct
               and  ni <= k or ni = _ for all 1 <= i <= m
    *)
    (* may raise Eta *)
    let isPatSub = isPatSub
    let makePatSub = makePatSub
    let dotEta = dotEta
    exception Eta = Eta
    let etaContract = function | __u -> etaContract (__u, id, 0)
    let whnf = whnf
    let expandDef = expandDef
    let whnfExpandDef = whnfExpandDef
    let etaExpandRoot = etaExpandRoot
    let whnfEta = whnfEta
    let lowerEVar = lowerEVar
    let newLoweredEVar = newLoweredEVar
    let newSpineVar = newSpineVar
    let spineToSub = spineToSub
    let normalize = normalizeExp
    let normalizeDec = normalizeDec
    let normalizeCtx = normalizeCtx
    let invert = invert
    let strengthen = strengthen
    let isId = isId
    let cloInv = cloInv
    let compInv = compInv
  end ;;
