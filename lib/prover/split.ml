
(* Splitting: Version 1.4 *)
(* Author: Carsten Schuermann *)
module type SPLIT  =
  sig
    (*! structure IntSyn : INTSYN !*)
    (*! structure Tomega : TOMEGA !*)
    module State : STATE
    exception Error of string 
    type nonrec operator
    val expand : State.__Focus -> operator list
    val apply : operator -> unit
    val menu : operator -> string
  end;;




(* State definition for Proof Search *)
(* Author: Carsten Schuermann *)
module Split(Split:sig
                     module Global : GLOBAL
                     module State' : STATE
                     module Whnf : WHNF
                     module Unify : UNIFY
                     module Constraints : CONSTRAINTS
                     module Abstract : ABSTRACT
                     module Index : INDEX
                     module Print : PRINT
                     module TypeCheck : TYPECHECK
                     (*! structure IntSyn' : INTSYN !*)
                     (*! structure Tomega' : TOMEGA !*)
                     (*! sharing Tomega'.IntSyn = IntSyn' !*)
                     (*! sharing State'.IntSyn = IntSyn' !*)
                     (*! sharing State'.Tomega = Tomega' !*)
                     (*! sharing Whnf.IntSyn = IntSyn' !*)
                     (*! sharing Unify.IntSyn = IntSyn' !*)
                     (*! sharing Constraints.IntSyn = IntSyn' !*)
                     (*! sharing Abstract.IntSyn = IntSyn' !*)
                     (*! sharing Abstract.Tomega = Tomega' !*)
                     (*! sharing Index.IntSyn = IntSyn' !*)
                     (*! sharing Print.IntSyn = IntSyn' !*)
                     (*! sharing TypeCheck.IntSyn = IntSyn' !*)
                     module Subordinate : SUBORDINATE
                   end) : SPLIT =
  struct
    (*! sharing Subordinate.IntSyn = IntSyn' !*)
    (*! structure IntSyn = IntSyn' !*)
    (*! structure Tomega = Tomega' !*)
    module State = State'
    exception Error of string 
    module T = Tomega
    module I = IntSyn
    module S = State'
    type __Operator =
      | Split of (T.__Prg option ref * T.__Prg * string) 
    let rec weaken =
      function
      | (I.Null, a) -> I.id
      | (Decl (__g', (Dec (name, __v) as __d)), a) ->
          let w' = weaken (__g', a) in
          if Subordinate.belowEq ((I.targetFam __v), a)
          then I.dot1 w'
          else I.comp (w', I.shift)
    let rec createEVar (__g, __v) =
      let w = weaken (__g, (I.targetFam __v)) in
      let iw = Whnf.invert w in
      let __g' = Whnf.strengthen (iw, __g) in
      let x' = I.newEVar (__g', (I.EClo (__v, iw))) in
      let x = I.EClo (x', w) in x
    let rec instEVars (__Vs, p, XsRev) = instEVarsW ((Whnf.whnf __Vs), p, XsRev)
    let rec instEVarsW =
      function
      | (__Vs, 0, XsRev) -> (__Vs, XsRev)
      | ((Pi ((Dec (xOpt, V1), _), V2), s), p, XsRev) ->
          let X1 = I.newEVar (I.Null, (I.EClo (V1, s))) in
          instEVars
            ((V2, (I.Dot ((I.Exp X1), s))), (p - 1), ((Some X1) :: XsRev))
      | ((Pi ((BDec (_, (l, t)), _), V2), s), p, XsRev) ->
          let L1 = I.newLVar ((I.Shift 0), (l, (I.comp (t, s)))) in
          instEVars
            ((V2, (I.Dot ((I.Block L1), s))), (p - 1), (None :: XsRev))
    let (caseList : (T.__Dec I.__Ctx * T.__Sub) list ref) = ref nil
    let rec resetCases () = caseList := nil
    let rec addCase (Psi, t) = (!) ((::) (caseList := (Psi, t))) caseList
    let rec getCases () = !caseList
    let rec createEVarSpine (__g, __Vs) = createEVarSpineW (__g, (Whnf.whnf __Vs))
    let rec createEVarSpineW =
      function
      | (__g, ((Root _, s) as __Vs)) -> (I.Nil, __Vs)
      | (__g, (Pi (((Dec (_, V1) as __d), _), V2), s)) ->
          let x = createEVar (__g, (I.EClo (V1, s))) in
          let (S, __Vs) = createEVarSpine (__g, (V2, (I.Dot ((I.Exp x), s)))) in
          ((I.App (x, S)), __Vs)
    let rec createAtomConst (__g, (Const cid as H)) =
      let __v = I.constType cid in
      let (S, __Vs) = createEVarSpine (__g, (__v, I.id)) in ((I.Root (H, S)), __Vs)
    let rec createAtomBVar (__g, k) =
      let Dec (_, __v) = I.ctxDec (__g, k) in
      let (S, __Vs) = createEVarSpine (__g, (__v, I.id)) in
      ((I.Root ((I.BVar k), S)), __Vs)
    let rec createAtomProj (__g, H, (__v, s)) =
      let (S, __Vs') = createEVarSpine (__g, (__v, s)) in ((I.Root (H, S)), __Vs')
    let rec constCases =
      function
      | (__g, __Vs, nil, sc) -> ()
      | (__g, __Vs, (Const c)::sgn', sc) ->
          let (__u, __Vs') = createAtomConst (__g, (I.Const c)) in
          let _ =
            CSManager.trail
              (function
               | () -> if Unify.unifiable (__g, __Vs, __Vs') then sc __u else ()) in
          constCases (__g, __Vs, sgn', sc)
    let rec paramCases =
      function
      | (__g, __Vs, 0, sc) -> ()
      | (__g, __Vs, k, sc) ->
          let (__u, __Vs') = createAtomBVar (__g, k) in
          let _ =
            CSManager.trail
              (function
               | () -> if Unify.unifiable (__g, __Vs, __Vs') then sc __u else ()) in
          paramCases (__g, __Vs, (k - 1), sc)
    let rec createEVarSub =
      function
      | I.Null -> I.id
      | Decl (__g', (Dec (_, __v) as __d)) ->
          let s = createEVarSub __g' in
          let __v' = I.EClo (__v, s) in
          let x = I.newEVar (I.Null, __v') in I.Dot ((I.Exp x), s)
    let rec blockName cid = I.conDecName (I.sgnLookup cid)
    let rec blockCases (__g, __Vs, cid, (Gsome, piDecs), sc) =
      let t = createEVarSub Gsome in
      let sk = I.Shift (I.ctxLength __g) in
      let t' = I.comp (t, sk) in
      let lvar = I.newLVar (sk, (cid, t')) in
      blockCases' (__g, __Vs, (lvar, 1), (t', piDecs), sc)
    let rec blockCases' =
      function
      | (__g, __Vs, (lvar, i), (t, nil), sc) -> ()
      | (__g, __Vs, (lvar, i), (t, (Dec (_, __v'))::piDecs), sc) ->
          let (__u, __Vs') = createAtomProj (__g, (I.Proj (lvar, i)), (__v', t)) in
          let _ =
            CSManager.trail
              (function
               | () -> if Unify.unifiable (__g, __Vs, __Vs') then sc __u else ()) in
          let t' = I.Dot ((I.Exp (I.Root ((I.Proj (lvar, i)), I.Nil))), t) in
          blockCases' (__g, __Vs, (lvar, (i + 1)), (t', piDecs), sc)
    let rec worldCases =
      function
      | (__g, __Vs, Worlds nil, sc) -> ()
      | (__g, __Vs, Worlds (cid::cids), sc) ->
          (blockCases (__g, __Vs, cid, (I.constBlock cid), sc);
           worldCases (__g, __Vs, (T.Worlds cids), sc))
    let rec lowerSplit (__g, __Vs, W, sc) =
      lowerSplitW (__g, (Whnf.whnf __Vs), W, sc)
    let rec lowerSplitW (__g, ((Root (Const a, _), s) as __Vs), W, sc) =
      let _ = constCases (__g, __Vs, (Index.lookup a), sc) in
      let _ = paramCases (__g, __Vs, (I.ctxLength __g), sc) in
      let _ = worldCases (__g, __Vs, W, sc) in ()
    let rec splitEVar ((EVar (_, GX, __v, _) as x), W, sc) =
      lowerSplit
        (I.Null, (__v, I.id), W,
          (function
           | __u ->
               if Unify.unifiable (I.Null, (x, I.id), (__u, I.id))
               then sc ()
               else ()))
    let rec createSub =
      function
      | I.Null -> T.id
      | Decl (Psi, UDec (Dec (xOpt, V1))) ->
          let t' = createSub Psi in
          let x =
            I.newEVar (I.Null, (I.EClo (Whnf.whnf (V1, (T.coerceSub t'))))) in
          T.Dot ((T.Exp x), t')
      | Decl (Psi, UDec (BDec (_, (l, s)))) ->
          let t' = createSub Psi in
          let __l =
            I.newLVar ((I.Shift 0), (l, (I.comp (s, (T.coerceSub t'))))) in
          T.Dot ((T.Block __l), t')
      | Decl (Psi, PDec (_, F, TC1, TC2)) ->
          let t' = createSub Psi in
          let y = T.newEVarTC (I.Null, (T.FClo (F, t')), TC1, TC2) in
          T.Dot ((T.Prg y), t')
    let rec mkCases =
      function
      | (nil, F) -> nil
      | ((Psi, t)::cs, F) ->
          let x = T.newEVar (Psi, (T.FClo (F, t))) in
          (::) (Psi, t, x) mkCases (cs, F)
    let rec split (Focus (EVar (Psi, r, F, None, None, _), W)) =
      let rec splitXs arg__0 arg__1 =
        match (arg__0, arg__1) with
        | ((__g, i), (nil, _, _, _)) -> nil
        | ((__g, i), ((x)::__Xs, F, W, sc)) ->
            let _ =
              if (!Global.chatter) >= 6
              then
                print (((^) "Split " Print.expToString (I.Null, x)) ^ ".\n")
              else () in
            let __Os = splitXs (__g, (i + 1)) (__Xs, F, W, sc) in
            let _ = resetCases () in
            let s = Print.expToString (__g, x) in
            let __Os' =
              try
                splitEVar (x, W, sc);
                (Split
                   (r, (T.Case (T.Cases (mkCases ((getCases ()), F)))), s))
                  :: __Os
              with
              | Error constrs ->
                  (if (!Global.chatter) >= 6
                   then
                     print
                       (((^) "Inactive split:\n" Print.cnstrsToString constrs)
                          ^ "\n")
                   else ();
                   __Os) in
            __Os' in
      let t = createSub Psi in
      let __Xs = State.collectLFSub t in
      let rec init () = addCase (Abstract.abstractTomegaSub t) in
      let __g = T.coerceCtx Psi in
      let __Os = splitXs (__g, 1) (__Xs, F, W, init) in __Os
    let rec expand (Focus (EVar (Psi, r, F, None, None, _), W) as S) =
      if Abstract.closedCTX Psi then split S else []
    let rec apply (Split (r, P, s)) = (:=) r Some P
    let rec menu (Split (_, _, s)) = "Split " ^ s
    (* weaken (__g, a) = w'

       Invariant:
       If   a is a type family
       then __g |- w' : __g'
       and  forall x:A in __g'  A subordinate to a
     *)
    (* added next case, probably should not arise *)
    (* Sun Dec 16 10:42:05 2001 -fp !!! *)
    (*
      | weaken (I.Decl (__g', __d as I.BDec _), a) =
           I.dot1 (weaken (__g', a))
      *)
    (* createEVar (__g, __v) = x[w] where __g |- x[w] : __v

       Invariant:
       If __g |- __v : __l
       then __g |- x[w] : __v
    *)
    (* __g |- __v : __l *)
    (* __g  |- w  : __g'    *)
    (* __g' |- iw : __g     *)
    (* __g' |- x' : __v[iw] *)
    (* __g  |- x  : __v     *)
    (* instEVars ({x1:V1}...{xp:Vp} __v, p, nil) = (__v[s], [X1,...,Xn])
       where . |- s : {x1:V1}...{xp:Vp}
       and s = Xp...X1.id, all Xi are new EVars
    *)
    (* p > 0 *)
    (* all EVars are global *)
    (* G0 |- t : Gsome *)
    (* . |- s : G0 *)
    (* p > 0 *)
    (* --cs Sun Dec  1 06:33:27 2002 *)
    (* caseList is a list of possibilities for a variables
       to be split.  Maintained as a mutable reference so it
       can be updated in the success continuation.
    *)
    (* createEVarSpine (__g, (__v, s)) = (S', (__v', s'))

       Invariant:
       If   __g |- s : G1   and  G1 |- __v = Pi {V1 .. Vn}. W : __l
       and  G1, V1 .. Vn |- W atomic
       then __g |- s' : G2  and  G2 |- __v' : __l
       and  S = X1; ...; Xn; Nil
       and  __g |- W [1.2...n. s o ^n] = __v' [s']
       and  __g |- S : __v [s] >  __v' [s']
    *)
    (* s = id *)
    (* __g |- V1[s] : __l *)
    (* Uni or other cases should be impossible *)
    (* createAtomConst (__g, c) = (__u', (__v', s'))

       Invariant:
       If   S |- c : Pi {V1 .. Vn}. __v
       then . |- __u' = c @ (X1; .. Xn; Nil)
       and  . |- __u' : __v' [s']
    *)
    (* createAtomBVar (__g, k) = (__u', (__v', s'))

       Invariant:
       If   __g |- k : Pi {V1 .. Vn}. __v
       then . |- __u' = k @ (Xn; .. Xn; Nil)
       and  . |- __u' : __v' [s']
    *)
    (* createAtomProj (__g, #i(l), (__v, s)) = (__u', (__v', s'))

       Invariant:
       If   __g |- #i(l) : Pi {V1 .. Vn}. Va
       and  __g |- Pi {V1..Vn}. Va = __v[s] : type
       then . |- __u' = #i(l) @ (X1; .. Xn; Nil)
       and  . |- __u' : __v' [s']
    *)
    (* createEVarSub __g' = s

       Invariant:
       If   . |- __g' ctx
       then . |- s : __g' and s instantiates each x:A with an EVar . |- x : A

       Update: Always use empty context. Sat Dec  8 13:19:58 2001 -fp
    *)
    (* hack *)
    (* blockCases (__g, __Vs, B, (Gsome, piDecs), sc) =

       If __g |- __v[s] : type
          . |- Gsome ctx and Gsome |- piDecs decList
       then sc is called for any x:A in piDecs such thtat
            __g |- __v[s] = A[t] : type
            where t instantiates variable in Gsome with new EVars
    *)
    (* accounts for subordination *)
    (* . |- t : Gsome *)
    (* --cs Sun Dec  1 06:33:41 2002 *)
    (* __g |- t' : Gsome *)
    (* __g |- t : __g' and __g' |- ({_:__v'},piDecs) decList *)
    (* so __g |- __v'[t'] : type *)
    (* will trail *)
    (* will trail *)
    (* will trail *)
    (*     | lowerSplitW (__g, (I.Pi ((__d, P), __v), s), W, sc) =
        let
          val __d' = I.decSub (__d, s)
        in
          lowerSplit (I.Decl (__g, __d'), (__v, I.dot1 s), W, fn __u => sc (I.Lam (__d', __u)))
        end
      we assume that all EVars are lowere :-)
*)
    (* splitEVar (x, W, sc) = ()

       calls sc () for all cases, after instantiation of x
       W are the currently possible worlds
    *)
    (* GX = I.Null *)
    (* createSub (Psi) = s

       Invariant:
       If   Psi is a meta context
       then s = Xp...X1.id, all Xi are new EVars/LVars/MVars
       and  . |- s : Psi
    *)
    (* all EVars are global and lowered *)
    (* Psi0 |- t : Gsome *)
    (* . |- s : Psi0 *)
    (* --cs Sun Dec  1 06:34:00 2002 *)
    (* p > 0 *)
    (* mkCases __l F= __Ss

       Invariant:
       If   __l is a list of cases (Psi1, t1) .... (Psin, tn)
       and  Psii |- ti : Psi
       and  Psi  |- F formula
       then __Ss is a list of States S1 ... Sn
       and  Si = (Psii, Fi)
       where  Psii |- Fi = F [ti]  formula
    *)
    (* split S = S1 ... Sn

       Invariant:
       If   S = (P |> F)
       then Si = (Pi |> Fi)
       s.t. there exists substitution si
            and  Pi |- si : P
            and  Pi |- Fi = F[si]
            and  for every __g |- t : P,

                 there ex. an i among 1..n
                 and a substitution t',
                 s.t. __g |- t' : Pi
                 and  t = t' [si]
    *)
    (* splitXs (__g, i) (__Xs, F, W, sc) = __Os
           Invariant:
           If   Psi is a CONTEXT
           and  __g ~ Psi a context,
           and  __g |- i : __v
           and  Psi |- F formula
           and  __Xs are all logic variables
           then __Os is a list of splitting operators
        *)
    (* returns a list of operators *)
    (*            val I.Dec (Some s, _) = I.ctxLookup (__g, i) *)
    (* . |- t :: Psi *)
    (* apply (Op) = Sl'

       Invariant:
       If   Op = (_, Sl)
       then Sl' = Sl

       Side effect: If Sl contains inactive states, an exception is raised
    *)
    (* trailing required -cs Thu Apr 22 12:05:04 2004 *)
    type nonrec operator = __Operator
    let expand = expand
    let apply = apply
    let menu = menu
  end ;;
