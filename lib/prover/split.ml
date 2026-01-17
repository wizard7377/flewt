
module type SPLIT  =
  sig
    module State :
    ((STATE)(* Splitting: Version 1.4 *)(* Author: Carsten Schuermann *)
    (*! structure IntSyn : INTSYN !*)(*! structure Tomega : TOMEGA !*))
    exception Error of string 
    type nonrec operator
    val expand : State.__Focus -> operator list
    val apply : operator -> unit
    val menu : operator -> string
  end;;




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
                     module Subordinate :
                     ((SUBORDINATE)(* State definition for Proof Search *)
                     (* Author: Carsten Schuermann *)
                     (*! structure IntSyn' : INTSYN !*)
                     (*! structure Tomega' : TOMEGA !*)
                     (*! sharing Tomega'.IntSyn = IntSyn' !*)(*! sharing State'.IntSyn = IntSyn' !*)
                     (*! sharing State'.Tomega = Tomega' !*)
                     (*! sharing Whnf.IntSyn = IntSyn' !*)
                     (*! sharing Unify.IntSyn = IntSyn' !*)
                     (*! sharing Constraints.IntSyn = IntSyn' !*)
                     (*! sharing Abstract.IntSyn = IntSyn' !*)(*! sharing Abstract.Tomega = Tomega' !*)
                     (*! sharing Index.IntSyn = IntSyn' !*)
                     (*! sharing Print.IntSyn = IntSyn' !*)
                     (*! sharing TypeCheck.IntSyn = IntSyn' !*))
                   end) : SPLIT =
  struct
    module State =
      ((State')(*! sharing Subordinate.IntSyn = IntSyn' !*)
      (*! structure IntSyn = IntSyn' !*)(*! structure Tomega = Tomega' !*))
    exception Error of string 
    module T = Tomega
    module I = IntSyn
    module S = State'
    type __Operator =
      | Split of (T.__Prg option ref * T.__Prg * string) 
    let rec weaken =
      function
      | (I.Null, a) -> I.id
      | (Decl (g', (Dec (name, V) as D)), a) ->
          let w' = weaken (g', a) in
          if Subordinate.belowEq ((I.targetFam V), a)
          then I.dot1 w'
          else I.comp (w', I.shift)
    let rec createEVar (g, V) =
      let w = weaken (g, (I.targetFam V)) in
      let iw = Whnf.invert w in
      let g' = Whnf.strengthen (iw, g) in
      let X' = I.newEVar (g', (I.EClo (V, iw))) in
      let X = I.EClo (X', w) in X
    let rec instEVars (Vs, p, XsRev) = instEVarsW ((Whnf.whnf Vs), p, XsRev)
    let rec instEVarsW =
      function
      | (Vs, 0, XsRev) -> (Vs, XsRev)
      | ((Pi ((Dec (xOpt, V1), _), V2), s), p, XsRev) ->
          let X1 = I.newEVar (I.Null, (I.EClo (V1, s))) in
          instEVars
            ((V2, (I.Dot ((I.Exp X1), s))), (p - 1), ((SOME X1) :: XsRev))
      | ((Pi ((BDec (_, (l, t)), _), V2), s), p, XsRev) ->
          let L1 = I.newLVar ((I.Shift 0), (l, (I.comp (t, s)))) in
          instEVars
            ((V2, (I.Dot ((I.Block L1), s))), (p - 1), (NONE :: XsRev))
    let (caseList : (T.__Dec I.__Ctx * T.__Sub) list ref) = ref nil
    let rec resetCases () = caseList := nil
    let rec addCase (Psi, t) = (!) ((::) (caseList := (Psi, t))) caseList
    let rec getCases () = !caseList
    let rec createEVarSpine (g, Vs) = createEVarSpineW (g, (Whnf.whnf Vs))
    let rec createEVarSpineW =
      function
      | (g, ((Root _, s) as Vs)) -> (I.Nil, Vs)
      | (g, (Pi (((Dec (_, V1) as D), _), V2), s)) ->
          let X = createEVar (g, (I.EClo (V1, s))) in
          let (S, Vs) = createEVarSpine (g, (V2, (I.Dot ((I.Exp X), s)))) in
          ((I.App (X, S)), Vs)
    let rec createAtomConst (g, (Const cid as H)) =
      let V = I.constType cid in
      let (S, Vs) = createEVarSpine (g, (V, I.id)) in ((I.Root (H, S)), Vs)
    let rec createAtomBVar (g, k) =
      let Dec (_, V) = I.ctxDec (g, k) in
      let (S, Vs) = createEVarSpine (g, (V, I.id)) in
      ((I.Root ((I.BVar k), S)), Vs)
    let rec createAtomProj (g, H, (V, s)) =
      let (S, Vs') = createEVarSpine (g, (V, s)) in ((I.Root (H, S)), Vs')
    let rec constCases =
      function
      | (g, Vs, nil, sc) -> ()
      | (g, Vs, (Const c)::sgn', sc) ->
          let (U, Vs') = createAtomConst (g, (I.Const c)) in
          let _ =
            CSManager.trail
              (function
               | () -> if Unify.unifiable (g, Vs, Vs') then sc U else ()) in
          constCases (g, Vs, sgn', sc)
    let rec paramCases =
      function
      | (g, Vs, 0, sc) -> ()
      | (g, Vs, k, sc) ->
          let (U, Vs') = createAtomBVar (g, k) in
          let _ =
            CSManager.trail
              (function
               | () -> if Unify.unifiable (g, Vs, Vs') then sc U else ()) in
          paramCases (g, Vs, (k - 1), sc)
    let rec createEVarSub =
      function
      | I.Null -> I.id
      | Decl (g', (Dec (_, V) as D)) ->
          let s = createEVarSub g' in
          let V' = I.EClo (V, s) in
          let X = I.newEVar (I.Null, V') in I.Dot ((I.Exp X), s)
    let rec blockName cid = I.conDecName (I.sgnLookup cid)
    let rec blockCases (g, Vs, cid, (Gsome, piDecs), sc) =
      let t = createEVarSub Gsome in
      let sk = I.Shift (I.ctxLength g) in
      let t' = I.comp (t, sk) in
      let lvar = I.newLVar (sk, (cid, t')) in
      blockCases' (g, Vs, (lvar, 1), (t', piDecs), sc)
    let rec blockCases' =
      function
      | (g, Vs, (lvar, i), (t, nil), sc) -> ()
      | (g, Vs, (lvar, i), (t, (Dec (_, V'))::piDecs), sc) ->
          let (U, Vs') = createAtomProj (g, (I.Proj (lvar, i)), (V', t)) in
          let _ =
            CSManager.trail
              (function
               | () -> if Unify.unifiable (g, Vs, Vs') then sc U else ()) in
          let t' = I.Dot ((I.Exp (I.Root ((I.Proj (lvar, i)), I.Nil))), t) in
          blockCases' (g, Vs, (lvar, (i + 1)), (t', piDecs), sc)
    let rec worldCases =
      function
      | (g, Vs, Worlds nil, sc) -> ()
      | (g, Vs, Worlds (cid::cids), sc) ->
          (blockCases (g, Vs, cid, (I.constBlock cid), sc);
           worldCases (g, Vs, (T.Worlds cids), sc))
    let rec lowerSplit (g, Vs, W, sc) =
      lowerSplitW (g, (Whnf.whnf Vs), W, sc)
    let rec lowerSplitW (g, ((Root (Const a, _), s) as Vs), W, sc) =
      let _ = constCases (g, Vs, (Index.lookup a), sc) in
      let _ = paramCases (g, Vs, (I.ctxLength g), sc) in
      let _ = worldCases (g, Vs, W, sc) in ()
    let rec splitEVar ((EVar (_, GX, V, _) as X), W, sc) =
      lowerSplit
        (I.Null, (V, I.id), W,
          (function
           | U ->
               if Unify.unifiable (I.Null, (X, I.id), (U, I.id))
               then sc ()
               else ()))
    let rec createSub =
      function
      | I.Null -> T.id
      | Decl (Psi, UDec (Dec (xOpt, V1))) ->
          let t' = createSub Psi in
          let X =
            I.newEVar (I.Null, (I.EClo (Whnf.whnf (V1, (T.coerceSub t'))))) in
          T.Dot ((T.Exp X), t')
      | Decl (Psi, UDec (BDec (_, (l, s)))) ->
          let t' = createSub Psi in
          let L =
            I.newLVar ((I.Shift 0), (l, (I.comp (s, (T.coerceSub t'))))) in
          T.Dot ((T.Block L), t')
      | Decl (Psi, PDec (_, F, TC1, TC2)) ->
          let t' = createSub Psi in
          let Y = T.newEVarTC (I.Null, (T.FClo (F, t')), TC1, TC2) in
          T.Dot ((T.Prg Y), t')
    let rec mkCases =
      function
      | (nil, F) -> nil
      | ((Psi, t)::cs, F) ->
          let X = T.newEVar (Psi, (T.FClo (F, t))) in
          (::) (Psi, t, X) mkCases (cs, F)
    let rec split (Focus (EVar (Psi, r, F, NONE, NONE, _), W)) =
      let splitXs arg__0 arg__1 =
        match (arg__0, arg__1) with
        | ((g, i), (nil, _, _, _)) -> nil
        | ((g, i), ((X)::Xs, F, W, sc)) ->
            let _ =
              if (!Global.chatter) >= 6
              then
                print (((^) "Split " Print.expToString (I.Null, X)) ^ ".\n")
              else () in
            let Os = splitXs (g, (i + 1)) (Xs, F, W, sc) in
            let _ = resetCases () in
            let s = Print.expToString (g, X) in
            let Os' =
              try
                splitEVar (X, W, sc);
                (Split
                   (r, (T.Case (T.Cases (mkCases ((getCases ()), F)))), s))
                  :: Os
              with
              | Error constrs ->
                  (if (!Global.chatter) >= 6
                   then
                     print
                       (((^) "Inactive split:\n" Print.cnstrsToString constrs)
                          ^ "\n")
                   else ();
                   Os) in
            Os' in
      let t = createSub Psi in
      let Xs = State.collectLFSub t in
      let init () = addCase (Abstract.abstractTomegaSub t) in
      let g = T.coerceCtx Psi in
      let Os = splitXs (g, 1) (Xs, F, W, init) in Os
    let rec expand (Focus (EVar (Psi, r, F, NONE, NONE, _), W) as S) =
      if Abstract.closedCTX Psi then split S else []
    let rec apply (Split (r, P, s)) = (:=) r SOME P
    let rec menu (Split (_, _, s)) = "Split " ^ s
    type nonrec operator =
      ((__Operator)(* trailing required -cs Thu Apr 22 12:05:04 2004 *)
      (* apply (Op) = Sl'

       Invariant:
       If   Op = (_, Sl)
       then Sl' = Sl

       Side effect: If Sl contains inactive states, an exception is raised
    *)
      (* . |- t :: Psi *)(*            val I.Dec (SOME s, _) = I.ctxLookup (g, i) *)
      (* returns a list of operators *)(* splitXs (g, i) (Xs, F, W, sc) = Os
           Invariant:
           If   Psi is a CONTEXT
           and  g ~ Psi a context,
           and  g |- i : V
           and  Psi |- F formula
           and  Xs are all logic variables
           then Os is a list of splitting operators
        *)
      (* split S = s1 ... Sn

       Invariant:
       If   S = (P |> F)
       then Si = (Pi |> Fi)
       s.t. there exists substitution si
            and  Pi |- si : P
            and  Pi |- Fi = F[si]
            and  for every g |- t : P,

                 there ex. an i among 1..n
                 and a substitution t',
                 s.t. g |- t' : Pi
                 and  t = t' [si]
    *)
      (* mkCases L F= Ss

       Invariant:
       If   L is a list of cases (Psi1, t1) .... (Psin, tn)
       and  Psii |- ti : Psi
       and  Psi  |- F formula
       then Ss is a list of States s1 ... Sn
       and  Si = (Psii, Fi)
       where  Psii |- Fi = F [ti]  formula
    *)
      (* p > 0 *)(* --cs Sun Dec  1 06:34:00 2002 *)
      (* . |- s : Psi0 *)(* Psi0 |- t : Gsome *)
      (* all EVars are global and lowered *)(* createSub (Psi) = s

       Invariant:
       If   Psi is a meta context
       then s = Xp...X1.id, all Xi are new EVars/LVars/MVars
       and  . |- s : Psi
    *)
      (* GX = I.Null *)(* splitEVar (X, W, sc) = ()

       calls sc () for all cases, after instantiation of X
       W are the currently possible worlds
    *)
      (*     | lowerSplitW (g, (I.Pi ((D, P), V), s), W, sc) =
        let
          val D' = I.decSub (D, s)
        in
          lowerSplit (I.Decl (g, D'), (V, I.dot1 s), W, fn U => sc (I.Lam (D', U)))
        end
      we assume that all EVars are lowere :-)
*)
      (* will trail *)(* will trail *)
      (* will trail *)(* so g |- V'[t'] : type *)
      (* g |- t : g' and g' |- ({_:V'},piDecs) decList *)
      (* g |- t' : Gsome *)(* --cs Sun Dec  1 06:33:41 2002 *)
      (* . |- t : Gsome *)(* accounts for subordination *)
      (* blockCases (g, Vs, B, (Gsome, piDecs), sc) =

       If g |- V[s] : type
          . |- Gsome ctx and Gsome |- piDecs decList
       then sc is called for any x:A in piDecs such thtat
            g |- V[s] = A[t] : type
            where t instantiates variable in Gsome with new EVars
    *)
      (* hack *)(* createEVarSub g' = s

       Invariant:
       If   . |- g' ctx
       then . |- s : g' and s instantiates each x:A with an EVar . |- X : A

       Update: Always use empty context. Sat Dec  8 13:19:58 2001 -fp
    *)
      (* createAtomProj (g, #i(l), (V, s)) = (U', (V', s'))

       Invariant:
       If   g |- #i(l) : Pi {V1 .. Vn}. Va
       and  g |- Pi {V1..Vn}. Va = V[s] : type
       then . |- U' = #i(l) @ (X1; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
      (* createAtomBVar (g, k) = (U', (V', s'))

       Invariant:
       If   g |- k : Pi {V1 .. Vn}. V
       then . |- U' = k @ (Xn; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
      (* createAtomConst (g, c) = (U', (V', s'))

       Invariant:
       If   S |- c : Pi {V1 .. Vn}. V
       then . |- U' = c @ (X1; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
      (* Uni or other cases should be impossible *)(* g |- V1[s] : L *)
      (* s = id *)(* createEVarSpine (g, (V, s)) = (S', (V', s'))

       Invariant:
       If   g |- s : G1   and  G1 |- V = Pi {V1 .. Vn}. W : L
       and  G1, V1 .. Vn |- W atomic
       then g |- s' : G2  and  G2 |- V' : L
       and  S = X1; ...; Xn; Nil
       and  g |- W [1.2...n. s o ^n] = V' [s']
       and  g |- S : V [s] >  V' [s']
    *)
      (* caseList is a list of possibilities for a variables
       to be split.  Maintained as a mutable reference so it
       can be updated in the success continuation.
    *)
      (* --cs Sun Dec  1 06:33:27 2002 *)(* p > 0 *)
      (* . |- s : G0 *)(* G0 |- t : Gsome *)(* all EVars are global *)
      (* p > 0 *)(* instEVars ({x1:V1}...{xp:Vp} V, p, nil) = (V[s], [X1,...,Xn])
       where . |- s : {x1:V1}...{xp:Vp}
       and s = Xp...X1.id, all Xi are new EVars
    *)
      (* g  |- X  : V     *)(* g' |- X' : V[iw] *)
      (* g' |- iw : g     *)(* g  |- w  : g'    *)
      (* g |- V : L *)(* createEVar (g, V) = X[w] where g |- X[w] : V

       Invariant:
       If g |- V : L
       then g |- X[w] : V
    *)
      (*
      | weaken (I.Decl (g', D as I.BDec _), a) =
           I.dot1 (weaken (g', a))
      *)
      (* Sun Dec 16 10:42:05 2001 -fp !!! *)(* added next case, probably should not arise *)
      (* weaken (g, a) = w'

       Invariant:
       If   a is a type family
       then g |- w' : g'
       and  forall x:A in g'  A subordinate to a
     *))
    let expand = expand
    let apply = apply
    let menu = menu
  end ;;
