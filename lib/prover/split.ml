
module type SPLIT  =
  sig
    module State : STATE
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
                     module Subordinate : SUBORDINATE
                   end) : SPLIT =
  struct
    module State = State'
    exception Error of string 
    module T = Tomega
    module I = IntSyn
    module S = State'
    type __Operator =
      | Split of (T.__Prg option ref * T.__Prg * string) 
    let rec weaken __0__ __1__ =
      match (__0__, __1__) with
      | (I.Null, a) -> I.id
      | (Decl (__G', (Dec (name, __V) as D)), a) ->
          let w' = weaken (__G', a) in
          if Subordinate.belowEq ((I.targetFam __V), a)
          then I.dot1 w'
          else I.comp (w', I.shift)
    let rec createEVar (__G) (__V) =
      let w = weaken (__G, (I.targetFam __V)) in
      let iw = Whnf.invert w in
      let __G' = Whnf.strengthen (iw, __G) in
      let __X' = I.newEVar (__G', (I.EClo (__V, iw))) in
      let __X = I.EClo (__X', w) in ((__X)
        (* G |- V : L *)(* G  |- w  : G'    *)(* G' |- iw : G     *)
        (* G' |- X' : V[iw] *)(* G  |- X  : V     *))
    let rec instEVars (__Vs) p (XsRev) =
      instEVarsW ((Whnf.whnf __Vs), p, XsRev)
    let rec instEVarsW __2__ __3__ __4__ =
      match (__2__, __3__, __4__) with
      | (__Vs, 0, XsRev) -> (__Vs, XsRev)
      | ((Pi ((Dec (xOpt, __V1), _), __V2), s), p, XsRev) ->
          let __X1 = I.newEVar (I.Null, (I.EClo (__V1, s))) in
          ((instEVars
              ((__V2, (I.Dot ((I.Exp __X1), s))), (p - 1),
                ((Some __X1) :: XsRev)))
            (* p > 0 *)(* all EVars are global *))
      | ((Pi ((BDec (_, (l, t)), _), __V2), s), p, XsRev) ->
          let __L1 = I.newLVar ((I.Shift 0), (l, (I.comp (t, s)))) in
          ((instEVars
              ((__V2, (I.Dot ((I.Block __L1), s))), (p - 1), (NONE :: XsRev)))
            (* p > 0 *)(* --cs Sun Dec  1 06:33:27 2002 *))
      (* . |- s : G0 *)(* G0 |- t : Gsome *)
    let (caseList : (T.__Dec I.__Ctx * T.__Sub) list ref) = ref nil
    let rec resetCases () = caseList := nil
    let rec addCase (Psi) t = (!) ((::) (caseList := (Psi, t))) caseList
    let rec getCases () = !caseList
    let rec createEVarSpine (__G) (__Vs) =
      createEVarSpineW (__G, (Whnf.whnf __Vs))
    let rec createEVarSpineW __5__ __6__ =
      match (__5__, __6__) with
      | (__G, ((Root _, s) as Vs)) -> (I.Nil, __Vs)
      | (__G, (Pi (((Dec (_, __V1) as D), _), __V2), s)) ->
          let __X = createEVar (__G, (I.EClo (__V1, s))) in
          let (__S, __Vs) =
            createEVarSpine (__G, (__V2, (I.Dot ((I.Exp __X), s)))) in
          ((((I.App (__X, __S)), __Vs))(* G |- V1[s] : L *))
      (* s = id *)
    let rec createAtomConst (__G) (Const cid as H) =
      let __V = I.constType cid in
      let (__S, __Vs) = createEVarSpine (__G, (__V, I.id)) in
      ((I.Root (__H, __S)), __Vs)
    let rec createAtomBVar (__G) k =
      let Dec (_, __V) = I.ctxDec (__G, k) in
      let (__S, __Vs) = createEVarSpine (__G, (__V, I.id)) in
      ((I.Root ((I.BVar k), __S)), __Vs)
    let rec createAtomProj (__G) (__H) (__V, s) =
      let (__S, __Vs') = createEVarSpine (__G, (__V, s)) in
      ((I.Root (__H, __S)), __Vs')
    let rec constCases __7__ __8__ __9__ __10__ =
      match (__7__, __8__, __9__, __10__) with
      | (__G, __Vs, nil, sc) -> ()
      | (__G, __Vs, (Const c)::sgn', sc) ->
          let (__U, __Vs') = createAtomConst (__G, (I.Const c)) in
          let _ =
            CSManager.trail
              (fun () ->
                 if Unify.unifiable (__G, __Vs, __Vs') then sc __U else ()) in
          constCases (__G, __Vs, sgn', sc)
    let rec paramCases __11__ __12__ __13__ __14__ =
      match (__11__, __12__, __13__, __14__) with
      | (__G, __Vs, 0, sc) -> ()
      | (__G, __Vs, k, sc) ->
          let (__U, __Vs') = createAtomBVar (__G, k) in
          let _ =
            CSManager.trail
              (fun () ->
                 if Unify.unifiable (__G, __Vs, __Vs') then sc __U else ()) in
          paramCases (__G, __Vs, (k - 1), sc)
    let rec createEVarSub =
      function
      | I.Null -> I.id
      | Decl (__G', (Dec (_, __V) as D)) ->
          let s = createEVarSub __G' in
          let __V' = I.EClo (__V, s) in
          let __X = I.newEVar (I.Null, __V') in I.Dot ((I.Exp __X), s)
    let rec blockName cid = I.conDecName (I.sgnLookup cid)
    let rec blockCases (__G) (__Vs) cid (Gsome, piDecs) sc =
      let t = createEVarSub Gsome in
      let sk = I.Shift (I.ctxLength __G) in
      let t' = I.comp (t, sk) in
      let lvar = I.newLVar (sk, (cid, t')) in
      ((blockCases' (__G, __Vs, (lvar, 1), (t', piDecs), sc))
        (* accounts for subordination *)(* . |- t : Gsome *)
        (* --cs Sun Dec  1 06:33:41 2002 *)(* G |- t' : Gsome *))
    let rec blockCases' __15__ __16__ __17__ __18__ __19__ =
      match (__15__, __16__, __17__, __18__, __19__) with
      | (__G, __Vs, (lvar, i), (t, nil), sc) -> ()
      | (__G, __Vs, (lvar, i), (t, (Dec (_, __V'))::piDecs), sc) ->
          let (__U, __Vs') =
            createAtomProj (__G, (I.Proj (lvar, i)), (__V', t)) in
          let _ =
            CSManager.trail
              (fun () ->
                 if Unify.unifiable (__G, __Vs, __Vs') then sc __U else ()) in
          let t' = I.Dot ((I.Exp (I.Root ((I.Proj (lvar, i)), I.Nil))), t) in
          ((blockCases' (__G, __Vs, (lvar, (i + 1)), (t', piDecs), sc))
            (* G |- t : G' and G' |- ({_:V'},piDecs) decList *)(* so G |- V'[t'] : type *))
    let rec worldCases __20__ __21__ __22__ __23__ =
      match (__20__, __21__, __22__, __23__) with
      | (__G, __Vs, Worlds nil, sc) -> ()
      | (__G, __Vs, Worlds (cid::cids), sc) ->
          (blockCases (__G, __Vs, cid, (I.constBlock cid), sc);
           worldCases (__G, __Vs, (T.Worlds cids), sc))
    let rec lowerSplit (__G) (__Vs) (__W) sc =
      lowerSplitW (__G, (Whnf.whnf __Vs), __W, sc)
    let rec lowerSplitW (__G) ((Root (Const a, _), s) as Vs) (__W) sc =
      let _ = constCases (__G, __Vs, (Index.lookup a), sc) in
      let _ = paramCases (__G, __Vs, (I.ctxLength __G), sc) in
      let _ = worldCases (__G, __Vs, __W, sc) in ((())
        (* will trail *)(* will trail *)
        (* will trail *))
    let rec splitEVar (EVar (_, GX, __V, _) as X) (__W) sc =
      lowerSplit
        (I.Null, (__V, I.id), __W,
          (fun (__U) ->
             if Unify.unifiable (I.Null, (__X, I.id), (__U, I.id))
             then sc ()
             else ()))(* GX = I.Null *)
    let rec createSub =
      function
      | I.Null -> T.id
      | Decl (Psi, UDec (Dec (xOpt, __V1))) ->
          let t' = createSub Psi in
          let __X =
            I.newEVar (I.Null, (I.EClo (Whnf.whnf (__V1, (T.coerceSub t'))))) in
          ((T.Dot ((T.Exp __X), t'))
            (* all EVars are global and lowered *))
      | Decl (Psi, UDec (BDec (_, (l, s)))) ->
          let t' = createSub Psi in
          let __L =
            I.newLVar ((I.Shift 0), (l, (I.comp (s, (T.coerceSub t'))))) in
          ((T.Dot ((T.Block __L), t'))
            (* --cs Sun Dec  1 06:34:00 2002 *))
      | Decl (Psi, PDec (_, __F, TC1, TC2)) ->
          let t' = createSub Psi in
          let __Y = T.newEVarTC (I.Null, (T.FClo (__F, t')), TC1, TC2) in
          ((T.Dot ((T.Prg __Y), t'))(* p > 0 *))(* . |- s : Psi0 *)
      (* Psi0 |- t : Gsome *)
    let rec mkCases __24__ __25__ =
      match (__24__, __25__) with
      | (nil, __F) -> nil
      | ((Psi, t)::cs, __F) ->
          let __X = T.newEVar (Psi, (T.FClo (__F, t))) in
          (::) (Psi, t, __X) mkCases (cs, __F)
    let rec split (Focus (EVar (Psi, r, __F, NONE, NONE, _), __W)) =
      let rec splitXs __26__ __27__ __28__ __29__ __30__ __31__ =
        match (__26__, __27__, __28__, __29__, __30__, __31__) with
        | (__G, i, nil, _, _, _) -> nil
        | (__G, i, (__X)::__Xs, __F, __W, sc) ->
            let _ =
              if (!Global.chatter) >= 6
              then
                print
                  (((^) "Split " Print.expToString (I.Null, __X)) ^ ".\n")
              else () in
            let __Os = splitXs (__G, (i + 1)) (__Xs, __F, __W, sc) in
            let _ = resetCases () in
            let s = Print.expToString (__G, __X) in
            let __Os' =
              try
                splitEVar (__X, __W, sc);
                (Split
                   (r, (T.Case (T.Cases (mkCases ((getCases ()), __F)))), s))
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
            ((__Os')
              (* returns a list of operators *)(*            val I.Dec (Some s, _) = I.ctxLookup (G, i) *)) in
      let t = createSub Psi in
      let __Xs = State.collectLFSub t in
      let rec init () = addCase (Abstract.abstractTomegaSub t) in
      let __G = T.coerceCtx Psi in
      let __Os = splitXs (__G, 1) (__Xs, __F, __W, init) in ((__Os)
        (* splitXs (G, i) (Xs, F, W, sc) = Os
           Invariant:
           If   Psi is a CONTEXT
           and  G ~ Psi a context,
           and  G |- i : V
           and  Psi |- F formula
           and  Xs are all logic variables
           then Os is a list of splitting operators
        *)
        (* . |- t :: Psi *))
    let rec expand (Focus (EVar (Psi, r, __F, NONE, NONE, _), __W) as S) =
      if Abstract.closedCTX Psi then split __S else []
    let rec apply (Split (r, __P, s)) = (:=) r Some __P
    let rec menu (Split (_, _, s)) = "Split " ^ s
    type nonrec operator = __Operator
    let expand = expand
    let apply = apply
    let menu = menu
  end ;;
