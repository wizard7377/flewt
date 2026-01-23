module type SPLIT  =
  sig
    module State : STATE
    exception Error of string 
    type nonrec operator
    val expand : State.focus_ -> operator list
    val apply : operator -> unit
    val menu : operator -> string
  end


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
    type operator_ =
      | Split of (T.prg_ option ref * T.prg_ * string) 
    let rec weaken =
      begin function
      | (I.Null, a) -> I.id
      | (Decl (g'_, (Dec (name, v_) as d_)), a) ->
          let w' = weaken (g'_, a) in
          if Subordinate.belowEq ((I.targetFam v_), a)
          then begin I.dot1 w' end else begin I.comp (w', I.shift) end end
let rec createEVar (g_, v_) =
  let w = weaken (g_, (I.targetFam v_)) in
  let iw = Whnf.invert w in
  let g'_ = Whnf.strengthen (iw, g_) in
  let x'_ = I.newEVar (g'_, (I.EClo (v_, iw))) in
  let x_ = I.EClo (x'_, w) in ((x_)
    (* G |- V : L *)(* G  |- w  : G'    *)
    (* G' |- iw : G     *)(* G' |- X' : V[iw] *)
    (* G  |- X  : V     *))
let rec instEVars (vs_, p, XsRev) = instEVarsW ((Whnf.whnf vs_), p, XsRev)
let rec instEVarsW =
  begin function
  | (vs_, 0, XsRev) -> (vs_, XsRev)
  | ((Pi ((Dec (xOpt, v1_), _), v2_), s), p, XsRev) ->
      let x1_ = I.newEVar (I.Null, (I.EClo (v1_, s))) in
      ((instEVars
          ((v2_, (I.Dot ((I.Exp x1_), s))), (p - 1), ((Some x1_) :: XsRev)))
        (* p > 0 *)(* all EVars are global *))
  | ((Pi ((BDec (_, (l, t)), _), v2_), s), p, XsRev) ->
      let l1_ = I.newLVar ((I.Shift 0), (l, (I.comp (t, s)))) in
      ((instEVars
          ((v2_, (I.Dot ((I.Block l1_), s))), (p - 1), (None :: XsRev)))
        (* p > 0 *)(* --cs Sun Dec  1 06:33:27 2002 *)) end
(* . |- s : G0 *)(* G0 |- t : Gsome *)
let (caseList : (T.dec_ I.ctx_ * T.sub_) list ref) = ref []
let rec resetCases () = caseList := []
let rec addCase (Psi, t) = (!) ((::) (caseList := (Psi, t))) caseList
let rec getCases () = !caseList
let rec createEVarSpine (g_, vs_) = createEVarSpineW (g_, (Whnf.whnf vs_))
let rec createEVarSpineW =
  begin function
  | (g_, ((Root _, s) as vs_)) -> (I.Nil, vs_)
  | (g_, (Pi (((Dec (_, v1_) as d_), _), v2_), s)) ->
      let x_ = createEVar (g_, (I.EClo (v1_, s))) in
      let (s_, vs_) = createEVarSpine (g_, (v2_, (I.Dot ((I.Exp x_), s)))) in
      ((((I.App (x_, s_)), vs_))(* G |- V1[s] : L *)) end
(* s = id *)
let rec createAtomConst (g_, (Const cid as h_)) =
  let v_ = I.constType cid in
  let (s_, vs_) = createEVarSpine (g_, (v_, I.id)) in
  ((I.Root (h_, s_)), vs_)
let rec createAtomBVar (g_, k) =
  let Dec (_, v_) = I.ctxDec (g_, k) in
  let (s_, vs_) = createEVarSpine (g_, (v_, I.id)) in
  ((I.Root ((I.BVar k), s_)), vs_)
let rec createAtomProj (g_, h_, (v_, s)) =
  let (s_, vs'_) = createEVarSpine (g_, (v_, s)) in ((I.Root (h_, s_)), vs'_)
let rec constCases =
  begin function
  | (g_, vs_, [], sc) -> ()
  | (g_, vs_, (Const c)::sgn', sc) ->
      let (u_, vs'_) = createAtomConst (g_, (I.Const c)) in
      let _ =
        CSManager.trail
          (begin function
           | () -> if Unify.unifiable (g_, vs_, vs'_) then begin sc u_ end
               else begin () end end) in
constCases (g_, vs_, sgn', sc) end
let rec paramCases =
  begin function
  | (g_, vs_, 0, sc) -> ()
  | (g_, vs_, k, sc) ->
      let (u_, vs'_) = createAtomBVar (g_, k) in
      let _ =
        CSManager.trail
          (begin function
           | () -> if Unify.unifiable (g_, vs_, vs'_) then begin sc u_ end
               else begin () end end) in
paramCases (g_, vs_, (k - 1), sc) end
let rec createEVarSub =
  begin function
  | I.Null -> I.id
  | Decl (g'_, (Dec (_, v_) as d_)) ->
      let s = createEVarSub g'_ in
      let v'_ = I.EClo (v_, s) in
      let x_ = I.newEVar (I.Null, v'_) in I.Dot ((I.Exp x_), s) end
let rec blockName cid = I.conDecName (I.sgnLookup cid)
let rec blockCases (g_, vs_, cid, (Gsome, piDecs), sc) =
  let t = createEVarSub Gsome in
  let sk = I.Shift (I.ctxLength g_) in
  let t' = I.comp (t, sk) in
  let lvar = I.newLVar (sk, (cid, t')) in
  ((blockCases' (g_, vs_, (lvar, 1), (t', piDecs), sc))
    (* accounts for subordination *)(* . |- t : Gsome *)
    (* --cs Sun Dec  1 06:33:41 2002 *)(* G |- t' : Gsome *))
let rec blockCases' =
  begin function
  | (g_, vs_, (lvar, i), (t, []), sc) -> ()
  | (g_, vs_, (lvar, i), (t, (Dec (_, v'_))::piDecs), sc) ->
      let (u_, vs'_) = createAtomProj (g_, (I.Proj (lvar, i)), (v'_, t)) in
      let _ =
        CSManager.trail
          (begin function
           | () -> if Unify.unifiable (g_, vs_, vs'_) then begin sc u_ end
               else begin () end end) in
let t' = I.Dot ((I.Exp (I.Root ((I.Proj (lvar, i)), I.Nil))), t) in
((blockCases' (g_, vs_, (lvar, (i + 1)), (t', piDecs), sc))
  (* G |- t : G' and G' |- ({_:V'},piDecs) decList *)
  (* so G |- V'[t'] : type *)) end
let rec worldCases =
  begin function
  | (g_, vs_, Worlds [], sc) -> ()
  | (g_, vs_, Worlds (cid::cids), sc) ->
      (begin blockCases (g_, vs_, cid, (I.constBlock cid), sc);
       worldCases (g_, vs_, (T.Worlds cids), sc) end) end
let rec lowerSplit (g_, vs_, w_, sc) =
  lowerSplitW (g_, (Whnf.whnf vs_), w_, sc)
let rec lowerSplitW (g_, ((Root (Const a, _), s) as vs_), w_, sc) =
  let _ = constCases (g_, vs_, (Index.lookup a), sc) in
  let _ = paramCases (g_, vs_, (I.ctxLength g_), sc) in
  let _ = worldCases (g_, vs_, w_, sc) in ((())
    (* will trail *)(* will trail *)
    (* will trail *))
let rec splitEVar ((EVar (_, GX, v_, _) as x_), w_, sc) =
  lowerSplit
    (I.Null, (v_, I.id), w_,
      (begin function
       | u_ ->
           if Unify.unifiable (I.Null, (x_, I.id), (u_, I.id))
           then begin sc () end else begin () end end))(* GX = I.Null *)
let rec createSub =
  begin function
  | I.Null -> T.id
  | Decl (Psi, UDec (Dec (xOpt, v1_))) ->
      let t' = createSub Psi in
      let x_ =
        I.newEVar (I.Null, (I.EClo (Whnf.whnf (v1_, (T.coerceSub t'))))) in
      ((T.Dot ((T.Exp x_), t'))
        (* all EVars are global and lowered *))
  | Decl (Psi, UDec (BDec (_, (l, s)))) ->
      let t' = createSub Psi in
      let l_ = I.newLVar ((I.Shift 0), (l, (I.comp (s, (T.coerceSub t'))))) in
      ((T.Dot ((T.Block l_), t'))
        (* --cs Sun Dec  1 06:34:00 2002 *))
  | Decl (Psi, PDec (_, f_, TC1, TC2)) ->
      let t' = createSub Psi in
      let y_ = T.newEVarTC (I.Null, (T.FClo (f_, t')), TC1, TC2) in
      ((T.Dot ((T.Prg y_), t'))(* p > 0 *)) end(* . |- s : Psi0 *)
(* Psi0 |- t : Gsome *)
let rec mkCases =
  begin function
  | ([], f_) -> []
  | ((Psi, t)::cs, f_) ->
      let x_ = T.newEVar (Psi, (T.FClo (f_, t))) in
      (::) (Psi, t, x_) mkCases (cs, f_) end
let rec split (Focus (EVar (Psi, r, f_, None, None, _), w_)) =
  let rec splitXs arg__0 arg__1 =
    begin match (arg__0, arg__1) with
    | ((g_, i), ([], _, _, _)) -> []
    | ((g_, i), ((x_)::xs_, f_, w_, sc)) ->
        let _ =
          if !Global.chatter >= 6
          then
            begin print
                    (((^) "Split " Print.expToString (I.Null, x_)) ^ ".\n") end
          else begin () end in
  let os_ = splitXs (g_, (i + 1)) (xs_, f_, w_, sc) in
  let _ = resetCases () in
  let s = Print.expToString (g_, x_) in
  let os'_ =
    begin try
            begin splitEVar (x_, w_, sc);
            (Split (r, (T.Case (T.Cases (mkCases ((getCases ()), f_)))), s))
              :: os_ end
    with
    | Error constrs ->
        (begin if !Global.chatter >= 6
               then
                 begin print
                         (((^) "Inactive split:\n" Print.cnstrsToString
                             constrs)
                            ^ "\n") end
         else begin () end;
    os_ end) end in
  ((os'_)
    (* returns a list of operators *)(*            val I.Dec (SOME s, _) = I.ctxLookup (G, i) *)) end in
let t = createSub Psi in
let xs_ = State.collectLFSub t in
let rec init () = addCase (Abstract.abstractTomegaSub t) in
let g_ = T.coerceCtx Psi in
let os_ = splitXs (g_, 1) (xs_, f_, w_, init) in ((os_)
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
let rec expand (Focus (EVar (Psi, r, f_, None, None, _), w_) as s_) =
  if Abstract.closedCTX Psi then begin split s_ end else begin [] end
let rec apply (Split (r, p_, s)) = (:=) r Some p_
let rec menu (Split (_, _, s)) = "Split " ^ s
type nonrec operator = operator_
let expand = expand
let apply = apply
let menu = menu end
