module type MTPSPLITTING  =
  sig
    module StateSyn : STATESYN
    exception Error of string 
    type nonrec operator
    val expand : StateSyn.state_ -> operator list
    val applicable : operator -> bool
    val apply : operator -> StateSyn.state_ list
    val menu : operator -> string
    val index : operator -> int
    val compare : (operator * operator) -> order
  end


module MTPSplitting(MTPSplitting:sig
                                   module MTPGlobal : MTPGLOBAL
                                   module Global : GLOBAL
                                   module StateSyn' : STATESYN
                                   module Heuristic : HEURISTIC
                                   module MTPAbstract : MTPABSTRACT
                                   module MTPrint : MTPRINT
                                   module Names : NAMES
                                   module Conv : CONV
                                   module Whnf : WHNF
                                   module TypeCheck : TYPECHECK
                                   module Subordinate : SUBORDINATE
                                   module FunTypeCheck : FUNTYPECHECK
                                   module Index : INDEX
                                   module Print : PRINT
                                   module Unify : UNIFY
                                 end) : MTPSPLITTING =
  struct
    module StateSyn = StateSyn'
    exception Error of string 
    type 'a flag =
      | Active of 'a 
      | InActive 
    type operator_ =
      | Operator of ((StateSyn.state_ * int) * StateSyn.state_ flag list *
      Heuristic.index) 
    type nonrec operator = operator_
    module I = IntSyn
    module F = FunSyn
    module S = StateSyn
    module H = Heuristic
    let rec makeOperator =
      begin function
      | ((s_, k), l_, Splits n, g, i_, m, true) ->
          Operator
            ((s_, k), l_,
              { sd = n; ind = i_; c = (List.length l_); m; r = 1; p = (g + 1)
              })
      | ((s_, k), l_, Splits n, g, i_, m, false) ->
          Operator
            ((s_, k), l_,
              { sd = n; ind = i_; c = (List.length l_); m; r = 0; p = (g + 1)
              }) end(* non-recursive case *)(* recursive case *)
    let rec aux =
      begin function
      | (I.Null, I.Null) -> I.Null
      | (Decl (g_, d_), Decl (b_, Lemma _)) ->
          I.Decl ((aux (g_, b_)), (F.Prim d_))
      | ((Decl (_, d_) as g_), (Decl (_, Parameter (Some l)) as b_)) ->
          let LabelDec (name, _, g2_) = F.labelLookup l in
          let (Psi', g'_) = aux' (g_, b_, (List.length g2_)) in
          I.Decl (Psi', (F.Block (F.CtxBlock ((Some l), g'_)))) end
  let rec aux' =
    begin function
    | (g_, b_, 0) -> ((aux (g_, b_)), I.Null)
    | (Decl (g_, d_), Decl (b_, Parameter (Some _)), n) ->
        let (Psi', g'_) = aux' (g_, b_, (n - 1)) in
        (Psi', (I.Decl (g'_, d_))) end
let rec conv (gs_, gs'_) =
  let exception Conv  in
    let rec conv =
      begin function
      | ((I.Null, s), (I.Null, s')) -> (s, s')
      | ((Decl (g_, Dec (_, v_)), s), (Decl (g'_, Dec (_, v'_)), s')) ->
          let (s1, s1') = conv ((g_, s), (g'_, s')) in
          let (s2, s2') as ps = ((I.dot1 s1), (I.dot1 s1')) in
          if Conv.conv ((v_, s1), (v'_, s1')) then begin ps end
            else begin raise Conv end
      | _ -> raise Conv end in
begin try begin conv (gs_, gs'_); true end with | Conv -> false end
let rec createEVarSpine (g_, vs_) = createEVarSpineW (g_, (Whnf.whnf vs_))
let rec createEVarSpineW =
  begin function
  | (g_, ((Uni (I.Type), s) as vs_)) -> (I.Nil, vs_)
  | (g_, ((Root _, s) as vs_)) -> (I.Nil, vs_)
  | (g_, (Pi (((Dec (_, v1_) as d_), _), v2_), s)) ->
      let x_ = I.newEVar (g_, (I.EClo (v1_, s))) in
      let (s_, vs_) = createEVarSpine (g_, (v2_, (I.Dot ((I.Exp x_), s)))) in
      ((I.App (x_, s_)), vs_) end(* s = id *)(* s = id *)
let rec createAtomConst (g_, h_) =
  let cid = begin match h_ with | Const cid -> cid | Skonst cid -> cid end in
let v_ = I.constType cid in
let (s_, vs_) = createEVarSpine (g_, (v_, I.id)) in ((I.Root (h_, s_)), vs_)
let rec createAtomBVar (g_, k) =
  let Dec (_, v_) = I.ctxDec (g_, k) in
  let (s_, vs_) = createEVarSpine (g_, (v_, I.id)) in
  ((I.Root ((I.BVar k), s_)), vs_)
let rec someEVars =
  begin function
  | (g_, [], s) -> s
  | (g_, (Dec (_, v_))::l_, s) ->
      someEVars
        (g_, l_, (I.Dot ((I.Exp (I.newEVar (g_, (I.EClo (v_, s))))), s))) end
let rec maxNumberParams a =
  let rec maxNumberParams' n = if n < 0 then begin 0 end
    else begin
      (let LabelDec (name, g1_, g2_) = F.labelLookup n in
       let m' =
         foldr
           (begin function
            | (Dec (_, v_), m) ->
                if (I.targetFam v_) = a then begin m + 1 end else begin m end end)
         0 g2_ in
  (maxNumberParams' (n - 1)) + m') end in
maxNumberParams' ((F.labelSize ()) - 1)
let rec maxNumberLocalParams =
  begin function
  | (Pi ((Dec (_, v1_), _), v2_), a) ->
      let m = maxNumberLocalParams (v2_, a) in
      if (I.targetFam v1_) = a then begin m + 1 end else begin m end
  | (Root _, a) -> 0 end
let rec maxNumberConstCases a = List.length (Index.lookup a)
let rec maxNumberCases (v_, a) =
  (+) ((+) (maxNumberParams a) maxNumberLocalParams (v_, a))
    maxNumberConstCases a
let rec ctxSub =
  begin function
  | ([], s) -> []
  | ((d_)::g_, s) -> (::) (I.decSub (d_, s)) ctxSub (g_, (I.dot1 s)) end
let rec createTags =
  begin function
  | (0, l) -> I.Null
  | (n, l) -> I.Decl ((createTags ((n - 1), l)), (S.Parameter (Some l))) end
let rec createLemmaTags =
  begin function
  | I.Null -> I.Null
  | Decl (g_, d_) ->
      I.Decl ((createLemmaTags g_), (S.Lemma (S.Splits !MTPGlobal.maxSplit))) end
let rec constCases =
  begin function
  | (g_, vs_, [], abstract, ops) -> ops
  | (g_, vs_, (Const c)::Sgn, abstract, ops) ->
      let (u_, vs'_) = createAtomConst (g_, (I.Const c)) in
      constCases
        (g_, vs_, Sgn, abstract,
          (CSManager.trail
             (begin function
              | () ->
                  (begin try
                           if Unify.unifiable (g_, vs_, vs'_)
                           then begin (Active (abstract u_)) :: ops end
                           else begin ops end
              with | Error _ -> InActive :: ops end) end))) end
let rec paramCases =
  begin function
  | (g_, vs_, 0, abstract, ops) -> ops
  | (g_, vs_, k, abstract, ops) ->
      let (u_, vs'_) = createAtomBVar (g_, k) in
      paramCases
        (g_, vs_, (k - 1), abstract,
          (CSManager.trail
             (begin function
              | () ->
                  (begin try
                           if Unify.unifiable (g_, vs_, vs'_)
                           then begin (Active (abstract u_)) :: ops end
                           else begin ops end
              with | Error _ -> InActive :: ops end) end))) end
let rec constAndParamCases ops0 (c, g_, k, (v_, s'), abstract) =
  constCases
    (g_, (v_, s'), (Index.lookup c), abstract,
      (paramCases (g_, (v_, s'), k, abstract, ops0)))
let rec metaCases (d, ops0) (c, g_, k, vs_, abstract) =
  let g = I.ctxLength g_ in
  let rec select =
    begin function
    | (0, ops) -> ops
    | (d', ops) ->
        let n = (g - d') + 1 in
        let Dec (_, v_) = I.ctxDec (g_, n) in
        let ops' =
          if (I.targetFam v_) = c
          then
            begin let (u_, vs'_) = createAtomBVar (g_, n) in
                  CSManager.trail
                    (begin function
                     | () ->
                         (begin try
                                  ((if Unify.unifiable (g_, vs_, vs'_)
                                    then begin (Active (abstract u_)) :: ops end
                                  else begin ops end)
                         (* abstract state *))
                     with | Error _ -> InActive :: ops end) end) end
        else begin ops end in
  select ((d' - 1), ops') end in
select (d, ops0)
let rec lowerSplitDest =
  begin function
  | (g_, k, ((Root (Const c, _) as v_), s'), abstract, cases) ->
      cases (c, g_, (I.ctxLength g_), (v_, s'), abstract)
  | (g_, k, (Pi ((d_, p_), v_), s'), abstract, cases) ->
      let d'_ = I.decSub (d_, s') in
      lowerSplitDest
        ((I.Decl (g_, d'_)), (k + 1), (v_, (I.dot1 s')),
          (begin function | u_ -> abstract (I.Lam (d'_, u_)) end), cases) end
let rec abstractErrorLeft ((g_, b_), s) =
  raise (MTPAbstract.Error "Cannot split left of parameters")
let rec abstractErrorRight ((g_, b_), s) =
  raise (MTPAbstract.Error "Cannot split right of parameters")
let rec split (((Dec (_, v_) as d_), t_), sc, abstract) =
  let rec split' (n, cases) =
    if n < 0
    then
      begin let ((g'_, b'_), s', (g0_, b0_), _) = sc (I.Null, I.Null) in
            let rec abstract' (u'_) =
              let ((G'', B''), s'') =
                MTPAbstract.abstractSub'
                  ((g'_, b'_), (I.Dot ((I.Exp u'_), s')), (I.Decl (b0_, t_))) in
              let _ =
                if !Global.doubleCheck
                then
                  begin let Psi'' = aux (G'', B'') in
                        let _ = TypeCheck.typeCheckCtx (F.makectx Psi'') in
                        let Psi =
                          aux ((I.Decl (g0_, d_)), (I.Decl (b0_, t_))) in
                        let _ = TypeCheck.typeCheckCtx (F.makectx Psi) in
                        FunTypeCheck.checkSub (Psi'', s'', Psi) end
                else begin () end in
            ((abstract ((G'', B''), s''))
              (* G' |- U' : V[s'] *)(* G' |- U'.s' : G, V[s'] *)) in
    ((lowerSplitDest
        (g'_, 0, (v_, s'), abstract', (constAndParamCases cases)))
      (* |- G' = parameter blocks of G  ctx*)(* G' |- B' tags *)
      (* G' |- s' : G *)) end
  else begin
    (let LabelDec (name, g1_, g2_) = F.labelLookup n in
     let t = someEVars (I.Null, g1_, I.id) in
     let b1_ = createLemmaTags (F.listToCtx g1_) in
     let G2t = ctxSub (g2_, t) in
     let length = List.length g2_ in
     let b2_ = createTags (length, n) in
     let ((g'_, b'_), s', (g0_, b0_), p) =
       sc ((Names.ctxName (F.listToCtx G2t)), b2_) in
     let rec abstract' (u'_) =
       if p
       then
         begin raise (MTPAbstract.Error "Cannot split right of parameters") end
       else begin
         (let ((G'', B''), s'') =
            MTPAbstract.abstractSub
              (t, b1_, (g'_, b'_), (I.Dot ((I.Exp u'_), s')),
                (I.Decl (b0_, t_))) in
          let _ =
            if !Global.doubleCheck
            then
              begin let Psi'' = aux (G'', B'') in
                    let _ = TypeCheck.typeCheckCtx (F.makectx Psi'') in
                    let Psi = aux ((I.Decl (g0_, d_)), (I.Decl (b0_, t_))) in
                    let _ = TypeCheck.typeCheckCtx (F.makectx Psi) in
                    FunTypeCheck.checkSub (Psi'', s'', Psi) end
            else begin () end in
       ((abstract ((G'', B''), s''))
         (* G' |- U.s' : G, V *)(* . |- t : G1 *)
         (* . |- G'' ctx *)(* G'' |- B'' tags *)
         (* G'' = G1'', G2', G2'' *)(* where G1'' |- G2' ctx, G2' is the abstracted parameter block *))) end
       (* G' |- U' : V[s'] *) in
     let cases' =
       lowerSplitDest
         (g'_, 0, (v_, s'), abstract', (metaCases (length, cases))) in
     ((split' ((n - 1), cases'))
       (* . |- t : G1 *)(* . |- G2 [t] ctx *)(* G2 [t] |- B2 tags *)
       (* . |- G' ctx *)(* G' |- B' tags *)
       (* G' |- s : G = G0 *)(* G0 |- B0 tags *)
       (* abstract' U = S'

                   Invariant:
                   If   G' |- U' : V[s']
                   then |- S' state *))) end in
split' (((F.labelSize ()) - 1), [])
let rec occursInExp =
  begin function
  | (k, Uni _) -> false
  | (k, Pi (DP, v_)) -> (occursInDecP (k, DP)) || (occursInExp ((k + 1), v_))
  | (k, Root (c_, s_)) -> (occursInCon (k, c_)) || (occursInSpine (k, s_))
  | (k, Lam (d_, v_)) -> (occursInDec (k, d_)) || (occursInExp ((k + 1), v_))
  | (k, FgnExp csfe) ->
      I.FgnExpStd.fold csfe
        (begin function
         | (u_, b_) -> b_ || (occursInExp (k, (Whnf.normalize (u_, I.id)))) end)
      false end
let rec occursInCon =
  begin function
  | (k, BVar k') -> k = k'
  | (k, Const _) -> false
  | (k, Def _) -> false
  | (k, Skonst _) -> false end
let rec occursInSpine =
  begin function
  | (_, I.Nil) -> false
  | (k, App (u_, s_)) -> (occursInExp (k, u_)) || (occursInSpine (k, s_)) end
let rec occursInDec (k, Dec (_, v_)) = occursInExp (k, v_)
let rec occursInDecP (k, (d_, _)) = occursInDec (k, d_)
let rec isIndexInit k = false
let rec isIndexSucc (d_, isIndex) k =
  (occursInDec (k, d_)) || (isIndex (k + 1))
let rec isIndexFail (d_, isIndex) k = isIndex (k + 1)
let rec abstractInit (State (n, (g_, b_), (IH, OH), d, o_, h_, f_) as s_)
  ((g'_, b'_), s') =
  begin if !Global.doubleCheck then begin TypeCheck.typeCheckCtx g'_ end
  else begin () end;
  if !Global.doubleCheck
  then begin FunTypeCheck.isFor (g'_, (F.forSub (f_, s'))) end
  else begin () end;
S.State
  (n, (g'_, b'_), (IH, OH), d, (S.orderSub (o_, s')),
    (map (begin function | (i, f'_) -> (i, (F.forSub (f'_, s'))) end) h_),
  (F.forSub (f_, s'))) end
let rec abstractCont ((d_, t_), abstract) ((g_, b_), s) =
  abstract
    (((I.Decl (g_, (Whnf.normalizeDec (d_, s)))),
       (I.Decl (b_, (S.normalizeTag (t_, s))))), (I.dot1 s))
let rec makeAddressInit (s_) k = (s_, k)
let rec makeAddressCont makeAddress k = makeAddress (k + 1)
let rec occursInOrder =
  begin function
  | (n, Arg (us_, Vt), k, sc) ->
      let u'_ = Whnf.normalize us_ in
      if occursInExp (k, u'_) then begin Some n end else begin sc (n + 1) end
  | (n, Lex (os_), k, sc) -> occursInOrders (n, os_, k, sc)
  | (n, Simul (os_), k, sc) -> occursInOrders (n, os_, k, sc) end
let rec occursInOrders =
  begin function
  | (n, [], k, sc) -> sc n
  | (n, (o_)::os_, k, sc) ->
      occursInOrder
        (n, o_, k,
          (begin function | n' -> occursInOrders (n', os_, k, sc) end)) end
let rec inductionInit (o_) k =
  occursInOrder (0, o_, k, (begin function | n -> None end))
let rec inductionCont induction k = induction (k + 1)
let rec expand' =
  begin function
  | (((I.Null, I.Null) as GB), isIndex, abstract, makeAddress, induction) ->
      (((begin function
         | (Gp, Bp) -> ((Gp, Bp), (I.Shift (I.ctxLength Gp)), GB, false) end)),
      [])
  | (((Decl (g_, d_), Decl (b_, (Lemma (Splits _ as k_) as t_))) as GB),
     isIndex, abstract, makeAddress, induction) ->
      let (sc, ops) =
        expand'
          ((g_, b_), (isIndexSucc (d_, isIndex)),
            (abstractCont ((d_, t_), abstract)),
            (makeAddressCont makeAddress), (inductionCont induction)) in
      let Dec (xOpt, v_) = d_ in
      let rec sc' (Gp, Bp) =
        let ((g'_, b'_), s', (g0_, b0_), p') = sc (Gp, Bp) in
        let x_ = I.newEVar (g'_, (I.EClo (v_, s'))) in
        ((((g'_, b'_), (I.Dot ((I.Exp x_), s')),
            ((I.Decl (g0_, d_)), (I.Decl (b0_, t_))), p'))
          (* G' |- X : V[s'] *)(* G' |- X.s' : G, D *)) in
      let ops' =
        if (not (isIndex 1)) && ((S.splitDepth k_) > 0)
        then
          begin let a = I.targetFam v_ in
                (makeOperator
                   ((makeAddress 1), (split ((d_, t_), sc, abstract)), k_,
                     (I.ctxLength g_), (induction 1),
                     (maxNumberCases (v_, a)), (Subordinate.below (a, a))))
                  :: ops end
        else begin ops end in
      (sc', ops')
| ((Decl (g_, d_), Decl (b_, (Lemma (S.RL) as t_))), isIndex, abstract,
   makeAddress, induction) ->
    let (sc, ops) =
      expand'
        ((g_, b_), (isIndexSucc (d_, isIndex)),
          (abstractCont ((d_, t_), abstract)), (makeAddressCont makeAddress),
          (inductionCont induction)) in
    let Dec (xOpt, v_) = d_ in
    let rec sc' (Gp, Bp) =
      let ((g'_, b'_), s', (g0_, b0_), p') = sc (Gp, Bp) in
      let x_ = I.newEVar (g'_, (I.EClo (v_, s'))) in
      ((g'_, b'_), (I.Dot ((I.Exp x_), s')),
        ((I.Decl (g0_, d_)), (I.Decl (b0_, t_))), p') in
    (sc', ops)
| ((Decl (g_, d_), Decl (b_, (Lemma (S.RLdone) as t_))), isIndex, abstract,
   makeAddress, induction) ->
    let (sc, ops) =
      expand'
        ((g_, b_), (isIndexSucc (d_, isIndex)),
          (abstractCont ((d_, t_), abstract)), (makeAddressCont makeAddress),
          (inductionCont induction)) in
    let Dec (xOpt, v_) = d_ in
    let rec sc' (Gp, Bp) =
      let ((g'_, b'_), s', (g0_, b0_), p') = sc (Gp, Bp) in
      let x_ = I.newEVar (g'_, (I.EClo (v_, s'))) in
      ((g'_, b'_), (I.Dot ((I.Exp x_), s')),
        ((I.Decl (g0_, d_)), (I.Decl (b0_, t_))), p') in
    (sc', ops)
| ((Decl (g_, d_), Decl (b_, (Parameter (Some _) as t_))), isIndex, abstract,
   makeAddress, induction) ->
    let (sc, ops) =
      expand'
        ((g_, b_), (isIndexSucc (d_, isIndex)), abstractErrorLeft,
          (makeAddressCont makeAddress), (inductionCont induction)) in
    let Dec (xOpt, v_) = d_ in
    let rec sc' (Gp, Bp) =
      let ((g'_, b'_), s', (g0_, b0_), _) = sc (Gp, Bp) in
      (((I.Decl (g'_, (Names.decName (g'_, (I.decSub (d_, s')))))),
         (I.Decl (b'_, t_))), (I.dot1 s'),
        ((I.Decl (g0_, d_)), (I.Decl (b0_, t_))), true) in
    (sc', ops) end
let rec expand (State (n, (g0_, b0_), _, _, o_, _, _) as s0_) =
  let _ = if !Global.doubleCheck then begin FunTypeCheck.isState s0_ end
    else begin () end in
let (_, ops) =
  expand'
    ((g0_, b0_), isIndexInit, (abstractInit s0_), (makeAddressInit s0_),
      (inductionInit o_)) in
ops
let rec index (Operator ((s_, index), Sl, { c = k })) = k
let rec compare (Operator (_, _, i1_), Operator (_, _, i2_)) =
  H.compare (i1_, i2_)
let rec isInActive =
  begin function | Active _ -> false | InActive -> true end
let rec applicable (Operator (_, Sl, i_)) = not (List.exists isInActive Sl)
let rec apply (Operator (_, Sl, i_)) =
  map
    (begin function
     | Active (s_) ->
         (begin if !Global.doubleCheck then begin FunTypeCheck.isState s_ end
          else begin () end;
     s_ end)
  | InActive -> raise (Error "Not applicable: leftover constraints") end)
Sl
let rec menu
  (Operator ((State (n, (g_, b_), (IH, OH), d, o_, h_, f_), i), Sl, i_) as Op)
  =
  let rec active =
    begin function
    | ([], n) -> n
    | ((InActive)::l_, n) -> active (l_, n)
    | ((Active _)::l_, n) -> active (l_, (n + 1)) end in
let rec inactive =
  begin function
  | ([], n) -> n
  | ((InActive)::l_, n) -> inactive (l_, (n + 1))
  | ((Active _)::l_, n) -> inactive (l_, n) end in
let rec casesToString =
  begin function
  | 0 -> "zero cases"
  | 1 -> "1 case"
  | n -> (Int.toString n) ^ " cases" end in
let rec flagToString =
  begin function
  | (_, 0) -> ""
  | (n, m) ->
      (((" [active: " ^ (Int.toString n)) ^ " inactive: ") ^ (Int.toString m))
        ^ "]" end in
(((((^) "Splitting : " Print.decToString (g_, (I.ctxDec (g_, i)))) ^ " ") ^
    (H.indexToString i_))
   ^ (flagToString ((active (Sl, 0)), (inactive (Sl, 0)))))
  ^ ""
let expand = expand
let menu = menu
let applicable = applicable
let apply = apply
let index = index
let compare = compare end
