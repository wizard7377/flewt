module type CHECKING  =
  sig
    module Order : ORDER
    type quantifier_ =
      | All 
      | Exist 
      | And of Paths.occ 
    type 'a predicate_ =
      | Less of ('a * 'a) 
      | Leq of ('a * 'a) 
      | Eq of ('a * 'a) 
      | Pi of (IntSyn.dec_ * 'a predicate_) 
    type nonrec order = (IntSyn.eclo * IntSyn.eclo) Order.order_
    type nonrec rctx = order predicate_ list
    type nonrec qctx = quantifier_ IntSyn.ctx_
    val shiftRCtx : rctx -> (IntSyn.sub_ -> IntSyn.sub_) -> rctx
    val shiftPred :
      order predicate_ -> (IntSyn.sub_ -> IntSyn.sub_) -> order predicate_
    val deduce : (IntSyn.dctx * qctx * rctx * order predicate_) -> bool
  end


module Checking(Checking:sig
                           module Global : GLOBAL
                           module Whnf : WHNF
                           module Conv : CONV
                           module Unify : UNIFY
                           module Names : NAMES
                           module Index : INDEX
                           module Subordinate : SUBORDINATE
                           module Formatter : FORMATTER
                           module Print : PRINT
                           module Order : ORDER
                           module Origins : ORIGINS
                         end) : CHECKING =
  struct
    module Order = Order
    type quantifier_ =
      | All 
      | Exist 
      | And of Paths.occ 
    type 'a predicate_ =
      | Less of ('a * 'a) 
      | Leq of ('a * 'a) 
      | Eq of ('a * 'a) 
      | Pi of (IntSyn.dec_ * 'a predicate_) 
    type nonrec order = (IntSyn.eclo * IntSyn.eclo) Order.order_
    type nonrec rctx = order predicate_ list
    type nonrec qctx = quantifier_ IntSyn.ctx_
    module I = IntSyn
    module P = Paths
    module N = Names
    module F = Formatter
    module R = Order
    let rec atomicPredToString =
      begin function
      | (g_, Less ((us_, _), (us'_, _))) ->
          (^) ((Print.expToString (g_, (I.EClo us_))) ^ " < ")
            Print.expToString (g_, (I.EClo us'_))
      | (g_, Leq ((us_, _), (us'_, _))) ->
          (^) ((Print.expToString (g_, (I.EClo us_))) ^ " <= ")
            Print.expToString (g_, (I.EClo us'_))
      | (g_, Eq ((us_, _), (us'_, _))) ->
          (^) ((Print.expToString (g_, (I.EClo us_))) ^ " = ")
            Print.expToString (g_, (I.EClo us'_)) end
    let rec atomicRCtxToString =
      begin function
      | (g_, []) -> " "
      | (g_, (o_)::[]) -> atomicPredToString (g_, o_)
      | (g_, (o_)::d'_) ->
          (^) ((atomicRCtxToString (g_, d'_)) ^ ", ") atomicPredToString
            (g_, o_) end
  let rec shiftO arg__0 arg__1 =
    begin match (arg__0, arg__1) with
    | (Arg ((u_, us), (v_, vs)), f) -> R.Arg ((u_, (f us)), (v_, (f vs)))
    | (Lex (l_), f) ->
        R.Lex (map (begin function | o_ -> shiftO o_ f end) l_)
    | (Simul (l_), f) ->
        R.Simul (map (begin function | o_ -> shiftO o_ f end) l_) end
let rec shiftP arg__2 arg__3 =
  begin match (arg__2, arg__3) with
  | (Less (o1_, o2_), f) -> Less ((shiftO o1_ f), (shiftO o2_ f))
  | (Leq (o1_, o2_), f) -> Leq ((shiftO o1_ f), (shiftO o2_ f))
  | (Eq (o1_, o2_), f) -> Eq ((shiftO o1_ f), (shiftO o2_ f))
  | (Pi ((Dec (x_, v_) as d_), p_), f) -> Pi (d_, (shiftP p_ f)) end
let rec shiftRCtx (Rl) f = map (begin function | p -> shiftP p f end) Rl
let rec shiftArg arg__4 arg__5 =
  begin match (arg__4, arg__5) with
  | (Less (((u1_, s1), (v1_, s1')), ((u2_, s2), (v2_, s2'))), f) ->
      Less (((u1_, (f s1)), (v1_, (f s1'))), ((u2_, (f s2)), (v2_, (f s2'))))
  | (Leq (((u1_, s1), (v1_, s1')), ((u2_, s2), (v2_, s2'))), f) ->
      Leq (((u1_, (f s1)), (v1_, (f s1'))), ((u2_, (f s2)), (v2_, (f s2'))))
  | (Eq (((u1_, s1), (v1_, s1')), ((u2_, s2), (v2_, s2'))), f) ->
      Eq (((u1_, (f s1)), (v1_, (f s1'))), ((u2_, (f s2)), (v2_, (f s2')))) end
let rec shiftACtx (Rl) f = map (begin function | p -> shiftArg p f end) Rl
let rec fmtOrder (g_, o_) =
  let rec fmtOrder' =
    begin function
    | Arg (((u_, s) as us_), ((v_, s') as vs_)) ->
        F.Hbox
          [F.String "("; Print.formatExp (g_, (I.EClo us_)); F.String ")"]
    | Lex (l_) ->
        F.Hbox [F.String "{"; F.HOVbox0 1 0 1 (fmtOrders l_); F.String "}"]
    | Simul (l_) ->
        F.Hbox [F.String "["; F.HOVbox0 1 0 1 (fmtOrders l_); F.String "]"] end
    and fmtOrders =
      begin function
      | [] -> []
      | (o_)::[] -> (fmtOrder' o_) :: []
      | (o_)::l_ -> (::) ((fmtOrder' o_) :: F.Break) fmtOrders l_ end in
fmtOrder' o_
let rec fmtComparison (g_, o_, comp, o'_) =
  F.HOVbox0 1 0 1
    [fmtOrder (g_, o_); F.Break; F.String comp; F.Break; fmtOrder (g_, o'_)]
let rec fmtPredicate' =
  begin function
  | (g_, Less (o_, o'_)) -> fmtComparison (g_, o_, "<", o'_)
  | (g_, Leq (o_, o'_)) -> fmtComparison (g_, o_, "<=", o'_)
  | (g_, Eq (o_, o'_)) -> fmtComparison (g_, o_, "=", o'_)
  | (g_, Pi (d_, p_)) ->
      F.Hbox [F.String "Pi "; fmtPredicate' ((I.Decl (g_, d_)), p_)] end
(* F.String "Pi predicate"  *)
let rec fmtPredicate (g_, p_) = fmtPredicate' ((Names.ctxName g_), p_)
let rec fmtRGCtx' =
  begin function
  | (g_, []) -> ""
  | (g_, (p_)::[]) -> F.makestring_fmt (fmtPredicate' (g_, p_))
  | (g_, (p_)::Rl) ->
      (^) ((F.makestring_fmt (fmtPredicate' (g_, p_))) ^ " ,") fmtRGCtx'
        (g_, Rl) end
let rec fmtRGCtx (g_, Rl) = fmtRGCtx' ((Names.ctxName g_), Rl)
let rec init () = true
let rec eqCid (c, c') = c = c'
let rec conv ((us_, vs_), (us'_, vs'_)) =
  (Conv.conv (vs_, vs'_)) && (Conv.conv (us_, us'_))
let rec isUniversal =
  begin function | All -> true | Exist -> false | Exist' -> false end
let rec isExistential =
  begin function | All -> false | Exist -> true | Exist' -> true end
let rec isParameter (q_, x_) = isParameterW (q_, (Whnf.whnf (x_, I.id)))
let rec isParameterW (q_, us_) =
  begin try isUniversal (I.ctxLookup (q_, (Whnf.etaContract (I.EClo us_))))
  with | Whnf.Eta -> isFreeEVar us_ end
let rec isFreeEVar =
  begin function
  | (EVar (_, _, _, { contents = [] }), _) -> true
  | (Lam (d_, u_), s) -> isFreeEVar (Whnf.whnf (u_, (I.dot1 s)))
  | _ -> false end(* constraints must be empty *)
let rec isAtomic (GQ, us_) = isAtomicW (GQ, (Whnf.whnf us_))
let rec isAtomicW =
  begin function
  | (GQ, ((Root (Const c, s_) as x_), s)) -> isAtomicS (GQ, (s_, s))
  | (GQ, ((Root (Def c, s_) as x_), s)) -> isAtomicS (GQ, (s_, s))
  | (((g_, q_) as GQ), ((Root (BVar n, s_) as x_), s)) ->
      (isExistential (I.ctxLookup (q_, n))) || (isAtomicS (GQ, (s_, s)))
  | (GQ, _) -> false end(*      | isAtomicW (GQ, (X as (I.EClo _))) = true    existential var *)
(* should disallow orelse ? *)
let rec isAtomicS =
  begin function
  | (GQ, (I.Nil, _)) -> true
  | (GQ, (SClo (s_, s'), s'')) -> isAtomicS (GQ, (s_, (I.comp (s', s''))))
  | (GQ, (App (u'_, s'_), s1')) -> false end
let rec eq (g_, (us_, vs_), (us'_, vs'_)) =
  (Unify.unifiable (g_, vs_, vs'_)) && (Unify.unifiable (g_, us_, us'_))
let rec lookupEq =
  begin function
  | (GQ, [], UsVs, UsVs', sc) -> false
  | (GQ, (Less (_, _))::d_, UsVs, UsVs', sc) ->
      lookupEq (GQ, d_, UsVs, UsVs', sc)
  | (((g_, q_) as GQ), (Eq (UsVs1, UsVs1'))::d_, UsVs, UsVs', sc) ->
      (CSManager.trail
         (begin function
          | () ->
              (eq (g_, UsVs1, UsVs)) && ((eq (g_, UsVs1', UsVs')) && (sc ())) end))
      ||
      ((CSManager.trail
          (begin function
           | () ->
               (eq (g_, UsVs1, UsVs')) &&
                 ((eq (g_, UsVs1', UsVs)) && (sc ())) end))
      || (lookupEq (GQ, d_, UsVs, UsVs', sc))) end
let rec lookupLt =
  begin function
  | (GQ, [], UsVs, UsVs', sc) -> false
  | (GQ, (Eq (_, _))::d_, UsVs, UsVs', sc) ->
      lookupLt (GQ, d_, UsVs, UsVs', sc)
  | (((g_, q_) as GQ), (Less (UsVs1, UsVs1'))::d_, UsVs, UsVs', sc) ->
      (CSManager.trail
         (begin function
          | () ->
              (eq (g_, UsVs1, UsVs)) && ((eq (g_, UsVs1', UsVs')) && (sc ())) end))
      || (lookupLt (GQ, d_, UsVs, UsVs', sc)) end
let rec eqAtomic =
  begin function
  | (((g_, q_) as GQ), [], d'_, UsVs, UsVs', sc) ->
      (CSManager.trail
         (begin function | () -> (eq (g_, UsVs, UsVs')) && (sc ()) end))
      || (lookupEq (GQ, d'_, UsVs, UsVs', sc))
  | (((g_, q_) as GQ), d_, d'_, UsVs, UsVs', sc) ->
      (CSManager.trail
         (begin function | () -> (eq (g_, UsVs, UsVs')) && (sc ()) end))
      ||
      ((lookupEq (GQ, d_, UsVs, UsVs', sc)) ||
         ((lookupEq (GQ, d'_, UsVs, UsVs', sc)) ||
            (transEq (GQ, d_, d'_, UsVs, UsVs', sc)))) end
let rec transEq =
  begin function
  | (((g_, q_) as GQ), [], d_, UsVs, UsVs', sc) -> false
  | (((g_, q_) as GQ), (Eq (UsVs1, UsVs1'))::d_, d'_, UsVs, UsVs', sc) ->
      (CSManager.trail
         (begin function
          | () ->
              (eq (g_, UsVs1', UsVs')) &&
                ((sc ()) &&
                   (eqAtomicR (GQ, (d_ @ d'_), UsVs, UsVs1, sc, atomic))) end))
      ||
      ((CSManager.trail
          (begin function
           | () ->
               (eq (g_, UsVs1, UsVs')) &&
                 ((sc ()) &&
                    (eqAtomicR (GQ, (d_ @ d'_), UsVs, UsVs1', sc, atomic))) end))
      || (transEq (GQ, d_, ((Eq (UsVs1, UsVs1')) :: d'_), UsVs, UsVs', sc)))
  | (((g_, q_) as GQ), (Less (UsVs1, UsVs1'))::d_, d'_, UsVs, UsVs', sc) ->
      transEq (GQ, d_, d'_, UsVs, UsVs', sc) end
let rec ltAtomic =
  begin function
  | (((g_, q_) as GQ), [], d'_, UsVs, UsVs', sc) ->
      lookupLt (GQ, d'_, UsVs, UsVs', sc)
  | (((g_, q_) as GQ), d_, d'_, UsVs, UsVs', sc) ->
      (lookupLt (GQ, d_, UsVs, UsVs', sc)) ||
        ((lookupLt (GQ, d'_, UsVs, UsVs', sc)) ||
           (transLt (GQ, d_, d'_, UsVs, UsVs', sc))) end
let rec transLt =
  begin function
  | (((g_, q_) as GQ), [], d_, UsVs, UsVs', sc) -> false
  | (((g_, q_) as GQ), (Eq (UsVs1, UsVs1'))::d_, d'_, UsVs, UsVs', sc) ->
      (CSManager.trail
         (begin function
          | () ->
              (eq (g_, UsVs1', UsVs')) &&
                ((sc ()) &&
                   (ltAtomicR (GQ, (d_ @ d'_), UsVs, UsVs1, sc, atomic))) end))
      ||
      ((CSManager.trail
          (begin function
           | () ->
               (eq (g_, UsVs1, UsVs')) &&
                 ((sc ()) &&
                    (ltAtomicR (GQ, (d_ @ d'_), UsVs, UsVs1', sc, atomic))) end))
      || (transLt (GQ, d_, ((Eq (UsVs1, UsVs1')) :: d'_), UsVs, UsVs', sc)))
  | (((g_, q_) as GQ), (Less (UsVs1, UsVs1'))::d_, d'_, UsVs, UsVs', sc) ->
      (CSManager.trail
         (begin function
          | () ->
              (eq (g_, UsVs1', UsVs')) &&
                ((sc ()) &&
                   (eqAtomicR (GQ, (d_ @ d'_), UsVs, UsVs1, sc, atomic))) end))
      ||
      ((CSManager.trail
          (begin function
           | () ->
               (eq (g_, UsVs1', UsVs')) &&
                 ((sc ()) &&
                    (ltAtomicR (GQ, (d_ @ d'_), UsVs, UsVs1, sc, atomic))) end))
      || (transLt (GQ, d_, ((Less (UsVs1, UsVs1')) :: d'_), UsVs, UsVs', sc))) end
let rec atomic =
  begin function
  | (GQ, d_, d'_, Eq (UsVs, UsVs'), sc) ->
      eqAtomic (GQ, d_, d'_, UsVs, UsVs', sc)
  | (GQ, d_, d'_, Less (UsVs, UsVs'), sc) ->
      ltAtomic (GQ, d_, d'_, UsVs, UsVs', sc) end
let rec leftInstantiate =
  begin function
  | (((g_, q_) as GQ), [], d'_, p_, sc) ->
      ((if atomic (GQ, d'_, [], p_, sc)
        then
          begin (begin if !Global.chatter > 4
                       then
                         begin print
                                 (((^) (((^) " Proved: " atomicRCtxToString
                                           (g_, d'_))
                                          ^ " ---> ")
                                     atomicPredToString (g_, p_))
                                    ^ "\n") end
                 else begin () end;
        true end) end
  else begin false end)
(* should never happen by invariant *))
| (GQ, (Less (UsVs, UsVs'))::d_, d'_, p_, sc) ->
    ltInstL (GQ, d_, d'_, UsVs, UsVs', p_, sc)
| (GQ, (Leq (UsVs, UsVs'))::d_, d'_, p_, sc) ->
    leInstL (GQ, d_, d'_, UsVs, UsVs', p_, sc)
| (GQ, (Eq (UsVs, UsVs'))::d_, d'_, p_, sc) ->
    eqInstL (GQ, d_, d'_, UsVs, UsVs', p_, sc) end
let rec ltInstL (GQ, d_, d'_, UsVs, UsVs', p'_, sc) =
  ltInstLW (GQ, d_, d'_, (Whnf.whnfEta UsVs), UsVs', p'_, sc)
let rec ltInstLW =
  begin function
  | (((g_, q_) as GQ), d_, d'_,
     ((Lam ((Dec (_, v1_) as Dec), u_), s1),
      (Pi ((Dec (_, v2_), _), v_), s2)),
     ((u'_, s1'), (v'_, s2')), p'_, sc) ->
      ((if Subordinate.equiv ((I.targetFam v'_), (I.targetFam v1_))
        then
          begin let x_ = I.newEVar (g_, (I.EClo (v1_, s1))) in
                let sc' =
                  begin function | () -> (isParameter (q_, x_)) && (sc ()) end in
                ((ltInstL
                    ((g_, q_), d_, d'_,
                      ((u_, (I.Dot ((I.Exp x_), s1))),
                        (v_, (I.Dot ((I.Exp x_), s2)))),
                      ((u'_, s1'), (v'_, s2')), p'_, sc'))
                  (* = I.newEVar (I.EClo (V2', s2')) *)
                  (* enforces that X can only bound to parameter or remain uninstantiated *)) end
  else begin
    if Subordinate.below ((I.targetFam v1_), (I.targetFam v'_))
    then
      begin (let x_ = I.newEVar (g_, (I.EClo (v1_, s1))) in
             ((ltInstL
                 ((g_, q_), d_, d'_,
                   ((u_, (I.Dot ((I.Exp x_), s1))),
                     (v_, (I.Dot ((I.Exp x_), s2)))),
                   ((u'_, s1'), (v'_, s2')), p'_, sc))
               (* = I.newEVar (I.EClo (V2', s2')) *))) end
    else begin false end end)(* == I.targetFam V2' *))
| (GQ, d_, d'_, UsVs, UsVs', p'_, sc) ->
    leftInstantiate (GQ, d_, ((Less (UsVs, UsVs')) :: d'_), p'_, sc) end
(* impossible, if additional invariant assumed (see ltW) *)
let rec leInstL (GQ, d_, d'_, UsVs, UsVs', p'_, sc) =
  leInstLW (GQ, d_, d'_, (Whnf.whnfEta UsVs), UsVs', p'_, sc)
let rec leInstLW =
  begin function
  | (((g_, q_) as GQ), d_, d'_,
     ((Lam (Dec (_, v1_), u_), s1), (Pi ((Dec (_, v2_), _), v_), s2)),
     ((u'_, s1'), (v'_, s2')), p'_, sc) ->
      ((if Subordinate.equiv ((I.targetFam v'_), (I.targetFam v1_))
        then
          begin let x_ = I.newEVar (g_, (I.EClo (v1_, s1))) in
                let sc' =
                  begin function | () -> (isParameter (q_, x_)) && (sc ()) end in
                ((leInstL
                    ((g_, q_), d_, d'_,
                      ((u_, (I.Dot ((I.Exp x_), s1))),
                        (v_, (I.Dot ((I.Exp x_), s2)))),
                      ((u'_, s1'), (v'_, s2')), p'_, sc'))
                  (* = I.newEVar (I.EClo (V2', s2')) *)
                  (* enforces that X can only bound to parameter or remain uninstantiated *)) end
  else begin
    if Subordinate.below ((I.targetFam v1_), (I.targetFam v'_))
    then
      begin (let x_ = I.newEVar (g_, (I.EClo (v1_, s1))) in
             ((leInstL
                 ((g_, q_), d_, d'_,
                   ((u_, (I.Dot ((I.Exp x_), s1))),
                     (v_, (I.Dot ((I.Exp x_), s2)))),
                   ((u'_, s1'), (v'_, s2')), p'_, sc))
               (* = I.newEVar (I.EClo (V2', s2')) *))) end
    else begin false end end)(* == I.targetFam V2' *))
| (GQ, d_, d'_, UsVs, UsVs', p_, sc) ->
    leftInstantiate (GQ, d_, ((Less (UsVs, UsVs')) :: d'_), p_, sc) end
(* impossible, if additional invariant assumed (see ltW) *)
let rec eqInstL (GQ, d_, d'_, UsVs, UsVs', p'_, sc) =
  eqInstLW (GQ, d_, d'_, (Whnf.whnfEta UsVs), (Whnf.whnfEta UsVs'), p'_, sc)
let rec eqInstLW =
  begin function
  | (((g_, q_) as GQ), d_, d'_,
     ((Lam (Dec (_, V1'), u'_), s1'), (Pi ((Dec (_, V2'), _), v'_), s2')),
     ((Lam (Dec (_, V1''), U''), s1''), (Pi ((Dec (_, V2''), _), V''), s2'')),
     p'_, sc) ->
      let x_ = I.newEVar (g_, (I.EClo (V1'', s1''))) in
      ((eqInstL
          (GQ, d_, d'_,
            ((u'_, (I.Dot ((I.Exp x_), s1'))),
              (v'_, (I.Dot ((I.Exp x_), s2')))),
            ((U'', (I.Dot ((I.Exp x_), s1''))),
              (V'', (I.Dot ((I.Exp x_), s2'')))), p'_,
            (begin function | () -> (begin isParameter (q_, x_); sc () end) end)))
  (* = I.newEVar (I.EClo (V2', s2')) *))
  | (GQ, d_, d'_, UsVs, UsVs', p'_, sc) ->
      eqIL (GQ, d_, d'_, UsVs, UsVs', p'_, sc) end
let rec eqIL =
  begin function
  | (((g_, q_) as GQ), d_, d'_, (((Root (Const c, s_), s), vs_) as UsVs),
     (((Root (Const c', s'_), s'), vs'_) as UsVs'), p'_, sc) ->
      if eqCid (c, c')
      then
        begin eqSpineIL
                (GQ, d_, d'_, ((s_, s), ((I.constType c), I.id)),
                  ((s'_, s'), ((I.constType c'), I.id)), p'_, sc) end
      else begin
        (begin if !Global.chatter > 4
               then
                 begin print
                         (((^) (((^) ((^) " Proved: " atomicRCtxToString
                                        (g_, ((Eq (UsVs, UsVs')) :: d_)))
                                   atomicRCtxToString (g_, d'_))
                                  ^ " ---> ")
                             atomicPredToString (g_, p'_))
                            ^ "\n") end
         else begin () end;
      true end) end
| (((g_, q_) as GQ), d_, d'_, (((Root (Def c, s_), s), vs_) as UsVs),
   (((Root (Def c', s'_), s'), vs'_) as UsVs'), p'_, sc) ->
    if eqCid (c, c')
    then
      begin eqSpineIL
              (GQ, d_, d'_, ((s_, s), ((I.constType c), I.id)),
                ((s'_, s'), ((I.constType c'), I.id)), p'_, sc) end
    else begin
      (begin if !Global.chatter > 4
             then
               begin print
                       (((^) (((^) ((^) " Proved: " atomicRCtxToString
                                      (g_, ((Eq (UsVs, UsVs')) :: d_)))
                                 atomicRCtxToString (g_, d'_))
                                ^ " ---> ")
                           atomicPredToString (g_, p'_))
                          ^ "\n") end
       else begin () end;
    true end) end
| (((g_, q_) as GQ), d_, d'_, (((Root (Const c, s_), s) as us_), vs_),
   (((Root (BVar n, s'_), s') as us'_), vs'_), p'_, sc) ->
    if isAtomic (GQ, us'_)
    then
      begin leftInstantiate
              (GQ, d_, ((Eq ((us'_, vs'_), (us_, vs_))) :: d'_), p'_, sc) end
    else begin
      (begin if !Global.chatter > 4
             then
               begin print
                       (((^) (((^) ((^) " Proved: " atomicRCtxToString
                                      (g_,
                                        ((Eq ((us_, vs_), (us'_, vs'_))) ::
                                           d_)))
                                 atomicRCtxToString (g_, d'_))
                                ^ " ---> ")
                           atomicPredToString (g_, p'_))
                          ^ "\n") end
       else begin () end;
    true end) end
| (((g_, q_) as GQ), d_, d'_, (((Root (Def c, s_), s) as us_), vs_),
   (((Root (BVar n, s'_), s') as us'_), vs'_), p'_, sc) ->
    if isAtomic (GQ, us'_)
    then
      begin leftInstantiate
              (GQ, d_, ((Eq ((us'_, vs'_), (us_, vs_))) :: d'_), p'_, sc) end
    else begin
      (begin if !Global.chatter > 4
             then
               begin print
                       (((^) (((^) ((^) " Proved: " atomicRCtxToString
                                      (g_,
                                        ((Eq ((us_, vs_), (us'_, vs'_))) ::
                                           d_)))
                                 atomicRCtxToString (g_, d'_))
                                ^ " ---> ")
                           atomicPredToString (g_, p'_))
                          ^ "\n") end
       else begin () end;
    true end) end
| (((g_, q_) as GQ), d_, d'_, (((Root (BVar n, s_), s) as us_), vs_),
   (((Root (Def c, s'_), s') as us'_), vs'_), p'_, sc) ->
    if isAtomic (GQ, us_)
    then
      begin leftInstantiate
              (GQ, d_, ((Eq ((us_, vs_), (us'_, vs'_))) :: d'_), p'_, sc) end
    else begin
      (begin if !Global.chatter > 4
             then
               begin print
                       (((^) (((^) ((^) " Proved: " atomicRCtxToString
                                      (g_,
                                        ((Eq ((us_, vs_), (us'_, vs'_))) ::
                                           d'_)))
                                 atomicRCtxToString (g_, d'_))
                                ^ " ---> ")
                           atomicPredToString (g_, p'_))
                          ^ "\n") end
       else begin () end;
    true end) end
| (((g_, q_) as GQ), d_, d'_, (((Root (BVar n, s_), s) as us_), vs_),
   (((Root (Const c, s'_), s') as us'_), vs'_), p'_, sc) ->
    if isAtomic (GQ, us_)
    then
      begin leftInstantiate
              (GQ, d_, ((Eq ((us_, vs_), (us'_, vs'_))) :: d'_), p'_, sc) end
    else begin
      (begin if !Global.chatter > 4
             then
               begin print
                       (((^) (((^) ((^) " Proved: " atomicRCtxToString
                                      (g_,
                                        ((Eq ((us_, vs_), (us'_, vs'_))) ::
                                           d'_)))
                                 atomicRCtxToString (g_, d'_))
                                ^ " ---> ")
                           atomicPredToString (g_, p'_))
                          ^ "\n") end
       else begin () end;
    true end) end
| (((g_, q_) as GQ), d_, d'_, (((Root (BVar n, s_), s) as us_), vs_),
   (((Root (BVar n', s'_), s') as us'_), vs'_), p'_, sc) ->
    if n = n'
    then
      begin let Dec (_, v'_) = I.ctxDec (g_, n) in
            eqSpineIL
              (GQ, d_, d'_, ((s_, s), (v'_, I.id)), ((s'_, s'), (v'_, I.id)),
                p'_, sc) end
    else begin
      leftInstantiate
        (GQ, d_, ((Eq ((us_, vs_), (us'_, vs'_))) :: d'_), p'_, sc) end
| (((g_, q_) as GQ), d_, d'_, UsVs, UsVs', p'_, sc) ->
    (begin if !Global.chatter > 4
           then
             begin print
                     (((^) (((^) ((^) " Proved: " atomicRCtxToString
                                    (g_, ((Eq (UsVs, UsVs')) :: d_)))
                               atomicRCtxToString (g_, d'_))
                              ^ " ---> ")
                         atomicPredToString (g_, p'_))
                        ^ "\n") end
     else begin () end;
true end) end(* (Us, Vs as (I.Pi _ , _)) and (Us', Vs' as (I.Root _, _))
           or the other way
         *)
let rec eqSpineIL (GQ, d_, d'_, (ss_, vs_), (ss'_, vs'_), p'_, sc) =
  eqSpineILW
    (GQ, d_, d'_, (ss_, (Whnf.whnf vs_)), (ss'_, (Whnf.whnf vs'_)), p'_, sc)
let rec eqSpineILW =
  begin function
  | (GQ, d_, d'_, ((I.Nil, s), vs_), ((I.Nil, s'), vs'_), p'_, sc) ->
      leftInstantiate (GQ, d_, d'_, p'_, sc)
  | (GQ, d_, d'_, ((SClo (s_, s'), s''), vs_), SsVs', p'_, sc) ->
      eqSpineIL
        (GQ, d_, d'_, ((s_, (I.comp (s', s''))), vs_), SsVs', p'_, sc)
  | (GQ, d_, d'_, SsVs, ((SClo (s'_, s'), s''), vs'_), p'_, sc) ->
      eqSpineIL
        (GQ, d_, d'_, SsVs, ((s'_, (I.comp (s', s''))), vs'_), p'_, sc)
  | (GQ, d_, d'_, ((App (u_, s_), s1), (Pi ((Dec (_, v1_), _), v2_), s2)),
     ((App (u'_, s'_), s1'), (Pi ((Dec (_, V1'), _), V2'), s2')), p'_, sc) ->
      let d1_ = (Eq (((u_, s1), (v1_, s2)), ((u'_, s1'), (V1', s2')))) :: d_ in
      eqSpineIL
        (GQ, d1_, d'_,
          ((s_, s1), (v2_, (I.Dot ((I.Exp (I.EClo (u_, s1))), s2)))),
          ((s'_, s1'), (V2', (I.Dot ((I.Exp (I.EClo (u'_, s1'))), s2')))),
          p'_, sc) end
let rec rightDecompose =
  begin function
  | (GQ, d'_, Less (o_, o'_)) -> ordLtR (GQ, d'_, o_, o'_)
  | (GQ, d'_, Leq (o_, o'_)) -> ordLeR (GQ, d'_, o_, o'_)
  | (GQ, d'_, Eq (o_, o'_)) -> ordEqR (GQ, d'_, o_, o'_) end
let rec ordLtR =
  begin function
  | (GQ, d'_, Arg (UsVs), Arg (UsVs')) ->
      ltAtomicR (GQ, d'_, UsVs, UsVs', init, leftInstantiate)
  | (GQ, d'_, Lex (o_), Lex (o'_)) -> ltLexR (GQ, d'_, o_, o'_)
  | (GQ, d'_, Simul (o_), Simul (o'_)) -> ltSimulR (GQ, d'_, o_, o'_) end
let rec ordLeR =
  begin function
  | (GQ, d'_, Arg (UsVs), Arg (UsVs')) ->
      leAtomicR (GQ, d'_, UsVs, UsVs', init, leftInstantiate)
  | (GQ, d'_, Lex (o_), Lex (o'_)) ->
      (ltLexR (GQ, d'_, o_, o'_)) || (ordEqsR (GQ, d'_, o_, o'_))
  | (GQ, d'_, Simul (o_), Simul (o'_)) -> leSimulR (GQ, d'_, o_, o'_) end
let rec ordEqR =
  begin function
  | (GQ, d'_, Arg (UsVs), Arg (UsVs')) ->
      (conv (UsVs, UsVs')) ||
        (eqAtomicR (GQ, d'_, UsVs, UsVs', init, leftInstantiate))
  | (GQ, d'_, Lex (o_), Lex (o'_)) -> ordEqsR (GQ, d'_, o_, o'_)
  | (GQ, d'_, Simul (o_), Simul (o'_)) -> ordEqsR (GQ, d'_, o_, o'_) end
let rec ordEqsR =
  begin function
  | (GQ, d'_, [], []) -> true
  | (GQ, d'_, (o_)::l_, (o'_)::l'_) ->
      (ordEqR (GQ, d'_, o_, o'_)) && (ordEqsR (GQ, d'_, l_, l'_)) end
let rec ltLexR =
  begin function
  | (GQ, d'_, [], []) -> false
  | (GQ, d'_, (o_)::l_, (o'_)::l'_) ->
      (ordLtR (GQ, d'_, o_, o'_)) ||
        ((ordEqR (GQ, d'_, o_, o'_)) && (ltLexR (GQ, d'_, l_, l'_))) end
let rec leLexR (GQ, d'_, l_, l'_) =
  (ltLexR (GQ, d'_, l_, l'_)) || (ordEqsR (GQ, d'_, l_, l'_))
let rec ltSimulR =
  begin function
  | (GQ, d_, [], []) -> false
  | (GQ, d_, (o_)::l_, (o'_)::l'_) ->
      ((ordLtR (GQ, d_, o_, o'_)) && (leSimulR (GQ, d_, l_, l'_))) ||
        ((ordEqR (GQ, d_, o_, o'_)) && (ltSimulR (GQ, d_, l_, l'_))) end
let rec leSimulR =
  begin function
  | (GQ, d_, [], []) -> true
  | (GQ, d_, (o_)::l_, (o'_)::l'_) ->
      (ordLeR (GQ, d_, o_, o'_)) && (leSimulR (GQ, d_, l_, l'_)) end
let rec ltAtomicR (GQ, d_, UsVs, UsVs', sc, k) =
  ltAtomicRW (GQ, d_, (Whnf.whnfEta UsVs), UsVs', sc, k)
let rec ltAtomicRW =
  begin function
  | (GQ, d_, ((us_, ((Root _, s') as vs_)) as UsVs), UsVs', sc, k) ->
      ltR (GQ, d_, UsVs, UsVs', sc, k)
  | (((g_, q_) as GQ), d_, ((Lam (_, u_), s1), (Pi ((Dec, _), v_), s2)),
     ((u'_, s1'), (v'_, s2')), sc, k) ->
      let UsVs' =
        ((u'_, (I.comp (s1', I.shift))), (v'_, (I.comp (s2', I.shift)))) in
      let UsVs = ((u_, (I.dot1 s1)), (v_, (I.dot1 s2))) in
      let d'_ = shiftACtx d_ (begin function | s -> I.comp (s, I.shift) end) in
      ltAtomicR
        (((I.Decl (g_, (N.decLUName (g_, (I.decSub (Dec, s2)))))),
           (I.Decl (q_, All))), d'_, UsVs, UsVs', sc, k) end
let rec leAtomicR (GQ, d_, UsVs, UsVs', sc, k) =
  leAtomicRW (GQ, d_, (Whnf.whnfEta UsVs), UsVs', sc, k)
let rec leAtomicRW =
  begin function
  | (GQ, d_, ((us_, ((Root _, s') as vs_)) as UsVs), UsVs', sc, k) ->
      leR (GQ, d_, UsVs, UsVs', sc, k)
  | (((g_, q_) as GQ), d_, ((Lam (_, u_), s1), (Pi ((Dec, _), v_), s2)),
     ((u'_, s1'), (v'_, s2')), sc, k) ->
      let d'_ = shiftACtx d_ (begin function | s -> I.comp (s, I.shift) end) in
    let UsVs' =
      ((u'_, (I.comp (s1', I.shift))), (v'_, (I.comp (s2', I.shift)))) in
    let UsVs = ((u_, (I.dot1 s1)), (v_, (I.dot1 s2))) in
    leAtomicR
      (((I.Decl (g_, (N.decLUName (g_, (I.decSub (Dec, s2)))))),
         (I.Decl (q_, All))), d'_, UsVs, UsVs', sc, k) end
let rec eqAtomicR (((g_, q_) as GQ), d_, UsVs, UsVs', sc, k) =
  eqAtomicRW (GQ, d_, (Whnf.whnfEta UsVs), (Whnf.whnfEta UsVs'), sc, k)
let rec eqAtomicRW =
  begin function
  | (((g_, q_) as GQ), d_, ((Lam (_, u_), s1), (Pi ((Dec, _), v_), s2)),
     ((Lam (_, u'_), s1'), (Pi ((Dec', _), v'_), s2')), sc, k) ->
      eqAtomicR
        (((I.Decl (g_, (N.decLUName (g_, (I.decSub (Dec, s2)))))),
           (I.Decl (q_, All))),
          (shiftACtx d_ (begin function | s -> I.comp (s, I.shift) end)),
        ((u_, (I.dot1 s1')), (v_, (I.dot1 s2'))),
        ((u'_, (I.dot1 s1')), (v'_, (I.dot1 s2'))), sc, k)
  | (GQ, d_, (us_, ((Root _, s2) as vs_)), (us'_, ((Root _, s2') as vs'_)),
     sc, k) -> eqR (GQ, d_, (us_, vs_), (us'_, vs'_), sc, k)
  | (GQ, d_, (us_, vs_), (us'_, vs'_), sc, k) -> false end(* Fri Feb 25 21:26:39 2005 -fp !!! *)
(* mismatch: not equal *)(* Dec = Dec' *)
let rec ltR (((g_, q_) as GQ), d_, UsVs, UsVs', sc, k) =
  ltRW (GQ, d_, UsVs, (Whnf.whnfEta UsVs'), sc, k)
let rec ltRW =
  begin function
  | (GQ, d_, (us_, vs_), (((Root (Const c, s'_), s') as us'_), vs'_), sc, k)
      ->
      ((if isAtomic (GQ, us'_)
        then begin k (GQ, d_, [], (Less ((us_, vs_), (us'_, vs'_))), sc) end
      else begin
        ltSpineR
          (GQ, d_, (us_, vs_), ((s'_, s'), ((I.constType c), I.id)), sc, k) end)
  (* either leftInstantiate D or  atomic reasoning *))
  | (GQ, d_, (us_, vs_), (((Root (Def c, s'_), s') as us'_), vs'_), sc, k) ->
      ((if isAtomic (GQ, us'_)
        then begin k (GQ, d_, [], (Less ((us_, vs_), (us'_, vs'_))), sc) end
      else begin
        ltSpineR
          (GQ, d_, (us_, vs_), ((s'_, s'), ((I.constType c), I.id)), sc, k) end)
(* either leftInstantiate D or  atomic reasoning *))
| (((g_, q_) as GQ), d_, (us_, vs_),
   (((Root (BVar n, s'_), s') as us'_), vs'_), sc, k) ->
    ((if isAtomic (GQ, us'_)
      then begin k (GQ, d_, [], (Less ((us_, vs_), (us'_, vs'_))), sc) end
    else begin
      (let Dec (_, v'_) = I.ctxDec (g_, n) in
       ltSpineR (GQ, d_, (us_, vs_), ((s'_, s'), (v'_, I.id)), sc, k)) end)
(* either leftInstantiate D or  atomic reasoning *))
| (GQ, d_, _, ((EVar _, _), _), _, _) -> false
| (((g_, q_) as GQ), d_, ((u_, s1), (v_, s2)),
   ((Lam (Dec (_, V1'), u'_), s1'), (Pi ((Dec (_, V2'), _), v'_), s2')), sc,
   k) ->
    ((if Subordinate.equiv ((I.targetFam v_), (I.targetFam V1'))
      then
        begin let x_ = I.newEVar (g_, (I.EClo (V1', s1'))) in
              let sc' =
                begin function
                | () -> (begin isParameter (q_, x_); sc () end) end in
      ((ltR
          (GQ, d_, ((u_, s1), (v_, s2)),
            ((u'_, (I.Dot ((I.Exp x_), s1'))),
              (v'_, (I.Dot ((I.Exp x_), s2')))), sc', k))
        (* enforce that X is only instantiated to parameters *)(* = I.newEVar (I.EClo (V2', s2')) *)) end
else begin
  if Subordinate.below ((I.targetFam V1'), (I.targetFam v_))
  then
    begin (let x_ = I.newEVar (g_, (I.EClo (V1', s1'))) in
           ((ltR
               (GQ, d_, ((u_, s1), (v_, s2)),
                 ((u'_, (I.Dot ((I.Exp x_), s1'))),
                   (v'_, (I.Dot ((I.Exp x_), s2')))), sc, k))
             (* = I.newEVar (I.EClo (V2', s2')) *))) end
  else begin false end end)
(* == I.targetFam V2' *)) end
let rec ltSpineR (GQ, d_, (us_, vs_), (ss'_, vs'_), sc, k) =
  ltSpineRW (GQ, d_, (us_, vs_), (ss'_, (Whnf.whnf vs'_)), sc, k)
let rec ltSpineRW =
  begin function
  | (GQ, d_, (us_, vs_), ((I.Nil, _), _), _, _) -> false
  | (GQ, d_, (us_, vs_), ((SClo (s_, s'), s''), vs'_), sc, k) ->
      ltSpineR (GQ, d_, (us_, vs_), ((s_, (I.comp (s', s''))), vs'_), sc, k)
  | (GQ, d_, (us_, vs_),
     ((App (u'_, s'_), s1'), (Pi ((Dec (_, V1'), _), V2'), s2')), sc, k) ->
      (leAtomicR (GQ, d_, (us_, vs_), ((u'_, s1'), (V1', s2')), sc, k)) ||
        (ltSpineR
           (GQ, d_, (us_, vs_),
             ((s'_, s1'), (V2', (I.Dot ((I.Exp (I.EClo (u'_, s1'))), s2')))),
             sc, k)) end(* cannot happen Sat Apr 20 16:08:30 2002 -bp *)
let rec leR (GQ, d_, UsVs, UsVs', sc, k) =
  leRW (GQ, d_, UsVs, (Whnf.whnfEta UsVs'), sc, k)
let rec leRW =
  begin function
  | (((g_, q_) as GQ), d_, ((u_, s1), (v_, s2)),
     ((Lam (Dec (_, V1'), u'_), s1'), (Pi ((Dec (_, V2'), _), v'_), s2')),
     sc, k) ->
      ((if Subordinate.equiv ((I.targetFam v_), (I.targetFam V1'))
        then
          begin let x_ = I.newEVar (g_, (I.EClo (V1', s1'))) in
                let sc' =
                  begin function | () -> (isParameter (q_, x_)) && (sc ()) end in
                ((leR
                    (GQ, d_, ((u_, s1), (v_, s2)),
                      ((u'_, (I.Dot ((I.Exp x_), s1'))),
                        (v'_, (I.Dot ((I.Exp x_), s2')))), sc', k))
                  (* = I.newEVar (I.EClo (V2', s2')) *)
                  (* enforces that X can only bound to parameter or remain uninstantiated *)) end
  else begin
    if Subordinate.below ((I.targetFam V1'), (I.targetFam v_))
    then
      begin (let x_ = I.newEVar (g_, (I.EClo (V1', s1'))) in
             ((leR
                 (GQ, d_, ((u_, s1), (v_, s2)),
                   ((u'_, (I.Dot ((I.Exp x_), s1'))),
                     (v'_, (I.Dot ((I.Exp x_), s2')))), sc, k))
               (* = I.newEVar (I.EClo (V2', s2')) *))) end
    else begin false end end)(* == I.targetFam V2' *))
| (GQ, d_, UsVs, UsVs', sc, k) ->
    (ltR (GQ, d_, UsVs, UsVs', sc, k)) || (eqR (GQ, d_, UsVs, UsVs', sc, k)) end
(* impossible, if additional invariant assumed (see ltW) *)
let rec eqR (((g_, q_) as GQ), d_, UsVs, UsVs', sc, k) =
  (CSManager.trail
     (begin function | () -> (eq (g_, UsVs, UsVs')) && (sc ()) end))
  || (eqR' (GQ, d_, UsVs, UsVs', sc, k))
let rec eqR' =
  begin function
  | (GQ, d_, (us_, ((Pi ((Dec (_, V2'), _), v'_), s2') as vs_)),
     (us'_, ((Root _, s2'') as vs'_)), sc, k) -> false
  | (GQ, d_, (us_, ((Root _, s2') as vs_)),
     (us'_, ((Pi ((Dec (_, V2''), _), V''), s2'') as vs'_)), sc, k) -> false
  | (GQ, d_, (((Root (Const c, s_), s), vs_) as UsVs),
     (((Root (Const c', s'_), s'), vs'_) as UsVs'), sc, k) ->
      if eqCid (c, c')
      then
        begin eqSpineR
                (GQ, d_, ((s_, s), ((I.constType c), I.id)),
                  ((s'_, s'), ((I.constType c'), I.id)), sc, k) end
      else begin false end
  | (GQ, d_, (((Root (Const c, s_), s) as us_), vs_),
     (((Root (BVar n, s'_), s') as us'_), vs'_), sc, k) ->
      ((if isAtomic (GQ, us'_)
        then begin k (GQ, d_, [], (Eq ((us'_, vs'_), (us_, vs_))), sc) end
      else begin false end)
(* either leftInstantiate D or atomic reasoning *))
| (GQ, d_, (((Root (BVar n, s_), s) as us_), vs_),
   (((Root (Const c, s'_), s') as us'_), vs'_), sc, k) ->
    ((if isAtomic (GQ, us_)
      then begin k (GQ, d_, [], (Eq ((us_, vs_), (us'_, vs'_))), sc) end
    else begin false end)
(* either leftInstantiate D or atomic reasoning *))
| (GQ, d_, (((Root (Def c, s_), s), vs_) as UsVs),
   (((Root (Def c', s'_), s'), vs'_) as UsVs'), sc, k) ->
    if eqCid (c, c')
    then
      begin eqSpineR
              (GQ, d_, ((s_, s), ((I.constType c), I.id)),
                ((s'_, s'), ((I.constType c'), I.id)), sc, k) end
    else begin false end
| (GQ, d_, (((Root (Def c, s_), s) as us_), vs_),
   (((Root (BVar n, s'_), s') as us'_), vs'_), sc, k) ->
    ((if isAtomic (GQ, us'_)
      then begin k (GQ, d_, [], (Eq ((us'_, vs'_), (us_, vs_))), sc) end
    else begin false end)
(* either leftInstantiate D or atomic reasoning *))
| (GQ, d_, (((Root (BVar n, s_), s) as us_), vs_),
   (((Root (Def c, s'_), s') as us'_), vs'_), sc, k) ->
    ((if isAtomic (GQ, us_)
      then begin k (GQ, d_, [], (Eq ((us_, vs_), (us'_, vs'_))), sc) end
    else begin false end)
(* either leftInstantiate D or atomic reasoning *))
| (((g_, q_) as GQ), d_, (((Root (BVar n, s_), s) as us_), vs_),
   (((Root (BVar n', s'_), s') as us'_), vs'_), sc, k) ->
    if n = n'
    then
      begin let Dec (_, v'_) = I.ctxDec (g_, n) in
            eqSpineR
              (GQ, d_, ((s_, s), (v'_, I.id)), ((s'_, s'), (v'_, I.id)), sc,
                k) end
    else begin k (GQ, d_, [], (Eq ((us_, vs_), (us'_, vs'_))), sc) end
| (GQ, d_, UsVs, UsVs', sc, k) -> k (GQ, d_, [], (Eq (UsVs, UsVs')), sc) end
(* UsVs = Lam *)(* either leftInstantiate D or atomic reasoning *)
let rec eqSpineR (GQ, d_, (ss_, vs_), (ss'_, vs'_), sc, k) =
  eqSpineRW (GQ, d_, (ss_, (Whnf.whnf vs_)), (ss'_, (Whnf.whnf vs'_)), sc, k)
let rec eqSpineRW =
  begin function
  | (GQ, d_, ((I.Nil, s), vs_), ((I.Nil, s'), vs'_), sc, k) -> true
  | (GQ, d_, ((SClo (s_, s'), s''), vs_), SsVs', sc, k) ->
      eqSpineR (GQ, d_, ((s_, (I.comp (s', s''))), vs_), SsVs', sc, k)
  | (GQ, d_, SsVs, ((SClo (s'_, s'), s''), vs'_), sc, k) ->
      eqSpineR (GQ, d_, SsVs, ((s'_, (I.comp (s', s''))), vs'_), sc, k)
  | (GQ, d_, ((App (u_, s_), s1), (Pi ((Dec (_, v1_), _), v2_), s2)),
     ((App (u'_, s'_), s1'), (Pi ((Dec (_, V1'), _), V2'), s2')), sc, k) ->
      (eqAtomicR
         (GQ, d_, ((u_, s1), (v1_, s2)), ((u'_, s1'), (V1', s2')), sc, k))
        &&
        (eqSpineR
           (GQ, d_,
             ((s_, s1), (v2_, (I.Dot ((I.Exp (I.EClo (u_, s1))), s2)))),
             ((s'_, s1'), (V2', (I.Dot ((I.Exp (I.EClo (u'_, s1'))), s2')))),
             sc, k))
  | (GQ, d_, SsVs, SsVs', sc, k) -> false end
let rec leftDecompose =
  begin function
  | (((g_, q_) as GQ), [], d'_, p_) -> rightDecompose (GQ, d'_, p_)
  | (GQ, (Less (Arg (UsVs), Arg (UsVs')))::d_, d'_, p_) ->
      ltAtomicL (GQ, d_, d'_, UsVs, UsVs', p_)
  | (GQ, (Less (Lex (o_), Lex (o'_)))::d_, d'_, p_) ->
      ltLexL (GQ, d_, d'_, o_, o'_, p_)
  | (GQ, (Less (Simul (o_), Simul (o'_)))::d_, d'_, p_) ->
      ltSimulL (GQ, d_, d'_, o_, o'_, p_)
  | (GQ, (Leq (Arg (UsVs), Arg (UsVs')))::d_, d'_, p_) ->
      leAtomicL (GQ, d_, d'_, UsVs, UsVs', p_)
  | (GQ, (Leq (Lex (o_), Lex (o'_)))::d_, d'_, p_) ->
      (leftDecompose (GQ, ((Less ((R.Lex o_), (R.Lex o'_))) :: d_), d'_, p_))
        &&
        (leftDecompose (GQ, ((Eq ((R.Lex o_), (R.Lex o'_))) :: d_), d'_, p_))
  | (GQ, (Leq (Simul (o_), Simul (o'_)))::d_, d'_, p_) ->
      leSimulL (GQ, d_, d'_, o_, o'_, p_)
  | (GQ, (Eq (Arg (UsVs), Arg (UsVs')))::d_, d'_, p_) ->
      eqAtomicL (GQ, d_, d'_, UsVs, UsVs', p_)
  | (GQ, (Eq (Lex (o_), Lex (o'_)))::d_, d'_, p_) ->
      eqsL (GQ, d_, d'_, o_, o'_, p_)
  | (GQ, (Eq (Simul (o_), Simul (o'_)))::d_, d'_, p_) ->
      eqsL (GQ, d_, d'_, o_, o'_, p_)
  | (((g_, q_) as GQ), (Pi (Dec, o_))::d_, d'_, p_) ->
      (begin if !Global.chatter > 3
             then
               begin (begin print " Ignoring quantified order ";
                      print
                        (F.makestring_fmt (fmtPredicate (g_, (Pi (Dec, o_))))) end) end
      else begin () end;
  leftDecompose (GQ, d_, d'_, p_) end) end(* drop assumption Pi D. P *)
(* eq *)(* le *)(* less *)
let rec ltLexL =
  begin function
  | (GQ, d_, d'_, [], [], p_) -> true
  | (GQ, d_, d'_, (o_)::l_, (o'_)::l'_, p_) ->
      (leftDecompose (GQ, ((Less (o_, o'_)) :: d_), d'_, p_)) &&
        (ltLexL (GQ, ((Eq (o_, o'_)) :: d_), d'_, l_, l'_, p_)) end
let rec eqsL =
  begin function
  | (GQ, d_, d'_, [], [], p_) -> true
  | (GQ, d_, d'_, (o_)::l_, (o'_)::l'_, p_) ->
      (leftDecompose (GQ, ((Eq (o_, o'_)) :: d_), d'_, p_)) &&
        (eqsL (GQ, d_, d'_, l_, l'_, p_)) end
let rec ltSimulL =
  begin function
  | (GQ, d_, d'_, [], [], p_) -> leftDecompose (GQ, d_, d'_, p_)
  | (GQ, d_, d'_, (o_)::l_, (o'_)::l'_, p_) ->
      (leSimulL (GQ, ((Less (o_, o'_)) :: d_), d'_, l_, l'_, p_)) ||
        (ltSimulL (GQ, ((Eq (o_, o'_)) :: d_), d'_, l_, l'_, p_)) end
let rec leSimulL =
  begin function
  | (GQ, d_, d'_, [], [], p_) -> leftDecompose (GQ, d_, d'_, p_)
  | (GQ, d_, d'_, (o_)::l_, (o'_)::l'_, p_) ->
      leSimulL (GQ, ((Leq (o_, o'_)) :: d_), d'_, l_, l'_, p_) end
let rec ltAtomicL (GQ, d_, d'_, UsVs, UsVs', p_) =
  ltAtomicLW (GQ, d_, d'_, UsVs, (Whnf.whnfEta UsVs'), p_)
let rec ltAtomicLW =
  begin function
  | (((g_, q_) as GQ), d_, d'_, UsVs, (us'_, ((Root _, s') as vs'_)), p_) ->
      ltL (GQ, d_, d'_, UsVs, (us'_, vs'_), p_)
  | (((g_, q_) as GQ), d_, d'_, ((u_, s1), (v_, s2)),
     ((Lam (_, u'_), s1'), (Pi ((Dec', _), v'_), s2')), p_) ->
      let d1_ = shiftRCtx d_ (begin function | s -> I.comp (s, I.shift) end) in
    let D1' = shiftACtx d'_ (begin function | s -> I.comp (s, I.shift) end) in
    let UsVs = ((u_, (I.comp (s1, I.shift))), (v_, (I.comp (s2, I.shift)))) in
    let UsVs' = ((u'_, (I.dot1 s1')), (v'_, (I.dot1 s2'))) in
    let p'_ = shiftP p_ (begin function | s -> I.comp (s, I.shift) end) in
    ltAtomicL
      (((I.Decl (g_, (N.decLUName (g_, (I.decSub (Dec', s2')))))),
         (I.Decl (q_, All))), d1_, D1', UsVs, UsVs', p'_) end
let rec leAtomicL (GQ, d_, d'_, UsVs, UsVs', p_) =
  leAtomicLW (GQ, d_, d'_, UsVs, (Whnf.whnfEta UsVs'), p_)
let rec leAtomicLW =
  begin function
  | (GQ, d_, d'_, UsVs, (us'_, ((Root (h_, s_), s') as vs'_)), p_) ->
      leL (GQ, d_, d'_, UsVs, (us'_, vs'_), p_)
  | (((g_, q_) as GQ), d_, d'_, ((u_, s1), (v_, s2)),
     ((Lam (_, u'_), s1'), (Pi ((Dec', _), v'_), s2')), p_) ->
      let d1_ = shiftRCtx d_ (begin function | s -> I.comp (s, I.shift) end) in
    let D1' = shiftACtx d'_ (begin function | s -> I.comp (s, I.shift) end) in
    let UsVs = ((u_, (I.comp (s1, I.shift))), (v_, (I.comp (s2, I.shift)))) in
    let UsVs' = ((u'_, (I.dot1 s1')), (v'_, (I.dot1 s2'))) in
    let p'_ = shiftP p_ (begin function | s -> I.comp (s, I.shift) end) in
    leAtomicL
      (((I.Decl (g_, (N.decLUName (g_, (I.decSub (Dec', s2')))))),
         (I.Decl (q_, All))), d1_, D1', UsVs, UsVs', p'_) end
let rec eqAtomicL (GQ, d_, d'_, UsVs, UsVs', p_) =
  eqAtomicLW (GQ, d_, d'_, (Whnf.whnfEta UsVs), (Whnf.whnfEta UsVs'), p_)
let rec eqAtomicLW =
  begin function
  | (GQ, d_, d'_, (us_, ((Root _, s) as vs_)),
     (us'_, ((Root _, s') as vs'_)), p_) ->
      eqL (GQ, d_, d'_, (us_, vs_), (us'_, vs'_), p_)
  | (GQ, d_, d'_, (us_, ((Root _, s) as vs_)), (us'_, ((Pi _, s') as vs'_)),
     p_) -> true
  | (GQ, d_, d'_, (us_, ((Pi _, s) as vs_)), (us'_, ((Root _, s') as vs'_)),
     p_) -> true
  | (GQ, d_, d'_, (us_, ((Pi _, s) as vs_)), (us'_, ((Pi _, s') as vs'_)),
     p_) ->
      leftDecompose (GQ, d_, ((Eq ((us_, vs_), (us'_, vs'_))) :: d'_), p_) end
let rec leL (GQ, d_, d'_, UsVs, UsVs', p_) =
  (ltAtomicL (GQ, d_, d'_, UsVs, UsVs', p_)) &&
    (eqAtomicL (GQ, d_, d'_, UsVs, UsVs', p_))
let rec ltL (GQ, d_, d'_, UsVs, (us'_, vs'_), p_) =
  ltLW (GQ, d_, d'_, UsVs, ((Whnf.whnf us'_), vs'_), p_)
let rec ltLW =
  begin function
  | (((g_, q_) as GQ), d_, d'_, UsVs,
     (((Root (BVar n, s'_), s') as us'_), vs'_), p_) ->
      if isAtomic (GQ, us'_)
      then
        begin leftDecompose
                (GQ, d_, ((Less (UsVs, (us'_, vs'_))) :: d'_), p_) end
      else begin
        (let Dec (_, v'_) = I.ctxDec (g_, n) in
         ltSpineL (GQ, d_, d'_, UsVs, ((s'_, s'), (v'_, I.id)), p_)) end
  | (GQ, d_, d'_, UsVs, ((Root (Const c, s'_), s'), vs'_), p_) ->
      ltSpineL (GQ, d_, d'_, UsVs, ((s'_, s'), ((I.constType c), I.id)), p_)
  | (GQ, d_, d'_, UsVs, ((Root (Def c, s'_), s'), vs'_), p_) ->
      ltSpineL (GQ, d_, d'_, UsVs, ((s'_, s'), ((I.constType c), I.id)), p_) end
let rec ltSpineL (GQ, d_, d'_, UsVs, (ss'_, vs'_), p_) =
  ltSpineLW (GQ, d_, d'_, UsVs, (ss'_, (Whnf.whnf vs'_)), p_)
let rec ltSpineLW =
  begin function
  | (GQ, d_, d'_, UsVs, ((I.Nil, _), _), _) -> true
  | (GQ, d_, d'_, UsVs, ((SClo (s_, s'), s''), vs'_), p_) ->
      ltSpineL (GQ, d_, d'_, UsVs, ((s_, (I.comp (s', s''))), vs'_), p_)
  | (GQ, d_, d'_, UsVs,
     ((App (u'_, s'_), s1'), (Pi ((Dec (_, V1'), _), V2'), s2')), p_) ->
      (leAtomicL (GQ, d_, d'_, UsVs, ((u'_, s1'), (V1', s2')), p_)) &&
        (ltSpineL
           (GQ, d_, d'_, UsVs,
             ((s'_, s1'), (V2', (I.Dot ((I.Exp (I.EClo (u'_, s1'))), s2')))),
             p_)) end
let rec eqL (GQ, d_, d'_, UsVs, UsVs', p_) =
  eqLW (GQ, d_, d'_, (Whnf.whnfEta UsVs), (Whnf.whnfEta UsVs'), p_)
let rec eqLW =
  begin function
  | (GQ, d_, d'_, (us_, ((Pi ((Dec (_, V2'), _), v'_), s2') as vs_)),
     (us'_, ((Pi ((Dec (_, V2''), _), V''), s2'') as vs'_)), p_) ->
      leftDecompose (GQ, d_, ((Eq ((us_, vs_), (us'_, vs'_))) :: d'_), p_)
  | (GQ, d_, d'_, (us_, ((Pi ((Dec (_, V2'), _), v'_), s2') as vs_)),
     (us'_, ((Root _, s2'') as vs'_)), p_) -> true
  | (GQ, d_, d'_, (us_, ((Root _, s2') as vs_)),
     (us'_, ((Pi ((Dec (_, V2''), _), V''), s2'') as vs'_)), p_) -> true
  | (GQ, d_, d'_, (((Root (Const c, s_), s), vs_) as UsVs),
     (((Root (Const c', s'_), s'), vs'_) as UsVs'), p_) ->
      if eqCid (c, c')
      then
        begin eqSpineL
                (GQ, d_, d'_, ((s_, s), ((I.constType c), I.id)),
                  ((s'_, s'), ((I.constType c'), I.id)), p_) end
      else begin true end
  | (GQ, d_, d'_, (((Root (Const c, s_), s) as us_), vs_),
     (((Root (BVar n, s'_), s') as us'_), vs'_), p_) ->
      if isAtomic (GQ, us'_)
      then
        begin leftDecompose
                (GQ, d_, ((Eq ((us'_, vs'_), (us_, vs_))) :: d'_), p_) end
      else begin true end
| (GQ, d_, d'_, (((Root (BVar n, s_), s) as us_), vs_),
   (((Root (Const c, s'_), s') as us'_), vs'_), p_) ->
    if isAtomic (GQ, us_)
    then
      begin leftDecompose
              (GQ, d_, ((Eq ((us_, vs_), (us'_, vs'_))) :: d'_), p_) end
    else begin true end
| (GQ, d_, d'_, (((Root (Def c, s_), s), vs_) as UsVs),
   (((Root (Def c', s'_), s'), vs'_) as UsVs'), p_) ->
    if eqCid (c, c')
    then
      begin eqSpineL
              (GQ, d_, d'_, ((s_, s), ((I.constType c), I.id)),
                ((s'_, s'), ((I.constType c'), I.id)), p_) end
    else begin true end
| (GQ, d_, d'_, (((Root (Def c, s_), s) as us_), vs_),
   (((Root (BVar n, s'_), s') as us'_), vs'_), p_) ->
    if isAtomic (GQ, us'_)
    then
      begin leftDecompose
              (GQ, d_, ((Eq ((us'_, vs'_), (us_, vs_))) :: d'_), p_) end
    else begin true end
| (GQ, d_, d'_, (((Root (BVar n, s_), s) as us_), vs_),
   (((Root (Def c, s'_), s') as us'_), vs'_), p_) ->
    if isAtomic (GQ, us_)
    then
      begin leftDecompose
              (GQ, d_, ((Eq ((us_, vs_), (us'_, vs'_))) :: d'_), p_) end
    else begin true end
| (((g_, q_) as GQ), d_, d'_, (((Root (BVar n, s_), s) as us_), vs_),
   (((Root (BVar n', s'_), s') as us'_), vs'_), p_) ->
    if n = n'
    then
      begin let Dec (_, v'_) = I.ctxDec (g_, n) in
            eqSpineL
              (GQ, d_, d'_, ((s_, s), (v'_, I.id)), ((s'_, s'), (v'_, I.id)),
                p_) end
    else begin
      leftDecompose (GQ, d_, ((Eq ((us_, vs_), (us'_, vs'_))) :: d'_), p_) end
| (GQ, d_, d'_, UsVs, UsVs', p_) ->
    leftDecompose (GQ, d_, ((Eq (UsVs, UsVs')) :: d'_), p_) end(* UsVs = Lam *)
(*
     | eqLW (GQ, D, D', UsVs as ((I.Root (I.BVar n, I.Nil), s), Vs),
            UsVs' as ((I.Root (I.BVar n', I.Nil), s'), Vs'), P) =
         if (n = n')
           then leftDecompose (GQ, D, D', P)
         else
           leftDecompose (GQ, D, (Eq(UsVs, UsVs') :: D'), P)

*)
let rec eqSpineL (GQ, d_, d'_, (ss_, vs_), (ss'_, vs'_), p_) =
  eqSpineLW
    (GQ, d_, d'_, (ss_, (Whnf.whnf vs_)), (ss'_, (Whnf.whnf vs'_)), p_)
let rec eqSpineLW =
  begin function
  | (GQ, d_, d'_, ((I.Nil, s), vs_), ((I.Nil, s'), vs'_), p_) ->
      leftDecompose (GQ, d_, d'_, p_)
  | (GQ, d_, d'_, ((SClo (s_, s'), s''), vs_), SsVs', p_) ->
      eqSpineL (GQ, d_, d'_, ((s_, (I.comp (s', s''))), vs_), SsVs', p_)
  | (GQ, d_, d'_, SsVs, ((SClo (s'_, s'), s''), vs'_), p_) ->
      eqSpineL (GQ, d_, d'_, SsVs, ((s'_, (I.comp (s', s''))), vs'_), p_)
  | (GQ, d_, d'_, ((App (u_, s_), s1), (Pi ((Dec (_, v1_), _), v2_), s2)),
     ((App (u'_, s'_), s1'), (Pi ((Dec (_, V1'), _), V2'), s2')), p_) ->
      let d1_ =
        (Eq ((R.Arg ((u_, s1), (v1_, s2))), (R.Arg ((u'_, s1'), (V1', s2')))))
          :: d_ in
      eqSpineL
        (GQ, d1_, d'_,
          ((s_, s1), (v2_, (I.Dot ((I.Exp (I.EClo (u_, s1))), s2)))),
          ((s'_, s1'), (V2', (I.Dot ((I.Exp (I.EClo (u'_, s1'))), s2')))),
          p_) end
let rec deduce (g_, q_, d_, p_) = leftDecompose ((g_, q_), d_, [], p_)
let deduce = deduce
let shiftRCtx = shiftRCtx
let shiftPred = shiftP end
