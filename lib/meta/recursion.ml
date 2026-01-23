module type MTPRECURSION  =
  sig
    module StateSyn : STATESYN
    exception Error of string 
    type nonrec operator
    val expand : StateSyn.state_ -> operator
    val apply : operator -> StateSyn.state_
    val menu : operator -> string
  end


module MTPRecursion(MTPRecursion:sig
                                   module MTPGlobal : MTPGLOBAL
                                   module Global : GLOBAL
                                   module StateSyn' : STATESYN
                                   module Abstract : ABSTRACT
                                   module MTPAbstract : MTPABSTRACT
                                   module FunTypeCheck : FUNTYPECHECK
                                   module MTPrint : MTPRINT
                                   module Whnf : WHNF
                                   module Unify : UNIFY
                                   module Conv : CONV
                                   module Names : NAMES
                                   module Subordinate : SUBORDINATE
                                   module Print : PRINT
                                   module TypeCheck : TYPECHECK
                                   module Formatter : FORMATTER
                                   module FunPrint : FUNPRINT
                                 end) : MTPRECURSION =
  struct
    module StateSyn = StateSyn'
    exception Error of string 
    type nonrec operator = StateSyn.state_
    module I = IntSyn
    module F = FunSyn
    module S = StateSyn
    module N = Names
    module Fmt = Formatter
    module A = MTPAbstract
    type dec_ =
      | Lemma of (int * F.for_) 
    let rec closedCtx =
      begin function
      | I.Null -> ()
      | Decl (g_, d_) ->
          if Abstract.closedDec (g_, (d_, I.id)) then begin raise Domain end
          else begin closedCtx g_ end end
let rec spine =
  begin function
  | 0 -> I.Nil
  | n -> I.App ((I.Root ((I.BVar n), I.Nil)), (spine (n - 1))) end
let rec someEVars =
  begin function
  | (g_, [], s) -> s
  | (g_, (Dec (_, v_))::l_, s) ->
      someEVars
        (g_, l_, (I.Dot ((I.Exp (I.newEVar (g_, (I.EClo (v_, s))))), s))) end
let rec ctxSub =
  begin function
  | ([], s) -> []
  | ((d_)::g_, s) -> (::) (I.decSub (d_, s)) ctxSub (g_, (I.dot1 s)) end
let rec appendCtx =
  begin function
  | (GB1, t_, []) -> GB1
  | ((g1_, b1_), t_, (d_)::g2_) ->
      appendCtx (((I.Decl (g1_, d_)), (I.Decl (b1_, t_))), t_, g2_) end
let rec createCtx =
  begin function
  | ((g_, b_), [], s) -> ((g_, b_), s, ((begin function | AF -> AF end)))
  | ((g_, b_), n::ll, s) ->
      let LabelDec (l, g1_, g2_) = F.labelLookup n in
      let t = someEVars (g_, g1_, I.id) in
      let G2' = ctxSub (g2_, t) in
      let (g'_, b'_) = appendCtx ((g_, b_), (S.Parameter (Some n)), G2') in
      let s' = I.comp (s, (I.Shift (List.length G2'))) in
      let (GB'', s'', af'') = createCtx ((g'_, b'_), ll, s') in
      (((GB'', s'',
          ((begin function
            | AF -> A.Block ((g_, t, (List.length g1_), G2'), (af'' AF)) end))))
        (* G |- s' : G1 *)(* G |- G2' ctx *)(* . |- G' = G, G2' ctx *)
        (* G' |- s'' : G0 *)) end
let rec createEVars =
  begin function
  | (g_, I.Null) -> I.Shift (I.ctxLength g_)
  | (g_, Decl (g0_, Dec (_, v_))) ->
      let s = createEVars (g_, g0_) in
      I.Dot ((I.Exp (I.newEVar (g_, (I.EClo (v_, s))))), s) end
let rec checkCtx =
  begin function
  | (g_, [], (v2_, s)) -> false
  | (g_, (Dec (_, v1_) as d_)::g2_, (v2_, s)) ->
      (CSManager.trail
         (begin function | () -> Unify.unifiable (g_, (v1_, I.id), (v2_, s)) end))
      || (checkCtx ((I.Decl (g_, d_)), g2_, (v2_, (I.comp (s, I.shift))))) end
let rec checkLabels
  ((((g'_, b'_), (v_, s), ll, l))(* as nil *)) =
  if l < 0 then begin None end
  else begin
    (let LabelDec (name, g1_, g2_) = F.labelLookup l in
     let s = someEVars (g'_, g1_, I.id) in
     let G2' = ctxSub (g2_, s) in
     let t = someEVars (g'_, g1_, I.id) in
     let G2' = ctxSub (g2_, t) in
     ((if (not (List.exists (begin function | l' -> l = l' end) ll)) &&
         (checkCtx (g'_, G2', (v_, s)))
       then begin Some l end
       else begin checkLabels ((g'_, b'_), (v_, s), ll, (l - 1)) end)
       (* G' |- t : G1 *)(* G |- G2' ctx *))) end
let rec appendRL =
  begin function
  | ([], ds_) -> ds_
  | ((Lemma (n, f_) as l_)::ds1_, ds2_) ->
      let ds'_ = appendRL (ds1_, ds2_) in
      if
        List.exists
          (begin function
           | Lemma (n', f'_) ->
               (n = n') && (F.convFor ((f_, I.id), (f'_, I.id))) end)
        ds'_ then begin ds'_ end
      else begin l_ :: ds'_ end end
let rec recursion
  ((nih, Gall, Fex, Oex), (ncurrent, (g0_, b0_), ll, Ocurrent, h_, f_)) =
  let ((g'_, b'_), s', af) = createCtx ((g0_, b0_), ll, I.id) in
  let t' = createEVars (g'_, Gall) in
  let AF = af (A.Head (g'_, (Fex, t'), (I.ctxLength Gall))) in
  let Oex' = S.orderSub (Oex, t') in
  let Ocurrent' = S.orderSub (Ocurrent, s') in
  let rec sc (ds_) =
    let Fnew = A.abstractApproxFor AF in
    if
      List.exists
        (begin function
         | (nhist, Fhist) ->
             (nih = nhist) && (F.convFor ((Fnew, I.id), (Fhist, I.id))) end)
      h_ then begin ds_ end
    else begin (Lemma (nih, Fnew)) :: ds_ end in
  let rec ac ((g'_, b'_), vs_, ds_) =
    begin match checkLabels ((g'_, b'_), vs_, ll, ((F.labelSize ()) - 1))
          with
    | None -> ds_
    | Some l' ->
        let ds'_ =
          recursion
            ((nih, Gall, Fex, Oex),
              (ncurrent, (g0_, b0_), (l' :: ll), Ocurrent, h_, f_)) in
        appendRL (ds'_, ds_) end in
  ((if ncurrent < nih
    then begin ordle ((g'_, b'_), Oex', Ocurrent', sc, ac, []) end
    else begin ordlt ((g'_, b'_), Oex', Ocurrent', sc, ac, []) end)
    (* G' |- s' : G0 *)(* G' |- t' : Gall *))
let rec set_parameter
  (((g1_, b1_) as GB), (EVar (r, _, v_, _) as x_), k, sc, ac, ds_) =
  let rec set_parameter' =
    begin function
    | ((I.Null, I.Null), _, ds_) -> ds_
    | ((Decl (g_, d_), Decl (b_, Parameter _)), k, ds_) ->
        let Dec (_, v'_) as d'_ = I.decSub (d_, (I.Shift k)) in
        let ds'_ =
          CSManager.trail
            (begin function
             | () ->
                 if
                   (Unify.unifiable (g1_, (v_, I.id), (v'_, I.id))) &&
                     (Unify.unifiable
                        (g1_, (x_, I.id),
                          ((I.Root ((I.BVar k), I.Nil)), I.id)))
                 then begin sc ds_ end else begin ds_ end end) in
  set_parameter' ((g_, b_), (k + 1), ds'_)
  | ((Decl (g_, d_), Decl (b_, _)), k, ds_) ->
      set_parameter' ((g_, b_), (k + 1), ds_) end in
((set_parameter' (GB, 1, ds_))
(* set_parameter' ((G, B), k, Ds) = Ds'

           Invariant:
           If    G1, D < G
        *))
let rec ltinit (GB, k, (us_, vs_), UsVs', sc, ac, ds_) =
  ltinitW (GB, k, (Whnf.whnfEta (us_, vs_)), UsVs', sc, ac, ds_)
let rec ltinitW =
  begin function
  | (GB, k, (us_, ((Root _, _) as vs_)), UsVs', sc, ac, ds_) ->
      lt (GB, k, (us_, vs_), UsVs', sc, ac, ds_)
  | ((g_, b_), k, ((Lam (d1_, u_), s1), (Pi (d2_, v_), s2)),
     ((u'_, s1'), (v'_, s2')), sc, ac, ds_) ->
      ltinit
        (((I.Decl (((g_, (I.decSub (d1_, s1))))
             (* = I.decSub (D2, s2) *))),
           (I.Decl (b_, (S.Parameter None)))), (k + 1),
          ((u_, (I.dot1 s1)), (v_, (I.dot1 s2))),
          ((u'_, (I.comp (s1', I.shift))), (v'_, (I.comp (s2', I.shift)))),
          sc, ac, ds_) end
let rec lt (GB, k, (us_, vs_), (us'_, vs'_), sc, ac, ds_) =
  ltW (GB, k, (us_, vs_), (Whnf.whnfEta (us'_, vs'_)), sc, ac, ds_)
let rec ltW =
  begin function
  | (GB, k, (us_, vs_), ((Root (Const c, s'_), s'), vs'_), sc, ac, ds_) ->
      ltSpine
        (GB, k, (us_, vs_), ((s'_, s'), ((I.constType c), I.id)), sc, ac,
          ds_)
  | (((g_, b_) as GB), k, (us_, vs_), ((Root (BVar n, s'_), s'), vs'_), sc,
     ac, ds_) ->
      (begin match I.ctxLookup (b_, n) with
       | Parameter _ ->
           let Dec (_, v'_) = I.ctxDec (g_, n) in
           ltSpine (GB, k, (us_, vs_), ((s'_, s'), (v'_, I.id)), sc, ac, ds_)
       | Lemma _ -> ds_ end)
  | (GB, _, _, ((EVar _, _), _), _, _, ds_) -> ds_
  | (((g_, b_) as GB), k, ((u_, s1), (v_, s2)),
     ((Lam ((Dec (_, V1') as d_), u'_), s1'),
      (Pi ((Dec (_, V2'), _), v'_), s2')),
     sc, ac, ds_) ->
      let ds'_ = ds_ in
      ((if Subordinate.equiv ((I.targetFam v_), (I.targetFam V1'))
        then
          begin let x_ = I.newEVar (g_, (I.EClo (V1', s1'))) in
                let sc' =
                  begin function
                  | Ds'' -> set_parameter (GB, x_, k, sc, ac, Ds'') end in
                ((lt
                    (GB, k, ((u_, s1), (v_, s2)),
                      ((u'_, (I.Dot ((I.Exp x_), s1'))),
                        (v'_, (I.Dot ((I.Exp x_), s2')))), sc', ac, ds'_))
                  (* enforce that X gets only bound to parameters *)
                  (* = I.newEVar (I.EClo (V2', s2')) *)) end
      else begin
        if Subordinate.below ((I.targetFam V1'), (I.targetFam v_))
        then
          begin (let x_ = I.newEVar (g_, (I.EClo (V1', s1'))) in
                 ((lt
                     (GB, k, ((u_, s1), (v_, s2)),
                       ((u'_, (I.Dot ((I.Exp x_), s1'))),
                         (v'_, (I.Dot ((I.Exp x_), s2')))), sc, ac, ds'_))
                   (* = I.newEVar (I.EClo (V2', s2')) *))) end
        else begin ds'_ end end)
(* == I.targetFam V2' *)(* ctxBlock (GB, I.EClo (V1', s1'), k, sc, ac, Ds) *)) end
(*            else Ds *)(* k might not be needed any more: Check --cs *)
(*          if n <= k then   n must be a local variable *)
let rec ltSpine (GB, k, (us_, vs_), (ss'_, vs'_), sc, ac, ds_) =
  ltSpineW (GB, k, (us_, vs_), (ss'_, (Whnf.whnf vs'_)), sc, ac, ds_)
let rec ltSpineW =
  begin function
  | (GB, k, (us_, vs_), ((I.Nil, _), _), _, _, ds_) -> ds_
  | (GB, k, (us_, vs_), ((SClo (s_, s'), s''), vs'_), sc, ac, ds_) ->
      ltSpineW
        (GB, k, (us_, vs_), ((s_, (I.comp (s', s''))), vs'_), sc, ac, ds_)
  | (GB, k, (us_, vs_),
     ((App (u'_, s'_), s1'), (Pi ((Dec (_, V1'), _), V2'), s2')), sc, ac,
     ds_) ->
      let ds'_ =
        le (GB, k, (us_, vs_), ((u'_, s1'), (V1', s2')), sc, ac, ds_) in
      ltSpine
        (GB, k, (us_, vs_),
          ((s'_, s1'), (V2', (I.Dot ((I.Exp (I.EClo (u'_, s1'))), s2')))),
          sc, ac, ds'_) end
let rec eq ((g_, b_), (us_, vs_), (us'_, vs'_), sc, ac, ds_) =
  CSManager.trail
    (begin function
     | () ->
         if
           (Unify.unifiable (g_, vs_, vs'_)) &&
             (Unify.unifiable (g_, us_, us'_))
         then begin sc ds_ end else begin ds_ end end)
let rec le (GB, k, (us_, vs_), (us'_, vs'_), sc, ac, ds_) =
  let ds'_ = eq (GB, (us_, vs_), (us'_, vs'_), sc, ac, ds_) in
  leW (GB, k, (us_, vs_), (Whnf.whnfEta (us'_, vs'_)), sc, ac, ds'_)
let rec leW =
  begin function
  | (((g_, b_) as GB), k, ((u_, s1), (v_, s2)),
     ((Lam ((Dec (_, V1') as d_), u'_), s1'),
      (Pi ((Dec (_, V2'), _), v'_), s2')),
     sc, ac, ds_) ->
      let ds'_ = ac (GB, (V1', s1'), ds_) in
      ((if Subordinate.equiv ((I.targetFam v_), (I.targetFam V1'))
        then
          begin let x_ = I.newEVar (g_, (I.EClo (V1', s1'))) in
                let sc' =
                  begin function
                  | Ds'' -> set_parameter (GB, x_, k, sc, ac, Ds'') end in
                ((le
                    (GB, k, ((u_, s1), (v_, s2)),
                      ((u'_, (I.Dot ((I.Exp x_), s1'))),
                        (v'_, (I.Dot ((I.Exp x_), s2')))), sc', ac, ds'_))
                  (* = I.newEVar (I.EClo (V2', s2')) *)
                  (* enforces that X can only bound to parameter *)) end
      else begin
        if Subordinate.below ((I.targetFam V1'), (I.targetFam v_))
        then
          begin (let x_ = I.newEVar (g_, (I.EClo (V1', s1'))) in
                 let sc' = sc in
                 let Ds'' =
                   le
                     (GB, k, ((u_, s1), (v_, s2)),
                       ((u'_, (I.Dot ((I.Exp x_), s1'))),
                         (v'_, (I.Dot ((I.Exp x_), s2')))), sc', ac, ds'_) in
                 ((Ds'')
                   (* = I.newEVar (I.EClo (V2', s2')) *)
                   (*              val sc'' = fn Ds'' => set_parameter (GB, X, k, sc, ac, Ds'')    BUG -cs *))) end
        else begin ds'_ end end)(* == I.targetFam V2' *))
| (GB, k, (us_, vs_), (us'_, vs'_), sc, ac, ds_) ->
    lt (GB, k, (us_, vs_), (us'_, vs'_), sc, ac, ds_) end
let rec ordlt =
  begin function
  | (GB, Arg (UsVs), Arg (UsVs'), sc, ac, ds_) ->
      ltinit (GB, 0, UsVs, UsVs', sc, ac, ds_)
  | (GB, Lex (l_), Lex (l'_), sc, ac, ds_) ->
      ordltLex (GB, l_, l'_, sc, ac, ds_)
  | (GB, Simul (l_), Simul (l'_), sc, ac, ds_) ->
      ordltSimul (GB, l_, l'_, sc, ac, ds_) end
let rec ordltLex =
  begin function
  | (GB, [], [], sc, ac, ds_) -> ds_
  | (GB, (o_)::l_, (o'_)::l'_, sc, ac, ds_) ->
      let ds'_ =
        CSManager.trail
          (begin function | () -> ordlt (GB, o_, o'_, sc, ac, ds_) end) in
    ordeq
      (GB, o_, o'_,
        (begin function | Ds'' -> ordltLex (GB, l_, l'_, sc, ac, Ds'') end),
      ac, ds'_) end
let rec ordltSimul =
  begin function
  | (GB, [], [], sc, ac, ds_) -> ds_
  | (GB, (o_)::l_, (o'_)::l'_, sc, ac, ds_) ->
      let Ds'' =
        CSManager.trail
          (begin function
           | () ->
               ordlt
                 (GB, o_, o'_,
                   (begin function
                    | ds'_ -> ordleSimul (GB, l_, l'_, sc, ac, ds'_) end),
                 ac, ds_) end) in
ordeq
  (GB, o_, o'_,
    (begin function | ds'_ -> ordltSimul (GB, l_, l'_, sc, ac, ds'_) end),
  ac, Ds'') end
let rec ordleSimul =
  begin function
  | (GB, [], [], sc, ac, ds_) -> sc ds_
  | (GB, (o_)::l_, (o'_)::l'_, sc, ac, ds_) ->
      ordle
        (GB, o_, o'_,
          (begin function | ds'_ -> ordleSimul (GB, l_, l'_, sc, ac, ds'_) end),
        ac, ds_) end
let rec ordeq =
  begin function
  | ((g_, b_), Arg (us_, vs_), Arg (us'_, vs'_), sc, ac, ds_) ->
      if
        (Unify.unifiable (g_, vs_, vs'_)) &&
          (Unify.unifiable (g_, us_, us'_))
      then begin sc ds_ end else begin ds_ end
  | (GB, Lex (l_), Lex (l'_), sc, ac, ds_) ->
      ordeqs (GB, l_, l'_, sc, ac, ds_)
  | (GB, Simul (l_), Simul (l'_), sc, ac, ds_) ->
      ordeqs (GB, l_, l'_, sc, ac, ds_) end
let rec ordeqs =
  begin function
  | (GB, [], [], sc, ac, ds_) -> sc ds_
  | (GB, (o_)::l_, (o'_)::l'_, sc, ac, ds_) ->
      ordeq
        (GB, o_, o'_,
          (begin function | ds'_ -> ordeqs (GB, l_, l'_, sc, ac, ds'_) end),
        ac, ds_) end
let rec ordle (GB, o_, o'_, sc, ac, ds_) =
  let ds'_ =
    CSManager.trail
      (begin function | () -> ordeq (GB, o_, o'_, sc, ac, ds_) end) in
ordlt (GB, o_, o'_, sc, ac, ds'_)
let rec skolem =
  begin function
  | ((du, de), GB, w, F.True, sc) -> (GB, w)
  | ((du, de), GB, w, All (Prim (d_), f_), sc) ->
      skolem
        (((du + 1), de), GB, w, f_,
          ((begin function
            | (s, de') ->
                let (s', v'_, f'_) = sc (s, de') in
                ((((I.dot1 s'),
                    ((begin function
                      | v_ ->
                          v'_
                            (Abstract.piDepend
                               (((Whnf.normalizeDec (d_, s')), I.Meta),
                                 (Whnf.normalize (v_, I.id)))) end)),
                  ((begin function
                    | f_ -> f'_ (F.All ((F.Prim (I.decSub (d_, s'))), f_)) end))))
            (* _   : GB, Ds, G'[...], D[?] |- _ : GB, G, D *)(* _   : maps (GB, Ds, G'[....], D[?] |- V : type) to  (GB, Ds, |- {G[....], D[?]} V : type) *)
            (* _   : maps (GB, Ds, G'[....], D[?] |- F : for) to  (GB, Ds, |- {{G[....], D[?]}} F : for) *)
            (* s'  : GB, Ds, G'[...] |- s' : GB, G *)
            (* V'  : maps (GB, Ds, G'[...] |- V type) to (GB, Ds |- {G'[...]} V type) *)
            (* F'  : maps (GB, Ds, G'[...] |- F for) to (GB, Ds |- {{G'[...]}} F for) *)) end)
  (* s'  :  GB, Ds |- s : GB   *)))
| ((du, de), (g_, b_), w, Ex (Dec (name, v_), f_), sc) ->
    let (s', v'_, f'_) = sc (w, de) in
    let v1_ = I.EClo (v_, s') in
    let v2_ = Whnf.normalize ((v'_ v1_), I.id) in
    let f1_ = F.Ex ((I.Dec (name, v1_)), F.True) in
    let f2_ = f'_ f1_ in
    let _ =
      if !Global.doubleCheck then begin FunTypeCheck.isFor (g_, f2_) end
      else begin () end in
    let d2_ = I.Dec (None, v2_) in
    let t2_ =
      begin match f2_ with
      | All _ -> S.Lemma S.RL
      | _ -> S.Lemma (S.Splits !MTPGlobal.maxSplit) end in
    ((skolem
        ((du, (de + 1)), ((I.Decl (g_, d2_)), (I.Decl (b_, t2_))),
          (I.comp (w, I.shift)), f_,
          ((begin function
            | (s, de') ->
                let (s', v'_, f'_) = sc (s, de') in
                ((((I.Dot
                      ((I.Exp
                          (I.Root ((I.BVar (du + (de' - de))), (spine du)))),
                        s')), v'_, f'_))
                  (* _ : GB, Ds, D2, G'[...] |- s'' : GB, G, D *)
                  (* s'  : GB, Ds, D2, G'[...] |- s' : GB, G *)(* V'  : maps (GB, Ds, D2, G'[...] |- V type) to (GB, Ds, D2 |- {G'[...]} V type) *)
                  (* F'  : maps (GB, Ds, D2, G'[...] |- F for) to (GB, Ds, D2 |- {{G'[...]}} F for) *)) end)
        (* s   : GB, Ds, D2 |- s : GB *))))
      (* s'  : GB, Ds, G'[...] |- s' : GB, G *)(* V'  : maps  (GB, Ds, G'[...] |- V : type)   to   (GB, Ds |- {G'[...]} V : type) *)
      (* F'  : maps  (GB, Ds, G'[...] |- F : for)    to   (GB, Ds |- {{G'[...]}} F : for) *)
      (* V1  : GB, Ds, G'[...] |- V1 = V [s'] : type *)
      (* V2  : GB, Ds |- {G'[...]} V2 : type *)(* F1  : GB, Ds, G'[...] |- F1 : for *)
      (* F2  : GB, Ds |- {{G'[...]}} F2 : for *)(* D2  : GB, Ds |- D2 : type *)
      (* T2  : GB, Ds |- T2 : tag *)) end(* V   : GB, G |- V type *)
let rec updateState =
  begin function
  | (s_, ([], s)) -> s_
  | ((State (n, (g_, b_), (IH, OH), d, o_, h_, f_) as s_),
     ((Lemma (n', Frl'))::l_, s)) ->
      let ((G'', B''), s') =
        skolem
          ((0, 0), (g_, b_), I.id, (F.forSub (Frl', s)),
            (begin function
             | (s', _) -> (s', ((begin function | v'_ -> v'_ end)),
                 ((begin function | f'_ -> f'_ end))) end)) in
let s'' = I.comp (s, s') in
updateState
  ((S.State
      (n, (G'', B''), (IH, OH), d, (S.orderSub (o_, s')),
        ((::) (n', (F.forSub (Frl', s''))) map
           (begin function | (n', f'_) -> (n', (F.forSub (f'_, s'))) end) h_),
      (F.forSub (f_, s')))), (l_, s'')) end
let rec selectFormula =
  begin function
  | (n, (g0_, All (Prim (Dec (_, v_) as d_), f_), All (_, o_)), s_) ->
      selectFormula (n, ((I.Decl (g0_, d_)), f_, o_), s_)
  | (n, (g0_, And (f1_, f2_), And (o1_, o2_)), s_) ->
      let (n', s'_) = selectFormula (n, (g0_, f1_, o1_), s_) in
      selectFormula (n, (g0_, f2_, o2_), s'_)
  | (nih, (Gall, Fex, Oex),
     (State (ncurrent, (g0_, b0_), (_, _), _, Ocurrent, h_, f_) as s_)) ->
      let ds_ =
        recursion
          ((nih, Gall, Fex, Oex),
            (ncurrent, (g0_, b0_), [], Ocurrent, h_, f_)) in
      ((nih + 1), (updateState (s_, (ds_, I.id)))) end
let rec expand (State (n, (g_, b_), (IH, OH), d, o_, h_, f_) as s_) =
  let _ = if !Global.doubleCheck then begin FunTypeCheck.isState s_ end
    else begin () end in
let (_, s'_) = selectFormula (1, (I.Null, IH, OH), s_) in s'_
let rec apply (s_) =
  begin if !Global.doubleCheck then begin FunTypeCheck.isState s_ end
  else begin () end; s_ end
let rec menu _ =
  "Recursion (calculates ALL new assumptions & residual lemmas)"
let rec handleExceptions f (p_) =
  begin try f p_ with | Error s -> raise (Error s) end
let expand = handleExceptions expand
let apply = apply
let menu = menu end
