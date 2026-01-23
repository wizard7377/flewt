module type OLDSEARCH  =
  sig
    module MetaSyn : METASYN
    exception Error of string 
    val searchEx :
      (IntSyn.dctx * IntSyn.exp_ list * (IntSyn.exp_ * IntSyn.sub_) *
        (unit -> unit)) -> MetaSyn.state_ list
    val searchAll :
      (IntSyn.dctx * IntSyn.exp_ list * (IntSyn.exp_ * IntSyn.sub_) *
        (MetaSyn.state_ list -> MetaSyn.state_ list)) -> MetaSyn.state_ list
  end


module OLDSearch(OLDSearch:sig
                             module MetaGlobal : METAGLOBAL
                             module MetaSyn' : METASYN
                             module Whnf : WHNF
                             module Unify : UNIFY
                             module Index : INDEX
                             module Compile : COMPILE
                             module CPrint : CPRINT
                             module Print : PRINT
                             module Names : NAMES
                           end) : OLDSEARCH =
  struct
    module MetaSyn = MetaSyn'
    exception Error of string 
    module I = IntSyn
    module M = MetaSyn
    module C = CompSyn
    let rec cidFromHead =
      begin function | Const a -> a | Def a -> a | Skonst a -> a end
    let rec eqHead =
      begin function
      | (Const a, Const a') -> a = a'
      | (Def a, Def a') -> a = a'
      | _ -> false end
  let rec solve =
    begin function
    | ((Atom p, s), dp, sc, acck) -> matchAtom ((p, s), dp, sc, acck)
    | ((Impl (r, a_, h_, g), s), DProg (g_, dPool), sc, acck) ->
        let d'_ = I.Dec (None, (I.EClo (a_, s))) in
        solve
          ((g, (I.dot1 s)),
            (C.DProg
               ((I.Decl (g_, d'_)), (I.Decl (dPool, (C.Dec (r, s, h_)))))),
            (begin function | (m_, acck') -> sc ((I.Lam (d'_, m_)), acck') end),
          acck)
    | ((All (d_, g), s), DProg (g_, dPool), sc, acck) ->
        let d'_ = I.decSub (d_, s) in
        solve
          ((g, (I.dot1 s)),
            (C.DProg ((I.Decl (g_, d'_)), (I.Decl (dPool, C.Parameter)))),
            (begin function | (m_, acck') -> sc ((I.Lam (d'_, m_)), acck') end),
          acck) end
let rec rSolve =
  begin function
  | (ps', (Eq (q_), s), DProg (g_, dPool), sc, ((acc, k) as acck)) ->
      if Unify.unifiable (g_, ps', (q_, s)) then begin sc (I.Nil, acck) end
      else begin acc end
  | (ps', (And (r, a_, g), s), (DProg (g_, dPool) as dp), sc, acck) ->
      let x_ = I.newEVar (g_, (I.EClo (a_, s))) in
      rSolve
        (ps', (r, (I.Dot ((I.Exp x_), s))), dp,
          (begin function
           | (s_, acck') ->
               solve
                 ((g, s), dp,
                   (begin function
                    | (m_, acck'') ->
                        (begin try
                                 ((begin Unify.unify
                                           (g_, (x_, I.id), (m_, I.id));
                                   sc ((I.App (m_, s_)), acck'') end)
                         (* why doesn't it always succeed?
                                                                --cs *))
                        with | Unify _ -> [] end) end),
           acck') end),
  acck)
| (ps', (Exists (Dec (_, a_), r), s), (DProg (g_, dPool) as dp), sc, acck) ->
    let x_ = I.newEVar (g_, (I.EClo (a_, s))) in
    rSolve
      (ps', (r, (I.Dot ((I.Exp x_), s))), dp,
        (begin function | (s_, acck') -> sc ((I.App (x_, s_)), acck') end),
      acck) end(*
    | rSolve (ps', (C.Assign (Q, ag), s), dp, sc, acck as (acc, k)) =
        ((Assign.assign (ps', (Q, s));
          aSolve ((ag, s), dp, (fn () => sc (I.Nil, acck)) , acc))
          handle Unify.Unify _ => acc
               | Assign.Assign _ => acc)
    *)
(* replaced below by above.  -fp Mon Aug 17 10:41:09 1998
        ((Unify.unify (ps', (Q, s)); sc (I.Nil, acck)) handle Unify.Unify _ => acc) *)
let rec aSolve ((C.Trivial, s), dp, sc, acc) = sc ()
let rec matchAtom
  (((Root (Ha, _), _) as ps'), (DProg (g_, dPool) as dp), sc, (acc, k)) =
  let rec matchSig acc' =
    let rec matchSig' =
      begin function
      | ([], acc'') -> acc''
      | ((Hc)::sgn', acc'') ->
          let SClause r = C.sProgLookup (cidFromHead Hc) in
          let acc''' =
            CSManager.trail
              (begin function
               | () ->
                   rSolve
                     (ps', (r, I.id), dp,
                       (begin function
                        | (s_, acck') -> sc ((I.Root (Hc, s_)), acck') end),
                     (acc'', (k - 1))) end) in
        matchSig' (sgn', acc''') end in
matchSig' ((Index.lookup (cidFromHead Ha)), acc') in
let rec matchDProg =
begin function
| (I.Null, _, acc') -> matchSig acc'
| (Decl (dPool', Dec (r, s, Ha')), n, acc') ->
    if eqHead (Ha, Ha')
    then
      begin let acc'' =
              CSManager.trail
                (begin function
                 | () ->
                     rSolve
                       (ps', (r, (I.comp (s, (I.Shift n)))), dp,
                         (begin function
                          | (s_, acck') ->
                              sc ((I.Root ((I.BVar n), s_)), acck') end),
                       (acc', (k - 1))) end) in
  matchDProg (dPool', (n + 1), acc'') end
else begin matchDProg (dPool', (n + 1), acc') end
| (Decl (dPool', C.Parameter), n, acc') -> matchDProg (dPool', (n + 1), acc') end in
if k < 0 then begin acc end
else begin matchDProg (dPool, 1, acc) end
let rec occursInExp (r, vs_) = occursInExpW (r, (Whnf.whnf vs_))
let rec occursInExpW =
  begin function
  | (r, (Uni _, _)) -> false
  | (r, (Pi ((d_, _), v_), s)) ->
      (occursInDec (r, (d_, s))) || (occursInExp (r, (v_, (I.dot1 s))))
  | (r, (Root (_, s_), s)) -> occursInSpine (r, (s_, s))
  | (r, (Lam (d_, v_), s)) ->
      (occursInDec (r, (d_, s))) || (occursInExp (r, (v_, (I.dot1 s))))
  | (r, (EVar (r', _, v'_, _), s)) -> (r = r') || (occursInExp (r, (v'_, s)))
  | (r, (FgnExp csfe, s)) ->
      I.FgnExpStd.fold csfe
        (begin function | (u_, b_) -> b_ || (occursInExp (r, (u_, s))) end)
      false end
let rec occursInSpine =
  begin function
  | (_, (I.Nil, _)) -> false
  | (r, (SClo (s_, s'), s)) -> occursInSpine (r, (s_, (I.comp (s', s))))
  | (r, (App (u_, s_), s)) ->
      (occursInExp (r, (u_, s))) || (occursInSpine (r, (s_, s))) end
let rec occursInDec (r, (Dec (_, v_), s)) = occursInExp (r, (v_, s))
let rec nonIndex =
  begin function
  | (_, []) -> true
  | (r, (EVar (_, _, v_, _))::GE) ->
      (not (occursInExp (r, (v_, I.id)))) && (nonIndex (r, GE)) end
let rec selectEVar =
  begin function
  | ([], _, acc) -> acc
  | ((EVar (r, _, _, _) as x_)::GE, vs_, acc) ->
      if (occursInExp (r, vs_)) && (nonIndex (r, acc))
      then begin selectEVar (GE, vs_, (x_ :: acc)) end
      else begin selectEVar (GE, vs_, acc) end end
let rec searchEx' arg__0 arg__1 =
  begin match (arg__0, arg__1) with
  | (max, ([], sc)) -> [sc ()]
  | (max, ((EVar (r, g_, v_, _))::GE, sc)) ->
      solve
        (((Compile.compileGoal (g_, v_)), I.id),
          (Compile.compileCtx false g_),
          (begin function
           | (u'_, (acc', _)) ->
               (begin Unify.instantiateEVar (r, u'_, []);
                searchEx' max (GE, sc) end) end),
      ([], max)) end(* Possible optimization:
           Check if there are still variables left over
        *)
let rec deepen f (p_) =
  let rec deepen' (level, acc) =
    if level > !MetaGlobal.maxFill then begin acc end
    else begin
      (begin if !Global.chatter > 5 then begin print "#" end
       else begin () end;
    deepen' ((level + 1), (f level p_)) end) end in
deepen' (1, [])
let rec searchEx (g_, GE, vs_, sc) =
  begin if !Global.chatter > 5 then begin print "[Search: " end
  else begin () end;
  deepen searchEx'
    ((selectEVar (GE, vs_, [])),
      (begin function
       | Params ->
           (begin if !Global.chatter > 5 then begin print "OK]\n" end
            else begin () end;
       sc Params end) end));
if !Global.chatter > 5 then begin print "FAIL]\n" end else begin () end;
raise (Error "No object found") end
let rec searchAll' =
  begin function
  | ([], acc, sc) -> sc acc
  | ((EVar (r, g_, v_, _))::GE, acc, sc) ->
      solve
        (((Compile.compileGoal (g_, v_)), I.id),
          (Compile.compileCtx false g_),
          (begin function
           | (u'_, (acc', _)) ->
               (begin Unify.instantiateEVar (r, u'_, []);
                searchAll' (GE, acc', sc) end) end),
      (acc, !MetaGlobal.maxFill)) end
let rec searchAll (g_, GE, vs_, sc) =
  searchAll' ((selectEVar (GE, vs_, [])), [], sc)
let searchEx = searchEx
let searchAll = searchAll end
