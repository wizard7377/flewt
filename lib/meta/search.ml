module type MTPSEARCH  =
  sig
    module StateSyn : STATESYN
    exception Error of string 
    val searchEx :
      (((int * IntSyn.exp_ list * (int -> unit)))(*      * (IntSyn.Exp * IntSyn.Sub) *))
        -> unit
  end


module MTPSearch(MTPSearch:sig
                             module Global : GLOBAL
                             module Abstract : ABSTRACT
                             module MTPGlobal : MTPGLOBAL
                             module StateSyn' : STATESYN
                             module Whnf : WHNF
                             module Unify : UNIFY
                             module Assign : ASSIGN
                             module Index : INDEX
                             module Compile : COMPILE
                             module CPrint : CPRINT
                             module Print : PRINT
                             module Names : NAMES
                           end) : MTPSEARCH =
  struct
    module StateSyn = StateSyn'
    exception Error of string 
    module I = IntSyn
    module C = CompSyn
    let rec isInstantiated =
      begin function
      | Root (Const cid, _) -> true
      | Pi (_, v_) -> isInstantiated v_
      | Root (Def cid, _) -> true
      | Redex (v_, s_) -> isInstantiated v_
      | Lam (_, v_) -> isInstantiated v_
      | EVar ({ contents = Some (v_) }, _, _, _) -> isInstantiated v_
      | EClo (v_, s) -> isInstantiated v_
      | _ -> false end
    let rec compose' =
      begin function
      | (IntSyn.Null, g_) -> g_
      | (Decl (g_, d_), g'_) -> IntSyn.Decl ((compose' (g_, g'_)), d_) end
  let rec shift =
    begin function
    | (IntSyn.Null, s) -> s
    | (Decl (g_, d_), s) -> I.dot1 (shift (g_, s)) end
let rec raiseType =
  begin function
  | (I.Null, v_) -> v_
  | (Decl (g_, d_), v_) -> raiseType (g_, (I.Pi ((d_, I.Maybe), v_))) end
let rec exists (p_) (k_) =
  let rec exists' =
    begin function
    | I.Null -> false
    | Decl (k'_, y_) -> (p_ y_) || (exists' k'_) end in
exists' k_
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
  | [] -> []
  | (EVar (r, _, _, { contents = [] }) as x_)::GE ->
      let xs_ = selectEVar GE in
      if nonIndex (r, xs_) then begin xs_ @ [x_] end else begin xs_ end
  | (EVar (r, _, _, cnstrs) as x_)::GE ->
      let xs_ = selectEVar GE in
      if nonIndex (r, xs_) then begin x_ :: xs_ end else begin xs_ end end
(* Constraint case *)
let rec pruneCtx =
  begin function
  | (g_, 0) -> g_
  | (Decl (g_, _), n) -> pruneCtx (g_, (n - 1)) end
let rec cidFromHead =
  begin function | Const a -> a | Def a -> a | Skonst a -> a end
let rec eqHead =
  begin function
  | (Const a, Const a') -> a = a'
  | (Def a, Def a') -> a = a'
  | _ -> false end
let rec solve =
  begin function
  | (max, depth, (Atom p, s), (DProg (g_, dPool) as dp), sc) ->
      matchAtom (max, depth, (p, s), dp, sc)
  | (max, depth, (Impl (r, a_, Ha, g), s), DProg (g_, dPool), sc) ->
      let d'_ = I.Dec (None, (I.EClo (a_, s))) in
      solve
        (max, (depth + 1), (g, (I.dot1 s)),
          (C.DProg ((I.Decl (g_, d'_)), (I.Decl (dPool, (C.Dec (r, s, Ha)))))),
          (begin function | m_ -> sc (I.Lam (d'_, m_)) end))
  | (max, depth, (All (d_, g), s), DProg (g_, dPool), sc) ->
      let d'_ = I.decSub (d_, s) in
      solve
        (max, (depth + 1), (g, (I.dot1 s)),
          (C.DProg ((I.Decl (g_, d'_)), (I.Decl (dPool, C.Parameter)))),
          (begin function | m_ -> sc (I.Lam (d'_, m_)) end)) end
let rec rSolve =
  begin function
  | (max, depth, ps', (Eq (q_), s), DProg (g_, dPool), sc) ->
      if Unify.unifiable (g_, ps', (q_, s)) then begin sc I.Nil end
      else begin () end
  | (max, depth, ps', (Assign (q_, eqns), s), (DProg (g_, dPool) as dp), sc)
      ->
      (begin match Assign.assignable (g_, ps', (q_, s)) with
       | Some cnstr ->
           aSolve
             ((eqns, s), dp, cnstr, (begin function | () -> sc I.Nil end))
      | None -> () end)
| (max, depth, ps', (And (r, a_, g), s), (DProg (g_, dPool) as dp), sc) ->
    let x_ = I.newEVar (g_, (I.EClo (a_, s))) in
    ((rSolve
        (max, depth, ps', (r, (I.Dot ((I.Exp x_), s))), dp,
          (begin function
           | s_ ->
               solve
                 (max, depth, (g, s), dp,
                   (begin function | m_ -> sc (I.App (m_, s_)) end)) end)))
(* is this EVar redundant? -fp *))
| (max, depth, ps', (In (r, a_, g), s), (DProg (g_, dPool) as dp), sc) ->
    let g0_ = pruneCtx (g_, depth) in
    let dPool0 = pruneCtx (dPool, depth) in
    let w = I.Shift depth in
    let iw = Whnf.invert w in
    let s' = I.comp (s, iw) in
    let x_ = I.newEVar (g0_, (I.EClo (a_, s'))) in
    let x'_ = I.EClo (x_, w) in
    ((rSolve
        (max, depth, ps', (r, (I.Dot ((I.Exp x'_), s))), dp,
          (begin function
           | s_ -> if isInstantiated x_ then begin sc (I.App (x'_, s_)) end
               else begin
                 solve
                   (max, 0, (g, s'), (C.DProg (g0_, dPool0)),
                     (begin function
                      | m_ ->
                          (begin try
                                   begin Unify.unify
                                           (g0_, (x_, I.id), (m_, I.id));
                                   sc (I.App ((I.EClo (m_, w)), s_)) end
                          with | Unify _ -> () end) end)) end end)))
      (* G |- g goal *)(* G |- A : type *)
      (* G, A |- r resgoal *)(* G0, Gl  |- s : G *)
      (* G0, Gl  |- w : G0 *)(* G0 |- iw : G0, Gl *)
      (* G0 |- w : G *)(* G0 |- X : A[s'] *)(* G0, Gl |- X' : A[s'][w] = A[s] *))
| (max, depth, ps', (Exists (Dec (_, a_), r), s), (DProg (g_, dPool) as dp),
   sc) ->
    let x_ = I.newEVar (g_, (I.EClo (a_, s))) in
    rSolve
      (max, depth, ps', (r, (I.Dot ((I.Exp x_), s))), dp,
        (begin function | s_ -> sc (I.App (x_, s_)) end))
| (max, depth, ps', (Axists (ADec (Some (x_), d), r), s),
   (DProg (g_, dPool) as dp), sc) ->
    let x'_ = I.newAVar () in
    ((rSolve
        (max, depth, ps',
          (r, (I.Dot ((I.Exp (I.EClo (x'_, (I.Shift (- d))))), s))), dp, sc))
      (* we don't increase the proof term here! *)) end
(* replaced below by above.  -fp Mon Aug 17 10:41:09 1998
        ((Unify.unify (ps', (Q, s)); sc (I.Nil, acck)) handle Unify.Unify _ => acc) *)
let rec aSolve =
  begin function
  | ((C.Trivial, s), dp, cnstr, sc) ->
      if Assign.solveCnstr cnstr then begin sc () end else begin () end
  | ((UnifyEq (g'_, e1, n_, eqns), s), (DProg (g_, dPool) as dp), cnstr, sc)
      ->
      let G'' = compose' (g'_, g_) in
      let s' = shift (g'_, s) in
      if Assign.unifiable (G'', (n_, s'), (e1, s'))
      then begin aSolve ((eqns, s), dp, cnstr, sc) end else begin () end end
let rec matchAtom =
  begin function
  | (0, _, _, _, _) -> ()
  | (max, depth, ((Root (Ha, _), _) as ps'), (DProg (g_, dPool) as dp), sc)
      ->
      let rec matchSig' =
        begin function
        | [] -> ()
        | (Hc)::sgn' ->
            let SClause r = C.sProgLookup (cidFromHead Hc) in
            let _ =
              CSManager.trail
                (begin function
                 | () ->
                     rSolve
                       ((max - 1), depth, ps', (r, I.id), dp,
                         (begin function | s_ -> sc (I.Root (Hc, s_)) end)) end) in
          matchSig' sgn' end in
let rec matchDProg =
  begin function
  | (I.Null, _) -> matchSig' (Index.lookup (cidFromHead Ha))
  | (Decl (dPool', Dec (r, s, Ha')), n) ->
      if eqHead (Ha, Ha')
      then
        begin let _ =
                CSManager.trail
                  (begin function
                   | () ->
                       rSolve
                         ((max - 1), depth, ps',
                           (r, (I.comp (s, (I.Shift n)))), dp,
                           (begin function
                            | s_ -> sc (I.Root ((I.BVar n), s_)) end)) end) in
    matchDProg (dPool', (n + 1)) end
  else begin matchDProg (dPool', (n + 1)) end
  | (Decl (dPool', C.Parameter), n) -> matchDProg (dPool', (n + 1)) end in
matchDProg (dPool, 1) end
let rec searchEx' arg__0 arg__1 =
  begin match (arg__0, arg__1) with
  | (max, ([], sc)) -> sc max
  | (max, ((EVar (r, g_, v_, _) as x_)::GE, sc)) ->
      solve
        (max, 0, ((Compile.compileGoal (g_, v_)), I.id),
          (Compile.compileCtx false g_),
          (begin function
           | u'_ ->
               (begin try
                        begin Unify.unify (g_, (x_, I.id), (u'_, I.id));
                        searchEx' max (GE, sc) end
               with | Unify _ -> () end) end)) end(* Possible optimization:
           Check if there are still variables left over
        *)
let rec deepen depth f (p_) =
  let rec deepen' level = if level > depth then begin () end
    else begin
      (begin if !Global.chatter > 5 then begin print "#" end
       else begin () end;
    f level p_; deepen' (level + 1) end) end in
deepen' 1
let rec searchEx (it, depth) (GE, sc) =
  begin if !Global.chatter > 5 then begin print "[Search: " end
  else begin () end;
  deepen depth searchEx'
    ((selectEVar GE),
      (begin function
       | max ->
           (begin if !Global.chatter > 5 then begin print "OK]\n" end
            else begin () end;
       (let GE' =
          foldr
            (begin function
             | ((EVar (_, g_, _, _) as x_), l_) ->
                 Abstract.collectEVars (g_, (x_, I.id), l_) end)
          [] GE in
     let gE' = List.length GE' in
     ((if gE' > 0
       then begin (if it > 0 then begin searchEx ((it - 1), 1) (GE', sc) end
         else begin () end) end else begin sc max end)
  (* warning: iterative deepening depth is not propably updated.
                                             possible that it runs into an endless loop ? *))) end) end));
if !Global.chatter > 5 then begin print "FAIL]\n" end else begin () end;
() end
let rec search (maxFill, GE, sc) = searchEx (1, maxFill) (GE, sc)
let searchEx = search end
