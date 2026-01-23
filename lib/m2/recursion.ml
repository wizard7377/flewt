module type RECURSION  =
  sig
    module MetaSyn : METASYN
    exception Error of string 
    type nonrec operator
    val expandLazy : MetaSyn.state_ -> operator list
    val expandEager : MetaSyn.state_ -> operator list
    val apply : operator -> MetaSyn.state_
    val menu : operator -> string
  end


module Recursion(Recursion:sig
                             module Global : GLOBAL
                             module MetaSyn' : METASYN
                             module Whnf : WHNF
                             module Unify : UNIFY
                             module Conv : CONV
                             module Names : NAMES
                             module Subordinate : SUBORDINATE
                             module Print : PRINT
                             module Order : ORDER
                             module ModeTable : MODETABLE
                             module Lemma : LEMMA
                             module Filling : FILLING
                             module MetaPrint : METAPRINT
                             module MetaAbstract : METAABSTRACT
                             module Formatter : FORMATTER
                           end) : RECURSION =
  struct
    module MetaSyn = MetaSyn'
    exception Error of string 
    type nonrec operator = MetaSyn.state_
    module M = MetaSyn
    module I = IntSyn
    module O = Order
    module N = Names
    module F = Formatter
    type quantifier_ =
      | Universal 
      | Existential 
    let rec vectorToString (g_, o_) =
      let rec fmtOrder =
        begin function
        | Arg (us_, vs_) ->
            [F.String (Print.expToString (g_, (I.EClo us_)));
            F.String ":";
            F.String (Print.expToString (g_, (I.EClo vs_)))]
        | Lex (l_) -> [F.String "{"; F.HVbox (fmtOrders l_); F.String "}"]
        | Simul (l_) -> [F.String "["; F.HVbox (fmtOrders l_); F.String "]"] end
        and fmtOrders =
          begin function
          | [] -> []
          | (o_)::[] -> fmtOrder o_
          | (o_)::l_ -> (fmtOrder o_) @ ((::) (F.String " ") fmtOrders l_) end in
    F.makestring_fmt (F.HVbox (fmtOrder o_))
  let rec vector (c, (s_, s)) =
    let Vid = ((I.constType c), I.id) in
    let rec select' (n, (ss'_, Vs'')) =
      select'W (n, (ss'_, (Whnf.whnf Vs'')))
    and select'W =
      begin function
      | (1, ((App (u'_, s'_), s'), (Pi ((Dec (_, V''), _), _), s''))) ->
          ((u'_, s'), (V'', s''))
      | (n, ((SClo (s'_, s1'), s2'), Vs'')) ->
          select'W (n, ((s'_, (I.comp (s1', s2'))), Vs''))
      | (n, ((App (u'_, s'_), s'), (Pi ((Dec (_, V1''), _), V2''), s''))) ->
          select'
            ((n - 1),
              ((s'_, s'), (V2'', (I.Dot ((I.Exp (I.EClo (u'_, s'))), s''))))) end
      (* select'W (1, _, (I.Root _, _)) cannot occur by invariant ! *) in
    let rec select =
      begin function
      | Arg n -> O.Arg (select' (n, ((s_, s), Vid)))
      | Lex (l_) -> O.Lex (map select l_)
      | Simul (l_) -> O.Simul (map select l_) end in
    select (O.selLookup c)
let rec set_parameter (g_, (EVar (r, _, v_, _) as x_), k, sc, ops) =
  let rec set_parameter' =
    begin function
    | (0, ops') -> ops'
    | (k', ops') ->
        let Dec (_, v'_) as d'_ = I.ctxDec (g_, k') in
        let ops'' =
          CSManager.trail
            (begin function
             | () ->
                 if
                   (Unify.unifiable (g_, (v_, I.id), (v'_, I.id))) &&
                     (Unify.unifiable
                        (g_, (x_, I.id),
                          ((I.Root ((I.BVar k'), I.Nil)), I.id)))
                 then begin sc ops' end else begin ops' end end) in
  set_parameter' ((k' - 1), ops'') end in
set_parameter' (k, ops)
let rec ltinit (g_, k, (us_, vs_), UsVs', sc, ops) =
  ltinitW (g_, k, (Whnf.whnfEta (us_, vs_)), UsVs', sc, ops)
let rec ltinitW =
  begin function
  | (g_, k, (us_, ((Root _, _) as vs_)), UsVs', sc, ops) ->
      lt (g_, k, (us_, vs_), UsVs', sc, ops)
  | (g_, k, ((Lam (d1_, u_), s1), (Pi (d2_, v_), s2)),
     ((u'_, s1'), (v'_, s2')), sc, ops) ->
      ltinit
        ((I.Decl (((g_, (I.decSub (d1_, s1))))
            (* = I.decSub (D2, s2) *))), (k + 1),
          ((u_, (I.dot1 s1)), (v_, (I.dot1 s2))),
          ((u'_, (I.comp (s1', I.shift))), (v'_, (I.comp (s2', I.shift)))),
          sc, ops) end
let rec lt (g_, k, (us_, vs_), (us'_, vs'_), sc, ops) =
  ltW (g_, k, (us_, vs_), (Whnf.whnfEta (us'_, vs'_)), sc, ops)
let rec ltW =
  begin function
  | (g_, k, (us_, vs_), ((Root (Const c, s'_), s'), vs'_), sc, ops) ->
      ltSpine
        (g_, k, (us_, vs_), ((s'_, s'), ((I.constType c), I.id)), sc, ops)
  | (g_, k, (us_, vs_), ((Root (BVar n, s'_), s'), vs'_), sc, ops) ->
      ((if n <= k
        then
          begin let Dec (_, v'_) = I.ctxDec (g_, n) in
                ltSpine
                  (g_, k, (us_, vs_), ((s'_, s'), (v'_, I.id)), sc, ops) end
      else begin ops end)
  (* n must be a local variable *))
  | (g_, _, _, ((EVar _, _), _), _, ops) -> ops
  | (g_, k, ((u_, s1), (v_, s2)),
     ((Lam ((Dec (_, V1') as d_), u'_), s1'),
      (Pi ((Dec (_, V2'), _), v'_), s2')),
     sc, ops) ->
      ((if Subordinate.equiv ((I.targetFam v_), (I.targetFam V1'))
        then
          begin let x_ = I.newEVar (g_, (I.EClo (V1', s1'))) in
                let sc' =
                  begin function
                  | ops' -> set_parameter (g_, x_, k, sc, ops') end in
                ((lt
                    (g_, k, ((u_, s1), (v_, s2)),
                      ((u'_, (I.Dot ((I.Exp x_), s1'))),
                        (v'_, (I.Dot ((I.Exp x_), s2')))), sc', ops))
                  (* enforce that X gets only bound to parameters *)
                  (* = I.newEVar (I.EClo (V2', s2')) *)) end
  else begin
    if Subordinate.below ((I.targetFam V1'), (I.targetFam v_))
    then
      begin (let x_ = I.newEVar (g_, (I.EClo (V1', s1'))) in
             ((lt
                 (g_, k, ((u_, s1), (v_, s2)),
                   ((u'_, (I.Dot ((I.Exp x_), s1'))),
                     (v'_, (I.Dot ((I.Exp x_), s2')))), sc, ops))
               (* = I.newEVar (I.EClo (V2', s2')) *))) end
    else begin ops end end)
(* == I.targetFam V2' *)) end
let rec ltSpine (g_, k, (us_, vs_), (ss'_, vs'_), sc, ops) =
  ltSpineW (g_, k, (us_, vs_), (ss'_, (Whnf.whnf vs'_)), sc, ops)
let rec ltSpineW =
  begin function
  | (g_, k, (us_, vs_), ((I.Nil, _), _), _, ops) -> ops
  | (g_, k, (us_, vs_), ((SClo (s_, s'), s''), vs'_), sc, ops) ->
      ltSpineW (g_, k, (us_, vs_), ((s_, (I.comp (s', s''))), vs'_), sc, ops)
  | (g_, k, (us_, vs_),
     ((App (u'_, s'_), s1'), (Pi ((Dec (_, V1'), _), V2'), s2')), sc, ops) ->
      let ops' = le (g_, k, (us_, vs_), ((u'_, s1'), (V1', s2')), sc, ops) in
      ltSpine
        (g_, k, (us_, vs_),
          ((s'_, s1'), (V2', (I.Dot ((I.Exp (I.EClo (u'_, s1'))), s2')))),
          sc, ops') end
let rec eq (g_, (us_, vs_), (us'_, vs'_), sc, ops) =
  CSManager.trail
    (begin function
     | () ->
         if
           (Unify.unifiable (g_, vs_, vs'_)) &&
             (Unify.unifiable (g_, us_, us'_))
         then begin sc ops end else begin ops end end)
let rec le (g_, k, (us_, vs_), (us'_, vs'_), sc, ops) =
  let ops' = eq (g_, (us_, vs_), (us'_, vs'_), sc, ops) in
  leW (g_, k, (us_, vs_), (Whnf.whnfEta (us'_, vs'_)), sc, ops')
let rec leW =
  begin function
  | (g_, k, ((u_, s1), (v_, s2)),
     ((Lam ((Dec (_, V1') as d_), u'_), s1'),
      (Pi ((Dec (_, V2'), _), v'_), s2')),
     sc, ops) ->
      ((if Subordinate.equiv ((I.targetFam v_), (I.targetFam V1'))
        then
          begin let x_ = I.newEVar (g_, (I.EClo (V1', s1'))) in
                let sc' =
                  begin function
                  | ops' -> set_parameter (g_, x_, k, sc, ops') end in
                ((le
                    (g_, k, ((u_, s1), (v_, s2)),
                      ((u'_, (I.Dot ((I.Exp x_), s1'))),
                        (v'_, (I.Dot ((I.Exp x_), s2')))), sc', ops))
                  (* = I.newEVar (I.EClo (V2', s2')) *)
                  (* enforces that X can only bound to parameter *)) end
  else begin
    if Subordinate.below ((I.targetFam V1'), (I.targetFam v_))
    then
      begin (let x_ = I.newEVar (g_, (I.EClo (V1', s1'))) in
             ((le
                 (g_, k, ((u_, s1), (v_, s2)),
                   ((u'_, (I.Dot ((I.Exp x_), s1'))),
                     (v'_, (I.Dot ((I.Exp x_), s2')))), sc, ops))
               (* = I.newEVar (I.EClo (V2', s2')) *))) end
    else begin ops end end)(* == I.targetFam V2' *))
| (g_, k, (us_, vs_), (us'_, vs'_), sc, ops) ->
    lt (g_, k, (us_, vs_), (us'_, vs'_), sc, ops) end
let rec ordlt =
  begin function
  | (g_, Arg (UsVs), Arg (UsVs'), sc, ops) ->
      ltinit (g_, 0, UsVs, UsVs', sc, ops)
  | (g_, Lex (l_), Lex (l'_), sc, ops) -> ordltLex (g_, l_, l'_, sc, ops)
  | (g_, Simul (l_), Simul (l'_), sc, ops) ->
      ordltSimul (g_, l_, l'_, sc, ops) end
let rec ordltLex =
  begin function
  | (g_, [], [], sc, ops) -> ops
  | (g_, (o_)::l_, (o'_)::l'_, sc, ops) ->
      let ops' =
        CSManager.trail
          (begin function | () -> ordlt (g_, o_, o'_, sc, ops) end) in
    ordeq
      (g_, o_, o'_,
        (begin function | ops'' -> ordltLex (g_, l_, l'_, sc, ops'') end),
      ops') end
let rec ordltSimul =
  begin function
  | (g_, [], [], sc, ops) -> ops
  | (g_, (o_)::l_, (o'_)::l'_, sc, ops) ->
      let ops'' =
        CSManager.trail
          (begin function
           | () ->
               ordlt
                 (g_, o_, o'_,
                   (begin function
                    | ops' -> ordleSimul (g_, l_, l'_, sc, ops') end), ops) end) in
ordeq
  (g_, o_, o'_,
    (begin function | ops' -> ordltSimul (g_, l_, l'_, sc, ops') end), ops'') end
let rec ordleSimul =
  begin function
  | (g_, [], [], sc, ops) -> sc ops
  | (g_, (o_)::l_, (o'_)::l'_, sc, ops) ->
      ordle
        (g_, o_, o'_,
          (begin function | ops' -> ordleSimul (g_, l_, l'_, sc, ops') end),
        ops) end
let rec ordeq =
  begin function
  | (g_, Arg (us_, vs_), Arg (us'_, vs'_), sc, ops) ->
      if
        (Unify.unifiable (g_, vs_, vs'_)) &&
          (Unify.unifiable (g_, us_, us'_))
      then begin sc ops end else begin ops end
  | (g_, Lex (l_), Lex (l'_), sc, ops) -> ordeqs (g_, l_, l'_, sc, ops)
  | (g_, Simul (l_), Simul (l'_), sc, ops) -> ordeqs (g_, l_, l'_, sc, ops) end
let rec ordeqs =
  begin function
  | (g_, [], [], sc, ops) -> sc ops
  | (g_, (o_)::l_, (o'_)::l'_, sc, ops) ->
      ordeq
        (g_, o_, o'_,
          (begin function | ops' -> ordeqs (g_, l_, l'_, sc, ops') end), ops) end
let rec ordle (g_, o_, o'_, sc, ops) =
  let ops' =
    CSManager.trail (begin function | () -> ordeq (g_, o_, o'_, sc, ops) end) in
ordlt (g_, o_, o'_, sc, ops')
let rec createEVars =
  begin function
  | Prefix (I.Null, I.Null, I.Null) ->
      ((M.Prefix (I.Null, I.Null, I.Null)), I.id)
  | Prefix (Decl (g_, d_), Decl (m_, M.Top), Decl (b_, b)) ->
      let (Prefix (g'_, m'_, b'_), s') = createEVars (M.Prefix (g_, m_, b_)) in
      ((M.Prefix
          ((I.Decl (g'_, (I.decSub (d_, s')))), (I.Decl (m'_, M.Top)),
            (I.Decl (b'_, b)))), (I.dot1 s'))
  | Prefix (Decl (g_, Dec (_, v_)), Decl (m_, M.Bot), Decl (b_, _)) ->
      let (Prefix (g'_, m'_, b'_), s') = createEVars (M.Prefix (g_, m_, b_)) in
      let x_ = I.newEVar (g'_, (I.EClo (v_, s'))) in
      ((M.Prefix (g'_, m'_, b'_)), (I.Dot ((I.Exp x_), s'))) end
let rec select (g_, vs_) = selectW (g_, (Whnf.whnf vs_))
let rec selectW (g_, (Pi (((Dec (_, v1_) as d_), _), v2_), s)) =
  let rec select' (g_, (vs1_, vs2_)) =
    selectW' (g_, (vs1_, (Whnf.whnf vs2_)))
  and selectW' =
    begin function
    | (g_, (vs1_, ((Root _, _) as vs2_))) -> (g_, (vs1_, vs2_))
    | (g_, ((v1_, s1), (Pi ((d_, p_), V2'), s2))) ->
        select'
          ((I.Decl (g_, (I.decSub (d_, s2)))),
            ((v1_, (I.comp (s1, I.shift))), (V2', (I.dot1 s2)))) end in
select'
  ((I.Decl (g_, (I.decSub (d_, s)))),
    ((v1_, (I.comp (s, I.shift))), (v2_, (I.dot1 s))))
let rec lemma (s_, t, ops) =
  let State (name, GM, v_) = Lemma.apply (s_, t) in
  let (Prefix (g'_, m'_, b'_), s') = createEVars GM in
  let (G'', ((Root (Const a1, s1_), s1), (Root (Const a2, s2_), s2))) =
    select (g'_, (v_, s')) in
  (G'', (vector (a1, (s1_, s1))), (vector (a2, (s2_, s2))),
    (begin function
     | ops' ->
         (MetaAbstract.abstract
            (M.State (name, (M.Prefix (g'_, m'_, b'_)), (I.EClo (v_, s')))))
           :: ops' end),
    ops)
let rec expandLazy' =
  begin function
  | (s_, O.Empty, ops) -> ops
  | (s_, LE (t, l_), ops) ->
      expandLazy' (s_, l_, (ordle (lemma (s_, t, ops))))
  | (s_, LT (t, l_), ops) ->
      expandLazy' (s_, l_, (ordlt (lemma (s_, t, ops)))) end
let rec recursionDepth (v_) =
  let rec recursionDepth' =
    begin function
    | (Root _, n) -> n
    | (Pi (_, v_), n) -> recursionDepth' (v_, (n + 1)) end in
recursionDepth' (v_, 0)
let rec expandLazy (State (_, _, v_) as s_) =
  if (recursionDepth v_) > !MetaGlobal.maxRecurse then begin [] end
  else begin expandLazy' (s_, (O.mutLookup (I.targetFam v_)), []) end
let rec inputConv (vs1_, vs2_) =
  inputConvW ((Whnf.whnf vs1_), (Whnf.whnf vs2_))
let rec inputConvW ((Root (Const c1, s1_), s1), (Root (Const c2, s2_), s2)) =
  if c1 = c2
  then
    begin inputConvSpine
            ((valOf (ModeTable.modeLookup c1)),
              ((s1_, s1), ((I.constType c1), I.id)),
              ((s2_, s2), ((I.constType c2), I.id))) end
  else begin false end(* s1 = s2 = id *)
let rec inputConvSpine =
  begin function
  | (ModeSyn.Mnil, ((s1_, _), _), ((s2_, _), _)) -> true
  | (mS, ((SClo (s1_, s1'), s1), vs1_), (ss2_, vs2_)) ->
      inputConvSpine (mS, ((s1_, (I.comp (s1', s1))), vs1_), (ss2_, vs2_))
  | (mS, (ss1_, vs1_), ((SClo (s2_, s2'), s2), vs2_)) ->
      inputConvSpine (mS, (ss1_, vs1_), ((s2_, (I.comp (s2', s2))), vs2_))
  | (Mapp (Marg (ModeSyn.Minus, _), mS),
     ((App (u1_, s1_), s1), (Pi ((Dec (_, v1_), _), w1_), t1)),
     ((App (u2_, s2_), s2), (Pi ((Dec (_, v2_), _), w2_), t2))) ->
      (Conv.conv ((v1_, t1), (v2_, t2))) &&
        (inputConvSpine
           (mS, ((s1_, s1), (w1_, (I.Dot ((I.Exp (I.EClo (u1_, s1))), t1)))),
             ((s2_, s2), (w2_, (I.Dot ((I.Exp (I.EClo (u1_, s1))), t2))))))
  | (Mapp (Marg (ModeSyn.Plus, _), mS),
     ((App (u1_, s1_), s1), (Pi ((Dec (_, v1_), _), w1_), t1)),
     ((App (u2_, s2_), s2), (Pi ((Dec (_, v2_), _), w2_), t2))) ->
      inputConvSpine
        (mS, ((s1_, s1), (w1_, (I.Dot ((I.Exp (I.EClo (u1_, s1))), t1)))),
          ((s2_, s2), (w2_, (I.Dot ((I.Exp (I.EClo (u2_, s2))), t2))))) end
(* BUG: use the same variable (U1, s1) to continue comparing! --cs
                  in ((S2, s2), (W2, I.Dot (I.Exp (I.EClo (U2, s2), V2), t2))))
             FIXED: --cs Mon Nov  9 19:38:55 EST 1998 *)
(* S1 = S2 = Nil *)
let rec removeDuplicates =
  begin function
  | [] -> []
  | (s'_)::ops ->
      let rec compExp (vs1_, vs2_) =
        compExpW ((Whnf.whnf vs1_), (Whnf.whnf vs2_))
      and compExpW =
        begin function
        | (vs1_, (Root _, _)) -> false
        | (((v1_, s1) as vs1_), (Pi ((d2_, _), v2_), s2)) ->
            (compDec (vs1_, (d2_, s2))) ||
              (compExp ((v1_, (I.comp (s1, I.shift))), (v2_, (I.dot1 s2)))) end
        and compDec (vs1_, (Dec (_, v2_), s2)) = inputConv (vs1_, (v2_, s2)) in
    let rec check (State (name, GM, v_)) = checkW (Whnf.whnf (v_, I.id))
    and checkW (Pi ((d_, _), v_), s) =
      checkDec ((d_, (I.comp (s, I.shift))), (v_, (I.dot1 s)))
    and checkDec ((Dec (_, v1_), s1), vs2_) = compExp ((v1_, s1), vs2_) in
    if check s'_ then begin removeDuplicates ops end
      else begin s'_ :: (removeDuplicates ops) end end
let rec fillOps =
  begin function
  | [] -> []
  | (s'_)::ops ->
      let rec fillOps' =
        begin function | [] -> [] | (o_)::_ -> Filling.apply o_ end in
    let (fillop, _) = Filling.expand s'_ in (fillOps' fillop) @ (fillOps ops) end
let rec expandEager (s_) = removeDuplicates (fillOps (expandLazy s_))
let rec apply (s_) = s_
let rec menu
  (State (name, Prefix (g'_, m'_, b'_), Pi ((Dec (_, v_), _), _)) as s_) =
  "Recursion : " ^ (Print.expToString (g'_, v_))
let rec handleExceptions f (p_) =
  begin try f p_ with | Error s -> raise (Error s) end
let expandLazy = handleExceptions expandLazy
let expandEager = handleExceptions expandEager
let apply = apply
let menu = menu end
