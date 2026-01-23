module type RELFUN  =
  sig
    exception Error of string 
    val convertFor : IntSyn.cid list -> FunSyn.for_
    val convertPro : IntSyn.cid list -> FunSyn.pro_
  end


module RelFun(RelFun:sig
                       module Global : GLOBAL
                       module ModeTable : MODETABLE
                       module Names : NAMES
                       module Unify : UNIFY
                       module Whnf : WHNF
                       module Weaken : WEAKEN
                       module TypeCheck : TYPECHECK
                       module FunWeaken : FUNWEAKEN
                       module FunNames : FUNNAMES
                     end) : RELFUN =
  struct
    exception Error of string 
    module F = FunSyn
    module I = IntSyn
    module M = ModeSyn
    let rec ctxSub =
      begin function
      | (I.Null, s) -> (I.Null, s)
      | (Decl (g_, d_), s) ->
          let (g'_, s') = ctxSub (g_, s) in
          ((I.Decl (g'_, (I.decSub (d_, s')))), (I.dot1 s)) end
    let rec convertOneFor cid =
      let v_ =
        begin match I.sgnLookup cid with
        | ConDec (name, _, _, _, v_, I.Kind) -> v_
        | _ -> raise (Error "Type Constant declaration expected") end in
    let mS =
      begin match ModeTable.modeLookup cid with
      | None -> raise (Error "Mode declaration expected")
      | Some mS -> mS end in
    let rec convertFor' =
      begin function
      | (Pi ((d_, _), v_), Mapp (Marg (M.Plus, _), mS), w1, w2, n) ->
          let (f'_, F'') =
            convertFor'
              (v_, mS, (I.dot1 w1), (I.Dot ((I.Idx n), w2)), (n - 1)) in
          (((begin function
             | f_ ->
                 F.All ((F.Prim (Weaken.strengthenDec (d_, w1))), (f'_ f_)) end)),
            F'')
      | (Pi ((d_, _), v_), Mapp (Marg (M.Minus, _), mS), w1, w2, n) ->
          let (f'_, F'') =
            convertFor'
              (v_, mS, (I.comp (w1, I.shift)), (I.dot1 w2), (n + 1)) in
          (f'_, (F.Ex ((I.decSub (d_, w2)), F'')))
      | (Uni (I.Type), M.Mnil, _, _, _) ->
          (((begin function | f_ -> f_ end)), F.True)
      | _ -> raise (Error "type family must be +/- moded") end in
  let rec shiftPlus mS =
    let rec shiftPlus' =
      begin function
      | (M.Mnil, n) -> n
      | (Mapp (Marg (M.Plus, _), mS'), n) -> shiftPlus' (mS', (n + 1))
      | (Mapp (Marg (M.Minus, _), mS'), n) -> shiftPlus' (mS', n) end in
  shiftPlus' (mS, 0) in
  let n = shiftPlus mS in
  let (f_, f'_) = convertFor' (v_, mS, I.id, (I.Shift n), n) in ((f_ f'_)
    (* convertFor' (V, mS, w1, w2, n) = (F', F'')

           Invariant:
           If   G |- V = {{G'}} type :kind
           and  G |- w1 : G+
           and  G+, G'+, G- |- w2 : G
           and  G+, G'+, G- |- ^n : G+
           and  mS is a spine for G'
           then F'  is a formula excepting a another formula as argument s.t.
                If G+, G'+ |- F formula,
                then . |- F' F formula
           and  G+, G'+ |- F'' formula
        *)
    (* shiftPlus (mS) = s'

         Invariant:
         s' = ^(# of +'s in mS)
         *))
let rec convertFor =
  begin function
  | [] -> raise (Error "Empty theorem")
  | a::[] -> convertOneFor a
  | a::l_ -> F.And ((convertOneFor a), (convertFor l_)) end
let rec occursInExpN =
  begin function
  | (k, Uni _) -> false
  | (k, Pi (DP, v_)) ->
      (occursInDecP (k, DP)) || (occursInExpN ((k + 1), v_))
  | (k, Root (h_, s_)) -> (occursInHead (k, h_)) || (occursInSpine (k, s_))
  | (k, Lam (d_, v_)) ->
      (occursInDec (k, d_)) || (occursInExpN ((k + 1), v_))
  | (k, FgnExp csfe) ->
      I.FgnExpStd.fold csfe
        (begin function
         | (u_, b_) -> b_ || (occursInExpN (k, (Whnf.normalize (u_, I.id)))) end)
      false end
let rec occursInHead =
  begin function
  | (k, BVar k') -> k = k'
  | (k, Const _) -> false
  | (k, Def _) -> false
  | (k, FgnConst _) -> false end
let rec occursInSpine =
  begin function
  | (_, I.Nil) -> false
  | (k, App (u_, s_)) -> (occursInExpN (k, u_)) || (occursInSpine (k, s_)) end
let rec occursInDec (k, Dec (_, v_)) = occursInExpN (k, v_)
let rec occursInDecP (k, (d_, _)) = occursInDec (k, d_)
let rec occursInExp (k, u_) = occursInExpN (k, (Whnf.normalize (u_, I.id)))
let rec dot1inv w = Weaken.strengthenSub ((I.comp (I.shift, w)), I.shift)
let rec shiftinv w = Weaken.strengthenSub (w, I.shift)
let rec eqIdx = begin function | (Idx n, Idx k) -> n = k | _ -> false end
let rec peel w =
  if eqIdx ((I.bvarSub (1, w)), (I.Idx 1)) then begin dot1inv w end
  else begin shiftinv w end
let rec peeln =
  begin function | (0, w) -> w | (n, w) -> peeln ((n - 1), (peel w)) end
let rec domain =
  begin function
  | (g_, Dot (Idx _, s)) -> (domain (g_, s)) + 1
  | (I.Null, Shift 0) -> 0
  | ((Decl _ as g_), Shift 0) ->
      domain (g_, (I.Dot ((I.Idx 1), (I.Shift 1))))
  | (Decl (g_, _), Shift n) -> domain (g_, (I.Shift (n - 1))) end
let rec strengthen (Psi, (a, s_), w, m) =
  let mS =
    begin match ModeTable.modeLookup a with
    | None -> raise (Error "Mode declaration expected")
    | Some mS -> mS end in
let rec args =
  begin function
  | (I.Nil, M.Mnil) -> []
  | (App (u_, s'_), Mapp (Marg (m', _), mS)) ->
      let l_ = args (s'_, mS) in
      (begin match M.modeEqual (m, m') with | true -> u_ :: l_ | false -> l_ end) end in
let rec strengthenArgs =
  begin function
  | ([], s) -> []
  | ((u_)::l_, s) ->
      (::) (Weaken.strengthenExp (u_, s)) strengthenArgs (l_, s) end in
let rec occursInArgs =
  begin function
  | (n, []) -> false
  | (n, (u_)::l_) -> (occursInExp (n, u_)) || (occursInArgs (n, l_)) end in
let rec occursInPsi =
  begin function
  | (n, ([], l_)) -> occursInArgs (n, l_)
  | (n, ((Prim (Dec (_, v_)))::Psi1, l_)) ->
      (occursInExp (n, v_)) || (occursInPsi ((n + 1), (Psi1, l_)))
  | (n, ((Block (CtxBlock (l, g_)))::Psi1, l_)) ->
      occursInG
        (n, g_, (begin function | n' -> occursInPsi (n', (Psi1, l_)) end)) end
  and occursInG =
    begin function
    | (n, I.Null, k) -> k n
    | (n, Decl (g_, Dec (_, v_)), k) ->
        occursInG
          (n, g_,
            (begin function | n' -> (occursInExp (n', v_)) || (k (n' + 1)) end)) end in
let rec occursBlock (g_, (Psi2, l_)) =
let rec occursBlock =
  begin function
  | (I.Null, n) -> false
  | (Decl (g_, d_), n) ->
      (occursInPsi (n, (Psi2, l_))) || (occursBlock (g_, (n + 1))) end in
occursBlock (g_, 1) in
let rec inBlock =
begin function
| (I.Null, (bw, w1)) -> (bw, w1)
| (Decl (g_, d_), (bw, w1)) ->
    if eqIdx ((I.bvarSub (1, w1)), (I.Idx 1))
    then begin inBlock (g_, (true, (dot1inv w1))) end
    else begin inBlock (g_, (bw, (Weaken.strengthenSub (w1, I.shift)))) end end in
let rec blockSub =
begin function
| (I.Null, w) -> (I.Null, w)
| (Decl (g_, Dec (name, v_)), w) ->
    let (g'_, w') = blockSub (g_, w) in
    let v'_ = Weaken.strengthenExp (v_, w') in
    ((I.Decl (g'_, (I.Dec (name, v'_)))), (I.dot1 w')) end in
let rec strengthen' =
begin function
| (((I.Null, Psi2, l_, w1))(* =  I.id *)) -> (I.Null, I.id)
| (Decl (Psi1, (Prim (Dec (name, v_)) as LD)), Psi2, l_, w1) ->
    let (bw, w1') =
      if eqIdx ((I.bvarSub (1, w1)), (I.Idx 1))
      then begin (true, (dot1inv w1)) end
      else begin (false, (Weaken.strengthenSub (w1, I.shift))) end in
if bw || (occursInPsi (1, (Psi2, l_)))
then
begin let (Psi1', w') = strengthen' (Psi1, (LD :: Psi2), l_, w1') in
      let v'_ = Weaken.strengthenExp (v_, w') in
      ((I.Decl (Psi1', (F.Prim (I.Dec (name, v'_))))), (I.dot1 w')) end
else begin
  (let w2 = I.shift in
   let (Psi2', w2') = FunWeaken.strengthenPsi' (Psi2, w2) in
   let l'_ = strengthenArgs (l_, w2') in
   let (Psi1'', w') = strengthen' (Psi1, Psi2', l'_, w1') in
   (Psi1'', (I.comp (w', I.shift)))) end
| (Decl (Psi1, (Block (CtxBlock (name, g_)) as LD)), Psi2, l_, w1) ->
    let (bw, w1') = inBlock (g_, (false, w1)) in
    if bw || (occursBlock (g_, (Psi2, l_)))
    then
      begin let (Psi1', w') = strengthen' (Psi1, (LD :: Psi2), l_, w1') in
            let (G'', w'') = blockSub (g_, w') in
            ((I.Decl (Psi1', (F.Block (F.CtxBlock (name, G''))))), w'') end
      else begin
        (let w2 = I.Shift (I.ctxLength g_) in
         let (Psi2', w2') = FunWeaken.strengthenPsi' (Psi2, w2) in
         let l'_ = strengthenArgs (l_, w2') in
         strengthen' (Psi1, Psi2', l'_, w1')) end end in
((strengthen' (Psi, [], (args (s_, mS)), w))
(* testBlock (G, (bw, w1)) = (bw', w')

           Invariant:
           If   |- G ctx
           and  |- G1 ctx
           and  |- G2 ctx
           and  G1 |- w1 : G2, G
           and  bw is a boolean value
           then there ex. a G1'
           s.t. |- G1' ctx
           and  G1' |- w' : G2
           and  bw' = bw or (G1 =/= G1')
         *)
(* strengthen' (Psi1, Psi2, S, w1) =  (Psi', w')

           Invariant:
           If   |- Psi1 ctx
           and  Psi1 |- Psi2 ctx      (Psi2 is a list to maintain order)
           and  |- Psi3 ctx
           and  Psi1 |- w1 : Psi3     where w1 is a weakening substitution
           and  Psi1, Psi2 |- S : V1 > V2
           then |- Psi' ctx
           and  Psi1 |- w' : Psi'     where w' is a weakening substitution
           where Psi3 < Psi' < Psi1   (Psi' contains all variables of Psi3
                                       and all variables occuring in m
                                       position in S)
        *))
let rec recursion (l_) =
  let f_ = convertFor l_ in
  let rec name =
    begin function
    | a::[] -> I.conDecName (I.sgnLookup a)
    | a::l_ -> ((I.conDecName (I.sgnLookup a)) ^ "/") ^ (name l_) end in
  begin function | p -> F.Rec ((F.MDec ((Some (name l_)), f_)), p) end
let rec abstract a =
  let mS =
    begin match ModeTable.modeLookup a with
    | None -> raise (Error "Mode declaration expected")
    | Some mS -> mS end in
let v_ =
  begin match I.sgnLookup a with
  | ConDec (name, _, _, _, v_, I.Kind) -> v_
  | _ -> raise (Error "Type Constant declaration expected") end in
let rec abstract' =
  begin function | ((_, M.Mnil), w) -> (begin function | p -> p end)
  | ((Pi ((d_, _), v2_), Mapp (Marg (M.Plus, _), mS)), w) ->
      let d'_ = Weaken.strengthenDec (d_, w) in
      let p_ = abstract' ((v2_, mS), (I.dot1 w)) in
      (begin function | p -> F.Lam ((F.Prim d'_), (p_ p)) end)
  | ((Pi (_, v2_), Mapp (Marg (M.Minus, _), mS)), w) ->
      abstract' ((v2_, mS), (I.comp (w, I.shift))) end in
((abstract' ((v_, mS), I.id))
(* abstract' ((V, mS), w) = P'

           Invariant:
           If  Sigma (a) = {x1:A1} .. {xn:An} type
           and  Psi |- S : m1{x1:A1} .. mn{xn:An} type > type
           and  Gamma= x1:A1, .. x(j-1):A(j-1)
           and  Gamma |- w : Gamma+
           then P' is a Lam abstraction
        *))
let rec transformInit (Psi, (a, s_), w1) =
  let mS =
    begin match ModeTable.modeLookup a with
    | None -> raise (Error "Mode declaration expected")
    | Some mS -> mS end in
let v_ =
  begin match I.sgnLookup a with
  | ConDec (name, _, _, _, v_, I.Kind) -> v_
  | _ -> raise (Error "Type Constant declaration expected") end in
let rec transformInit' =
  begin function
  | ((I.Nil, M.Mnil), Uni (I.Type), (w, s)) -> (w, s)
  | ((App (u_, s_), Mapp (Marg (M.Minus, _), mS)), Pi (_, v2_), (w, s)) ->
      let w' = I.comp (w, I.shift) in
      let s' = s in transformInit' ((s_, mS), v2_, (w', s'))
  | ((App (u_, s_), Mapp (Marg (M.Plus, _), mS)), Pi
     ((Dec (name, v1_), _), v2_), (w, s)) ->
      let V1' = Weaken.strengthenExp (v1_, w) in
      let w' = I.dot1 w in
      let u'_ = Weaken.strengthenExp (u_, w1) in
      let s' = Whnf.dotEta ((I.Exp u'_), s) in
      transformInit' ((s_, mS), v2_, (w', s')) end in
((transformInit' ((s_, mS), v_, (I.id, (I.Shift (F.lfctxLength Psi)))))
  (* transformInit' ((S, mS), V, (w, s)) = (w', s')

           Invariant:
           If   Psi |- S : V > type
           and  x1:A1...x(j-1):A(j-1) |- V = mj{xj:Aj} .. mn{xn:An} type : kind
           and  x1:A1...x(j-1):A(j-1) |- w : +x1:A1... +x(j-1):A(j-1)
           and  Psi |- w1 : Psi+
           and  Psi+ |- s : +x1:A1... +x(j-1):A(j-1)
           then x1:A1...xn:An |- w' : +x1:A1... +xn:An
           and  Psi+ |- s' : +x1:A1 .. +xn:An
        *))
let rec transformDec (ts_, (Psi, g0_), d, (a, s_), w1, w2, t0) =
  let mS =
    begin match ModeTable.modeLookup a with
    | None -> raise (Error "Mode declaration expected")
    | Some mS -> mS end in
let v_ =
  begin match I.sgnLookup a with
  | ConDec (name, _, _, _, v_, I.Kind) -> v_
  | _ -> raise (Error "Type Constant declaration expected") end in
let rec raiseExp (g_, u_, a) =
  let rec raiseExp' =
    begin function | I.Null -> (I.id, ((begin function | x -> x end)))
    | Decl (g_, (Dec (_, v_) as d_)) ->
        let (w, k) = raiseExp' g_ in
        if Subordinate.belowEq ((I.targetFam v_), a)
        then
          begin ((I.dot1 w),
                  ((begin function
                    | x -> k (I.Lam ((Weaken.strengthenDec (d_, w)), x)) end))) end
        else begin ((I.comp (w, I.shift)), k) end end in
let (w, k) = raiseExp' g_ in ((k (Weaken.strengthenExp (u_, w)))
(* raiseExp G = (w', k)

               Invariant:
               If   |-  Psi ctx
               and  Psi |- G ctx
               and  Psi |- G' ctx   which ARE subordinate to a
               then Psi, G |- w : Psi, G'
               and  k is a continuation calculuting the right exprssion:
                    for all U, s.t. Psi, G |- U : V
                    Psi |- [[G']] U : {{G'}} V
            *)) in
let rec raiseType (g_, u_, a) =
let rec raiseType' =
  begin function
  | (I.Null, n) -> (I.id, ((begin function | x -> x end)),
      ((begin function | s_ -> s_ end)))
  | (Decl (g_, (Dec (_, v_) as d_)), n) ->
      let (w, k, k') = raiseType' (g_, (n + 1)) in
      if Subordinate.belowEq ((I.targetFam v_), a)
      then
        begin ((I.dot1 w),
                ((begin function
                  | x ->
                      k (I.Pi (((Weaken.strengthenDec (d_, w)), I.Maybe), x)) end)),
        ((begin function | s_ -> I.App ((I.Root ((I.BVar n), I.Nil)), s_) end))) end
  else begin ((I.comp (w, I.shift)), k, k') end end in
let (w, k, k') = raiseType' (g_, 2) in
((((k (Weaken.strengthenExp (u_, w))), (I.Root ((I.BVar 1), (k' I.Nil)))))
(* raiseType (G, n) = (w', k, S')

              Invariant:
              If   |-  Psi ctx
              and  Psi |- G, Gv ctx
              and  Psi |- G' ctx   which ARE subordinate to a
              and  n = |Gv| + 1
              then Psi, G |- w : Psi, G'
              and  k is a continuation calculating the right exprssion:
                   for all U, s.t. Psi, G |- U : V
                   Psi |- [[G']] U : {{G'}} V
              and  k' is a continuation calculating the corresponding spine:
                   for all S, s.t. Psi, G, G0,|- ... refine
            *)) in
let rec exchangeSub (g0_) =
let g0 = I.ctxLength g0_ in
let rec exchangeSub' =
  begin function
  | (0, s) -> s
  | (k, s) -> exchangeSub' ((k - 1), (I.Dot ((I.Idx k), s))) end in
I.Dot ((I.Idx (g0 + 1)), (exchangeSub' (g0, (I.Shift (g0 + 1))))) in
let rec transformDec' =
begin function
| (d, (I.Nil, M.Mnil), Uni (I.Type), (z1, z2), (w, t)) ->
    (w, t, (d, ((begin function | (k, ds_) -> ds_ k end)),
      ((begin function | _ -> F.Empty end))))
| (d, (App (u_, s_), Mapp (Marg (M.Minus, _), mS)), Pi
   ((Dec (_, v1_), DP), v2_), (z1, z2), (w, t)) ->
    let g = I.ctxLength g0_ in
    let w1' = peeln (g, w1) in
    let (g1_, _) = Weaken.strengthenCtx (g0_, w1') in
    let (g2_, _) = ctxSub (g1_, z1) in
    let (V1'', Ur) = raiseType (g2_, (I.EClo (v1_, z2)), (I.targetFam v1_)) in
    let w' =
      begin match DP with | I.Maybe -> I.dot1 w | I.No -> I.comp (w, I.shift) end in
    let u0_ = raiseExp (g0_, u_, (I.targetFam V1'')) in
    let u'_ = Weaken.strengthenExp (u0_, w2) in
    let t' = Whnf.dotEta ((I.Exp u'_), t) in
    let z1' = I.comp (z1, I.shift) in
    let xc = exchangeSub g0_ in
    let z2n = I.comp (z2, (I.comp (I.shift, xc))) in
    let Ur' = I.EClo (Ur, xc) in
    let z2' = Whnf.dotEta ((I.Exp Ur'), z2n) in
    let (w'', t'', (d', Dplus, Dminus)) =
      transformDec' ((d + 1), (s_, mS), v2_, (z1', z2'), (w', t')) in
    (w'', t'',
      (d', Dplus, ((begin function | k -> F.Split (k, (Dminus 1)) end))))
| (d, (App (u_, s_), Mapp (Marg (M.Plus, _), mS)), Pi
   ((Dec (name, v1_), _), v2_), (z1, z2), (w, t)) ->
    let V1' = Weaken.strengthenExp (v1_, w) in
    let w' = I.dot1 w in
    let u'_ = Weaken.strengthenExp (u_, w1) in
    let t' = t in
    let z1' = F.dot1n (g0_, z1) in
    let z2' = I.Dot ((I.Exp (I.EClo (u'_, z1'))), z2) in
    let (w'', t'', (d', Dplus, Dminus)) =
      transformDec' ((d + 1), (s_, mS), v2_, (z1, z2'), (w', t')) in
    (w'', t'',
      (d',
        ((begin function | (k, ds_) -> F.App ((k, u'_), (Dplus (1, ds_))) end)),
      Dminus)) end in
let (w'', t'', (d', Dplus, Dminus)) =
transformDec'
  (d, (s_, mS), v_,
    (I.id, (I.Shift ((+) (domain (Psi, t0)) I.ctxLength g0_))), (I.id, t0)) in
let rec varHead (ts_) (w'', t'', (d', Dplus, Dminus)) =
let rec head' =
  begin function
  | (a'::[], d1, k1) -> (d1, k1)
  | (a'::ts'_, d1, k1) ->
      if a = a'
      then
        begin ((d1 + 1), ((begin function | xx -> F.Left (xx, (k1 1)) end))) end
  else begin
    (let (d2, k2) = head' (ts'_, (d1 + 1), k1) in
     (d2, (begin function | xx -> F.Right (xx, (k2 1)) end))) end end in
let (d2, k2) = head' (ts_, d', (begin function | xx -> Dplus (xx, Dminus) end)) in
(d2, w'', t'', (k2 d)) in
let rec lemmaHead (w'', t'', (d', Dplus, Dminus)) =
let name = I.conDecName (I.sgnLookup a) in
let l =
  begin match FunNames.nameLookup name with
  | None -> raise (Error (("Lemma " ^ name) ^ " not defined"))
  | Some lemma -> lemma end in
((d' + 1), w'', t'', (F.Lemma (l, (Dplus (1, Dminus))))) in
((if List.exists (begin function | x -> x = a end) ts_
then begin varHead ts_ (w'', t'', (d', Dplus, Dminus)) end
else begin lemmaHead (w'', t'', (d', Dplus, Dminus)) end)
(* raiseExp (G, U, a) = U'

           Invariant:
           If   |- Psi ctx         (for some given Psi)
           and  Psi |- G ctx
           and  Psi, G |- U : V    (for some V)
           then Psi, G |- [[G]] U : {{G}} V     (wrt subordination)
        *)
(* raiseType (G, U, a) = U'

           Invariant:
           If   |- Psi ctx         (for some given Psi)
           and  Psi |- G ctx
           and  Psi, G |- U : V    (for some V)
           then Psi, G |- [[G]] U : {{G}} V     (wrt subordination)
           and  Psi, G, x:{{G}} V |- x G : V
        *)
(* exchangeSub (G0) = s'

           Invariant:
           For some Psi, some G, some V:
           Psi, V, G0 |- s' : Psi, G0, V
        *)
(* transformDec' (d, (S, mS), V, (z1, z2), (w, t)) = (d', w', t', (Ds+, Ds-))

           Invariant:
           If   Psi, G0 |- S : V > type
           and  S doesn't contain Skolem constants
           and  d = |Delta|
           and  x1:A1...x(j-1):A(j-1) |- V = mj{xj:Aj} .. mn{xn:An} type : kind
           and  x1:A1...x(j-1):A(j-1) |- w : +x1:A1... +x(j-1):A(j-1)
           and  Psi, G0 |- w1 : Psi+, G0[w1^-1]
           and  Psi |- w2 : Psi+-
           and  Psi+- |- t : Psi+, -x1:{{G0}} A1... -xj:{{G0}} Aj
           and  Psi+, -x1:{{G0}} A1...-x(j-1):{{G0}} A(j-1) |- z1: Psi+
           and  Psi+, -x1:{{G0}} A1...-x(j-1):{{G0}} A(j-1), G0 |- z2: x1:A1...x(j-1):A(j-1)
           then x1:A1...xn:An |- w' : +x1:A1... +xn:An
           and  Psi+- |- s' : +x1:A1 .. +xn:An
           and  Psi+- |- t' : Psi+, -x1:{{G0}} A1... -xn:{{G0}} An
           and  d' = |Delta'|
        *)
(* head Ts (w, t, (d, Dplus, Dminus)) = (d', w', t', P')

             Invariant:
             If   a not in Ts  then d'= d+1,  P' makes a lemma call
             If   Ts = [a]     then d'= d     P' used directly the ih.
             If   Ts = a1 .. ai ... and ai = a
             then d' = d+i   and P' select ih, and then decomposes is, using
                  (i-1) Rights and 1 Left
          *))
let rec transformConc ((a, s_), w) =
  let mS =
    begin match ModeTable.modeLookup a with
    | None -> raise (Error "Mode declaration expected")
    | Some mS -> mS end in
let rec transformConc' =
  begin function
  | (I.Nil, M.Mnil) -> F.Unit
  | (App (u_, s'_), Mapp (Marg (M.Plus, _), mS')) ->
      transformConc' (s'_, mS')
  | (App (u_, s'_), Mapp (Marg (M.Minus, _), mS')) ->
      F.Inx ((Weaken.strengthenExp (u_, w)), (transformConc' (s'_, mS'))) end in
transformConc' (s_, mS)
let rec traverse (ts_, c) =
  let rec traverseNeg =
    begin function
    | (c'', Psi, (Pi (((Dec (_, v1_) as d_), I.Maybe), v2_), v), l_) ->
        (begin match traverseNeg
                       (((c'',
                           (I.Decl
                              (Psi, (F.Prim (Weaken.strengthenDec (d_, v))))),
                           (v2_, (I.dot1 v)), l_))
                       (*                                   (Names.decName (F.makectx Psi, Weaken.strengthenDec (D, v)))),
*))
               with
         | (Some (w', d', PQ'), l'_) -> ((Some ((peel w'), d', PQ')), l'_)
         | (None, l'_) -> (None, l'_) end)
    | (c'', Psi, (Pi (((Dec (_, v1_) as d_), I.No), v2_), v), l_) ->
        (begin match traverseNeg (c'', Psi, (v2_, (I.comp (v, I.shift))), l_)
               with
         | (Some (w', d', PQ'), l'_) ->
             traversePos
               (c'', Psi, I.Null, ((Weaken.strengthenExp (v1_, v)), I.id),
                 (Some (w', d', PQ')), l'_)
         | (None, l'_) ->
             traversePos
               (c'', Psi, I.Null, ((Weaken.strengthenExp (v1_, v)), I.id),
                 None, l'_) end)
  | (c'', Psi, ((Root (Const c', s_) as v_), v), l_) ->
      if c = c'
      then
        begin let s'_ = Weaken.strengthenSpine (s_, v) in
              let (Psi', w') =
                strengthen
                  (Psi, (c', s'_), (I.Shift (F.lfctxLength Psi)), M.Plus) in
              let (w'', s'') = transformInit (Psi', (c', s'_), w') in
              ((((Some
                    (w', 1, ((begin function | p -> (Psi', s'', p) end),
                      (begin function | wf -> transformConc ((c', s'_), wf) end)))),
                l_))(* Clause head found *)) end
    else begin (None, l_) end end
and traversePos =
  begin function
  | (c'', Psi, g_, (Pi (((Dec (_, v1_) as d_), I.Maybe), v2_), v), Some
     (w, d, PQ), l_) ->
      (begin match traversePos
                     (c'', Psi,
                       (I.Decl (g_, (Weaken.strengthenDec (d_, v)))),
                       (v2_, (I.dot1 v)), (Some ((I.dot1 w), d, PQ)), l_)
             with
       | (Some (w', d', PQ'), l'_) -> ((Some (w', d', PQ')), l'_) end)
  | (c'', Psi, g_, (Pi (((Dec (_, v1_) as d_), I.No), v2_), v), Some
     (w, d, PQ), l_) ->
      (begin match traversePos
                     (c'', Psi, g_, (v2_, (I.comp (v, I.shift))),
                       (Some (w, d, PQ)), l_)
             with
       | (Some (w', d', PQ'), l'_) ->
           (begin match traverseNeg
                          (c'',
                            (I.Decl (Psi, (F.Block (F.CtxBlock (None, g_))))),
                            (v1_, v), l'_)
                  with
            | (Some (w'', d'', (P'', Q'')), L'') ->
                ((Some (w', d', PQ')), ((P'' (Q'' w'')) :: L''))
            | (None, L'') -> ((Some (w', d', PQ')), L'') end) end)
| (c'', Psi, I.Null, (v_, v), Some (w1, d, (p_, q_)), l_) ->
    let Root (Const a', s_) =
      Whnf.normalize ((Weaken.strengthenExp (v_, v)), I.id) in
    let (Psi', w2) = strengthen (Psi, (a', s_), w1, M.Minus) in
    let _ =
      if !Global.doubleCheck
      then
        begin TypeCheck.typeCheck
                ((F.makectx Psi'), ((I.Uni I.Type), (I.Uni I.Kind))) end
      else begin () end in
    let w3 = Weaken.strengthenSub (w1, w2) in
    let (d4, w4, t4, ds_) =
      transformDec (ts_, (Psi', I.Null), d, (a', s_), w1, w2, w3) in
    ((((Some
          (w2, d4,
            ((begin function
              | p -> p_ (F.Let (ds_, (F.Case (F.Opts [(Psi', t4, p)])))) end),
            q_))),
      l_))
      (* Lemma calls (no context block) *)(* provide typeCheckCtx from typecheck *))
| (c'', Psi, g_, (v_, v), Some (w1, d, (p_, q_)), l_) ->
    let Root (Const a', s_) = Weaken.strengthenExp (v_, v) in
    let ((Decl (Psi', Block (CtxBlock (name, g2_))) as dummy), w2) =
      strengthen
        ((I.Decl (Psi, (F.Block (F.CtxBlock (None, g_))))), (a', s_), w1,
          M.Minus) in
    let _ =
      if !Global.doubleCheck
      then
        begin TypeCheck.typeCheck
                ((F.makectx dummy), ((I.Uni I.Type), (I.Uni I.Kind))) end
      else begin () end in
    let g = I.ctxLength g_ in
    let w1' = peeln (g, w1) in
    let w2' = peeln (g, w2) in
    let (g1_, _) = Weaken.strengthenCtx (g_, w1') in
    let w3 = Weaken.strengthenSub (w1', w2') in
    let (d4, w4, t4, ds_) =
      transformDec (ts_, (Psi', g_), d, (a', s_), w1, w2', w3) in
    ((((Some
          (w2', d4,
            ((begin function
              | p ->
                  p_
                    (F.Let
                       ((F.New ((F.CtxBlock (None, g1_)), ds_)),
                         (F.Case (F.Opts [(Psi', t4, p)])))) end), q_))),
      l_))
      (* Lemma calls (under a context block) *)(* provide typeCheckCtx from typecheck *)
      (* change w1 to w1' and w2 to w2' below *))
| (c'', Psi, g_, (Pi (((Dec (_, v1_) as d_), I.Maybe), v2_), v), None, l_) ->
    traversePos
      (c'', Psi, (I.Decl (g_, (Weaken.strengthenDec (d_, v)))),
        (v2_, (I.dot1 v)), None, l_)
| (c'', Psi, g_, (Pi (((Dec (_, v1_) as d_), I.No), v2_), v), None, l_) ->
    (begin match traversePos
                   (c'', Psi, g_, (v2_, (I.comp (v, I.shift))), None, l_)
           with
     | (None, l'_) ->
         (begin match traverseNeg
                        (c'',
                          (I.Decl (Psi, (F.Block (F.CtxBlock (None, g_))))),
                          (v1_, v), l'_)
                with
          | (Some (w'', d'', (P'', Q'')), L'') ->
              (None, ((P'' (Q'' w'')) :: L''))
          | (None, L'') -> (None, L'') end) end)
| (c'', Psi, g_, (v_, v), None, l_) -> (None, l_) end in
let rec traverseSig' (c'', l_) =
if (=) c'' (fun r -> r.1) (I.sgnSize ()) then begin l_ end
else begin
  (begin match I.sgnLookup c'' with
   | ConDec (name, _, _, _, v_, I.Type) ->
       (begin match traverseNeg (c'', I.Null, (v_, I.id), l_) with
        | (Some (wf, d', (p'_, q'_)), l'_) ->
            traverseSig' ((c'' + 1), ((p'_ (q'_ wf)) :: l'_))
        | (None, l'_) -> traverseSig' ((c'' + 1), l'_) end)
  | _ -> traverseSig' ((c'' + 1), l_) end) end in ((traverseSig' (0, []))
(* traverseNeg (c'', Psi, (V, v), L) = ([w', d', PQ'], L')    [] means optional

           Invariant:
           If   Psi0 |- V : type
           and  Psi0 |- v : Psi
           and  V[v^-1] does not contain Skolem constants
           and  c'' is the name of the object constant currently considered
           and  L is a list of cases
           then L' list of cases and CL' extends CL
           and  Psi |- w' : Psi'   (Psi' is the context of all variables considered so far)
           and  d' is the length of Delta
           and  PQ'  is a pair, generating the proof term
        *)
(* traversePos (c, Psi, G, (V, v), [w', d', PQ'], L) =  ([w'', d'', PQ''], L'')

           Invariant:
           If   Psi, G |- V : type
           and  Psi, G |- v : Psi'       (s.t.  Psi' |- V[v^-1] : type exists)
           and V[v^-1] does not contain Skolem constants
           [ and Psi', G |- w' : Psi''
             and |Delta'| = d'    for a Delta'
             and PQ' can generate the proof term so far in Delta'; Psi''
           ]
           and  c is the name of the constant currently considered
           and  L is a list of cases
           then L'' list of cases and L'' extends L
           and  Psi |- w'' : Psi2
           and  |Delta''| = d''  for a Delta'
           and  PQ'' can genreate the proof term so far in Delta''; Psi2
        *))
let rec convertPro (ts_) =
  let rec convertOnePro a =
    let v_ =
      begin match I.sgnLookup a with
      | ConDec (name, _, _, _, v_, I.Kind) -> v_
      | _ -> raise (Error "Type Constant declaration expected") end in
  let mS =
    begin match ModeTable.modeLookup a with
    | None -> raise (Error "Mode declaration expected")
    | Some mS -> mS end in
  let p_ = abstract a in p_ (F.Case (F.Opts (traverse (ts_, a)))) in
let rec convertPro' =
  begin function
  | [] -> raise (Error "Cannot convert Empty program")
  | a::[] -> convertOnePro a
  | a::ts'_ -> F.Pair ((convertOnePro a), (convertPro' ts'_)) end in
let r_ = recursion ts_ in r_ (convertPro' ts_)
let convertFor = convertFor
let convertPro = convertPro
let traverse = traverse end
