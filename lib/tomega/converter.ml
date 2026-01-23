module type CONVERTER  =
  sig
    exception Error of string 
    exception Error' of Tomega.sub_ 
    val convertFor : IntSyn.cid list -> Tomega.for_
    val convertPrg : IntSyn.cid list -> Tomega.prg_
    val installPrg :
      IntSyn.cid list ->
        (((IntSyn.cid * Tomega.lemma list * Tomega.lemma list))(* projections *))
    val convertGoal : (Tomega.dec_ IntSyn.ctx_ * IntSyn.exp_) -> Tomega.prg_
  end


module Converter(Converter:sig
                             module Global : GLOBAL
                             module Abstract : ABSTRACT
                             module ModeTable : MODETABLE
                             module Names : NAMES
                             module Unify : UNIFY
                             module Whnf : WHNF
                             module Print : PRINT
                             module TomegaPrint : TOMEGAPRINT
                             module WorldSyn : WORLDSYN
                             module Worldify : WORLDIFY
                             module TomegaTypeCheck : TOMEGATYPECHECK
                             module Subordinate : SUBORDINATE
                             module TypeCheck : TYPECHECK
                             module Redundant : REDUNDANT
                             module TomegaAbstract : TOMEGAABSTRACT
                           end) : CONVERTER =
  struct
    exception Error of string 
    exception Error' of Tomega.sub_ 
    module T = Tomega
    module I = IntSyn
    module M = ModeSyn
    module S = Subordinate
    module A = Abstract
    module TA = TomegaAbstract
    let rec isIdx1 = begin function | Idx 1 -> true | _ -> false end
    let rec modeSpine a =
      begin match ModeTable.modeLookup a with
      | None -> raise (Error "Mode declaration expected")
      | Some mS -> mS end
  let rec typeOf a =
    begin match I.sgnLookup a with
    | ConDec (name, _, _, _, v_, I.Kind) -> v_
    | _ -> raise (Error "Type Constant declaration expected") end
let rec nameOf a =
  begin match I.sgnLookup a with
  | ConDec (name, _, _, _, v_, I.Kind) -> name
  | _ -> raise (Error "Type Constant declaration expected") end
let rec chatter chlev f =
  if !Global.chatter >= chlev then begin print ((^) "[tomega] " f ()) end
  else begin () end
let rec strengthenExp (u_, s) = Whnf.normalize ((Whnf.cloInv (u_, s)), I.id)
let rec strengthenSub (s, t) = Whnf.compInv (s, t)
let rec strengthenDec =
  begin function
  | (Dec (name, v_), s) -> I.Dec (name, (strengthenExp (v_, s)))
  | (BDec (name, (l_, t)), s) -> I.BDec (name, (l_, (strengthenSub (t, s)))) end
(* to show  G' |- t o s^1 : Gsome *)(* G0  |- s : G' *)
(* G0 |- t : Gsome *)
let rec strengthenCtx =
  begin function
  | (I.Null, s) -> (I.Null, s)
  | (Decl (g_, d_), s) ->
      let (g'_, s') = strengthenCtx (g_, s) in
      ((I.Decl (g'_, (strengthenDec (d_, s')))), (I.dot1 s')) end
let rec strengthenFor =
  begin function
  | (T.True, s) -> T.True
  | (And (f1_, f2_), s) ->
      T.And ((strengthenFor (f1_, s)), (strengthenFor (f2_, s)))
  | (All ((UDec (d_), q_), f_), s) ->
      T.All
        (((T.UDec (strengthenDec (d_, s))), q_),
          (strengthenFor (f_, (I.dot1 s))))
  | (Ex ((d_, q_), f_), s) ->
      T.Ex (((strengthenDec (d_, s)), q_), (strengthenFor (f_, (I.dot1 s)))) end
let rec strengthenOrder =
  begin function
  | (Arg ((u_, s1), (v_, s2)), s) ->
      Order.Arg
        ((u_, (strengthenSub (s1, s))), (v_, (strengthenSub (s2, s))))
  | (Simul (os_), s) ->
      Order.Simul (map (begin function | o_ -> strengthenOrder (o_, s) end)
        os_)
  | (Lex (os_), s) ->
      Order.Lex (map (begin function | o_ -> strengthenOrder (o_, s) end) os_) end
let rec strengthenTC =
  begin function
  | (Base (o_), s) -> T.Base (strengthenOrder (o_, s))
  | (Conj (TC1, TC2), s) ->
      T.Conj ((strengthenTC (TC1, s)), (strengthenTC (TC2, s)))
  | (Abs (d_, TC), s) ->
      T.Abs ((strengthenDec (d_, s)), (strengthenTC (TC, (I.dot1 s)))) end
let rec strengthenSpine =
  begin function
  | (I.Nil, t) -> I.Nil
  | (App (u_, s_), t) ->
      I.App ((strengthenExp (u_, t)), (strengthenSpine (s_, t))) end
let rec strengthenPsi =
  begin function
  | (I.Null, s) -> (I.Null, s)
  | (Decl (Psi, UDec (d_)), s) ->
      let (Psi', s') = strengthenPsi (Psi, s) in
      ((I.Decl (Psi', (T.UDec (strengthenDec (d_, s'))))), (I.dot1 s'))
  | (Decl (Psi, PDec (name, f_, None, None)), s) ->
      let (Psi', s') = strengthenPsi (Psi, s) in
      ((I.Decl (Psi', (T.PDec (name, (strengthenFor (f_, s')), None, None)))),
        (I.dot1 s')) end
let rec strengthenPsi' =
  begin function
  | ([], s) -> ([], s)
  | ((UDec (d_))::Psi, s) ->
      let d'_ = strengthenDec (d_, s) in
      let s' = I.dot1 s in
      let (Psi'', s'') = strengthenPsi' (Psi, s') in
      (((T.UDec d'_) :: Psi''), s'') end
let rec ctxSub =
  begin function
  | (I.Null, s) -> (I.Null, s)
  | (Decl (g_, d_), s) ->
      let (g'_, s') = ctxSub (g_, s) in
      ((I.Decl (g'_, (I.decSub (d_, s')))), (I.dot1 s)) end
let rec validMode =
  begin function
  | M.Mnil -> ()
  | Mapp (Marg (M.Plus, _), mS) -> validMode mS
  | Mapp (Marg (M.Minus, _), mS) -> validMode mS
  | Mapp (Marg (M.Star, _), mS) ->
      raise (Error "+ or - mode expected, * found") end
let rec validSig =
  begin function
  | (Psi0, []) -> ()
  | (Psi0, (g_, v_)::Sig) ->
      let rec append =
        begin function
        | (g_, I.Null) -> g_
        | (g_, Decl (g'_, d_)) -> I.Decl ((append (g_, g'_)), d_) end in
    (begin TypeCheck.typeCheck
             ((T.coerceCtx (append (Psi0, (T.embedCtx g_)))),
               (v_, (I.Uni I.Type)));
     validSig (Psi0, Sig) end) end
let rec convertOneFor cid =
  let v_ =
    begin match I.sgnLookup cid with
    | ConDec (name, _, _, _, v_, I.Kind) -> v_
    | _ -> raise (Error "Type Constant declaration expected") end in
let mS =
  begin match ModeTable.modeLookup cid with
  | None -> raise (Error "Mode declaration expected")
  | Some mS -> mS end in
let _ = validMode mS in
let rec convertFor' =
  begin function
  | (Pi ((d_, _), v_), Mapp (Marg (M.Plus, _), mS), w1, w2, n) ->
      let (f'_, F'') =
        convertFor' (v_, mS, (I.dot1 w1), (I.Dot ((I.Idx n), w2)), (n - 1)) in
      (((begin function
         | f_ ->
             T.All
               (((T.UDec (strengthenDec (d_, w1))), T.Explicit), (f'_ f_)) end)),
        F'')
  | (Pi ((d_, _), v_), Mapp (Marg (M.Minus, _), mS), w1, w2, n) ->
      let (f'_, F'') =
        convertFor' (v_, mS, (I.comp (w1, I.shift)), (I.dot1 w2), (n + 1)) in
      (f'_, (T.Ex (((I.decSub (d_, w2)), T.Explicit), F'')))
  | (Uni (I.Type), M.Mnil, _, _, _) -> (((begin function | f_ -> f_ end)),
      T.True)
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
let rec createIH =
  begin function
  | [] -> raise (Error "Empty theorem")
  | a::[] ->
      let name = I.conDecName (I.sgnLookup a) in
      let f_ = convertOneFor a in (name, f_)
  | a::l_ ->
      let name = I.conDecName (I.sgnLookup a) in
      let f_ = convertOneFor a in
      let (name', f'_) = createIH l_ in
      (((name ^ "/") ^ name'), (T.And (f_, f'_))) end
let rec convertFor (l_) = let (_, f'_) = createIH l_ in f'_
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
         | (u_, DP) -> DP || (occursInExp (k, (Whnf.normalize (u_, I.id)))) end)
      false end(* | occursInExpN (k, I.FgnExp (cs, ops)) =
         occursInExpN (k, Whnf.normalize (#toInternal(ops) (), I.id)) MERGE Fri Aug 22 23:09:53 2003 --cs *)
let rec occursInHead =
  begin function
  | (k, BVar k') -> k = k'
  | (k, Const _) -> false
  | (k, Def _) -> false
  | (k, FgnConst _) -> false
  | (k, Proj _) -> false end
let rec occursInSpine =
  begin function
  | (_, I.Nil) -> false
  | (k, App (u_, s_)) -> (occursInExpN (k, u_)) || (occursInSpine (k, s_)) end
let rec occursInDec (k, Dec (_, v_)) = occursInExpN (k, v_)
let rec occursInDecP (k, (d_, _)) = occursInDec (k, d_)
let rec occursInExp (k, u_) = occursInExpN (k, (Whnf.normalize (u_, I.id)))
let rec dot1inv w = strengthenSub ((I.comp (I.shift, w)), I.shift)
let rec shiftinv w = strengthenSub (w, I.shift)
let rec peel w = if isIdx1 (I.bvarSub (1, w)) then begin dot1inv w end
  else begin shiftinv w end
let rec peeln =
  begin function | (0, w) -> w | (n, w) -> peeln ((n - 1), (peel w)) end
let rec popn =
  begin function
  | (0, Psi) -> (Psi, I.Null)
  | (n, Decl (Psi, UDec (d_))) ->
      let (Psi', g'_) = popn ((n - 1), Psi) in (Psi', (I.Decl (g'_, d_))) end
let rec domain =
  begin function
  | (g_, Dot (Idx _, s)) -> (domain (g_, s)) + 1
  | (I.Null, Shift 0) -> 0
  | ((Decl _ as g_), Shift 0) ->
      domain (g_, (I.Dot ((I.Idx 1), (I.Shift 1))))
  | (Decl (g_, _), Shift n) -> domain (g_, (I.Shift (n - 1))) end
let rec strengthen (Psi, (a, s_), w, m) =
  let mS = modeSpine a in
  let rec args =
    begin function
    | (I.Nil, M.Mnil) -> []
    | (App (u_, s'_), Mapp (Marg (m', _), mS)) ->
        let l_ = args (s'_, mS) in
        (begin match M.modeEqual (m, m') with
         | true -> u_ :: l_
         | false -> l_ end) end in
let rec strengthenArgs =
  begin function
  | ([], s) -> []
  | ((u_)::l_, s) -> (::) (strengthenExp (u_, s)) strengthenArgs (l_, s) end in
let rec occursInArgs =
  begin function
  | (n, []) -> false
  | (n, (u_)::l_) -> (occursInExp (n, u_)) || (occursInArgs (n, l_)) end in
let rec occursInPsi =
  begin function
  | (n, ([], l_)) -> occursInArgs (n, l_)
  | (n, ((UDec (Dec (_, v_)))::Psi1, l_)) ->
      (occursInExp (n, v_)) || (occursInPsi ((n + 1), (Psi1, l_)))
  | (n, ((UDec (BDec (_, (cid, s))))::Psi1, l_)) ->
      let BlockDec (_, _, g_, _) = I.sgnLookup cid in
      (occursInSub (n, s, g_)) || (occursInPsi ((n + 1), (Psi1, l_))) end
  and occursInSub =
    begin function
    | (_, _, I.Null) -> false
    | (n, Shift k, g_) ->
        occursInSub (n, (I.Dot ((I.Idx (k + 1)), (I.Shift (k + 1)))), g_)
    | (n, Dot (Idx k, s), Decl (g_, _)) ->
        (n = k) || (occursInSub (n, s, g_))
    | (n, Dot (Exp (u_), s), Decl (g_, _)) ->
        (occursInExp (n, u_)) || (occursInSub (n, s, g_))
    | (n, Dot (Block _, s), Decl (g_, _)) -> occursInSub (n, s, g_) end
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
    if isIdx1 (I.bvarSub (1, w1))
    then begin inBlock (g_, (true, (dot1inv w1))) end
    else begin inBlock (g_, (bw, (strengthenSub (w1, I.shift)))) end end in
let rec blockSub =
begin function
| (I.Null, w) -> (I.Null, w)
| (Decl (g_, Dec (name, v_)), w) ->
    let (g'_, w') = blockSub (g_, w) in
    let v'_ = strengthenExp (v_, w') in
    ((I.Decl (g'_, (I.Dec (name, v'_)))), (I.dot1 w')) end in
let rec strengthen' =
begin function
| (((I.Null, Psi2, l_, w1))(* =  I.id *)) ->
    (I.Null, I.id, I.id)
| (Decl (Psi1, (UDec (Dec (name, v_)) as LD)), Psi2, l_, w1) ->
    if isIdx1 (I.bvarSub (1, w1))
    then
      begin let w1' = dot1inv w1 in
            let (Psi1', w', z') = strengthen' (Psi1, (LD :: Psi2), l_, w1') in
            let v'_ = strengthenExp (v_, w') in
            ((I.Decl (Psi1', (T.UDec (I.Dec (name, v'_))))), (I.dot1 w'),
              (I.dot1 z')) end
    else begin
      if occursInPsi (1, (Psi2, l_))
      then
        begin (let w1' = strengthenSub (w1, I.shift) in
               let (Psi1', w', z') =
                 strengthen' (Psi1, (LD :: Psi2), l_, w1') in
               let v'_ = strengthenExp (v_, w') in
               ((I.Decl (Psi1', (T.UDec (I.Dec (name, v'_))))), (I.dot1 w'),
                 (I.comp (z', I.shift)))) end
      else begin
        (let w1' = strengthenSub (w1, I.shift) in
         let w2 = I.shift in
         let (Psi2', w2') = strengthenPsi' (Psi2, w2) in
         let l'_ = strengthenArgs (l_, w2') in
         let (Psi1'', w', z') = strengthen' (Psi1, Psi2', l'_, w1') in
         (Psi1'', (I.comp (w', I.shift)), z')) end end
| (Decl (Psi1, (PDec (name, f_, None, None) as d_)), Psi2, l_, w1) ->
    let w1' = dot1inv w1 in
    let (Psi1', w', z') = strengthen' (Psi1, (d_ :: Psi2), l_, w1') in
    let f'_ = strengthenFor (f_, w') in
    ((I.Decl (Psi1', (T.PDec (name, f'_, None, None)))), (I.dot1 w'),
      (I.dot1 z'))
| (Decl (Psi1, (UDec (BDec (name, (cid, s))) as LD)), Psi2, l_, w1) ->
    let w1' = dot1inv w1 in
    let (Psi1', w', z') = strengthen' (Psi1, (LD :: Psi2), l_, w1') in
    let s' = strengthenSub (s, w') in
    ((((I.Decl (Psi1', (T.UDec (I.BDec (name, (cid, s')))))), (I.dot1 w'),
        (I.dot1 z')))
      (* blocks are always used! *)) end in
((strengthen' (Psi, [], (args (s_, mS)), w))
(* is this ok? -- cs *)(* no other cases *)
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
let rec lookupIH (Psi, l_, a) =
  let rec lookupIH' (b::l_, a, k) = if a = b then begin k end
    else begin lookupIH' (l_, a, (k - 1)) end in
lookupIH' (l_, a, (I.ctxLength Psi))
let rec createIHSub (Psi, l_) =
  T.Shift (((I.ctxLength Psi) - 1)(*List.length L *))
let rec transformInit (Psi, l_, (a, s_), w1) =
  let mS = modeSpine a in
  let v_ = typeOf a in
  let rec transformInit' =
    begin function
    | ((I.Nil, M.Mnil), Uni (I.Type), (w, s)) -> (w, s)
    | ((App (u_, s_), Mapp (Marg (M.Minus, _), mS)), Pi (_, v2_), (w, s)) ->
        let w' = I.comp (w, I.shift) in
        let s' = s in transformInit' ((s_, mS), v2_, (w', s'))
    | ((App (u_, s_), Mapp (Marg (M.Plus, _), mS)), Pi
       ((Dec (name, v1_), _), v2_), (w, s)) ->
        let V1' = strengthenExp (v1_, w) in
        let w' = I.dot1 w in
        let u'_ = strengthenExp (u_, w1) in
        let s' = T.dotEta ((T.Exp u'_), s) in
        transformInit' ((s_, mS), v2_, (w', s')) end in
  ((transformInit' ((s_, mS), v_, (I.id, (createIHSub (Psi, l_)))))
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
let rec transformConc ((a, s_), w) =
  let rec transformConc' =
    begin function
    | (I.Nil, M.Mnil) -> T.Unit
    | (App (u_, s'_), Mapp (Marg (M.Plus, _), mS')) ->
        transformConc' (s'_, mS')
    | (App (u_, s'_), Mapp (Marg (M.Minus, _), mS')) ->
        T.PairExp ((strengthenExp (u_, w)), (transformConc' (s'_, mS'))) end in
transformConc' (s_, (modeSpine a))
let rec renameExp arg__0 arg__1 =
  begin match (arg__0, arg__1) with
  | (f, (Uni _ as u_)) -> u_
  | (f, Pi ((d_, DP), v_)) -> I.Pi (((renameDec f d_), DP), (renameExp f v_))
  | (f, Root (h_, s_)) -> I.Root ((renameHead f h_), (renameSpine f s_))
  | (f, Lam (d_, u_)) -> I.Lam ((renameDec f d_), (renameExp f u_)) end
let rec renameDec f (Dec (x, v_)) = I.Dec (x, (renameExp f v_))
let rec renameHead arg__2 arg__3 =
  begin match (arg__2, arg__3) with | (f, Proj bi) -> f bi | (f, h_) -> h_ end
let rec renameSpine arg__4 arg__5 =
  begin match (arg__4, arg__5) with
  | (f, I.Nil) -> I.Nil
  | (f, App (u_, s_)) -> I.App ((renameExp f u_), (renameSpine f s_)) end
let rec rename (BDec (_, (c, s)), v_) =
  let (g_, l_) = I.constBlock c in
  let rec makeSubst =
    begin function
    | (n, g_, s, [], f) -> (g_, f)
    | (n, g_, s, (Dec (x, v'_) as d_)::l_, f) ->
        if Subordinate.belowEq ((I.targetFam v'_), (I.targetFam v_))
        then
          begin makeSubst
                  ((n + 1), (I.Decl (g_, (I.decSub (d_, s)))), (I.dot1 s),
                    l_, f) end
        else begin makeSubst (n, g_, (I.comp (s, I.shift)), l_, f) end end in
let (g'_, f) = makeSubst (1, g_, s, l_, (begin function | x -> I.Proj x end)) in
(g_, (renameExp f v_))
let rec append =
  begin function
  | (g_, I.Null) -> g_
  | (g_, Decl (g'_, d_)) -> I.Decl ((append (g_, g'_)), d_) end
let rec traverseNeg arg__6 arg__7 =
  begin match (arg__6, arg__7) with
  | ((l_, wmap, projs),
     ((Psi0, Psi), Pi (((Dec (_, v1_) as d_), I.Maybe), v2_), w)) ->
      (begin match traverseNeg (l_, wmap, projs)
                     ((Psi0, (I.Decl (Psi, (T.UDec d_)))), v2_, (I.dot1 w))
             with
       | Some (w', PQ') -> Some ((peel w'), PQ') end)
  | ((l_, wmap, projs),
     ((Psi0, Psi), Pi (((Dec (_, v1_) as d_), I.No), v2_), w)) ->
      (begin match traverseNeg (l_, wmap, projs)
                     ((Psi0, (I.Decl (Psi, (T.UDec d_)))), v2_,
                       (I.comp (w, I.shift)))
             with
       | Some (w', PQ') ->
           traversePos (l_, wmap, projs)
             ((Psi0, Psi, I.Null), v1_, (Some ((peel w'), PQ'))) end)
  | ((l_, wmap, projs), ((Psi0, Psi), Root (Const a, s_), w)) ->
      let Psi1 = append (Psi0, Psi) in
      let w0 = I.Shift (I.ctxLength Psi) in
      let (Psi', w', _) = strengthen (Psi1, (a, s_), w0, M.Plus) in
      let (w'', s'') = transformInit (Psi', l_, (a, s_), w') in
      let _ = TomegaTypeCheck.checkCtx Psi' in
      ((Some
          (w', ((begin function | p_ -> (Psi', s'', p_) end),
            (transformConc ((a, s_), w)))))
        (* Psi1 = Psi0, Psi *)(* Psi1 |- w0 : Psi0 *)
        (* |- Psi' ctx *)(* Psi1 |- w' : Psi' *)
        (* Psi' |- s'' : G+ *)(* G |- w'' : G+ *)) end
(* Psi0, Psi |- S : {G} type > type *)(* Sigma (a) = Va *)
(* Psi0, Psi |- w : Psi0, Psi' *)
let rec traversePos arg__8 arg__9 =
  begin match (arg__8, arg__9) with
  | ((l_, wmap, projs),
     ((Psi0, Psi, g_), Pi (((BDec (x, (c, s)) as d_), _), v_), Some
      (w1, (p_, q_)))) ->
      let c' = wmap c in
      let n = (+) (I.ctxLength Psi0) I.ctxLength g_ in
      let (Gsome, Lpi) = I.constBlock c in
      let _ =
        TypeCheck.typeCheckCtx
          (T.coerceCtx (append ((append (Psi0, Psi)), (T.embedCtx g_)))) in
      let _ =
        TypeCheck.typeCheckSub
          ((T.coerceCtx (append ((append (Psi0, Psi)), (T.embedCtx g_)))), s,
            Gsome) in
      let (Gsome', Lpi') = I.constBlock c' in
      let _ =
        TypeCheck.typeCheckCtx
          (T.coerceCtx (append ((append (Psi0, Psi)), (T.embedCtx g_)))) in
      let _ =
        TypeCheck.typeCheckSub
          ((T.coerceCtx (append ((append (Psi0, Psi)), (T.embedCtx g_)))), s,
            Gsome') in
      traversePos (l_, wmap, projs)
        ((Psi0, Psi,
           (I.Decl (((g_, (I.BDec (x, (c', s)))))
              (* T.UDec *)))), v_,
          (Some ((I.dot1 w1), (p_, q_))))
  | ((l_, wmap, projs),
     ((Psi0, g_, b_), (Root (Const a, s_) as v_), Some (w1, (p_, q_)))) ->
      let Psi1 = append (Psi0, (append (g_, (T.embedCtx b_)))) in
      let _ =
        TomegaTypeCheck.checkCtx
          (append ((append (Psi0, g_)), (T.embedCtx b_))) in
      let n = domain (Psi1, w1) in
      let m = I.ctxLength Psi0 in
      let rec lookupbase a =
        let s = I.conDecName (I.sgnLookup a) in
        let l = T.lemmaName s in
        let ValDec (_, p_, f_) = T.lemmaLookup l in ((T.Const l), f_) in
      let rec lookup =
        begin function
        | ((b::[], None, f_), a) ->
            if a = b then begin let p_ = T.Var n in (p_, f_) end
            else begin lookupbase a end
        | ((b::[], Some (lemma::[]), f_), a) ->
            if a = b
            then
              begin let p_ =
                      T.Redex
                        ((T.Const lemma), (T.AppPrg ((T.Var n), T.Nil))) in
                    (p_, f_) end
            else begin lookupbase a end
        | ((b::l_, Some (lemma::lemmas), And (f1_, f2_)), a) ->
            if a = b
            then
              begin let p_ =
                      T.Redex
                        ((T.Const lemma), (T.AppPrg ((T.Var n), T.Nil))) in
                    (p_, f1_) end
            else begin lookup ((l_, (Some lemmas), f2_), a) end end in
let (HP, f_) =
  if (I.ctxLength Psi0) > 0
  then
    begin let PDec (_, f0_, _, _) = I.ctxLookup (Psi0, 1) in
          lookup ((l_, projs, f0_), a) end
  else begin lookupbase a end in
let rec apply ((s_, mS), Ft) = applyW ((s_, mS), (T.whnfFor Ft))
and applyW =
  begin function
  | ((I.Nil, M.Mnil), Ft') -> (T.Nil, (T.forSub Ft'))
  | ((App (u_, s_), Mapp (Marg (M.Plus, _), mS)), (All (d_, f'_), t')) ->
      let u'_ = strengthenExp (u_, w1) in
      let (S'', F'') = apply ((s_, mS), (f'_, (T.Dot ((T.Exp u'_), t')))) in
      ((((T.AppExp (u'_, S'')), F''))
        (* Psi0, G', B' |- U' : V' *)(* Psi0, G', B' |- F'' :: for *)
        (* Psi0, G', B' |- S'' : F' [t'] >> F'' *)(* Psi0, G', B' |- U' ; S''
                                                       : all {x:V'} F' >> F'' *))
  | ((App (u_, s_), Mapp (Marg (M.Minus, _), mS)), Ft) ->
      applyW ((s_, mS), Ft) end(* Psi0, G', B', x:V' |- F' :: for *)
  (* Psi0, G', B' |- D = x:V' : type *) in
let (S'', F'') = apply ((s_, (modeSpine a)), (f_, T.id)) in
let _ =
  TomegaTypeCheck.checkFor
    ((append ((append (Psi0, g_)), (T.embedCtx b_))),
      (T.forSub (F'', (T.embedSub w1)))) in
let P'' = T.Redex (((HP, S''))(*T.Var k' *)) in
let b = I.ctxLength b_ in
let w1' = peeln (b, w1) in
let (b'_, _) = strengthenCtx (b_, w1') in
let n' = (-) n I.ctxLength b'_ in
let rec subCtx =
  begin function
  | (I.Null, s) -> (I.Null, s)
  | (Decl (g_, d_), s) ->
      let (g'_, s') = subCtx (g_, s) in
      ((I.Decl (g'_, (I.decSub (d_, s')))), (I.dot1 s')) end in
let (B'', _) = subCtx (b'_, w1') in
let _ =
  TomegaTypeCheck.checkCtx (append ((append (Psi0, g_)), (T.embedCtx B''))) in
let (GB', iota) = T.deblockify b'_ in
let _ =
  begin try TypeCheck.typeCheckSub (GB', (T.coerceSub iota), b'_)
  with | Error _ -> raise (Error' iota) end in
let RR = T.forSub (F'', iota) in
let F''' = TA.raiseFor (GB', (RR, I.id)) in
let rec lift =
  begin function
  | (I.Null, p_) -> p_
  | (Decl (g_, d_), p_) ->
      let (Bint, _) = T.deblockify (I.Decl (I.Null, d_)) in
      lift (g_, (T.New (T.Lam ((T.UDec d_), p_)))) end in
let P''' = lift (b'_, P'') in
let _ = TomegaTypeCheck.checkCtx (append (Psi0, g_)) in
let _ =
  TomegaTypeCheck.checkFor
    ((append (Psi0, g_)), (T.forSub (F''', (T.embedSub w1')))) in
let (Psi1'', w2, z2) = strengthen (Psi1, (a, s_), w1, M.Minus) in
let w3 = peeln (b, w2) in
let z3 = peeln (b, z2) in
let (Psi2, B3') = popn (b, Psi1'') in
let Pat' = transformConc ((a, s_), w2) in
let f4_ = T.forSub (F''', (T.embedSub z3)) in
let _ = TomegaTypeCheck.checkCtx Psi1'' in
let _ = TomegaTypeCheck.checkCtx (append (Psi2, (T.embedCtx B3'))) in
let _ =
  begin try TomegaTypeCheck.checkFor (Psi2, f4_) with | _ -> raise (Error "") end in
let (b3_, sigma3) = T.deblockify B3' in
let Pat'' = T.normalizePrg (Pat', sigma3) in
let Pat = TA.raisePrg (b3_, Pat'', f4_) in
let _ = TomegaTypeCheck.checkPrg (Psi2, (Pat, f4_)) in
let t = T.Dot ((T.Prg Pat), (T.embedSub z3)) in
((Some
    (w3,
      ((begin function
        | p ->
            p_
              (T.Let
                 ((T.PDec (None, F''', None, None)), P''',
                   (T.Case (T.Cases [(Psi2, t, p)])))) end), q_)))
  (* Psi1 = Psi0, G, B *)(* n = |Psi0, G', B'| *)
  (* m = |Psi0| *)(* strengthened invariant Psi0 might be empty --cs Fri Apr 11 15:25:32 2003 *)
  (* apply ((S, mS), F')= (S'', F'')

                 Invariant:
                 Psi0, G, B |- S : V >> type
                   (mS is the corresponding mode spine)
                 and  Psi0, G', B |- F'  :: for
                 then Psi0, G', B |- F'' :: for
                 and  Psi0, G', B |- S'' :: F' >> F''
              *)
  (* Psi0, G', B' |- F'' :: for *)(* Psi0, G', B' |- S'' :: F' >> F'' *)
  (* was T.Root  -cs Sun Jan  5 23:15:06 2003 *)(* Psi0, G', B' |- P'' :: F'' *)
  (* b = |B| = |B'| *)(* Psi0, G |- w1' : Psi0, G' *)
  (* |- Psi0, G', B' ctx *)(* n' = |Psi0, G'| *)
  (* Psi0, G' |- GB' ctx *)(* Psi0, G, B |- w1 : Psi0, G', B' *)
  (* Psi0, G', GB'  |- s' : Psi0, G', B' *)(* Psi0, G', GB' |- RR for *)
  (* Psi0, G |- w1' : Psi0, G' *)(* Psi0, G' |- F''' for *)
  (* lift (B, (P, F)) = (P', F')

                 Invariant:
                 If   Psi0, G, B |- P :: F
                 then Psi0, G |- P'  :: F'
                 and  P' =  (lam B. P)
                 and  F' = raiseFor (B, F)
              *)
  (* Psi0, G' |- P''' :: F''' *)(* |- Psi0, Psi1'' ctx *)
  (* Psi0, G, B |- w2 : Psi1'' *)(* Psi1'' = Psi0, G3, B3' *)
  (* |B| = |GB'| *)(* Psi'' |-  z2 : Psi0, G', B' *)
  (* Psi0, G, B |- w2 : Psi0, G3, B3' *)(* Psi0, G |- w3 : Psi0, G3 *)
  (* Psi0, G3 |-  z3 : Psi0, G' *)(* Psi2 = Psi0, G3 *)
  (* Psi0, G3, B3' |- Pat' :: For *)(* Psi0, G3 |- F4 for *)
  (* ' F4 *)(* Psi0, G3 |- Pat :: F4  *)
  (* Here's a commutative diagram
                                           at work which one has to prove
                                           correct
                                        *)
  (* Psi0, G3 |- t :: Psi0, G', x :: F4  *)) end(* Psi0, G, B |- w1 : Psi0, G', B' *)
(* Psi0, G, B |- V : type *)(* |- Psi0 matches L *)
(* Psi0 = x1::F1 ... xn::Fn *)
let rec traverse (Psi0, l_, Sig, wmap, projs) =
  let rec traverseSig' =
    begin function
    | [] -> []
    | (g_, v_)::Sig ->
        (begin TypeCheck.typeCheck
                 ((append ((T.coerceCtx Psi0), g_)), (v_, (I.Uni I.Type)));
         (begin match traverseNeg (l_, wmap, projs)
                        ((Psi0, (T.embedCtx g_)), v_, I.id)
                with
          | Some (wf, (p'_, q'_)) -> (traverseSig' Sig) @ [p'_ q'_] end) end) end in
traverseSig' Sig
let rec transformWorlds (fams, Worlds cids) =
  let rec transformList =
    begin function
    | ([], w) -> []
    | ((Dec (x, v_) as d_)::l_, w) ->
        if
          List.foldr
            (begin function
             | (a, b) -> b && (Subordinate.belowEq (a, (I.targetFam v_))) end)
          true fams
        then begin transformList (l_, (I.comp (w, I.shift))) end
    else begin
      (let l'_ = transformList (l_, (I.dot1 w)) in
       (I.Dec (x, (strengthenExp (v_, w)))) :: l'_) end end in
let rec transformWorlds' =
begin function
| [] -> ([], ((begin function | c -> raise (Error "World not found") end)))
| cid::cids' ->
    let BlockDec (s, m, g_, l_) = I.sgnLookup cid in
    let l'_ = transformList (l_, I.id) in
    let (cids'', wmap) = transformWorlds' cids' in
    let cid' = I.sgnAdd (I.BlockDec (s, m, g_, l'_)) in
    ((((cid' :: cids''),
        ((begin function
          | c -> if c = cid then begin cid' end else begin wmap c end end))))
      (* Design decision: Let's keep all of G *)) end in
let (cids', wmap) = transformWorlds' cids in ((((T.Worlds cids'), wmap))
(* convertList (a, L, w) = L'

             Invariant:
             If   G0 |- G, L : ctx
             and  G0, G |- w : G0, G'
             then G0 |- G', L' ctx
          *))
let rec dynamicSig (Psi0, a, Worlds cids) =
  let rec findDec =
    begin function
    | (g_, _, [], w, Sig) -> Sig
    | (g_, n, (d_)::l_, w, Sig) ->
        let Dec (x, v'_) as d'_ = I.decSub (d_, w) in
        let b = I.targetFam v'_ in
        let Sig' =
          if b = a then begin (g_, (Whnf.normalize (v'_, I.id))) :: Sig end
          else begin Sig end in
        findDec
          (g_, (n + 1), l_,
            (I.Dot ((I.Exp (I.Root ((I.Proj ((I.Bidx 1), n)), I.Nil))), w)),
            Sig') end in
let rec mediateSub =
begin function
| I.Null -> (I.Null, (I.Shift (I.ctxLength Psi0)))
| Decl (g_, d_) ->
    let (g0_, s') = mediateSub g_ in
    let d'_ = I.decSub (d_, s') in ((I.Decl (g0_, d'_)), (I.dot1 s')) end in
let rec findDecs' =
begin function
| ([], Sig) -> Sig
| (cid::cids', Sig) ->
    let BlockDec (s, m, g_, l_) = I.sgnLookup cid in
    let (g0_, s') = mediateSub g_ in
    let d'_ = Names.decName (g0_, (I.BDec (None, (cid, s')))) in
    let s'' = I.comp (s', I.shift) in
    let Sig' = findDec ((I.Decl (g0_, d'_)), 1, l_, s'', Sig) in
    ((findDecs' (cids', Sig'))
      (* G |- L ctx *)(* Psi0, G0 |- s'' : G *)
      (* Psi0, G0 |- D : dec *)(* Psi0, G0, D' |- s'' : G *)) end in
((findDecs' (cids, []))
(* findDec (G, n, L, s, S) = S'

             Invariant:
             If   G |-  L : ctx
             and  G |- w: G'
             then |- G', L' ctx
          *)
(* mediateSub G = (G0, s)

             Invariant:
             If   . |- G ctx
             then Psi0 |- G0 ctx
             and  Psi0, G0 |- s : G
          *))
let rec staticSig =
  begin function
  | (Psi0, []) -> []
  | (Psi0, (ConDec (name, _, _, _, v_, I.Type))::Sig) ->
      (::) (I.Null, (Whnf.normalize (v_, (I.Shift (I.ctxLength Psi0)))))
        staticSig (Psi0, Sig) end
let rec name =
  begin function
  | a::[] -> I.conDecName (I.sgnLookup a)
  | a::l_ -> ((I.conDecName (I.sgnLookup a)) ^ "/") ^ (name l_) end
let rec convertPrg (l_, projs) =
  let (name, f0_) = createIH l_ in
  let d0_ = T.PDec ((Some name), f0_, None, None) in
  let Psi0 = I.Decl (I.Null, d0_) in
  let Prec = begin function | p -> T.Rec (d0_, p) end in
  let rec convertWorlds =
    begin function
    | a::[] ->
        let w_ = WorldSyn.lookup a in ((w_)
          (* W describes the world of a *))
    | a::l'_ ->
        let w_ = WorldSyn.lookup a in
        let w'_ = convertWorlds l'_ in
        ((if T.eqWorlds (w_, w'_) then begin w'_ end
          else begin
            raise (Error "Type families different in different worlds") end)
        (* W describes the world of a *)) end in
  let w_ = convertWorlds l_ in
  let (w'_, wmap) = transformWorlds (l_, w_) in
  let rec convertOnePrg (a, f_) =
    let name = nameOf a in
    let v_ = typeOf a in
    let mS = modeSpine a in
    let Sig = Worldify.worldify a in
    let dynSig = dynamicSig (Psi0, a, w_) in
    let statSig = staticSig (Psi0, Sig) in
    let _ =
      map
        (begin function
         | ConDec (_, _, _, _, u_, v_) -> TypeCheck.check (u_, (I.Uni v_)) end)
      Sig in
    let _ = validSig (Psi0, statSig) in
    let _ = validSig (Psi0, dynSig) in
    let c0_ = traverse (Psi0, l_, dynSig, wmap, projs) in
    let rec init =
      begin function
      | All ((d_, _), f'_) ->
          let (F'', p'_) = init f'_ in
          (F'', ((begin function | p -> T.Lam (d_, (p'_ p)) end)))
      | f'_ -> (f'_, ((begin function | p -> p end))) end in
    let (f'_, Pinit) = init f_ in
    let c_ = traverse (Psi0, l_, statSig, wmap, projs) in
    ((Pinit (T.Case ((T.Cases (c0_ @ c_))(* F', *))))
      (* Psi0 |- {x1:V1} ... {xn:Vn} type *)(* |- mS : {x1:V1} ... {xn:Vn} > type *)
      (* Sig in LF(reg)   *)(* init' F = P'

               Invariant:
               If   F = All x1:A1. ... All xn:An. F'
               and  f' does not start with a universal quantifier
               then P' P'' = Lam x1:A1. ... Lam xn:An P''
                    for any P''
            *)
      (* Psi0, x1:V1, ..., xn:Vn |- C :: F *)) in
let rec convertPrg' =
  begin function
  | ([], _) -> raise (Error "Cannot convert Empty program")
  | (a::[], f_) -> convertOnePrg (a, f_)
  | (a::l'_, And (f1_, f2_)) ->
      T.PairPrg ((convertOnePrg (a, f1_)), (convertPrg' (l'_, f2_))) end in
let p_ = Prec (convertPrg' (l_, f0_)) in p_
let rec installFor (cid::[]) =
  let f_ = convertFor [cid] in
  let name = I.conDecName (I.sgnLookup cid) in
  let _ = T.lemmaAdd (T.ForDec (name, f_)) in ()
let rec depthConj =
  begin function | And (f1_, f2_) -> (+) 1 depthConj f2_ | f_ -> 1 end
let rec createProjection =
  begin function
  | (Psi, depth, (And (f1_, f2_) as f_), Pattern) ->
      createProjection
        ((I.Decl (Psi, (T.PDec (None, f1_, None, None)))), (depth + 1),
          (T.forSub (f2_, (T.Shift 1))),
          (T.PairPrg ((T.Var (depth + 2)), Pattern)))
  | (Psi, depth, f_, Pattern) ->
      let Psi' = I.Decl (Psi, (T.PDec (None, f_, None, None))) in
      let depth' = depth + 1 in
      (begin function
       | k ->
           let PDec (_, f'_, _, _) = T.ctxDec (Psi', k) in
           ((T.Case
               (T.Cases
                  [(Psi', (T.Dot ((T.Prg Pattern), (T.Shift depth'))),
                     (T.Var k))])), f'_) end) end
let rec installProjection =
  begin function
  | ([], _, f_, Proj) -> []
  | (cid::cids, n, f_, Proj) ->
      let (p'_, f'_) = Proj n in
      let p_ = T.Lam ((T.PDec (None, f_, None, None)), p'_) in
      let F'' = T.All (((T.PDec (None, f_, None, None)), T.Explicit), f'_) in
      let name = I.conDecName (I.sgnLookup cid) in
      let _ = TomegaTypeCheck.checkPrg (I.Null, (p_, F'')) in
      let lemma = T.lemmaAdd (T.ValDec (("#" ^ name), p_, F'')) in
      (::) lemma installProjection (cids, (n - 1), f_, Proj) end
let rec installSelection =
  begin function
  | (cid::[], lemma::[], f1_, main) ->
      let p_ = T.Redex ((T.Const lemma), (T.AppPrg ((T.Const main), T.Nil))) in
      let name = I.conDecName (I.sgnLookup cid) in
      let _ = TomegaTypeCheck.checkPrg (I.Null, (p_, f1_)) in
      let lemma' = T.lemmaAdd (T.ValDec (name, p_, f1_)) in [lemma']
  | (cid::cids, lemma::lemmas, And (f1_, f2_), main) ->
      let p_ = T.Redex ((T.Const lemma), (T.AppPrg ((T.Const main), T.Nil))) in
      let name = I.conDecName (I.sgnLookup cid) in
      let _ = TomegaTypeCheck.checkPrg (I.Null, (p_, f1_)) in
      let lemma' = T.lemmaAdd (T.ValDec (name, p_, f1_)) in
      (::) lemma' installSelection (cids, lemmas, f2_, main) end
let rec installPrg =
  begin function
  | cid::[] ->
      let f_ = convertFor [cid] in
      let p_ = convertPrg ([cid], None) in
      let name = I.conDecName (I.sgnLookup cid) in
      let _ = TomegaTypeCheck.checkPrg (I.Null, (p_, f_)) in
      let _ =
        if !Global.chatter >= 4
        then begin print "[Redundancy Checker (factoring) ..." end
        else begin () end in
      let factP = Redundant.convert p_ in
      let _ = if !Global.chatter >= 4 then begin print "done]\n" end
        else begin () end in
      let lemma = T.lemmaAdd (T.ValDec (name, factP, f_)) in (lemma, [], [])
| cids ->
    let f_ = convertFor cids in
    let _ = TomegaTypeCheck.checkFor (I.Null, f_) in
    let Proj = createProjection (I.Null, 0, f_, (T.Var 1)) in
    let projs = installProjection (cids, (depthConj f_), f_, Proj) in
    let p_ = convertPrg (cids, (Some projs)) in
    let s = name cids in
    let _ = TomegaTypeCheck.checkPrg (I.Null, (p_, f_)) in
    let _ =
      if !Global.chatter >= 4
      then begin print "[Redundancy Checker (factoring) ..." end
      else begin () end in
    let factP = Redundant.convert p_ in
    let _ = if !Global.chatter >= 4 then begin print "done]\n" end
      else begin () end in
    let lemma = T.lemmaAdd (T.ValDec (s, factP, f_)) in
    let sels = installSelection (cids, projs, f_, lemma) in
    (lemma, projs, sels) end
let rec mkResult =
  begin function
  | 0 -> T.Unit
  | n -> T.PairExp ((I.Root ((I.BVar n), I.Nil)), (mkResult (n - 1))) end
let rec convertGoal (g_, v_) =
  let a = I.targetFam v_ in
  let w_ = WorldSyn.lookup a in
  let (w'_, wmap) = transformWorlds ([a], w_) in
  let Some (_, (p'_, q'_)) =
    traversePos ([], wmap, None)
      ((I.Null, g_, I.Null), v_,
        (Some
           ((I.Shift (I.ctxLength g_)),
             ((begin function | p_ -> (I.Null, T.id, p_) end),
             (mkResult (I.ctxLength g_)))))) in
  let (_, _, P'') = p'_ q'_ in P''
let convertFor = convertFor
let convertPrg = begin function | l_ -> convertPrg (l_, None) end
let installFor = installFor
let installPrg = installPrg
let traverse = traverse
let convertGoal = convertGoal end
