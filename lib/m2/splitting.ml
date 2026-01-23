module type SPLITTING  =
  sig
    module MetaSyn : METASYN
    exception Error of string 
    type nonrec operator
    val expand : MetaSyn.state_ -> operator list
    val apply : operator -> MetaSyn.state_ list
    val var : operator -> int
    val menu : operator -> string
    val index : operator -> int
  end


module Splitting(Splitting:sig
                             module Global : GLOBAL
                             module MetaSyn' : METASYN
                             module MetaAbstract : METAABSTRACT
                             module MetaPrint : METAPRINT
                             module ModeTable : MODETABLE
                             module Whnf : WHNF
                             module Index : INDEX
                             module Print : PRINT
                             module Unify : UNIFY
                           end) : SPLITTING =
  struct
    module MetaSyn = MetaSyn'
    exception Error of string 
    type 'a flag =
      | Active of 'a 
      | InActive 
    type nonrec operator =
      ((MetaSyn.state_ * int) * MetaSyn.state_ flag list)
    module M = MetaSyn
    module I = IntSyn
    let rec constCases =
      begin function
      | (g_, vs_, [], abstract, ops) -> ops
      | (g_, vs_, (Const c)::Sgn, abstract, ops) ->
          let (u_, vs'_) = M.createAtomConst (g_, (I.Const c)) in
          constCases
            (g_, vs_, Sgn, abstract,
              (CSManager.trail
                 (begin function
                  | () ->
                      (begin try
                               if Unify.unifiable (g_, vs_, vs'_)
                               then
                                 begin (Active
                                          (abstract
                                             (((I.conDecName (I.sgnLookup c))
                                                 ^ "/"), u_)))
                                         :: ops end
                               else begin ops end
                  with | Error _ -> InActive :: ops end) end))) end
let rec paramCases =
  begin function
  | (g_, vs_, 0, abstract, ops) -> ops
  | (g_, vs_, k, abstract, ops) ->
      let (u_, vs'_) = M.createAtomBVar (g_, k) in
      paramCases
        (g_, vs_, (k - 1), abstract,
          (CSManager.trail
             (begin function
              | () ->
                  (begin try
                           if Unify.unifiable (g_, vs_, vs'_)
                           then
                             begin (Active
                                      (abstract
                                         (((Int.toString k) ^ "/"), u_)))
                                     :: ops end
                           else begin ops end
              with | Error _ -> InActive :: ops end) end))) end
let rec lowerSplitDest =
  begin function
  | (g_, ((Root (Const c, _) as v_), s'), abstract) ->
      constCases
        (g_, (v_, s'), (Index.lookup c), abstract,
          (paramCases (g_, (v_, s'), (I.ctxLength g_), abstract, [])))
  | (g_, (Pi ((d_, p_), v_), s'), abstract) ->
      let d'_ = I.decSub (d_, s') in
      lowerSplitDest
        ((I.Decl (g_, d'_)), (v_, (I.dot1 s')),
          (begin function | (name, u_) -> abstract (name, (I.Lam (d'_, u_))) end)) end
let rec split (Prefix (g_, m_, b_), ((Dec (_, v_) as d_), s), abstract) =
  lowerSplitDest
    (I.Null, (v_, s),
      (begin function
       | (name', u'_) ->
           abstract
             (name', (M.Prefix (g_, m_, b_)), (I.Dot ((I.Exp u'_), s))) end))
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
let rec checkVar =
  begin function
  | (Decl (m_, M.Top), 1) -> true
  | (Decl (m_, M.Bot), 1) -> false
  | (Decl (m_, _), k) -> checkVar (m_, (k - 1)) end
let rec checkExp =
  begin function
  | (m_, Uni _) -> true
  | (m_, Pi ((d_, p_), v_)) ->
      (checkDec (m_, d_)) && (checkExp ((I.Decl (m_, M.Top)), v_))
  | (m_, Lam (d_, v_)) ->
      (checkDec (m_, d_)) && (checkExp ((I.Decl (m_, M.Top)), v_))
  | (m_, Root (BVar k, s_)) -> (checkVar (m_, k)) && (checkSpine (m_, s_))
  | (m_, Root (_, s_)) -> checkSpine (m_, s_) end
let rec checkSpine =
  begin function
  | (m_, I.Nil) -> true
  | (m_, App (u_, s_)) -> (checkExp (m_, u_)) && (checkSpine (m_, s_)) end
let rec checkDec (m_, Dec (_, v_)) = checkExp (m_, v_)
let rec modeEq =
  begin function
  | (Marg (ModeSyn.Plus, _), M.Top) -> true
  | (Marg (ModeSyn.Minus, _), M.Bot) -> true
  | _ -> false end
let rec inheritBelow =
  begin function
  | (b', k', Lam (d'_, u'_), Bdd') ->
      inheritBelow (b', (k' + 1), u'_, (inheritBelowDec (b', k', d'_, Bdd')))
  | (b', k', Pi ((d'_, _), v'_), Bdd') ->
      inheritBelow (b', (k' + 1), v'_, (inheritBelowDec (b', k', d'_, Bdd')))
  | (b', k', Root (BVar n', s'_), (b'_, d, d')) ->
      ((if ((n' = k') + d') && (n' > k')
        then
          begin inheritBelowSpine
                  (b', k', s'_, ((I.Decl (b'_, b')), d, (d' - 1))) end
      else begin inheritBelowSpine (b', k', s'_, (b'_, d, d')) end)
  (* necessary for d' = 0 *))
  | (b', k', Root (c_, s'_), Bdd') -> inheritBelowSpine (b', k', s'_, Bdd') end
let rec inheritBelowSpine =
  begin function
  | (b', k', I.Nil, Bdd') -> Bdd'
  | (b', k', App (u'_, s'_), Bdd') ->
      inheritBelowSpine (b', k', s'_, (inheritBelow (b', k', u'_, Bdd'))) end
let rec inheritBelowDec (b', k', Dec (x, v'_), Bdd') =
  inheritBelow (b', k', v'_, Bdd')
let rec skip =
  begin function
  | (k, Lam (d_, u_), Bdd') -> skip ((k + 1), u_, (skipDec (k, d_, Bdd')))
  | (k, Pi ((d_, _), v_), Bdd') ->
      skip ((k + 1), v_, (skipDec (k, d_, Bdd')))
  | (k, Root (BVar n, s_), (b'_, d, d')) ->
      ((if ((n = k) + d) && (n > k)
        then begin skipSpine (k, s_, (b'_, (d - 1), d')) end
      else begin skipSpine (k, s_, (b'_, d, d')) end)
  (* necessary for d = 0 *))
  | (k, Root (c_, s_), Bdd') -> skipSpine (k, s_, Bdd') end
let rec skipSpine =
  begin function
  | (k, I.Nil, Bdd') -> Bdd'
  | (k, App (u_, s_), Bdd') -> skipSpine (k, s_, (skip (k, u_, Bdd'))) end
let rec skipDec (k, Dec (x, v_), Bdd') = skip (k, v_, Bdd')
let rec inheritExp =
  begin function
  | (b_, k, Lam (d_, u_), k', Lam (d'_, u'_), Bdd') ->
      inheritExp
        (b_, (k + 1), u_, (k' + 1), u'_,
          (inheritDec (b_, k, d_, k', d'_, Bdd')))
  | (b_, k, Pi ((d_, _), v_), k', Pi ((d'_, _), v'_), Bdd') ->
      inheritExp
        (b_, (k + 1), v_, (k' + 1), v'_,
          (inheritDec (b_, k, d_, k', d'_, Bdd')))
  | (b_, k, (Root (BVar n, s_) as v_), k', v'_, (b'_, d, d')) ->
      ((if ((n = k) + d) && (n > k)
        then
          begin skipSpine
                  (k, s_,
                    (inheritNewRoot
                       (b_, (I.ctxLookup (b_, (n - k))), k, v_, k', v'_,
                         (b'_, d, d')))) end
      else begin
        ((if (n > k) + d
          then
            begin skipSpine
                    (k, s_,
                      (inheritBelow
                         (((I.ctxLookup (b_, (n - k))) - 1), k', v'_,
                           (b'_, d, d')))) end
        else begin
          (let Root (c'_, s'_) = v'_ in
           ((inheritSpine (b_, k, s_, k', s'_, (b'_, d, d')))
             (* C' = BVar (n) *))) end)
  (* already seen original variable *)(* then (B', d, d') *)
  (* previous line avoids redundancy,
                  but may violate invariant outside pattern fragment *)
  (* must correspond *)) end)
(* new original variable *)(* inheritBelow (I.ctxLookup (B, n-k) - 1, k', V', (B', d-1, d')) *))
| (b_, k, Root (c_, s_), k', Root (c'_, s'_), Bdd') ->
    inheritSpine (b_, k, s_, k', s'_, Bdd') end(* C ~ C' *)
let rec inheritNewRoot =
  begin function
  | (b_, b, k, Root (BVar n, s_), k', (Root (BVar n', s'_) as v'_),
     (b'_, d, d')) ->
      ((if ((n' = k') + d') && (n' > k')
        then begin inheritBelow (b, k', v'_, (b'_, (d - 1), d')) end
      else begin inheritBelow ((b - 1), k', v'_, (b'_, (d - 1), d')) end)
  (* n' also new --- same variable: do not decrease *))
  | (b_, b, k, v_, k', v'_, (b'_, d, d')) ->
      inheritBelow ((b - 1), k', v'_, (b'_, (d - 1), d')) end(* n' not new --- decrease the splitting depth of all variables in V' *)
(* n = k+d *)
let rec inheritSpine =
  begin function
  | (b_, k, I.Nil, k', I.Nil, Bdd') -> Bdd'
  | (b_, k, App (u_, s_), k', App (u'_, s'_), Bdd') ->
      inheritSpine
        (b_, k, s_, k', s'_, (inheritExp (b_, k, u_, k', u'_, Bdd'))) end
let rec inheritDec (b_, k, Dec (_, v_), k', Dec (_, v'_), Bdd') =
  inheritExp (b_, k, v_, k', v'_, Bdd')
let rec inheritDTop =
  begin function
  | (b_, k, Pi ((Dec (_, v1_), I.No), v2_), k', Pi
     ((Dec (_, V1'), I.No), V2'), Bdd') ->
      inheritG
        (b_, k, v1_, k', V1',
          (inheritDTop (b_, (k + 1), v2_, (k' + 1), V2', Bdd')))
  | (b_, k, (Root (Const cid, s_) as v_), k',
     (Root (Const cid', s'_) as v'_), Bdd') ->
      let mS = valOf (ModeTable.modeLookup cid) in
      inheritSpineMode (M.Top, mS, b_, k, s_, k', s'_, Bdd') end(* cid = cid' *)
let rec inheritDBot =
  begin function
  | (b_, k, Pi ((Dec (_, v1_), I.No), v2_), k', Pi
     ((Dec (_, V1'), I.No), V2'), Bdd') ->
      inheritDBot (b_, (k + 1), v2_, (k' + 1), V2', Bdd')
  | (b_, k, Root (Const cid, s_), k', Root (Const cid', s'_), Bdd') ->
      let mS = valOf (ModeTable.modeLookup cid) in
      inheritSpineMode (M.Bot, mS, b_, k, s_, k', s'_, Bdd') end(* cid = cid' *)
let rec inheritG
  (b_, k, Root (Const cid, s_), k', (Root (Const cid', s'_) as v'_), Bdd') =
  let mS = valOf (ModeTable.modeLookup cid) in
  ((inheritSpineMode
      (M.Bot, mS, b_, k, s_, k', s'_,
        (inheritSpineMode (M.Top, mS, b_, k, s_, k', s'_, Bdd'))))
    (* mode dependency in Goal: first M.Top, then M.Bot *))
let rec inheritSpineMode =
  begin function
  | (mode, ModeSyn.Mnil, b_, k, I.Nil, k', I.Nil, Bdd') -> Bdd'
  | (mode, Mapp (m, mS), b_, k, App (u_, s_), k', App (u'_, s'_), Bdd') ->
      if modeEq (m, mode)
      then
        begin inheritSpineMode
                (mode, mS, b_, k, s_, k', s'_,
                  (inheritExp (b_, k, u_, k', u'_, Bdd'))) end
      else begin inheritSpineMode (mode, mS, b_, k, s_, k', s'_, Bdd') end end
let rec inheritSplitDepth
  ((State (_, Prefix (g_, m_, b_), v_) as s_),
   (State (name', Prefix (g'_, m'_, b'_), v'_) as s'_))
  =
  let d = I.ctxLength g_ in
  let d' = I.ctxLength g'_ in
  let v_ = Whnf.normalize (v_, I.id) in
  let v'_ = Whnf.normalize (v'_, I.id) in
  let (B'', 0, 0) =
    inheritDBot
      (b_, 0, v_, 0, v'_, (inheritDTop (b_, 0, v_, 0, v'_, (I.Null, d, d')))) in
  ((M.State (name', (M.Prefix (g'_, m'_, B'')), v'_))
    (* current first occurrence depth in V *)(* current first occurrence depth in V' *)
    (* mode dependency in Clause: first M.Top then M.Bot *)
    (* check proper traversal *))(* S' *)
let rec abstractInit (State (name, GM, v_))
  (name', Prefix (g'_, m'_, b'_), s') =
  inheritSplitDepth
    ((M.State (name, GM, v_)),
      (MetaAbstract.abstract
         (M.State
            ((name ^ name'), (M.Prefix (g'_, m'_, b'_)), (I.EClo (v_, s'))))))
let rec abstractCont ((d_, mode, b), abstract)
  (name', Prefix (g'_, m'_, b'_), s') =
  abstract
    (name',
      (M.Prefix
         ((I.Decl (g'_, (I.decSub (d_, s')))), (I.Decl (m'_, mode)),
           (I.Decl (b'_, b)))), (I.dot1 s'))
let rec makeAddressInit (s_) k = (s_, k)
let rec makeAddressCont makeAddress k = makeAddress (k + 1)
let rec expand' =
  begin function
  | (Prefix (I.Null, I.Null, I.Null), isIndex, abstract, makeAddress) ->
      ((M.Prefix (I.Null, I.Null, I.Null)), I.id, [])
  | (Prefix (Decl (g_, d_), Decl (m_, (M.Top as mode)), Decl (b_, b)),
     isIndex, abstract, makeAddress) ->
      let (Prefix (g'_, m'_, b'_), s', ops) =
        expand'
          ((M.Prefix (g_, m_, b_)), (isIndexSucc (d_, isIndex)),
            (abstractCont ((d_, mode, b), abstract)),
            (makeAddressCont makeAddress)) in
      let Dec (xOpt, v_) = d_ in
      let x_ = I.newEVar (g'_, (I.EClo (v_, s'))) in
      let ops' =
        if (((b > 0) && ((not (isIndex 1)) && (checkDec (m_, d_))))
          (* check if splitting bound > 0 *))
        then
          begin ((makeAddress 1),
                  (split ((M.Prefix (g'_, m'_, b'_)), (d_, s'), abstract)))
                  :: ops end
        else begin ops end in
      ((M.Prefix (g'_, m'_, b'_)), (I.Dot ((I.Exp x_), s')), ops')
  | (Prefix (Decl (g_, d_), Decl (m_, (M.Bot as mode)), Decl (b_, b)),
     isIndex, abstract, makeAddress) ->
      let (Prefix (g'_, m'_, b'_), s', ops) =
        expand'
          ((((M.Prefix (g_, m_, b_)), (isIndexSucc (d_, isIndex)),
              (abstractCont ((d_, mode, b), abstract)),
              (makeAddressCont makeAddress)))(* -###- *)) in
      ((((M.Prefix
            ((I.Decl (g'_, (I.decSub (d_, s')))), (I.Decl (m'_, M.Bot)),
              (I.Decl (b'_, b)))), (I.dot1 s'), ops))
        (* b = 0 *)) end
let rec expand (State (name, Prefix (g_, m_, b_), v_) as s_) =
  let (_, _, ops) =
    expand'
      ((M.Prefix (g_, m_, b_)), isIndexInit, (abstractInit s_),
        (makeAddressInit s_)) in
  ops
let rec index (_, Sl) = List.length Sl
let rec apply (_, Sl) =
  map
    (begin function
     | Active (s_) -> s_
     | InActive -> raise (Error "Not applicable: leftover constraints") end)
  Sl
let rec menu (((State (name, Prefix (g_, m_, b_), v_), i), Sl) as Op) =
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
let rec indexToString =
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
(((((^) "Splitting : " Print.decToString (g_, (I.ctxDec (g_, i)))) ^ " (") ^
    (indexToString (index Op)))
   ^ (flagToString ((active (Sl, 0)), (inactive (Sl, 0)))))
  ^ ")"
let rec var ((_, i), _) = i
let expand = expand
let apply = apply
let var = var
let index = index
let menu = menu end
