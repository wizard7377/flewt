module type COVER  =
  sig
    exception Error of string 
    val checkNoDef : IntSyn.cid -> unit
    val checkOut : (IntSyn.dctx * IntSyn.eclo) -> unit
    val checkCovers : (IntSyn.cid * ModeSyn.modeSpine_) -> unit
    val coverageCheckCases :
      (Tomega.worlds_ * (IntSyn.dctx * IntSyn.sub_) list * IntSyn.dctx) ->
        unit
  end


module Cover(Cover:sig
                     module Global : GLOBAL
                     module Whnf : WHNF
                     module Conv : CONV
                     module Abstract : ABSTRACT
                     module Unify : UNIFY
                     module Constraints : CONSTRAINTS
                     module ModeTable : MODETABLE
                     module UniqueTable : MODETABLE
                     module Index : INDEX
                     module Subordinate : SUBORDINATE
                     module WorldSyn : WORLDSYN
                     module Names : NAMES
                     module Print : PRINT
                     module TypeCheck : TYPECHECK
                     module Timers : TIMERS
                   end) : COVER =
  struct
    exception Error of string 
    module I = IntSyn
    module T = Tomega
    module M = ModeSyn
    module W = WorldSyn
    module P = Paths
    module F = Print.Formatter
    module N = Names
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
  let x'_ = Whnf.newLoweredEVar (g'_, (v_, iw)) in
  let x_ = I.EClo (x'_, w) in ((x_)
    (* G |- V : L *)(* G  |- w  : G'    *)
    (* G' |- iw : G     *)(* G' |- X' : V[iw] *)
    (* was I.newEvar (G', I.EClo (V, iw))  Mon Feb 28 14:30:36 2011 --cs *)
    (* G  |- X  : V     *))
type coverInst_ =
  | Match of coverInst_ 
  | Skip of coverInst_ 
  | Cnil 
let rec inCoverInst =
  begin function
  | M.Mnil -> Cnil
  | Mapp (Marg (M.Plus, x), ms') -> Match (inCoverInst ms')
  | Mapp (Marg (M.Minus, x), ms') -> Skip (inCoverInst ms')
  | Mapp (Marg (M.Star, x), ms') -> Skip (inCoverInst ms') end
let rec outCoverInst =
  begin function
  | M.Mnil -> Cnil
  | Mapp (Marg (M.Plus, x), ms') -> Skip (outCoverInst ms')
  | Mapp (Marg (M.Minus, x), ms') -> Match (outCoverInst ms') end
type caseLabel =
  | Top 
  | Child of (caseLabel * int) 
let rec labToString =
  begin function
  | Top -> "^"
  | Child (lab, n) -> (^) ((labToString lab) ^ ".") Int.toString n end
let rec chatter chlev f =
  if !Global.chatter >= chlev then begin print (f ()) end else begin () end
let rec pluralize = begin function | (1, s) -> s | (n, s) -> s ^ "s" end
let rec abbrevCSpine (s_, ci) = s_
let rec abbrevCGoal =
  begin function
  | (g_, v_, 0, ci) -> (g_, (abbrevCGoal' (g_, v_, ci)))
  | (g_, Pi ((d_, p_), v_), p, ci) ->
      let d'_ = N.decEName (g_, d_) in
      abbrevCGoal ((I.Decl (g_, d'_)), v_, (p - 1), ci) end(* p > 0 *)
let rec abbrevCGoal' =
  begin function
  | (g_, Pi ((d_, p_), v_), ci) ->
      let d'_ = N.decUName (g_, d_) in
      I.Pi ((d'_, p_), (abbrevCGoal' ((I.Decl (g_, d'_)), v_, ci)))
  | (g_, Root (a, s_), ci) -> I.Root (a, (abbrevCSpine (s_, ci))) end
let rec formatCGoal (v_, p, ci) =
  let _ = N.varReset I.Null in
  let (g_, v'_) = abbrevCGoal (I.Null, v_, p, ci) in
  F.HVbox
    [Print.formatCtx (I.Null, g_);
    F.Break;
    F.String "|-";
    F.Space;
    Print.formatExp (g_, v'_)]
let rec formatCGoals =
  begin function
  | ((v_, p)::[], ci) -> [formatCGoal (v_, p, ci)]
  | ((v_, p)::vs_, ci) ->
      (::) (((::) (formatCGoal (v_, p, ci)) F.String ",") :: F.Break)
        formatCGoals (vs_, ci) end
let rec missingToString (vs_, ci) =
  F.makestring_fmt
    (F.Hbox [F.Vbox0 0 1 (formatCGoals (vs_, ci)); F.String "."])
let rec showSplitVar (v_, p, k, ci) =
  let _ = N.varReset I.Null in
  let (g_, v'_) = abbrevCGoal (I.Null, v_, p, ci) in
  let Dec (Some x, _) = I.ctxLookup (g_, k) in
  (^) (("Split " ^ x) ^ " in ") Print.expToString (g_, v'_)
let rec showPendingGoal (v_, p, ci, lab) =
  F.makestring_fmt
    (F.Hbox
       [F.String (labToString lab);
       F.Space;
       F.String "?- ";
       formatCGoal (v_, p, ci);
       F.String "."])
let rec buildSpine =
  begin function
  | 0 -> I.Nil
  | n -> I.App ((I.Root ((I.BVar n), I.Nil)), (buildSpine (n - 1))) end
(* Eta-long invariant violation -kw *)(* n > 0 *)
let rec initCGoal' =
  begin function
  | (a, k, g_, Pi ((d_, p_), v_)) ->
      let d'_ = N.decEName (g_, d_) in
      let (v'_, p) = initCGoal' (a, (k + 1), (I.Decl (g_, d'_)), v_) in
      ((I.Pi ((d'_, I.Maybe), v'_)), p)
  | (a, k, g_, Uni (I.Type)) -> ((I.Root (a, (buildSpine k))), k) end
let rec initCGoal a = initCGoal' ((I.Const a), 0, I.Null, (I.constType a))
type coverClauses_ =
  | Input of I.exp_ list 
  | Output of (I.exp_ * int) 
type equation_ =
  | Eqn of (I.dctx * I.eclo * I.eclo) 
let rec equationToString (Eqn (g_, us1_, us2_)) =
  let g'_ = Names.ctxLUName g_ in
  let fmt =
    F.HVbox
      [Print.formatCtx (I.Null, g'_);
      F.Break;
      F.String "|-";
      F.Space;
      Print.formatExp (g'_, (I.EClo us1_));
      F.Break;
      F.String "=";
      F.Space;
      Print.formatExp (g'_, (I.EClo us2_))] in
  F.makestring_fmt fmt
let rec eqnsToString =
  begin function
  | [] -> ".\n"
  | eqn::eqns -> (^) ((equationToString eqn) ^ ",\n") eqnsToString eqns end
type candidates_ =
  | Eqns of equation_ list 
  | Cands of int list 
  | Fail 
let rec candsToString =
  begin function
  | Fail -> "Fail"
  | Cands ks ->
      (^) "Cands [" List.foldl
        ((begin function | (k, str) -> ((Int.toString k) ^ ",") ^ str end))
      "]" ks
  | Eqns eqns -> ((^) "Eqns [\n" eqnsToString eqns) ^ "]" end
let rec fail msg = begin chatter 7 (begin function | () -> msg ^ "\n" end);
  Fail end
let rec failAdd =
  begin function
  | (k, Eqns _) -> Cands (k :: [])
  | (k, Cands ks) -> Cands (k :: ks)
  | (k, Fail) -> Fail end(* remove duplicates? *)(* no longer matches *)
let rec addEqn =
  begin function
  | (e, Eqns es) -> Eqns (e :: es)
  | (e, (Cands ks as cands)) -> cands
  | (e, Fail) -> Fail end(* already failed: ignore new constraints *)
(* still may match: add equation *)
let rec unifiable (g_, us1_, us2_) = Unify.unifiable (g_, us1_, us2_)
let rec matchEqns =
  begin function
  | [] -> true
  | (Eqn (g_, us1_, ((u2_, s2) as us2_)))::es ->
      ((begin match Whnf.makePatSub s2 with
        | None -> unifiable (g_, us1_, us2_)
        | Some s2' -> unifiable (g_, us1_, (u2_, s2')) end)
      (* constraints will be left in this case *)) &&
      (matchEqns es) end(* was: unifiable (G, Us1, Us2) *)
(* Sat Dec  7 20:59:46 2002 -fp *)(* explicitly convert if possible *)
(* For some reason, s2 is sometimes not a patSub when it should be *)
let rec resolveCands =
  begin function
  | Eqns es -> if matchEqns (List.rev es) then begin Eqns [] end
      else begin Fail end
  | Cands ks -> Cands ks | Fail -> Fail end(* why is this important? --cs !!! *)
(* reversed equations Fri Dec 28 09:39:55 2001 -fp !!! *)
let rec collectConstraints =
  begin function
  | [] -> []
  | (EVar (_, _, _, { contents = [] }))::xs_ -> collectConstraints xs_
  | (EVar (_, _, _, { contents = constrs }))::xs_ ->
      (@) constrs collectConstraints xs_ end(* at present, do not simplify -fp *)
(* Constraints.simplify constrs @ *)(* constrs <> nil *)
let rec checkConstraints =
  begin function
  | (g_, qs_, Cands ks) -> Cands ks
  | (g_, qs_, Fail) -> Fail
  | (g_, qs_, Eqns _) ->
      let xs_ = Abstract.collectEVars (g_, qs_, []) in
      let constrs = collectConstraints xs_ in
      (((begin match constrs with | [] -> Eqns [] | _ -> Fail end))
        (* constraints remained: Fail without candidates *)) end
(* _ = nil *)
type candList_ =
  | Covered 
  | CandList of candidates_ list 
let rec addKs =
  begin function
  | ((Cands ks as ccs), CandList klist) -> CandList (ccs :: klist)
  | ((Eqns [] as ces), CandList klist) -> Covered
  | ((Fail as cfl), CandList klist) -> CandList (cfl :: klist) end
let rec matchExp (g_, d, us1_, us2_, cands) =
  matchExpW (g_, d, (Whnf.whnf us1_), (Whnf.whnf us2_), cands)
let rec matchExpW =
  begin function
  | (g_, d, ((Root (h1_, s1_), s1) as us1_), ((Root (h2_, s2_), s2) as us2_),
     cands) ->
      (((begin match (h1_, h2_) with
         | (BVar k1, BVar k2) ->
             if k1 = k2
             then begin matchSpine (g_, d, (s1_, s1), (s2_, s2), cands) end
             else begin ((if k1 > d then begin failAdd ((k1 - d), cands) end
               else begin fail "local variable / variable clash" end)
         (* k1 is coverage variable, new candidate *)) end
  | (Const c1, Const c2) ->
      if c1 = c2
      then begin matchSpine (g_, d, (s1_, s1), (s2_, s2), cands) end
      else begin fail "constant / constant clash" end
| (Def d1, Def d2) ->
    ((if d1 = d2
      then begin matchSpine (g_, d, (s1_, s1), (s2_, s2), cands) end
    else begin
      matchExpW (g_, d, (Whnf.expandDef us1_), (Whnf.expandDef us2_), cands) end)
(* because of strictness *))
| (Def d1, _) -> matchExpW (g_, d, (Whnf.expandDef us1_), us2_, cands)
| (_, Def d2) -> matchExpW (g_, d, us1_, (Whnf.expandDef us2_), cands)
| (BVar k1, Const _) -> ((if k1 > d then begin failAdd ((k1 - d), cands) end
    else begin fail "local variable / constant clash" end)
(* k1 is coverage variable, new candidate *))
| (Const _, BVar _) -> fail "constant / local variable clash"
| (Proj (Bidx k1, i1), Proj (Bidx k2, i2)) ->
    if (k1 = k2) && (i1 = i2)
    then begin matchSpine (g_, d, (s1_, s1), (s2_, s2), cands) end
    else begin fail "block index / block index clash" end
| (Proj (Bidx k1, i1), Proj (LVar (r2, Shift k2, (l2, t2)), i2)) ->
    let BDec (bOpt, (l1, t1)) = I.ctxDec (g_, k1) in
    if (l1 <> l2) || (i1 <> i2)
    then begin fail "block index / block variable clash" end
      else begin
        (let cands2 =
           matchSub (g_, d, t1, (I.comp (t2, (I.Shift k2))), cands) in
         let _ = Unify.instantiateLVar (r2, (I.Bidx (k1 - k2))) in
         ((matchSpine (g_, d, (s1_, s1), (s2_, s2), cands2))
           (* was: t2 in prev line, July 22, 2010 -fp -cs *)
           (* instantiate instead of postponing because LVars are *)
           (* only instantiated to Bidx which are rigid *)
           (* Sun Jan  5 12:03:13 2003 -fp *))) end
| (BVar k1, Proj _) -> ((if k1 > d then begin failAdd ((k1 - d), cands) end
    else begin fail "local variable / block projection clash" end)
(* k1 is splittable, new candidate *))
| (Const _, Proj _) -> fail "constant / block projection clash"
| (Proj _, Const _) -> fail "block projection / constant clash"
| (Proj _, BVar _) -> fail "block projection / local variable clash" end))
(* Note: I.Proj occurring here will always have the form
              I.Proj (I.Bidx (k), i) *)
(* No skolem constants, foreign constants, FVars *)(* otherwise fail with no candidates *)
(* fail with no candidates *)(* otherwise fail with no candidates *)
(* handled in above two cases now *)(*
            | (I.Proj (b1, i1), I.Proj (b2, i2)) =>
               if (i1 = i2) then
                 matchSpine (G, d, (S1, s1), (S2, s2),
                             matchBlock (G, d, b1, b2, cands))
               else fail ("block projection / block projection clash")
            *)
(* otherwise fail with no candidates *)(* no other cases should be possible *))
| (g_, d, (Lam (d1_, u1_), s1), (Lam (d2_, u2_), s2), cands) ->
    matchExp
      ((I.Decl (g_, (I.decSub (d1_, s1)))), (d + 1), (u1_, (I.dot1 s1)),
        (u2_, (I.dot1 s2)), cands)
| (g_, d, (Lam (d1_, u1_), s1), (u2_, s2), cands) ->
    matchExp
      ((I.Decl (g_, (I.decSub (d1_, s1)))), (d + 1), (u1_, (I.dot1 s1)),
        ((I.Redex
            ((I.EClo (u2_, I.shift)),
              (I.App ((I.Root ((I.BVar 1), I.Nil)), I.Nil)))), (I.dot1 s2)),
        cands)
| (g_, d, (u1_, s1), (Lam (d2_, u2_), s2), cands) ->
    matchExp
      ((I.Decl (g_, (I.decSub (d2_, s2)))), (d + 1),
        ((I.Redex
            ((I.EClo (u1_, I.shift)),
              (I.App ((I.Root ((I.BVar 1), I.Nil)), I.Nil)))), (I.dot1 s1)),
        (u2_, (I.dot1 s2)), cands)
| (g_, d, us1_, ((EVar _, s2) as us2_), cands) ->
    addEqn ((Eqn (g_, us1_, us2_)), cands) end(* eta-expand *)(* eta-expand *)
let rec matchSpine =
  begin function
  | (g_, d, (I.Nil, _), (I.Nil, _), cands) -> cands
  | (g_, d, (SClo (s1_, s1'), s1), ss2_, cands) ->
      matchSpine (g_, d, (s1_, (I.comp (s1', s1))), ss2_, cands)
  | (g_, d, ss1_, (SClo (s2_, s2'), s2), cands) ->
      matchSpine (g_, d, ss1_, (s2_, (I.comp (s2', s2))), cands)
  | (g_, d, (App (u1_, s1_), s1), (App (u2_, s2_), s2), cands) ->
      let cands' = matchExp (g_, d, (u1_, s1), (u2_, s2), cands) in
      matchSpine (g_, d, (s1_, s1), (s2_, s2), cands') end
let rec matchDec (g_, d, (Dec (_, v1_), s1), (Dec (_, v2_), s2), cands) =
  matchExp (g_, d, (v1_, s1), (v2_, s2), cands)
let rec matchSub =
  begin function
  | (g_, d, Shift n1, Shift n2, cands) -> cands
  | (g_, d, Shift n, (Dot _ as s2), cands) ->
      matchSub
        (g_, d, (I.Dot ((I.Idx (n + 1)), (I.Shift (n + 1)))), s2, cands)
  | (g_, d, (Dot _ as s1), Shift m, cands) ->
      matchSub
        (g_, d, s1, (I.Dot ((I.Idx (m + 1)), (I.Shift (m + 1)))), cands)
  | (g_, d, Dot (Ft1, s1), Dot (Ft2, s2), cands) ->
      let cands1 =
        begin match (Ft1, Ft2) with
        | (Idx n1, Idx n2) -> if n1 = n2 then begin cands end
            else begin if n1 > d then begin failAdd ((n1 - d), cands) end
              else begin
                fail
                  "local variable / local variable clash in block instance" end end
  | (Exp (u1_), Exp (u2_)) ->
      matchExp (g_, d, (u1_, I.id), (u2_, I.id), cands)
  | (Exp (u1_), Idx n2) ->
      matchExp
        (g_, d, (u1_, I.id), ((I.Root ((I.BVar n2), I.Nil)), I.id), cands)
  | (Idx n1, Exp (u2_)) ->
      matchExp
        (g_, d, ((I.Root ((I.BVar n1), I.Nil)), I.id), (u2_, I.id), cands) end in
matchSub (g_, d, s1, s2, cands1) end(* by invariant *)
let rec matchTop (g_, d, us1_, us2_, ci, cands) =
  matchTopW (g_, d, (Whnf.whnf us1_), (Whnf.whnf us2_), ci, cands)
let rec matchTopW =
  begin function
  | (g_, d, (Root (Const c1, s1_), s1), (Root (Const c2, s2_), s2), ci,
     cands) ->
      ((if c1 = c2
        then begin matchTopSpine (g_, d, (s1_, s1), (s2_, s2), ci, cands) end
      else begin fail "type family clash" end)
  (* unify spines, skipping output and ignore arguments in modeSpine *))
  | (g_, d, (Pi ((d1_, _), v1_), s1), (Pi ((d2_, _), v2_), s2), ci, cands) ->
      matchTopW
        ((I.Decl (g_, d1_)), (d + 1), (v1_, (I.dot1 s1)), (v2_, (I.dot1 s2)),
          ci, cands) end(* Sat Dec 22 23:53:44 2001 -fp !!! *)(* and no splittable variables should be suggested here *)
(* we do not match D1 and D2, since D1 is always an instance of D2 *)
(* this case can only arise in output coverage *)(* fails, with no candidates since type families don't match *)
let rec matchTopSpine =
  begin function
  | (g_, d, (I.Nil, _), (I.Nil, _), Cnil, cands) -> cands
  | (g_, d, (SClo (s1_, s1'), s1), ss2_, ci, cands) ->
      matchTopSpine (g_, d, (s1_, (I.comp (s1', s1))), ss2_, ci, cands)
  | (g_, d, ss1_, (SClo (s2_, s2'), s2), ci, cands) ->
      matchTopSpine (g_, d, ss1_, (s2_, (I.comp (s2', s2))), ci, cands)
  | (g_, d, (App (u1_, s1_), s1), (App (u2_, s2_), s2), Match ci', cands) ->
      let cands' = matchExp (g_, d, (u1_, s1), (u2_, s2), cands) in
      matchTopSpine (g_, d, (s1_, s1), (s2_, s2), ci', cands')
  | (g_, d, (App (u1_, s1_), s1), (App (u2_, s2_), s2), Skip ci', cands) ->
      matchTopSpine (g_, d, (s1_, s1), (s2_, s2), ci', cands) end(* an argument that need not be covered (Skip) *)
(* an argument that must be covered (Match) *)
let rec matchClause =
  begin function
  | (g_, ps', ((Root (_, _), s) as qs), ci) ->
      checkConstraints
        (g_, qs, (resolveCands (matchTop (g_, 0, ps', qs, ci, (Eqns [])))))
  | (g_, ps', (Pi ((Dec (_, v1_), _), v2_), s), ci) ->
      let x1_ = Whnf.newLoweredEVar (g_, (v1_, s)) in
      ((matchClause (g_, ps', (v2_, (I.Dot ((I.Exp x1_), s))), ci))
        (* changed to use subordination and strengthening here *)
        (* Sun Dec 16 10:39:34 2001 -fp *)(* val X1 = createEVar (G, I.EClo (V1, s)) *)
        (* changed back --- no effect *)(* was val X1 = I.newEVar (G, I.EClo (V1, s)) Mon Feb 28 14:37:22 2011 -cs *)
        (* was: I.Null instead of G in line above Wed Nov 21 16:40:40 2001 *)) end
let rec matchSig =
  begin function
  | (g_, ps', [], ci, klist) -> klist
  | (g_, ps', (v_)::ccs', ci, klist) ->
      let cands =
        CSManager.trail
          (begin function | () -> matchClause (g_, ps', (v_, I.id), ci) end) in
    matchSig' (g_, ps', ccs', ci, (addKs (cands, klist))) end
let rec matchSig' =
  begin function
  | (g_, ps', ccs, ci, Covered) -> Covered
  | (g_, ps', ccs, ci, CandList klist) ->
      matchSig (g_, ps', ccs, ci, (CandList klist)) end(* not yet covered: continue to search *)
(* already covered: return *)
let rec matchBlocks =
  begin function
  | (g_, s', [], v_, k, i, ci, klist) -> klist
  | (g_, s', (Dec (_, v'_))::piDecs, v_, k, i, ci, klist) ->
      let cands =
        CSManager.trail
          (begin function | () -> matchClause (g_, (v_, I.id), (v'_, s'), ci) end) in
    let s'' = I.Dot ((I.Exp (I.Root ((I.Proj ((I.Bidx k), i)), I.Nil))), s') in
    matchBlocks'
      (g_, s'', piDecs, v_, k, (i + 1), ci, (addKs (cands, klist))) end
let rec matchBlocks' =
  begin function
  | (g_, s', piDecs, v_, k, i, ci, Covered) -> Covered
  | (g_, s', piDecs, v_, k, i, ci, klist) ->
      matchBlocks (g_, s', piDecs, v_, k, i, ci, klist) end
let rec matchCtx =
  begin function
  | (g_, s', I.Null, v_, k, ci, klist) -> klist
  | (g_, s', Decl (G'', Dec (_, v'_)), v_, k, ci, klist) ->
      let s'' = I.comp (I.shift, s') in
      let cands =
        CSManager.trail
          (begin function
           | () -> matchClause (g_, (v_, I.id), (v'_, s''), ci) end) in
      ((matchCtx' (g_, s'', G'', v_, (k + 1), ci, (addKs (cands, klist))))
        (*  G'', V' |- ^ : G''
              G |- s' : G'', V'
          *)
        (*  G |- ^ o s' : G'' *))
  | (g_, s', Decl (G'', BDec (_, (cid, s))), v_, k, ci, klist) ->
      let (Gsome, piDecs) = I.constBlock cid in
      let s'' = I.comp (I.shift, s') in
      let klist' =
        matchBlocks (g_, (I.comp (s, s'')), piDecs, v_, k, 1, ci, klist) in
      ((matchCtx' (g_, s'', G'', v_, (k + 1), ci, klist'))
        (* G'' |- s : Gsome,
             G |- s'' : G''
             G |- s o s'' : Gsome
             Gsome |- piDecs : ctx
          *)) end
(* will always fail for input coverage *)
let rec matchCtx' =
  begin function
  | (g_, s', g'_, v_, k, ci, Covered) -> Covered
  | (g_, s', g'_, v_, k, ci, CandList klist) ->
      matchCtx (g_, s', g'_, v_, k, ci, (CandList klist)) end
let rec matchOut =
  begin function
  | (g_, v_, ci, (v'_, s'), 0) ->
      let cands = matchTop (g_, 0, (v_, I.id), (v'_, s'), ci, (Eqns [])) in
      let cands' = resolveCands cands in
      let cands'' = checkConstraints (g_, (v'_, s'), cands') in
      addKs (cands'', (CandList []))
  | (g_, v_, ci, ((Pi ((Dec (_, V1'), _), V2') as v'_), s'), p) ->
      let x1_ = Whnf.newLoweredEVar (g_, (V1', s')) in
      ((matchOut (g_, v_, ci, (V2', (I.Dot ((I.Exp x1_), s'))), (p - 1)))
        (* was val X1 = I.newEVar (G, I.EClo (V1', s')) Mon Feb 28 14:38:21 2011 -cs *)) end
(* p > 0 *)
let rec match_ =
  begin function
  | (g_, (Root (Const a, s_) as v_), 0, ci, Input ccs) ->
      matchCtx'
        (g_, I.id, g_, v_, 1, ci,
          (matchSig (g_, (v_, I.id), ccs, ci, (CandList []))))
  | (g_, v_, 0, ci, Output (v'_, q)) ->
      matchOut (g_, v_, ci, (v'_, (I.Shift (I.ctxLength g_))), q)
  | (g_, Pi ((d_, _), v'_), p, ci, ccs) ->
      match_ ((I.Decl (g_, d_)), v'_, (p - 1), ci, ccs) end
let rec insert =
  begin function
  | (k, []) -> (k, 1) :: []
  | (k, ((k', n')::ksn' as ksn)) ->
      (begin match Int.compare (k, k') with
       | LESS -> (k, 1) :: ksn
       | EQUAL -> (k', (n' + 1)) :: ksn'
       | GREATER -> (::) (k', n') insert (k, ksn') end) end
let rec join =
  begin function
  | ([], ksn) -> ksn
  | (k::ks, ksn) -> join (ks, (insert (k, ksn))) end
let rec selectCand =
  begin function
  | Covered -> None
  | CandList klist -> selectCand' (klist, []) end(* success: case is covered! *)
let rec selectCand' =
  begin function
  | ([], ksn) -> Some ksn
  | ((Fail)::klist, ksn) -> selectCand' (klist, ksn)
  | ((Cands [])::klist, ksn) -> selectCand' (klist, ksn)
  | ((Cands ks)::klist, ksn) -> selectCand' (klist, (join (ks, ksn))) end
(* found candidates ks <> nil *)(* local failure but no candidates *)
(* local failure (clash) and no candidates *)(* failure: case G,V is not covered! *)
let rec instEVars (vs_, p, XsRev) = instEVarsW ((Whnf.whnf vs_), p, XsRev)
let rec instEVarsW =
  begin function
  | (vs_, 0, XsRev) -> (vs_, XsRev)
  | ((Pi ((Dec (xOpt, v1_), _), v2_), s), p, XsRev) ->
      let x1_ = Whnf.newLoweredEVar (I.Null, (v1_, s)) in
      ((instEVars
          ((v2_, (I.Dot ((I.Exp x1_), s))), (p - 1), ((Some x1_) :: XsRev)))
        (* p > 0 *)(* all EVars are global *)(* was  val X1 = I.newEVar (I.Null, I.EClo (V1, s))  all EVars are global *))
  | ((Pi ((BDec (_, (l, t)), _), v2_), s), p, XsRev) ->
      let l1_ = I.newLVar ((I.Shift 0), (l, (I.comp (t, s)))) in
      ((instEVars
          ((v2_, (I.Dot ((I.Block l1_), s))), (p - 1), (None :: XsRev)))
        (* p > 0 *)(* new -fp Sun Dec  1 20:58:06 2002 *)
        (* new -cs  Sun Dec  1 06:27:57 2002 *)) end
(* . |- s : G0 *)(* G0 |- t : Gsome *)
let (caseList : (I.exp_ * int) list ref) = ref []
let rec resetCases () = caseList := []
let rec addCase (v_, p) = (!) ((::) (caseList := (v_, p))) caseList
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
      let x_ = Whnf.newLoweredEVar (I.Null, (v_, s)) in
      ((I.Dot ((I.Exp x_), s))
        (* was   val V' = I.EClo (V, s)
                   val X = I.newEVar (I.Null, V') Mon Feb 28 15:32:09 2011 --cs *)) end
let rec blockName cid = I.conDecName (I.sgnLookup cid)
let rec blockCases (g_, vs_, cid, (Gsome, piDecs), sc) =
  let t = createEVarSub Gsome in
  let sk = I.Shift (I.ctxLength g_) in
  let t' = I.comp (t, sk) in
  let lvar = I.newLVar (sk, (cid, t)) in
  ((blockCases' (g_, vs_, (lvar, 1), (t', piDecs), sc))
    (* . |- t : Gsome *)(* was: the above, using t' for t below *)
    (*  BUG. Breach in the invariant:
                         G |- sk : .
                         . |- t: Gsome
                         G <> .

                         replace t by t' in I.newLVar (sk, (cid, t))
                      --cs Fri Jan  3 11:07:41 2003 *)
    (* G |- t' : Gsome *))
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
let rec lowerSplitW =
  begin function
  | ((EVar (_, g_, v_, _) as x_), w_, sc) ->
      let sc' =
        begin function
        | u_ ->
            if Unify.unifiable (g_, (x_, I.id), (u_, I.id))
            then begin sc () end else begin () end end in
let _ = paramCases (g_, (v_, I.id), (I.ctxLength g_), sc') in
let _ = worldCases (g_, (v_, I.id), w_, sc') in
let _ = constCases (g_, (v_, I.id), (Index.lookup (I.targetFam v_)), sc') in
((())
  (* will trail *)(* will trail *)(* will trail *))
| (Lam (d_, u_), w_, sc) -> lowerSplitW (u_, w_, sc) end
let rec splitEVar (x_, w_, sc) = lowerSplitW (x_, w_, sc)
let rec abstract (v_, s) =
  let (i, v'_) = Abstract.abstractDecImp (I.EClo (v_, s)) in
  let _ =
    if !Global.doubleCheck
    then begin TypeCheck.typeCheck (I.Null, (v'_, (I.Uni I.Type))) end
    else begin () end in
(v'_, i)
let rec splitVar (v_, p, k, (w_, ci)) =
  ((begin try
            let _ =
              chatter 6
                (begin function | () -> (showSplitVar (v_, p, k, ci)) ^ "\n" end) in
          let ((v1_, s), XsRev) = instEVars ((v_, I.id), p, []) in
          let Some (x_) = List.nth (XsRev, (k - 1)) in
          let _ = resetCases () in
          let _ =
            splitEVar
              (x_, w_,
                (begin function | () -> addCase (abstract (v1_, s)) end)) in
          ((Some (getCases ()))
            (* split on k'th variable, counting from innermost *)
            (* may raise Constraints.Error *))
  with
  | Error constrs ->
      (begin chatter 7
               (begin function
                | () ->
                    ((^) "Inactive split:\n" Print.cnstrsToString constrs) ^
                      "\n" end);
      None end) end)
(* Constraints.Error could be raised by abstract *))
let rec occursInExp =
  begin function
  | (k, Uni _) -> false
  | (k, Pi (DP, v_)) -> (occursInDecP (k, DP)) || (occursInExp ((k + 1), v_))
  | (k, Root (h_, s_)) -> (occursInHead (k, h_)) || (occursInSpine (k, s_))
  | (k, Lam (d_, v_)) -> (occursInDec (k, d_)) || (occursInExp ((k + 1), v_))
  | (k, FgnExp (cs, ops)) -> false end
let rec occursInHead =
  begin function | (k, BVar k') -> k = k' | (k, _) -> false end
let rec occursInSpine =
  begin function
  | (_, I.Nil) -> false
  | (k, App (u_, s_)) -> (occursInExp (k, u_)) || (occursInSpine (k, s_)) end
let rec occursInDec (k, Dec (_, v_)) = occursInExp (k, v_)
let rec occursInDecP (k, (d_, _)) = occursInDec (k, d_)
let rec occursInMatchPos =
  begin function
  | (k, Pi (DP, v_), ci) -> occursInMatchPos ((k + 1), v_, ci)
  | (k, Root (h_, s_), ci) -> occursInMatchPosSpine (k, s_, ci) end
let rec occursInMatchPosSpine =
  begin function
  | (k, I.Nil, Cnil) -> false
  | (k, App (u_, s_), Match ci) ->
      (occursInExp (k, u_)) || (occursInMatchPosSpine (k, s_, ci))
  | (k, App (u_, s_), Skip ci) -> occursInMatchPosSpine (k, s_, ci) end
let rec instEVarsSkip (vs_, p, XsRev, ci) =
  InstEVarsSkipW ((Whnf.whnf vs_), p, XsRev, ci)
let rec InstEVarsSkipW =
  begin function
  | (vs_, 0, XsRev, ci) -> (vs_, XsRev)
  | ((Pi ((Dec (xOpt, v1_), _), v2_), s), p, XsRev, ci) ->
      let x1_ = Whnf.newLoweredEVar (I.Null, (v1_, s)) in
      let EVarOpt = if occursInMatchPos (1, v2_, ci) then begin Some x1_ end
        else begin None end in
    ((instEVarsSkip
        ((v2_, (I.Dot ((I.Exp x1_), s))), (p - 1), (EVarOpt :: XsRev), ci))
      (* p > 0 *)(* all EVars are global *)
      (* was val X1 = I.newEVar (I.Null, I.EClo (V1, s))  all EVars are global *))
  | ((Pi ((BDec (_, (l, t)), _), v2_), s), p, XsRev, ci) ->
      let l1_ = I.newLVar ((I.Shift 0), (l, (I.comp (t, s)))) in
      ((instEVarsSkip
          ((v2_, (I.Dot ((I.Block l1_), s))), (p - 1), (None :: XsRev), ci))
        (* p > 0 *)(* -fp Sun Dec  1 21:09:38 2002 *)
        (* -cs Sun Dec  1 06:30:59 2002 *)) end(* . |- s : G0 *)
(* G0 |- t : Gsome *)
let rec targetBelowEq =
  begin function
  | (a, EVar ({ contents = None }, GY, VY, { contents = [] })) ->
      Subordinate.belowEq (a, (I.targetFam VY))
  | (a, EVar ({ contents = None }, GY, VY, { contents = _::_ })) -> true end
(* if contraints remain, consider recursive and thereby unsplittable *)
let rec recursive =
  begin function
  | EVar ({ contents = Some (u_) }, GX, VX, _) as x_ ->
      let a = I.targetFam VX in
      let ys_ = Abstract.collectEVars (GX, (x_, I.id), []) in
      let recp =
        List.exists (begin function | y_ -> targetBelowEq (a, y_) end) ys_ in
      ((recp)
        (* GX = I.Null*)(* is this always true? --cs!!!*)
        (* LVars are ignored here.  OK because never splittable? *)
        (* Sat Dec 15 22:42:10 2001 -fp !!! *))
  | Lam (d_, u_) -> recursive u_ end
let counter = ref 0
let rec resetCount () = counter := 0
let rec incCount () = ((!) ((:=) counter) counter) + 1
let rec getCount () = !counter
exception NotFinitary 
let rec finitary1 (x_, k, w_, f, cands) =
  begin resetCount ();
  chatter 7
    (begin function
     | () -> (((^) "Trying " Print.expToString (I.Null, x_)) ^ " : ") ^ ".\n" end);
  (begin try
           begin splitEVar
                   (x_, w_,
                     (begin function
                      | () ->
                          (begin f ();
                           if recursive x_ then begin raise NotFinitary end
                           else begin incCount () end end) end));
  chatter 7
    (begin function
     | () ->
         ((^) "Finitary with " Int.toString (getCount ())) ^ " candidates.\n" end);
(k, (getCount ())) :: cands end
with
| NotFinitary ->
    (begin chatter 7 (begin function | () -> "Not finitary.\n" end); cands end)
| Error constrs ->
    (begin chatter 7 (begin function | () -> "Inactive finitary split.\n" end);
    cands end) end) end
let rec finitarySplits =
  begin function
  | ([], k, w_, f, cands) -> cands
  | ((None)::xs_, k, w_, f, cands) ->
      finitarySplits (xs_, (k + 1), w_, f, cands)
  | ((Some (x_))::xs_, k, w_, f, cands) ->
      finitarySplits
        (xs_, (k + 1), w_, f,
          (CSManager.trail
             (begin function | () -> finitary1 (x_, k, w_, f, cands) end))) end
(* parameter blocks can never be split *)
let rec finitary (v_, p, w_, ci) =
  let _ =
    if !Global.doubleCheck
    then begin TypeCheck.typeCheck (I.Null, (v_, (I.Uni I.Type))) end
    else begin () end in
let ((v1_, s), XsRev) = instEVarsSkip ((v_, I.id), p, [], ci) in
finitarySplits (XsRev, 1, w_, (begin function | () -> abstract (v1_, s) end),
  [])
let rec eqExp (us_, us'_) = Conv.conv (us_, us'_)
let rec eqInpSpine =
  begin function
  | (ms, (SClo (s1_, s1'), s1), ss2_) ->
      eqInpSpine (ms, (s1_, (I.comp (s1', s1))), ss2_)
  | (ms, ss1_, (SClo (s2_, s2'), s2)) ->
      eqInpSpine (ms, ss1_, (s2_, (I.comp (s2', s2))))
  | (M.Mnil, (I.Nil, s), (I.Nil, s')) -> true
  | (Mapp (Marg (M.Plus, _), ms'), (App (u_, s_), s), (App (u'_, s'_), s'))
      ->
      (eqExp ((u_, s), (u'_, s'))) && (eqInpSpine (ms', (s_, s), (s'_, s')))
  | (Mapp (_, ms'), (App (u_, s_), s), (App (u'_, s'_), s')) ->
      eqInpSpine (ms', (s_, s), (s'_, s')) end(* ignore Star, Minus, Minus1 *)
let rec eqInp =
  begin function
  | (I.Null, k, a, ss_, ms) -> []
  | (Decl (g'_, Dec (_, Root (Const a', s'_))), k, a, ss_, ms) ->
      if (a = a') && (eqInpSpine (ms, (s'_, (I.Shift k)), ss_))
      then begin (::) k eqInp (g'_, (k + 1), a, ss_, ms) end
      else begin eqInp (g'_, (k + 1), a, ss_, ms) end
  | (Decl (g'_, Dec (_, Pi _)), k, a, ss_, ms) ->
      eqInp (g'_, (k + 1), a, ss_, ms)
  | (Decl (g'_, NDec _), k, a, ss_, ms) -> eqInp (g'_, (k + 1), a, ss_, ms)
  | (Decl (g'_, BDec (_, (b, t))), k, a, ss_, ms) ->
      eqInp (g'_, (k + 1), a, ss_, ms) end(* defined type families disallowed here *)
let rec contractionCands =
  begin function
  | (I.Null, k) -> []
  | (Decl (g'_, Dec (_, Root (Const a, s_))), k) ->
      (begin match UniqueTable.modeLookup a with
       | None -> contractionCands (g'_, (k + 1))
       | Some ms ->
           (begin match eqInp (g'_, (k + 1), a, (s_, (I.Shift k)), ms) with
            | [] -> contractionCands (g'_, (k + 1))
            | ns -> (::) (k :: ns) contractionCands (g'_, (k + 1)) end) end)
  | (Decl (g'_, Dec (_, Pi _)), k) -> contractionCands (g'_, (k + 1))
  | (Decl (g'_, NDec _), k) -> contractionCands (g'_, (k + 1))
  | (Decl (g'_, BDec (_, (b, t))), k) -> contractionCands (g'_, (k + 1)) end
(* ignore blocks --- contraction cands unclear *)(* ignore Pi --- contraction cands unclear *)
(* using only one uniqueness declaration per type family *)
(* defined type families disallowed here *)
let rec isolateSplittable =
  begin function
  | (g_, v_, 0) -> (g_, v_)
  | (g_, Pi ((d_, _), v'_), p) ->
      isolateSplittable ((I.Decl (g_, d_)), v'_, (p - 1)) end
let rec unifyUOutSpine =
  begin function
  | (ms, (SClo (s1_, s1'), s1), ss2_) ->
      unifyUOutSpine (ms, (s1_, (I.comp (s1', s1))), ss2_)
  | (ms, ss1_, (SClo (s2_, s2'), s2)) ->
      unifyUOutSpine (ms, ss1_, (s2_, (I.comp (s2', s2))))
  | (M.Mnil, (I.Nil, s1), (I.Nil, s2)) -> true
  | (Mapp (Marg (M.Minus1, _), ms'), (App (u1_, s1_), s1),
     (App (u2_, s2_), s2)) ->
      (((Unify.unifiable (I.Null, (u1_, s1), (u2_, s2))) &&
          (unifyUOutSpine (ms', (s1_, s1), (s2_, s2))))
      (* will have effect! *))
  | (Mapp (_, ms'), (App (u1_, s1_), s1), (App (u2_, s2_), s2)) ->
      unifyUOutSpine (ms', (s1_, s1), (s2_, s2)) end(* if mode = + already equal by invariant; otherwise ignore *)
let rec unifyUOutType (v1_, v2_) =
  unifyUOutTypeW ((Whnf.whnf (v1_, I.id)), (Whnf.whnf (v2_, I.id)))
let rec unifyUOutTypeW
  ((Root (Const a1, s1_), s1), (Root (Const a2, s2_), s2)) =
  let Some ms = UniqueTable.modeLookup a1 in
  ((unifyUOutSpine (ms, (s1_, s1), (s2_, s2)))
    (* must succeed by invariant *))(* a1 = a2 by invariant *)
let rec unifyUOutEVars
  (Some (EVar (_, g1_, v1_, _)), Some (EVar (_, g2_, v2_, _))) =
  unifyUOutType (v1_, v2_)(* G1 = G2 = Null *)
let rec unifyUOut2 (XsRev, k1, k2) =
  unifyUOutEVars ((List.nth (XsRev, (k1 - 1))), (List.nth (XsRev, (k2 - 1))))
let rec unifyUOut1 =
  begin function
  | (XsRev, []) -> true
  | (XsRev, k1::[]) -> true
  | (XsRev, k1::k2::ks) ->
      (unifyUOut2 (XsRev, k1, k2)) && (unifyUOut1 (XsRev, (k2 :: ks))) end
let rec unifyUOut =
  begin function
  | (XsRev, []) -> true
  | (XsRev, ks::kss) -> (unifyUOut1 (XsRev, ks)) && (unifyUOut (XsRev, kss)) end
let rec contractAll (v_, p, ucands) =
  let ((v1_, s), XsRev) = instEVars ((v_, I.id), p, []) in
  ((if unifyUOut (XsRev, ucands) then begin Some (abstract (v1_, s)) end
    else begin None end)
  (* as in splitVar, may raise Constraints.Error *)(* as in splitVar *)
  (* unique outputs not simultaneously unifiable *))
let rec contract (v_, p, ci, lab) =
  let (g_, _) = isolateSplittable (I.Null, v_, p) in
  let ucands = contractionCands (g_, 1) in
  let n = List.length ucands in
  let _ =
    if n > 0
    then
      begin chatter 6
              (begin function
               | () ->
                   ((^) (((^) "Found " Int.toString n) ^ " contraction ")
                      pluralize (n, "candidate"))
                     ^ "\n" end) end
    else begin () end in
  let VpOpt' =
    ((if n > 0
      then
        begin begin try contractAll (v_, p, ucands)
              with
              | Error _ ->
                  (begin chatter 6
                           (begin function
                            | () -> "Contraction failed due to constraints\n" end);
                  Some (v_, p) end) end end
  else begin Some (v_, p) end)
(* no progress if constraints remain *)) in
let _ =
begin match VpOpt' with
| None ->
    chatter 6
      (begin function | () -> "Case impossible: conflicting unique outputs\n" end)
| Some (v'_, p') ->
    chatter 6
      (begin function | () -> (showPendingGoal (v'_, p', ci, lab)) ^ "\n" end) end in
((VpOpt')
(* ignore body of coverage goal *)(* no candidates, no progress *))
let rec findMin ((k, n)::kns) = findMin' ((k, n), kns)
let rec findMin' =
  begin function
  | ((k0, n0), []) -> (k0, n0)
  | ((k0, n0), (k', n')::kns) ->
      if n' < n0 then begin findMin' ((k', n'), kns) end
      else begin findMin' ((k0, n0), kns) end end
let rec cover (v_, p, ((w_, ci) as wci), ccs, lab, missing) =
  begin chatter 6
          (begin function | () -> (showPendingGoal (v_, p, ci, lab)) ^ "\n" end);
  cover' ((contract (v_, p, ci, lab)), wci, ccs, lab, missing) end
let rec cover' =
  begin function
  | (Some (v_, p), ((w_, ci) as wci), ccs, lab, missing) ->
      split
        (v_, p, (selectCand (match_ (I.Null, v_, p, ci, ccs))), wci, ccs,
          lab, missing)
  | (None, wci, ccs, lab, missing) ->
      (begin chatter 6 (begin function | () -> "Covered\n" end); missing end) end
(* V is covered by unique output inconsistency *)
let rec split =
  begin function
  | (v_, p, None, wci, ccs, lab, missing) ->
      (begin chatter 6 (begin function | () -> "Covered\n" end); missing end)
  | (v_, p, Some [], ((w_, ci) as wci), ccs, lab, missing) ->
      (begin chatter 6
               (begin function
                | () ->
                    "No strong candidates---calculating weak candidates\n" end);
      splitWeak (v_, p, (finitary (v_, p, w_, ci)), wci, ccs, lab, missing) end)
| (v_, p, Some ((k, _)::ksn), ((w_, ci) as wci), ccs, lab, missing) ->
    (((begin match splitVar (v_, p, k, wci) with
       | Some cases -> covers (cases, wci, ccs, lab, missing)
       | None -> split (v_, p, (Some ksn), wci, ccs, lab, missing) end))
(* splitting variable k generated constraints *)) end
(* splitVar shows splitting as it happens *)(* candidates are in reverse order, so non-index candidates are split first *)
(* some candidates: split first candidate, ignoring multiplicities *)
(* no strong candidates: check for finitary splitting candidates *)
(* V is covered: return missing patterns from other cases *)
let rec splitWeak =
  begin function
  | (v_, p, [], wci, ccs, lab, missing) ->
      (begin chatter 6
               (begin function
                | () ->
                    ((^) "No weak candidates---case " labToString lab) ^
                      " not covered\n" end);
      (v_, p) :: missing end)
  | (v_, p, ksn, wci, ccs, lab, missing) ->
      split (v_, p, (Some ((findMin ksn) :: [])), wci, ccs, lab, missing) end
(* commit to the minimal candidate, since no constraints can arise *)
(* ksn <> nil *)
let rec covers (cases, wci, ccs, lab, missing) =
  begin chatter 6
          (begin function
           | () ->
               ((^) ((^) "Found " Int.toString (List.length cases)) pluralize
                  ((List.length cases), " case"))
                 ^ "\n" end);
  covers' (cases, 1, wci, ccs, lab, missing) end
let rec covers' =
  begin function
  | ([], n, wci, ccs, lab, missing) ->
      (begin chatter 6
               (begin function
                | () ->
                    ((^) "All subcases of " labToString lab) ^
                      " considered\n" end);
      missing end)
  | ((v_, p)::cases', n, wci, ccs, lab, missing) ->
      covers'
        (cases', (n + 1), wci, ccs, lab,
          (cover (v_, p, wci, ccs, (Child (lab, n)), missing))) end
let rec constsToTypes =
  begin function
  | [] -> []
  | (Const c)::cs' -> (::) (I.constType c) constsToTypes cs'
  | (Def d)::cs' -> (::) (I.constType d) constsToTypes cs' end
let rec createCoverClause =
  begin function
  | (Decl (g_, d_), v_, p) ->
      createCoverClause (g_, (I.Pi ((d_, I.Maybe), v_)), (p + 1))
  | (I.Null, v_, p) -> ((Whnf.normalize (v_, I.id)), p) end
let rec createCoverGoal (g_, vs_, p, ms) =
  createCoverGoalW (g_, (Whnf.whnf vs_), p, ms)
let rec createCoverGoalW =
  begin function
  | (g_, (Pi ((d1_, p1_), v2_), s), 0, ms) ->
      let D1' = I.decSub (d1_, s) in
      let V2' =
        createCoverGoal ((I.Decl (g_, D1')), (v2_, (I.dot1 s)), 0, ms) in
      I.Pi ((D1', p1_), V2')
  | (g_, (Pi (((Dec (_, v1_) as d_), _), v2_), s), p, ms) ->
      let x_ = Whnf.newLoweredEVar (g_, (v1_, s)) in
      ((createCoverGoal (g_, (v2_, (I.Dot ((I.Exp x_), s))), (p - 1), ms))
        (* p > 0, G = I.Null *)(* was  val X = I.newEVar (G, I.EClo (V1, s))  Mon Feb 28 15:33:52 2011 -cs *))
  | (g_, (Root ((Const cid as a), s_), s), p, ms) ->
      I.Root
        (a, (createCoverSpine (g_, (s_, s), ((I.constType cid), I.id), ms))) end
(* s = id, p >= 0 *)
let rec createCoverSpine =
  begin function
  | (g_, (I.Nil, s), _, M.Mnil) -> I.Nil
  | (g_, (App (u1_, s2_), s), (Pi ((Dec (_, v1_), _), v2_), s'), Mapp
     (Marg (M.Minus, x), ms')) ->
      let x_ = createEVar (g_, (I.EClo (v1_, s'))) in
      let S2' =
        createCoverSpine (g_, (s2_, s), (v2_, (I.Dot ((I.Exp x_), s'))), ms') in
      ((I.App (x_, S2'))
        (* strengthen G based on subordination *))
  | (g_, (App (u1_, s2_), s), (Pi (_, v2_), s'), Mapp (_, ms')) ->
      I.App
        ((I.EClo (u1_, s)),
          (createCoverSpine
             (g_, (s2_, s),
               (Whnf.whnf (v2_, (I.Dot ((I.Exp (I.EClo (u1_, s))), s')))),
               ms')))
  | (g_, (SClo (s_, s'), s), vs_, ms) ->
      createCoverSpine (g_, (s_, (I.comp (s', s))), vs_, ms) end(* leave input ( + ) arguments as they are, ignore ( * ) impossible *)
(* replace output argument by new variable *)
let rec checkNoDef a =
  begin match I.sgnLookup a with
  | ConDef _ ->
      raise
        (Error
           (((^) "Coverage checking " N.qidToString (N.constQid a)) ^
              ":\ntype family must not be defined."))
  | _ -> () end
let rec checkCovers (a, ms) =
  let _ =
    chatter 4
      (begin function
       | () ->
           ((^) "Input coverage checking family " N.qidToString
              (N.constQid a))
             ^ "\n" end) in
let _ = checkNoDef a in
let _ =
  begin try Subordinate.checkNoDef a
  with
  | Error msg ->
      raise
        (Error
           ((((^) "Coverage checking " N.qidToString (N.constQid a)) ^ ":\n")
              ^ msg)) end in
let (v0_, p) = initCGoal a in
let _ =
  if !Global.doubleCheck
  then begin TypeCheck.typeCheck (I.Null, (v0_, (I.Uni I.Type))) end
  else begin () end in
let _ = CSManager.reset () in
let cIn = inCoverInst ms in
let cs = Index.lookup a in
let ccs = constsToTypes cs in
let w_ = W.lookup a in
let v0_ = createCoverGoal (I.Null, (v0_, I.id), p, ms) in
let (v0_, p) = abstract (v0_, I.id) in
let missing = cover (v0_, p, (w_, cIn), (Input ccs), Top, []) in
let _ =
  ((begin match missing with
    | [] -> ()
    | _::_ ->
        raise
          (Error
             (((^) "Coverage error --- missing cases:\n" missingToString
                 (missing, ms))
                ^ "\n")) end)
  (* all cases covered *)) in
((())
  (* convert mode spine to cover instructions *)(* lookup constants defining a *)
  (* calculate covering clauses *)(* world declarations for a; must be defined *)
  (* replace output by new EVars *)(* abstract will double-check *))
let rec checkOut (g_, (v_, s)) =
  let a = I.targetFam v_ in
  let Some ms = ModeTable.modeLookup a in
  let cOut = outCoverInst ms in
  let (v'_, q) = createCoverClause (g_, (I.EClo (v_, s)), 0) in
  let _ =
    if !Global.doubleCheck
    then begin TypeCheck.typeCheck (I.Null, (v'_, (I.Uni I.Type))) end
    else begin () end in
  let v0_ = createCoverGoal (I.Null, (v'_, I.id), q, ms) in
  let (V0', p) = abstract (v0_, I.id) in
  let w_ = W.lookup a in
  let missing = cover (V0', p, (w_, cOut), (Output (v'_, q)), Top, []) in
  let _ =
    begin match missing with
    | [] -> ()
    | _::_ ->
        raise
          (Error
             (((^) "Output coverage error --- missing cases:\n"
                 missingToString (missing, ms))
                ^ "\n")) end in
  ((())
    (* must be defined and well-moded *)(* determine cover instructions *)
    (* abstract all variables in G *)(* replace output by new EVars *)
    (* abstract will double-check *))
type coverGoal_ =
  | CGoal of (I.dctx * I.spine_) 
type coverClause_ =
  | CClause of (I.dctx * I.spine_) 
let rec formatCGoal (CGoal (g_, s_)) =
  let _ = N.varReset I.Null in
  F.HVbox
    ((@) [Print.formatCtx (I.Null, g_);
         F.Break;
         F.Break;
         F.String "|-";
         F.Space]
       Print.formatSpine (g_, s_))
let rec showPendingCGoal (CGoal (g_, s_), lab) =
  F.makestring_fmt
    (F.Hbox
       [F.String (labToString lab);
       F.Space;
       F.String "?- ";
       formatCGoal (CGoal (g_, s_));
       F.String "."])
let rec showCClause (CClause (g_, s_)) =
  let _ = N.varReset I.Null in
  F.makestring_fmt
    (F.HVbox ((@) [F.String "!- "] Print.formatSpine (g_, s_)))
let rec showSplitVar (CGoal (g_, s_), k) =
  let _ = N.varReset I.Null in
  let Dec (Some x, _) = I.ctxLookup (g_, k) in
  (^) (("Split " ^ x) ^ " in ") F.makestring_fmt
    (F.HVbox (Print.formatSpine (g_, s_)))
let rec newEVarSubst =
  begin function
  | (g_, I.Null) -> I.Shift (I.ctxLength g_)
  | (g_, Decl (g'_, (Dec (_, v_) as d_))) ->
      let s' = newEVarSubst (g_, g'_) in
      let x_ = Whnf.newLoweredEVar (g_, (v_, s')) in
      ((I.Dot ((I.Exp x_), s'))
        (* was val V' = I.EClo (V, s')
                 val X = I.newEVar (G, V') Mon Feb 28 15:34:31 2011 -cs *))
  | (g_, Decl (g'_, (NDec _ as d_))) ->
      let s' = newEVarSubst (g_, g'_) in I.Dot (I.Undef, s')
  | (g_, Decl (g'_, (BDec (_, (b, t)) as d_))) ->
      let s' = newEVarSubst (g_, g'_) in
      let l1_ = I.newLVar (s', (b, t)) in ((I.Dot ((I.Block l1_), s'))
        (* was  val L1 = I.newLVar (I.Shift(0), (b, I.comp(t, s')))
             --cs Fri Jul 23 16:39:27 2010 *)
        (* -cs Fri Jul 23 16:35:04 2010  FPCHECK *)(* L : Delta[t][G'] *)
        (* G |- s : G'  G |- L[s'] : V[s]
             G |- (L[s'].s : G', V *)
        (* -fp Sun Dec  1 21:10:45 2002 *)(* -cs Sun Dec  1 06:31:23 2002 *)) end
let rec checkConstraints =
  begin function
  | (g_, (Si, ti), Cands ks) -> Cands ks
  | (g_, (Si, ti), Fail) -> Fail
  | (g_, (Si, ti), Eqns _) ->
      let xs_ = Abstract.collectEVarsSpine (g_, (Si, ti), []) in
      let constrs = collectConstraints xs_ in
      (((begin match constrs with
         | [] -> Eqns []
         | _ -> fail "Remaining constraints" end))
        (* constraints remained: Fail without candidates *)) end
(* _ = nil *)
let rec matchClause (CGoal (g_, s_), (Si, ti)) =
  let cands1 = matchSpine (g_, 0, (s_, I.id), (Si, ti), (Eqns [])) in
  let cands2 = resolveCands cands1 in
  let cands3 = checkConstraints (g_, (Si, ti), cands2) in cands3
let rec matchClauses =
  begin function
  | (cg, [], klist) -> klist
  | ((CGoal (g_, s_) as cg), (CClause (Gi, Si))::ccs, klist) ->
      let ti = newEVarSubst (g_, Gi) in
      let cands =
        CSManager.trail
          (begin function | () -> matchClause (cg, (Si, ti)) end) in
      ((matchClauses' (cg, ccs, (addKs (cands, klist))))
        (* G |- ti : Gi *)) end
let rec matchClauses' =
  begin function
  | (cg, ccs, Covered) -> Covered
  | (cg, ccs, (CandList _ as klist)) -> matchClauses (cg, ccs, klist) end
let rec match_ (CGoal (g_, s_), ccs) =
  matchClauses ((CGoal (g_, s_)), ccs, (CandList []))
let rec abstractSpine (s_, s) =
  let (g'_, s'_) = Abstract.abstractSpine (s_, s) in
  let namedG' = N.ctxName g'_ in
  let _ =
    if !Global.doubleCheck
    then begin ((TypeCheck.typeCheckCtx namedG')
      (* TypeCheck.typeCheckSpine (namedG', S') *)) end
    else begin () end in
  ((CGoal (namedG', s'_))(* for printing purposes *))
let rec kthSub =
  begin function
  | (Dot (Exp (x_), s), 1) -> x_
  | (Dot (_, s), k) -> kthSub (s, (k - 1)) end
let rec subToXsRev =
  begin function
  | Shift 0 -> []
  | Dot (Exp (x_), s) -> (::) (Some x_) subToXsRev s
  | Dot (_, s) -> (::) None subToXsRev s end(* n = 0 *)
let (caseList : coverGoal_ list ref) = ref []
let rec resetCases () = caseList := []
let rec addCase cg = (!) ((::) (caseList := cg)) caseList
let rec getCases () = !caseList
let rec splitVar ((CGoal (g_, s_) as cg), k, w) =
  ((begin try
            let _ =
              chatter 6
                (begin function | () -> (showSplitVar (cg, k)) ^ "\n" end) in
          let s = newEVarSubst (I.Null, g_) in
          let x_ = kthSub (s, k) in
          let _ = resetCases () in
          let _ =
            splitEVar
              (x_, w,
                (begin function | () -> addCase (abstractSpine (s_, s)) end)) in
          ((Some (getCases ()))
            (* for splitting, EVars are always global *)
            (* G = xn:V1,...,x1:Vn *)(* s = X1....Xn.^0, where . |- s : G *)
            (* starts with k = 1 (a la deBruijn) *))
  with
  | Error constrs ->
      (begin chatter 7
               (begin function
                | () ->
                    ((^) "Inactive split:\n" Print.cnstrsToString constrs) ^
                      "\n" end);
      None end) end)
(* Constraints.Error could be raised by abstract *))
let rec finitary (CGoal (g_, s_), w) =
  let s = newEVarSubst (I.Null, g_) in
  let XsRev = subToXsRev s in
  ((finitarySplits
      (XsRev, 1, w, (begin function | () -> abstractSpine (s_, s) end), []))
    (* G = xn:Vn,...,x1:V1 *)(* for splitting, EVars are always global *)
    (* s = X1...Xn.^0,  . |- S : G *)(* XsRev = [SOME(X1),...,SOME(Xn)] *))
let rec contractAll (CGoal (g_, s_), ucands) =
  let s = newEVarSubst (I.Null, g_) in
  let XsRev = subToXsRev s in
  ((if unifyUOut (XsRev, ucands) then begin Some (abstractSpine (s_, s)) end
    else begin None end)
  (* as in splitVar, may raise Constraints.Error *)(* for unif, EVars are always global *))
let rec contract ((CGoal (g_, s_) as cg), lab) =
  let ucands = contractionCands (g_, 1) in
  let n = List.length ucands in
  let _ =
    if n > 0
    then
      begin chatter 6
              (begin function
               | () ->
                   ((^) (((^) "Found " Int.toString n) ^ " contraction ")
                      pluralize (n, "candidate"))
                     ^ "\n" end) end
    else begin () end in
let cgOpt' =
  ((if n > 0
    then
      begin begin try contractAll (cg, ucands)
            with
            | Error _ ->
                (begin chatter 6
                         (begin function
                          | () -> "Contraction failed due to constraints\n" end);
                Some cg end) end end
  else begin Some cg end)
(* no progress if constraints remain *)) in
let _ =
begin match cgOpt' with
| None ->
    chatter 6
      (begin function | () -> "Case impossible: conflicting unique outputs\n" end)
| Some cg' ->
    chatter 6
      (begin function | () -> (showPendingCGoal (cg', lab)) ^ "\n" end) end in
((cgOpt')
(* no candidates, no progress *))
let rec cover (cg, w, ccs, lab, missing) =
  begin chatter 6
          (begin function | () -> (showPendingCGoal (cg, lab)) ^ "\n" end);
  cover' ((contract (cg, lab)), w, ccs, lab, missing) end
let rec cover' =
  begin function
  | (Some cg, w, ccs, lab, missing) ->
      let cands = match_ (cg, ccs) in
      let cand = selectCand cands in
      ((split (cg, cand, w, ccs, lab, missing))
        (* determine splitting candidates *)(* select one candidate *))
  | (None, w, ccs, lab, missing) ->
      (begin chatter 6 (begin function | () -> "Covered\n" end); missing end) end
(* cg is covered by unique output inconsistency *)
let rec split =
  begin function
  | (cg, None, w, ccs, lab, missing) ->
      (begin chatter 6 (begin function | () -> "Covered\n" end); missing end)
  | (cg, Some [], w, ccs, lab, missing) ->
      (begin chatter 6
               (begin function
                | () ->
                    "No strong candidates --- calculating weak candidates\n" end);
      splitWeak (cg, (finitary (cg, w)), w, ccs, lab, missing) end)
| (cg, Some ((k, _)::ksn), w, ccs, lab, missing) ->
    (begin chatter 6
             (begin function
              | () -> ((^) "Splitting on " Int.toString k) ^ "\n" end);
    (begin match splitVar (cg, k, w) with
     | Some cases -> covers (cases, w, ccs, lab, missing)
     | None ->
         (begin chatter 6
                  (begin function
                   | () -> "Splitting failed due to generated constraints\n" end);
         split (cg, (Some ksn), w, ccs, lab, missing) end) end) end) end
(* splitVar shows splitting as it happens *)(* candidates are in reverse order, so non-index candidates are split first *)
(* some candidates: split first candidate, ignoring multiplicities *)
(* no strong candidates: check for finitary splitting candidates *)
(* cg is covered: return missing patterns from other cases *)
let rec splitWeak =
  begin function
  | (cg, [], w, ccs, lab, missing) ->
      (begin chatter 6
               (begin function
                | () ->
                    ((^) "No weak candidates---case " labToString lab) ^
                      " not covered\n" end);
      cg :: missing end)
  | (cg, ksn, w, ccs, lab, missing) ->
      split (cg, (Some ((findMin ksn) :: [])), w, ccs, lab, missing) end
(* ksn <> nil *)
let rec covers (cases, w, ccs, lab, missing) =
  begin chatter 6
          (begin function
           | () ->
               ((^) ((^) "Found " Int.toString (List.length cases)) pluralize
                  ((List.length cases), " case"))
                 ^ "\n" end);
  covers' (cases, 1, w, ccs, lab, missing) end
let rec covers' =
  begin function
  | ([], n, w, ccs, lab, missing) ->
      (begin chatter 6
               (begin function
                | () ->
                    ((^) "All subcases of " labToString lab) ^
                      " considered\n" end);
      missing end)
  | (cg::cases', n, w, ccs, lab, missing) ->
      let missing1 = cover (cg, w, ccs, (Child (lab, n)), missing) in
      covers' (cases', (n + 1), w, ccs, lab, missing1) end
let rec substToSpine' =
  begin function
  | (Shift n, I.Null, t_) -> t_
  | (Shift n, (Decl _ as g_), t_) ->
      substToSpine' ((I.Dot ((I.Idx (n + 1)), (I.Shift (n + 1)))), g_, t_)
  | (Dot (_, s), Decl (g_, NDec _), t_) -> substToSpine' (s, g_, t_)
  | (Dot (Exp (u_), s), Decl (g_, v_), t_) ->
      substToSpine' (s, g_, (I.App (u_, t_)))
  | (Dot (Idx n, s), Decl (g_, Dec (_, v_)), t_) ->
      let (us_, _) =
        Whnf.whnfEta (((I.Root ((I.BVar n), I.Nil)), I.id), (v_, I.id)) in
      substToSpine' (s, g_, (I.App ((I.EClo us_), t_)))
  | (Dot (_, s), Decl (g_, BDec (_, (l_, t))), t_) ->
      substToSpine' (s, g_, t_) end(* Attempted fix, didn't work because I don't know how you
             computed splitting candidates for Blocks
             --cs Sat Jan  4 22:38:01 2003
          *)
(* Treat like I.NDec *)(* was: I.Idx in previous line, Sun Jan  5 11:02:19 2003 -fp *)
(* Eta-expand *)(* Unusable meta-decs are eliminated here *)
(* Skip over NDec's; must be either Undef or Idx [from eta-expansion] *)
let rec substToSpine (s, g_) = substToSpine' (s, g_, I.Nil)
let rec purify' =
  begin function
  | I.Null -> (I.Null, I.id)
  | Decl (g_, NDec _) ->
      let (g'_, s) = purify' g_ in (((g'_, (I.Dot (I.Undef, s))))
        (* G' |- s : G *)(* G' |- _.s : G,_ *))
  | Decl (g_, (Dec _ as d_)) ->
      let (g'_, s) = purify' g_ in
      ((((I.Decl (g'_, (I.decSub (d_, s)))), (I.dot1 s)))
        (* G' |- s : G *)(* G |- D : type *)(* G' |- D[s] : type *)
        (* G', D[s] |- 1 : D[s][^] *)(* G', D[s] |- s o ^ : G *)
        (* G', D[s] |- 1.s o ^ : G, D *))
  | Decl (g_, (BDec _ as d_)) ->
      let (g'_, s) = purify' g_ in (((g'_, (I.Dot (I.Undef, s))))
        (* G' |- s : G *)(* G' |- _.s : G,_ *)) end
(* added a new case to throw out blocks
         -cs Sat Jan  4 22:55:12 2003
      *)
let rec purify (g_) = (fun r -> r.1) (purify' g_)
let rec coverageCheckCases (w, cs_, g_) =
  let _ =
    chatter 4 (begin function | () -> "[Tomega coverage checker..." end) in
let _ = chatter 4 (begin function | () -> "\n" end) in
let ccs =
  List.map
    (begin function | (Gi, si) -> CClause (Gi, (substToSpine (si, g_))) end)
  cs_ in
let _ = chatter 6 (begin function | () -> "[Begin covering clauses]\n" end) in
let _ =
  List.app
    (begin function
     | cc -> chatter 6 (begin function | () -> (showCClause cc) ^ "\n" end) end)
  ccs in
let _ = chatter 6 (begin function | () -> "[End covering clauses]\n" end) in
let pureG = purify g_ in
let namedG = N.ctxLUName pureG in
let r0_ = substToSpine (I.id, namedG) in
let cg0 = CGoal (namedG, r0_) in
let missing = cover (cg0, w, ccs, Top, []) in
let _ =
  ((begin match missing with
    | [] -> ()
    | _::_ -> raise (Error "Coverage error") end)
  (* all cases covered *)) in
let _ = chatter 4 (begin function | () -> "]\n" end) in ((())
  (* Question: are all the Gi's above named already? *)) end



module Cover =
  (Cover)(struct
                 module Global = Global
                 module Whnf = Whnf
                 module Conv = Conv
                 module Abstract = Abstract
                 module Unify = UnifyTrail
                 module Constraints = Constraints
                 module ModeTable = ModeTable
                 module UniqueTable = UniqueTable
                 module Index = Index
                 module Subordinate = Subordinate
                 module WorldSyn = WorldSyn
                 module Names = Names
                 module Print = Print
                 module TypeCheck = TypeCheck
                 module Timers = Timers
               end)
module Total =
  (Total)(struct
                 module Global = Global
                 module Table = IntRedBlackTree
                 module Whnf = Whnf
                 module Names = Names
                 module ModeTable = ModeTable
                 module ModeCheck = ModeCheck
                 module Index = Index
                 module Subordinate = Subordinate
                 module Order = Order
                 module Reduces = Reduces
                 module Cover = Cover
                 module Origins = Origins
                 module Timers = Timers
               end)