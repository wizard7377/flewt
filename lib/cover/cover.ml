
(* Coverage Checking *)
(* Author: Frank Pfenning *)
module type COVER  =
  sig
    exception Error of string 
    val checkNoDef : IntSyn.cid -> unit
    (* raises Error(msg) *)
    val checkOut : (IntSyn.dctx * IntSyn.eclo) -> unit
    val checkCovers : (IntSyn.cid * ModeSyn.__ModeSpine) -> unit
    val coverageCheckCases :
      (Tomega.__Worlds * (IntSyn.dctx * IntSyn.__Sub) list * IntSyn.dctx) ->
        unit
  end;;




(* Coverage Checking *)
(* Author: Frank Pfenning *)
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
                     (*! sharing Whnf.IntSyn = IntSyn' !*)
                     (*! sharing Abstract.IntSyn = IntSyn' !*)
                     (* must be trailing! *)
                     (*! sharing Unify.IntSyn = IntSyn' !*)
                     (*! sharing Constraints.IntSyn = IntSyn' !*)
                     (*! sharing Index.IntSyn = IntSyn' !*)
                     (*! sharing Subordinate.IntSyn = IntSyn' !*)
                     (*! sharing Names.IntSyn = IntSyn' !*)
                     (*! structure Paths : PATHS !*)
                     (*! sharing Print.IntSyn = IntSyn' !*)
                     (*! sharing TypeCheck.IntSyn = IntSyn' !*)
                     (*! structure CSManager : CS_MANAGER !*)
                     (*! sharing CSManager.IntSyn = IntSyn' !*)
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
      function
      | (I.Null, a) -> I.id
      | (Decl (G', (Dec (name, V) as D)), a) ->
          let w' = weaken (G', a) in
          if Subordinate.belowEq ((I.targetFam V), a)
          then I.dot1 w'
          else I.comp (w', I.shift)
    let rec createEVar (G, V) =
      let w = weaken (G, (I.targetFam V)) in
      let iw = Whnf.invert w in
      let G' = Whnf.strengthen (iw, G) in
      let X' = Whnf.newLoweredEVar (G', (V, iw)) in
      let X = I.EClo (X', w) in X
    type __CoverInst =
      | Match of __CoverInst 
      | Skip of __CoverInst 
      | Cnil 
    let rec inCoverInst =
      function
      | M.Mnil -> Cnil
      | Mapp (Marg (M.Plus, x), ms') -> Match (inCoverInst ms')
      | Mapp (Marg (M.Minus, x), ms') -> Skip (inCoverInst ms')
      | Mapp (Marg (M.Star, x), ms') -> Skip (inCoverInst ms')
    let rec outCoverInst =
      function
      | M.Mnil -> Cnil
      | Mapp (Marg (M.Plus, x), ms') -> Skip (outCoverInst ms')
      | Mapp (Marg (M.Minus, x), ms') -> Match (outCoverInst ms')
    type caseLabel =
      | Top 
      | Child of (caseLabel * int) 
    let rec labToString =
      function
      | Top -> "^"
      | Child (lab, n) -> (^) ((labToString lab) ^ ".") Int.toString n
    let rec chatter chlev f =
      if (!Global.chatter) >= chlev then print (f ()) else ()
    let rec pluralize = function | (1, s) -> s | (n, s) -> s ^ "s"
    let rec abbrevCSpine (S, ci) = S
    let rec abbrevCGoal =
      function
      | (G, V, 0, ci) -> (G, (abbrevCGoal' (G, V, ci)))
      | (G, Pi ((D, P), V), p, ci) ->
          let D' = N.decEName (G, D) in
          abbrevCGoal ((I.Decl (G, D')), V, (p - 1), ci)
    let rec abbrevCGoal' =
      function
      | (G, Pi ((D, P), V), ci) ->
          let D' = N.decUName (G, D) in
          I.Pi ((D', P), (abbrevCGoal' ((I.Decl (G, D')), V, ci)))
      | (G, Root (a, S), ci) -> I.Root (a, (abbrevCSpine (S, ci)))
    let rec formatCGoal (V, p, ci) =
      let _ = N.varReset I.Null in
      let (G, V') = abbrevCGoal (I.Null, V, p, ci) in
      F.HVbox
        [Print.formatCtx (I.Null, G);
        F.Break;
        F.String "|-";
        F.Space;
        Print.formatExp (G, V')]
    let rec formatCGoals =
      function
      | ((V, p)::nil, ci) -> [formatCGoal (V, p, ci)]
      | ((V, p)::Vs, ci) ->
          (::) (((::) (formatCGoal (V, p, ci)) F.String ",") :: F.Break)
            formatCGoals (Vs, ci)
    let rec missingToString (Vs, ci) =
      F.makestring_fmt
        (F.Hbox [F.Vbox0 0 1 (formatCGoals (Vs, ci)); F.String "."])
    let rec showSplitVar (V, p, k, ci) =
      let _ = N.varReset I.Null in
      let (G, V') = abbrevCGoal (I.Null, V, p, ci) in
      let Dec (SOME x, _) = I.ctxLookup (G, k) in
      (^) (("Split " ^ x) ^ " in ") Print.expToString (G, V')
    let rec showPendingGoal (V, p, ci, lab) =
      F.makestring_fmt
        (F.Hbox
           [F.String (labToString lab);
           F.Space;
           F.String "?- ";
           formatCGoal (V, p, ci);
           F.String "."])
    let rec buildSpine =
      function
      | 0 -> I.Nil
      | n -> I.App ((I.Root ((I.BVar n), I.Nil)), (buildSpine (n - 1)))
    let rec initCGoal' =
      function
      | (a, k, G, Pi ((D, P), V)) ->
          let D' = N.decEName (G, D) in
          let (V', p) = initCGoal' (a, (k + 1), (I.Decl (G, D')), V) in
          ((I.Pi ((D', I.Maybe), V')), p)
      | (a, k, G, Uni (I.Type)) -> ((I.Root (a, (buildSpine k))), k)
    let rec initCGoal a =
      initCGoal' ((I.Const a), 0, I.Null, (I.constType a))
    type __CoverClauses =
      | Input of I.__Exp list 
      | Output of (I.__Exp * int) 
    type __Equation =
      | Eqn of (I.dctx * I.eclo * I.eclo) 
    let rec equationToString (Eqn (G, Us1, Us2)) =
      let G' = Names.ctxLUName G in
      let fmt =
        F.HVbox
          [Print.formatCtx (I.Null, G');
          F.Break;
          F.String "|-";
          F.Space;
          Print.formatExp (G', (I.EClo Us1));
          F.Break;
          F.String "=";
          F.Space;
          Print.formatExp (G', (I.EClo Us2))] in
      F.makestring_fmt fmt
    let rec eqnsToString =
      function
      | nil -> ".\n"
      | eqn::eqns -> (^) ((equationToString eqn) ^ ",\n") eqnsToString eqns
    type __Candidates =
      | Eqns of __Equation list 
      | Cands of int list 
      | Fail 
    let rec candsToString =
      function
      | Fail -> "Fail"
      | Cands ks ->
          (^) "Cands [" List.foldl
            ((function | (k, str) -> ((Int.toString k) ^ ",") ^ str)) "]" ks
      | Eqns eqns -> ((^) "Eqns [\n" eqnsToString eqns) ^ "]"
    let rec fail msg = chatter 7 (function | () -> msg ^ "\n"); Fail
    let rec failAdd =
      function
      | (k, Eqns _) -> Cands (k :: nil)
      | (k, Cands ks) -> Cands (k :: ks)
      | (k, Fail) -> Fail
    let rec addEqn =
      function
      | (e, Eqns es) -> Eqns (e :: es)
      | (e, (Cands ks as cands)) -> cands
      | (e, Fail) -> Fail
    let rec unifiable (G, Us1, Us2) = Unify.unifiable (G, Us1, Us2)
    let rec matchEqns =
      function
      | nil -> true__
      | (Eqn (G, Us1, ((U2, s2) as Us2)))::es ->
          (match Whnf.makePatSub s2 with
           | NONE -> unifiable (G, Us1, Us2)
           | SOME s2' -> unifiable (G, Us1, (U2, s2'))) && (matchEqns es)
    let rec resolveCands =
      function
      | Eqns es -> if matchEqns (List.rev es) then Eqns nil else Fail
      | Cands ks -> Cands ks
      | Fail -> Fail
    let rec collectConstraints =
      function
      | nil -> nil
      | (EVar (_, _, _, ref nil))::Xs -> collectConstraints Xs
      | (EVar (_, _, _, ref constrs))::Xs ->
          (@) constrs collectConstraints Xs
    let rec checkConstraints =
      function
      | (G, Qs, Cands ks) -> Cands ks
      | (G, Qs, Fail) -> Fail
      | (G, Qs, Eqns _) ->
          let Xs = Abstract.collectEVars (G, Qs, nil) in
          let constrs = collectConstraints Xs in
          (match constrs with | nil -> Eqns nil | _ -> Fail)
    type __CandList =
      | Covered 
      | CandList of __Candidates list 
    let rec addKs =
      function
      | ((Cands ks as ccs), CandList klist) -> CandList (ccs :: klist)
      | ((Eqns nil as ces), CandList klist) -> Covered
      | ((Fail as cfl), CandList klist) -> CandList (cfl :: klist)
    let rec matchExp (G, d, Us1, Us2, cands) =
      matchExpW (G, d, (Whnf.whnf Us1), (Whnf.whnf Us2), cands)
    let rec matchExpW =
      function
      | (G, d, ((Root (H1, S1), s1) as Us1), ((Root (H2, S2), s2) as Us2),
         cands) ->
          (match (H1, H2) with
           | (BVar k1, BVar k2) ->
               if k1 = k2
               then matchSpine (G, d, (S1, s1), (S2, s2), cands)
               else
                 if k1 > d
                 then failAdd ((k1 - d), cands)
                 else fail "local variable / variable clash"
           | (Const c1, Const c2) ->
               if c1 = c2
               then matchSpine (G, d, (S1, s1), (S2, s2), cands)
               else fail "constant / constant clash"
           | (Def d1, Def d2) ->
               if d1 = d2
               then matchSpine (G, d, (S1, s1), (S2, s2), cands)
               else
                 matchExpW
                   (G, d, (Whnf.expandDef Us1), (Whnf.expandDef Us2), cands)
           | (Def d1, _) ->
               matchExpW (G, d, (Whnf.expandDef Us1), Us2, cands)
           | (_, Def d2) ->
               matchExpW (G, d, Us1, (Whnf.expandDef Us2), cands)
           | (BVar k1, Const _) ->
               if k1 > d
               then failAdd ((k1 - d), cands)
               else fail "local variable / constant clash"
           | (Const _, BVar _) -> fail "constant / local variable clash"
           | (Proj (Bidx k1, i1), Proj (Bidx k2, i2)) ->
               if (k1 = k2) && (i1 = i2)
               then matchSpine (G, d, (S1, s1), (S2, s2), cands)
               else fail "block index / block index clash"
           | (Proj (Bidx k1, i1), Proj (LVar (r2, Shift k2, (l2, t2)), i2))
               ->
               let BDec (bOpt, (l1, t1)) = I.ctxDec (G, k1) in
               if (l1 <> l2) || (i1 <> i2)
               then fail "block index / block variable clash"
               else
                 (let cands2 =
                    matchSub (G, d, t1, (I.comp (t2, (I.Shift k2))), cands) in
                  let _ = Unify.instantiateLVar (r2, (I.Bidx (k1 - k2))) in
                  matchSpine (G, d, (S1, s1), (S2, s2), cands2))
           | (BVar k1, Proj _) ->
               if k1 > d
               then failAdd ((k1 - d), cands)
               else fail "local variable / block projection clash"
           | (Const _, Proj _) -> fail "constant / block projection clash"
           | (Proj _, Const _) -> fail "block projection / constant clash"
           | (Proj _, BVar _) ->
               fail "block projection / local variable clash")
      | (G, d, (Lam (D1, U1), s1), (Lam (D2, U2), s2), cands) ->
          matchExp
            ((I.Decl (G, (I.decSub (D1, s1)))), (d + 1), (U1, (I.dot1 s1)),
              (U2, (I.dot1 s2)), cands)
      | (G, d, (Lam (D1, U1), s1), (U2, s2), cands) ->
          matchExp
            ((I.Decl (G, (I.decSub (D1, s1)))), (d + 1), (U1, (I.dot1 s1)),
              ((I.Redex
                  ((I.EClo (U2, I.shift)),
                    (I.App ((I.Root ((I.BVar 1), I.Nil)), I.Nil)))),
                (I.dot1 s2)), cands)
      | (G, d, (U1, s1), (Lam (D2, U2), s2), cands) ->
          matchExp
            ((I.Decl (G, (I.decSub (D2, s2)))), (d + 1),
              ((I.Redex
                  ((I.EClo (U1, I.shift)),
                    (I.App ((I.Root ((I.BVar 1), I.Nil)), I.Nil)))),
                (I.dot1 s1)), (U2, (I.dot1 s2)), cands)
      | (G, d, Us1, ((EVar _, s2) as Us2), cands) ->
          addEqn ((Eqn (G, Us1, Us2)), cands)
    let rec matchSpine =
      function
      | (G, d, (I.Nil, _), (I.Nil, _), cands) -> cands
      | (G, d, (SClo (S1, s1'), s1), Ss2, cands) ->
          matchSpine (G, d, (S1, (I.comp (s1', s1))), Ss2, cands)
      | (G, d, Ss1, (SClo (S2, s2'), s2), cands) ->
          matchSpine (G, d, Ss1, (S2, (I.comp (s2', s2))), cands)
      | (G, d, (App (U1, S1), s1), (App (U2, S2), s2), cands) ->
          let cands' = matchExp (G, d, (U1, s1), (U2, s2), cands) in
          matchSpine (G, d, (S1, s1), (S2, s2), cands')
    let rec matchDec (G, d, (Dec (_, V1), s1), (Dec (_, V2), s2), cands) =
      matchExp (G, d, (V1, s1), (V2, s2), cands)
    let rec matchSub =
      function
      | (G, d, Shift n1, Shift n2, cands) -> cands
      | (G, d, Shift n, (Dot _ as s2), cands) ->
          matchSub
            (G, d, (I.Dot ((I.Idx (n + 1)), (I.Shift (n + 1)))), s2, cands)
      | (G, d, (Dot _ as s1), Shift m, cands) ->
          matchSub
            (G, d, s1, (I.Dot ((I.Idx (m + 1)), (I.Shift (m + 1)))), cands)
      | (G, d, Dot (Ft1, s1), Dot (Ft2, s2), cands) ->
          let cands1 =
            match (Ft1, Ft2) with
            | (Idx n1, Idx n2) ->
                if n1 = n2
                then cands
                else
                  if n1 > d
                  then failAdd ((n1 - d), cands)
                  else
                    fail
                      "local variable / local variable clash in block instance"
            | (Exp (U1), Exp (U2)) ->
                matchExp (G, d, (U1, I.id), (U2, I.id), cands)
            | (Exp (U1), Idx n2) ->
                matchExp
                  (G, d, (U1, I.id), ((I.Root ((I.BVar n2), I.Nil)), I.id),
                    cands)
            | (Idx n1, Exp (U2)) ->
                matchExp
                  (G, d, ((I.Root ((I.BVar n1), I.Nil)), I.id), (U2, I.id),
                    cands) in
          matchSub (G, d, s1, s2, cands1)
    let rec matchTop (G, d, Us1, Us2, ci, cands) =
      matchTopW (G, d, (Whnf.whnf Us1), (Whnf.whnf Us2), ci, cands)
    let rec matchTopW =
      function
      | (G, d, (Root (Const c1, S1), s1), (Root (Const c2, S2), s2), ci,
         cands) ->
          if c1 = c2
          then matchTopSpine (G, d, (S1, s1), (S2, s2), ci, cands)
          else fail "type family clash"
      | (G, d, (Pi ((D1, _), V1), s1), (Pi ((D2, _), V2), s2), ci, cands) ->
          matchTopW
            ((I.Decl (G, D1)), (d + 1), (V1, (I.dot1 s1)), (V2, (I.dot1 s2)),
              ci, cands)
    let rec matchTopSpine =
      function
      | (G, d, (I.Nil, _), (I.Nil, _), Cnil, cands) -> cands
      | (G, d, (SClo (S1, s1'), s1), Ss2, ci, cands) ->
          matchTopSpine (G, d, (S1, (I.comp (s1', s1))), Ss2, ci, cands)
      | (G, d, Ss1, (SClo (S2, s2'), s2), ci, cands) ->
          matchTopSpine (G, d, Ss1, (S2, (I.comp (s2', s2))), ci, cands)
      | (G, d, (App (U1, S1), s1), (App (U2, S2), s2), Match ci', cands) ->
          let cands' = matchExp (G, d, (U1, s1), (U2, s2), cands) in
          matchTopSpine (G, d, (S1, s1), (S2, s2), ci', cands')
      | (G, d, (App (U1, S1), s1), (App (U2, S2), s2), Skip ci', cands) ->
          matchTopSpine (G, d, (S1, s1), (S2, s2), ci', cands)
    let rec matchClause =
      function
      | (G, ps', ((Root (_, _), s) as qs), ci) ->
          checkConstraints
            (G, qs,
              (resolveCands (matchTop (G, 0, ps', qs, ci, (Eqns nil)))))
      | (G, ps', (Pi ((Dec (_, V1), _), V2), s), ci) ->
          let X1 = Whnf.newLoweredEVar (G, (V1, s)) in
          matchClause (G, ps', (V2, (I.Dot ((I.Exp X1), s))), ci)
    let rec matchSig =
      function
      | (G, ps', nil, ci, klist) -> klist
      | (G, ps', (V)::ccs', ci, klist) ->
          let cands =
            CSManager.trail
              (function | () -> matchClause (G, ps', (V, I.id), ci)) in
          matchSig' (G, ps', ccs', ci, (addKs (cands, klist)))
    let rec matchSig' =
      function
      | (G, ps', ccs, ci, Covered) -> Covered
      | (G, ps', ccs, ci, CandList klist) ->
          matchSig (G, ps', ccs, ci, (CandList klist))
    let rec matchBlocks =
      function
      | (G, s', nil, V, k, i, ci, klist) -> klist
      | (G, s', (Dec (_, V'))::piDecs, V, k, i, ci, klist) ->
          let cands =
            CSManager.trail
              (function | () -> matchClause (G, (V, I.id), (V', s'), ci)) in
          let s'' =
            I.Dot ((I.Exp (I.Root ((I.Proj ((I.Bidx k), i)), I.Nil))), s') in
          matchBlocks'
            (G, s'', piDecs, V, k, (i + 1), ci, (addKs (cands, klist)))
    let rec matchBlocks' =
      function
      | (G, s', piDecs, V, k, i, ci, Covered) -> Covered
      | (G, s', piDecs, V, k, i, ci, klist) ->
          matchBlocks (G, s', piDecs, V, k, i, ci, klist)
    let rec matchCtx =
      function
      | (G, s', I.Null, V, k, ci, klist) -> klist
      | (G, s', Decl (G'', Dec (_, V')), V, k, ci, klist) ->
          let s'' = I.comp (I.shift, s') in
          let cands =
            CSManager.trail
              (function | () -> matchClause (G, (V, I.id), (V', s''), ci)) in
          matchCtx' (G, s'', G'', V, (k + 1), ci, (addKs (cands, klist)))
      | (G, s', Decl (G'', BDec (_, (cid, s))), V, k, ci, klist) ->
          let (Gsome, piDecs) = I.constBlock cid in
          let s'' = I.comp (I.shift, s') in
          let klist' =
            matchBlocks (G, (I.comp (s, s'')), piDecs, V, k, 1, ci, klist) in
          matchCtx' (G, s'', G'', V, (k + 1), ci, klist')
    let rec matchCtx' =
      function
      | (G, s', G', V, k, ci, Covered) -> Covered
      | (G, s', G', V, k, ci, CandList klist) ->
          matchCtx (G, s', G', V, k, ci, (CandList klist))
    let rec matchOut =
      function
      | (G, V, ci, (V', s'), 0) ->
          let cands = matchTop (G, 0, (V, I.id), (V', s'), ci, (Eqns nil)) in
          let cands' = resolveCands cands in
          let cands'' = checkConstraints (G, (V', s'), cands') in
          addKs (cands'', (CandList nil))
      | (G, V, ci, ((Pi ((Dec (_, V1'), _), V2') as V'), s'), p) ->
          let X1 = Whnf.newLoweredEVar (G, (V1', s')) in
          matchOut (G, V, ci, (V2', (I.Dot ((I.Exp X1), s'))), (p - 1))
    let rec match__ =
      function
      | (G, (Root (Const a, S) as V), 0, ci, Input ccs) ->
          matchCtx'
            (G, I.id, G, V, 1, ci,
              (matchSig (G, (V, I.id), ccs, ci, (CandList nil))))
      | (G, V, 0, ci, Output (V', q)) ->
          matchOut (G, V, ci, (V', (I.Shift (I.ctxLength G))), q)
      | (G, Pi ((D, _), V'), p, ci, ccs) ->
          match__ ((I.Decl (G, D)), V', (p - 1), ci, ccs)
    let rec insert =
      function
      | (k, nil) -> (k, 1) :: nil
      | (k, ((k', n')::ksn' as ksn)) ->
          (match Int.compare (k, k') with
           | LESS -> (k, 1) :: ksn
           | EQUAL -> (k', (n' + 1)) :: ksn'
           | GREATER -> (::) (k', n') insert (k, ksn'))
    let rec join =
      function
      | (nil, ksn) -> ksn
      | (k::ks, ksn) -> join (ks, (insert (k, ksn)))
    let rec selectCand =
      function | Covered -> NONE | CandList klist -> selectCand' (klist, nil)
    let rec selectCand' =
      function
      | (nil, ksn) -> SOME ksn
      | ((Fail)::klist, ksn) -> selectCand' (klist, ksn)
      | ((Cands nil)::klist, ksn) -> selectCand' (klist, ksn)
      | ((Cands ks)::klist, ksn) -> selectCand' (klist, (join (ks, ksn)))
    let rec instEVars (Vs, p, XsRev) = instEVarsW ((Whnf.whnf Vs), p, XsRev)
    let rec instEVarsW =
      function
      | (Vs, 0, XsRev) -> (Vs, XsRev)
      | ((Pi ((Dec (xOpt, V1), _), V2), s), p, XsRev) ->
          let X1 = Whnf.newLoweredEVar (I.Null, (V1, s)) in
          instEVars
            ((V2, (I.Dot ((I.Exp X1), s))), (p - 1), ((SOME X1) :: XsRev))
      | ((Pi ((BDec (_, (l, t)), _), V2), s), p, XsRev) ->
          let L1 = I.newLVar ((I.Shift 0), (l, (I.comp (t, s)))) in
          instEVars
            ((V2, (I.Dot ((I.Block L1), s))), (p - 1), (NONE :: XsRev))
    let (caseList : (I.__Exp * int) list ref) = ref nil
    let rec resetCases () = caseList := nil
    let rec addCase (V, p) = (!) ((::) (caseList := (V, p))) caseList
    let rec getCases () = !caseList
    let rec createEVarSpine (G, Vs) = createEVarSpineW (G, (Whnf.whnf Vs))
    let rec createEVarSpineW =
      function
      | (G, ((Root _, s) as Vs)) -> (I.Nil, Vs)
      | (G, (Pi (((Dec (_, V1) as D), _), V2), s)) ->
          let X = createEVar (G, (I.EClo (V1, s))) in
          let (S, Vs) = createEVarSpine (G, (V2, (I.Dot ((I.Exp X), s)))) in
          ((I.App (X, S)), Vs)
    let rec createAtomConst (G, (Const cid as H)) =
      let V = I.constType cid in
      let (S, Vs) = createEVarSpine (G, (V, I.id)) in ((I.Root (H, S)), Vs)
    let rec createAtomBVar (G, k) =
      let Dec (_, V) = I.ctxDec (G, k) in
      let (S, Vs) = createEVarSpine (G, (V, I.id)) in
      ((I.Root ((I.BVar k), S)), Vs)
    let rec createAtomProj (G, H, (V, s)) =
      let (S, Vs') = createEVarSpine (G, (V, s)) in ((I.Root (H, S)), Vs')
    let rec constCases =
      function
      | (G, Vs, nil, sc) -> ()
      | (G, Vs, (Const c)::sgn', sc) ->
          let (U, Vs') = createAtomConst (G, (I.Const c)) in
          let _ =
            CSManager.trail
              (function
               | () -> if Unify.unifiable (G, Vs, Vs') then sc U else ()) in
          constCases (G, Vs, sgn', sc)
    let rec paramCases =
      function
      | (G, Vs, 0, sc) -> ()
      | (G, Vs, k, sc) ->
          let (U, Vs') = createAtomBVar (G, k) in
          let _ =
            CSManager.trail
              (function
               | () -> if Unify.unifiable (G, Vs, Vs') then sc U else ()) in
          paramCases (G, Vs, (k - 1), sc)
    let rec createEVarSub =
      function
      | I.Null -> I.id
      | Decl (G', (Dec (_, V) as D)) ->
          let s = createEVarSub G' in
          let X = Whnf.newLoweredEVar (I.Null, (V, s)) in
          I.Dot ((I.Exp X), s)
    let rec blockName cid = I.conDecName (I.sgnLookup cid)
    let rec blockCases (G, Vs, cid, (Gsome, piDecs), sc) =
      let t = createEVarSub Gsome in
      let sk = I.Shift (I.ctxLength G) in
      let t' = I.comp (t, sk) in
      let lvar = I.newLVar (sk, (cid, t)) in
      blockCases' (G, Vs, (lvar, 1), (t', piDecs), sc)
    let rec blockCases' =
      function
      | (G, Vs, (lvar, i), (t, nil), sc) -> ()
      | (G, Vs, (lvar, i), (t, (Dec (_, V'))::piDecs), sc) ->
          let (U, Vs') = createAtomProj (G, (I.Proj (lvar, i)), (V', t)) in
          let _ =
            CSManager.trail
              (function
               | () -> if Unify.unifiable (G, Vs, Vs') then sc U else ()) in
          let t' = I.Dot ((I.Exp (I.Root ((I.Proj (lvar, i)), I.Nil))), t) in
          blockCases' (G, Vs, (lvar, (i + 1)), (t', piDecs), sc)
    let rec worldCases =
      function
      | (G, Vs, Worlds nil, sc) -> ()
      | (G, Vs, Worlds (cid::cids), sc) ->
          (blockCases (G, Vs, cid, (I.constBlock cid), sc);
           worldCases (G, Vs, (T.Worlds cids), sc))
    let rec lowerSplitW =
      function
      | ((EVar (_, G, V, _) as X), W, sc) ->
          let sc' =
            function
            | U ->
                if Unify.unifiable (G, (X, I.id), (U, I.id))
                then sc ()
                else () in
          let _ = paramCases (G, (V, I.id), (I.ctxLength G), sc') in
          let _ = worldCases (G, (V, I.id), W, sc') in
          let _ =
            constCases (G, (V, I.id), (Index.lookup (I.targetFam V)), sc') in
          ()
      | (Lam (D, U), W, sc) -> lowerSplitW (U, W, sc)
    let rec splitEVar (X, W, sc) = lowerSplitW (X, W, sc)
    let rec abstract (V, s) =
      let (i, V') = Abstract.abstractDecImp (I.EClo (V, s)) in
      let _ =
        if !Global.doubleCheck
        then TypeCheck.typeCheck (I.Null, (V', (I.Uni I.Type)))
        else () in
      (V', i)
    let rec splitVar (V, p, k, (W, ci)) =
      try
        let _ =
          chatter 6 (function | () -> (showSplitVar (V, p, k, ci)) ^ "\n") in
        let ((V1, s), XsRev) = instEVars ((V, I.id), p, nil) in
        let SOME (X) = List.nth (XsRev, (k - 1)) in
        let _ = resetCases () in
        let _ =
          splitEVar (X, W, (function | () -> addCase (abstract (V1, s)))) in
        SOME (getCases ())
      with
      | Error constrs ->
          (chatter 7
             (function
              | () ->
                  ((^) "Inactive split:\n" Print.cnstrsToString constrs) ^
                    "\n");
           NONE)
    let rec occursInExp =
      function
      | (k, Uni _) -> false__
      | (k, Pi (DP, V)) ->
          (occursInDecP (k, DP)) || (occursInExp ((k + 1), V))
      | (k, Root (H, S)) -> (occursInHead (k, H)) || (occursInSpine (k, S))
      | (k, Lam (D, V)) -> (occursInDec (k, D)) || (occursInExp ((k + 1), V))
      | (k, FgnExp (cs, ops)) -> false__
    let rec occursInHead =
      function | (k, BVar k') -> k = k' | (k, _) -> false__
    let rec occursInSpine =
      function
      | (_, I.Nil) -> false__
      | (k, App (U, S)) -> (occursInExp (k, U)) || (occursInSpine (k, S))
    let rec occursInDec (k, Dec (_, V)) = occursInExp (k, V)
    let rec occursInDecP (k, (D, _)) = occursInDec (k, D)
    let rec occursInMatchPos =
      function
      | (k, Pi (DP, V), ci) -> occursInMatchPos ((k + 1), V, ci)
      | (k, Root (H, S), ci) -> occursInMatchPosSpine (k, S, ci)
    let rec occursInMatchPosSpine =
      function
      | (k, I.Nil, Cnil) -> false__
      | (k, App (U, S), Match ci) ->
          (occursInExp (k, U)) || (occursInMatchPosSpine (k, S, ci))
      | (k, App (U, S), Skip ci) -> occursInMatchPosSpine (k, S, ci)
    let rec instEVarsSkip (Vs, p, XsRev, ci) =
      InstEVarsSkipW ((Whnf.whnf Vs), p, XsRev, ci)
    let rec InstEVarsSkipW =
      function
      | (Vs, 0, XsRev, ci) -> (Vs, XsRev)
      | ((Pi ((Dec (xOpt, V1), _), V2), s), p, XsRev, ci) ->
          let X1 = Whnf.newLoweredEVar (I.Null, (V1, s)) in
          let EVarOpt =
            if occursInMatchPos (1, V2, ci) then SOME X1 else NONE in
          instEVarsSkip
            ((V2, (I.Dot ((I.Exp X1), s))), (p - 1), (EVarOpt :: XsRev), ci)
      | ((Pi ((BDec (_, (l, t)), _), V2), s), p, XsRev, ci) ->
          let L1 = I.newLVar ((I.Shift 0), (l, (I.comp (t, s)))) in
          instEVarsSkip
            ((V2, (I.Dot ((I.Block L1), s))), (p - 1), (NONE :: XsRev), ci)
    let rec targetBelowEq =
      function
      | (a, EVar (ref (NONE), GY, VY, ref nil)) ->
          Subordinate.belowEq (a, (I.targetFam VY))
      | (a, EVar (ref (NONE), GY, VY, ref (_::_))) -> true__
    let rec recursive =
      function
      | EVar (ref (SOME (U)), GX, VX, _) as X ->
          let a = I.targetFam VX in
          let Ys = Abstract.collectEVars (GX, (X, I.id), nil) in
          let recp = List.exists (function | Y -> targetBelowEq (a, Y)) Ys in
          recp
      | Lam (D, U) -> recursive U
    let counter = ref 0
    let rec resetCount () = counter := 0
    let rec incCount () = ((!) ((:=) counter) counter) + 1
    let rec getCount () = !counter
    exception NotFinitary 
    let rec finitary1 (X, k, W, f, cands) =
      resetCount ();
      chatter 7
        (function
         | () ->
             (((^) "Trying " Print.expToString (I.Null, X)) ^ " : ") ^ ".\n");
      (try
         splitEVar
           (X, W,
             (function
              | () ->
                  (f ();
                   if recursive X then raise NotFinitary else incCount ())));
         chatter 7
           (function
            | () ->
                ((^) "Finitary with " Int.toString (getCount ())) ^
                  " candidates.\n");
         (k, (getCount ())) :: cands
       with
       | NotFinitary ->
           (chatter 7 (function | () -> "Not finitary.\n"); cands)
       | Error constrs ->
           (chatter 7 (function | () -> "Inactive finitary split.\n"); cands))
    let rec finitarySplits =
      function
      | (nil, k, W, f, cands) -> cands
      | ((NONE)::Xs, k, W, f, cands) ->
          finitarySplits (Xs, (k + 1), W, f, cands)
      | ((SOME (X))::Xs, k, W, f, cands) ->
          finitarySplits
            (Xs, (k + 1), W, f,
              (CSManager.trail
                 (function | () -> finitary1 (X, k, W, f, cands))))
    let rec finitary (V, p, W, ci) =
      let _ =
        if !Global.doubleCheck
        then TypeCheck.typeCheck (I.Null, (V, (I.Uni I.Type)))
        else () in
      let ((V1, s), XsRev) = instEVarsSkip ((V, I.id), p, nil, ci) in
      finitarySplits (XsRev, 1, W, (function | () -> abstract (V1, s)), nil)
    let rec eqExp (Us, Us') = Conv.conv (Us, Us')
    let rec eqInpSpine =
      function
      | (ms, (SClo (S1, s1'), s1), Ss2) ->
          eqInpSpine (ms, (S1, (I.comp (s1', s1))), Ss2)
      | (ms, Ss1, (SClo (S2, s2'), s2)) ->
          eqInpSpine (ms, Ss1, (S2, (I.comp (s2', s2))))
      | (M.Mnil, (I.Nil, s), (I.Nil, s')) -> true__
      | (Mapp (Marg (M.Plus, _), ms'), (App (U, S), s), (App (U', S'), s'))
          ->
          (eqExp ((U, s), (U', s'))) && (eqInpSpine (ms', (S, s), (S', s')))
      | (Mapp (_, ms'), (App (U, S), s), (App (U', S'), s')) ->
          eqInpSpine (ms', (S, s), (S', s'))
    let rec eqInp =
      function
      | (I.Null, k, a, Ss, ms) -> nil
      | (Decl (G', Dec (_, Root (Const a', S'))), k, a, Ss, ms) ->
          if (a = a') && (eqInpSpine (ms, (S', (I.Shift k)), Ss))
          then (::) k eqInp (G', (k + 1), a, Ss, ms)
          else eqInp (G', (k + 1), a, Ss, ms)
      | (Decl (G', Dec (_, Pi _)), k, a, Ss, ms) ->
          eqInp (G', (k + 1), a, Ss, ms)
      | (Decl (G', NDec _), k, a, Ss, ms) -> eqInp (G', (k + 1), a, Ss, ms)
      | (Decl (G', BDec (_, (b, t))), k, a, Ss, ms) ->
          eqInp (G', (k + 1), a, Ss, ms)
    let rec contractionCands =
      function
      | (I.Null, k) -> nil
      | (Decl (G', Dec (_, Root (Const a, S))), k) ->
          (match UniqueTable.modeLookup a with
           | NONE -> contractionCands (G', (k + 1))
           | SOME ms ->
               (match eqInp (G', (k + 1), a, (S, (I.Shift k)), ms) with
                | nil -> contractionCands (G', (k + 1))
                | ns -> (::) (k :: ns) contractionCands (G', (k + 1))))
      | (Decl (G', Dec (_, Pi _)), k) -> contractionCands (G', (k + 1))
      | (Decl (G', NDec _), k) -> contractionCands (G', (k + 1))
      | (Decl (G', BDec (_, (b, t))), k) -> contractionCands (G', (k + 1))
    let rec isolateSplittable =
      function
      | (G, V, 0) -> (G, V)
      | (G, Pi ((D, _), V'), p) ->
          isolateSplittable ((I.Decl (G, D)), V', (p - 1))
    let rec unifyUOutSpine =
      function
      | (ms, (SClo (S1, s1'), s1), Ss2) ->
          unifyUOutSpine (ms, (S1, (I.comp (s1', s1))), Ss2)
      | (ms, Ss1, (SClo (S2, s2'), s2)) ->
          unifyUOutSpine (ms, Ss1, (S2, (I.comp (s2', s2))))
      | (M.Mnil, (I.Nil, s1), (I.Nil, s2)) -> true__
      | (Mapp (Marg (M.Minus1, _), ms'), (App (U1, S1), s1),
         (App (U2, S2), s2)) ->
          (Unify.unifiable (I.Null, (U1, s1), (U2, s2))) &&
            (unifyUOutSpine (ms', (S1, s1), (S2, s2)))
      | (Mapp (_, ms'), (App (U1, S1), s1), (App (U2, S2), s2)) ->
          unifyUOutSpine (ms', (S1, s1), (S2, s2))
    let rec unifyUOutType (V1, V2) =
      unifyUOutTypeW ((Whnf.whnf (V1, I.id)), (Whnf.whnf (V2, I.id)))
    let rec unifyUOutTypeW
      ((Root (Const a1, S1), s1), (Root (Const a2, S2), s2)) =
      let SOME ms = UniqueTable.modeLookup a1 in
      unifyUOutSpine (ms, (S1, s1), (S2, s2))
    let rec unifyUOutEVars
      (SOME (EVar (_, G1, V1, _)), SOME (EVar (_, G2, V2, _))) =
      unifyUOutType (V1, V2)
    let rec unifyUOut2 (XsRev, k1, k2) =
      unifyUOutEVars
        ((List.nth (XsRev, (k1 - 1))), (List.nth (XsRev, (k2 - 1))))
    let rec unifyUOut1 =
      function
      | (XsRev, nil) -> true__
      | (XsRev, k1::nil) -> true__
      | (XsRev, k1::k2::ks) ->
          (unifyUOut2 (XsRev, k1, k2)) && (unifyUOut1 (XsRev, (k2 :: ks)))
    let rec unifyUOut =
      function
      | (XsRev, nil) -> true__
      | (XsRev, ks::kss) ->
          (unifyUOut1 (XsRev, ks)) && (unifyUOut (XsRev, kss))
    let rec contractAll (V, p, ucands) =
      let ((V1, s), XsRev) = instEVars ((V, I.id), p, nil) in
      if unifyUOut (XsRev, ucands) then SOME (abstract (V1, s)) else NONE
    let rec contract (V, p, ci, lab) =
      let (G, _) = isolateSplittable (I.Null, V, p) in
      let ucands = contractionCands (G, 1) in
      let n = List.length ucands in
      let _ =
        if n > 0
        then
          chatter 6
            (function
             | () ->
                 ((^) (((^) "Found " Int.toString n) ^ " contraction ")
                    pluralize (n, "candidate"))
                   ^ "\n")
        else () in
      let VpOpt' =
        if n > 0
        then
          try contractAll (V, p, ucands)
          with
          | Error _ ->
              (chatter 6
                 (function | () -> "Contraction failed due to constraints\n");
               SOME (V, p))
        else SOME (V, p) in
      let _ =
        match VpOpt' with
        | NONE ->
            chatter 6
              (function
               | () -> "Case impossible: conflicting unique outputs\n")
        | SOME (V', p') ->
            chatter 6
              (function | () -> (showPendingGoal (V', p', ci, lab)) ^ "\n") in
      VpOpt'
    let rec findMin ((k, n)::kns) = findMin' ((k, n), kns)
    let rec findMin' =
      function
      | ((k0, n0), nil) -> (k0, n0)
      | ((k0, n0), (k', n')::kns) ->
          if n' < n0
          then findMin' ((k', n'), kns)
          else findMin' ((k0, n0), kns)
    let rec cover (V, p, ((W, ci) as wci), ccs, lab, missing) =
      chatter 6 (function | () -> (showPendingGoal (V, p, ci, lab)) ^ "\n");
      cover' ((contract (V, p, ci, lab)), wci, ccs, lab, missing)
    let rec cover' =
      function
      | (SOME (V, p), ((W, ci) as wci), ccs, lab, missing) ->
          split
            (V, p, (selectCand (match__ (I.Null, V, p, ci, ccs))), wci, ccs,
              lab, missing)
      | (NONE, wci, ccs, lab, missing) ->
          (chatter 6 (function | () -> "Covered\n"); missing)
    let rec split =
      function
      | (V, p, NONE, wci, ccs, lab, missing) ->
          (chatter 6 (function | () -> "Covered\n"); missing)
      | (V, p, SOME nil, ((W, ci) as wci), ccs, lab, missing) ->
          (chatter 6
             (function
              | () -> "No strong candidates---calculating weak candidates\n");
           splitWeak (V, p, (finitary (V, p, W, ci)), wci, ccs, lab, missing))
      | (V, p, SOME ((k, _)::ksn), ((W, ci) as wci), ccs, lab, missing) ->
          (match splitVar (V, p, k, wci) with
           | SOME cases -> covers (cases, wci, ccs, lab, missing)
           | NONE -> split (V, p, (SOME ksn), wci, ccs, lab, missing))
    let rec splitWeak =
      function
      | (V, p, nil, wci, ccs, lab, missing) ->
          (chatter 6
             (function
              | () ->
                  ((^) "No weak candidates---case " labToString lab) ^
                    " not covered\n");
           (V, p) :: missing)
      | (V, p, ksn, wci, ccs, lab, missing) ->
          split (V, p, (SOME ((findMin ksn) :: nil)), wci, ccs, lab, missing)
    let rec covers (cases, wci, ccs, lab, missing) =
      chatter 6
        (function
         | () ->
             ((^) ((^) "Found " Int.toString (List.length cases)) pluralize
                ((List.length cases), " case"))
               ^ "\n");
      covers' (cases, 1, wci, ccs, lab, missing)
    let rec covers' =
      function
      | (nil, n, wci, ccs, lab, missing) ->
          (chatter 6
             (function
              | () ->
                  ((^) "All subcases of " labToString lab) ^ " considered\n");
           missing)
      | ((V, p)::cases', n, wci, ccs, lab, missing) ->
          covers'
            (cases', (n + 1), wci, ccs, lab,
              (cover (V, p, wci, ccs, (Child (lab, n)), missing)))
    let rec constsToTypes =
      function
      | nil -> nil
      | (Const c)::cs' -> (::) (I.constType c) constsToTypes cs'
      | (Def d)::cs' -> (::) (I.constType d) constsToTypes cs'
    let rec createCoverClause =
      function
      | (Decl (G, D), V, p) ->
          createCoverClause (G, (I.Pi ((D, I.Maybe), V)), (p + 1))
      | (I.Null, V, p) -> ((Whnf.normalize (V, I.id)), p)
    let rec createCoverGoal (G, Vs, p, ms) =
      createCoverGoalW (G, (Whnf.whnf Vs), p, ms)
    let rec createCoverGoalW =
      function
      | (G, (Pi ((D1, P1), V2), s), 0, ms) ->
          let D1' = I.decSub (D1, s) in
          let V2' =
            createCoverGoal ((I.Decl (G, D1')), (V2, (I.dot1 s)), 0, ms) in
          I.Pi ((D1', P1), V2')
      | (G, (Pi (((Dec (_, V1) as D), _), V2), s), p, ms) ->
          let X = Whnf.newLoweredEVar (G, (V1, s)) in
          createCoverGoal (G, (V2, (I.Dot ((I.Exp X), s))), (p - 1), ms)
      | (G, (Root ((Const cid as a), S), s), p, ms) ->
          I.Root
            (a,
              (createCoverSpine (G, (S, s), ((I.constType cid), I.id), ms)))
    let rec createCoverSpine =
      function
      | (G, (I.Nil, s), _, M.Mnil) -> I.Nil
      | (G, (App (U1, S2), s), (Pi ((Dec (_, V1), _), V2), s'), Mapp
         (Marg (M.Minus, x), ms')) ->
          let X = createEVar (G, (I.EClo (V1, s'))) in
          let S2' =
            createCoverSpine (G, (S2, s), (V2, (I.Dot ((I.Exp X), s'))), ms') in
          I.App (X, S2')
      | (G, (App (U1, S2), s), (Pi (_, V2), s'), Mapp (_, ms')) ->
          I.App
            ((I.EClo (U1, s)),
              (createCoverSpine
                 (G, (S2, s),
                   (Whnf.whnf (V2, (I.Dot ((I.Exp (I.EClo (U1, s))), s')))),
                   ms')))
      | (G, (SClo (S, s'), s), Vs, ms) ->
          createCoverSpine (G, (S, (I.comp (s', s))), Vs, ms)
    (*****************)
    (* Strengthening *)
    (*****************)
    (* next section adapted from m2/metasyn.fun *)
    (* weaken (G, a) = w'

       Invariant:
       If   a is a type family
       then G |- w' : G'
       and  forall x:A in G'  A subordinate to a
     *)
    (* added next case, probably should not arise *)
    (* Sun Dec 16 10:42:05 2001 -fp !!! *)
    (*
      | weaken (I.Decl (G', D as I.BDec _), a) =
           I.dot1 (weaken (G', a))
      *)
    (* createEVar (G, V) = X[w] where G |- X[w] : V

       Invariant:
       If G |- V : L
       then G |- X[w] : V
    *)
    (* G |- V : L *)
    (* G  |- w  : G'    *)
    (* G' |- iw : G     *)
    (* G' |- X' : V[iw] *)
    (* was I.newEvar (G', I.EClo (V, iw))  Mon Feb 28 14:30:36 2011 --cs *)
    (* G  |- X  : V     *)
    (*************************)
    (* Coverage instructions *)
    (*************************)
    (* Coverage instructions mirror mode spines, but they
       are computed from modes differently for input and output coverage.

       Match  --- call match and generate candidates
       Skip   --- ignore this argument for purposes of coverage checking

       For input coverage, match input (+) and skip ignore ( * ) and output (-).

       For output coverage, skip input (+), and match output (-).
       Ignore arguments ( * ) should be impossible for output coverage
    *)
    (* inCoverInst (ms) = ci
       converts mode spine ms to cover instructions ci for input coverage
    *)
    (* outCoverInst (ms) = ci
       converts mode spine ms to cover instructions ci for output coverage
    *)
    (* this last case should be impossible *)
    (* output coverage only from totality checking, where there can be *)
    (* no undirectional ( * ) arguments *)
    (*
      | outCoverInst (M.Mapp (M.Marg (M.Star, x), ms')) =
          Skip (outCoverInst ms')
      *)
    (***************************)
    (* Printing Coverage Goals *)
    (***************************)
    (* labels for cases for tracing coverage checker *)
    (* ^ *)
    (* lab.n, n >= 1 *)
    (* we pass in the mode spine specifying coverage, but currently ignore it *)
    (* fix to identify existential and universal prefixes *)
    (* p > 0 *)
    (* other cases are impossible by CGoal invariant *)
    (*
       Coverage goals have the form {{G}} {{L}} a @ S
       where G are splittable variables
       and L are local parameters (not splittable)
    *)
    (**********************************************)
    (* Creating the initial input coverage goal ***)
    (**********************************************)
    (* buildSpine n = n; n-1; ...; 1; Nil *)
    (* n > 0 *)
    (* Eta-long invariant violation -kw *)
    (* initCGoal' (a, 0, ., V) = ({x1:V1}...{xn:Vn} a x1...xn, n)
       for |- a : V and V = {x1:V1}...{xn:Vn} type

       Invariants for initCGoal' (a, k, G, V):
       G = {x1:V1}...{xk:Vk}
       V = {xk+1:Vk+1}...{xn:Vn} type
       G |- V : type
    *)
    (* initCGoal (a) = {x1:V1}...{xn:Vn} a x1...xn
       where a : {x1:V1}...{xn:Vn} type
    *)
    (****************)
    (*** Matching ***)
    (****************)
    (* for now, no factoring --- singleton list *)
    (* Equation G |- (U1,s1) = (U2,s2)
       Invariant:
       G |- U1[s1] : V
       G |- U2[s2] : V  for some V

       U1[s1] has no EVars (part of coverage goal)
    *)
    (* Splitting candidates *)
    (* Splitting candidates [k1,...,kl] are indices
       into coverage goal {xn:Vn}...{x1:V1} a M1...Mm, counting right-to-left
    *)
    (* equations to be solved, everything matches so far *)
    (* candidates for splitting, matching fails *)
    (* coverage fails without candidates *)
    (* fail () = Fail
       indicate failure without splitting candidates
     *)
    (* failAdd (k, cands) = cands'
       indicate failure, but add k as splitting candidate
    *)
    (* no longer matches *)
    (* remove duplicates? *)
    (* addEqn (e, cands) = cands'
       indicate possible match if equation e can be solved
    *)
    (* still may match: add equation *)
    (* already failed: ignore new constraints *)
    (* already failed without candidates *)
    (* matchEqns (es) = true
       iff  all equations in es can be simultaneously unified

       Effect: instantiate EVars right-hand sides of equations.
    *)
    (* For some reason, s2 is sometimes not a patSub when it should be *)
    (* explicitly convert if possible *)
    (* Sat Dec  7 20:59:46 2002 -fp *)
    (* was: unifiable (G, Us1, Us2) *)
    (* constraints will be left in this case *)
    (* resolveCands (cands) = cands'
       resolve to one of
         Eqns(nil) - match successful
         Fail      - no match, no candidates
         Cands(ks) - candidates ks
       Effect: instantiate EVars in right-hand sides of equations.
    *)
    (* reversed equations Fri Dec 28 09:39:55 2001 -fp !!! *)
    (* why is this important? --cs !!! *)
    (* collectConstraints (Xs) = constrs
       collect all the constraints that may be attached to EVars Xs

       try simplifying away the constraints in case they are "hard"
       disabled for now to get a truer approximation to operational semantics
    *)
    (* constrs <> nil *)
    (* Constraints.simplify constrs @ *)
    (* at present, do not simplify -fp *)
    (* checkConstraints (cands, (Q, s)) = cands'
       failure if constraints remain in Q[s] which indicates only partial match
       Q[s] is the clause head after matching the coverage goal.

       Invariants: if cands = Eqns (es) then es = nil.
    *)
    (* This ignores LVars, because collectEVars does *)
    (* Why is that OK?  Sun Dec 16 09:01:40 2001 -fp !!! *)
    (* _ = nil *)
    (* constraints remained: Fail without candidates *)
    (* Candidate Lists *)
    (*
       Candidate lists record constructors and candidates for each
       constructors or indicate that the coverage goal is matched.
    *)
    (* covered---no candidates *)
    (* cands1,..., candsn *)
    (* addKs (cands, klist) = klist'
       add new constructor to candidate list
    *)
    (* matchExp (G, d, (U1, s1), (U2, s2), cands) = cands'
       matches U1[s1] (part of coverage goal)
       against U2[s2] (part of clause head)
       adds new candidates to cands to return cands'
         this could collapse to Fail,
         postponed equations Eqns(es),
         or candidates Cands(ks)
       d is depth, k <= d means local variable, k > d means coverage variable

       Invariants:
       G |- U1[s1] : V
       G |- U2[s2] : V  for some V
       G = Gc, Gl where d = |Gl|
    *)
    (* Note: I.Proj occurring here will always have the form
              I.Proj (I.Bidx (k), i) *)
    (* No skolem constants, foreign constants, FVars *)
    (* k1 is coverage variable, new candidate *)
    (* otherwise fail with no candidates *)
    (* fail with no candidates *)
    (* because of strictness *)
    (* k1 is coverage variable, new candidate *)
    (* otherwise fail with no candidates *)
    (* was: t2 in prev line, July 22, 2010 -fp -cs *)
    (* instantiate instead of postponing because LVars are *)
    (* only instantiated to Bidx which are rigid *)
    (* Sun Jan  5 12:03:13 2003 -fp *)
    (* handled in above two cases now *)
    (*
            | (I.Proj (b1, i1), I.Proj (b2, i2)) =>
               if (i1 = i2) then
                 matchSpine (G, d, (S1, s1), (S2, s2),
                             matchBlock (G, d, b1, b2, cands))
               else fail ("block projection / block projection clash")
            *)
    (* k1 is splittable, new candidate *)
    (* otherwise fail with no candidates *)
    (* no other cases should be possible *)
    (* eta-expand *)
    (* eta-expand *)
    (* next 3 cases are only for output coverage *)
    (* not needed since we skip input arguments for output coverage *)
    (* see comments on CoverInst -fp Fri Dec 21 20:58:55 2001 !!! *)
    (*
      | matchExpW (G, d, (I.Pi ((D1, _), V1), s1), (I.Pi ((D2, _), V2), s2), cands) =
        let
          val cands' = matchDec (G, d, (D1, s1), (D2, s2), cands)
        in
          matchExp (I.Decl (G, D1), d+1, (V1, I.dot1 s1), (V2, I.dot1 s2), cands')
        end
      | matchExpW (G, d, (I.Pi _, _), _, cands) = fail ()
      | matchExpW (G, d, _, (I.Pi _, _), cands) = fail ()
      *)
    (* nothing else should be possible, by invariants *)
    (* No I.Uni, I.FgnExp, and no I.Redex by whnf *)
    (* BDec should be impossible here *)
    (* matchBlock now unfolded into the first case of matchExpW *)
    (* Sun Jan  5 12:02:49 2003 -fp *)
    (*
    and matchBlock (G, d, I.Bidx(k), I.Bidx(k'), cands) =
        if (k = k') then cands
          else fail ("block index / block index clash")
      | matchBlock (G, d, B1 as I.Bidx(k), I.LVar (r2, I.Shift(k'), (l2, t2)), cands) =
         Updated LVar --cs Sun Dec  1 06:24:41 2002 *)
    (* else if k < k' then raise Bind *)
    (* k >= k' by invariant  Sat Dec  7 22:00:41 2002 -fp *)
    (* instantiate if matching is successful *)
    (* val _ = print (candsToString (cands2) ^ "\n") *)
    (* instantiate, instead of postponing because *)
    (* LVars are only instantiated to Bidx's which are rigid *)
    (* !!!BUG!!! r2 and B1 make sense in different contexts *)
    (* fixed by k-k' Sat Dec  7 21:12:57 2002 -fp *)
    (* by invariant *)
    (* matchTop (G, (a @ S1, s1), (a @ S2, s2), ci) = cands
       matches S1[s1] (spine of coverage goal)
       against S2[s2] (spine of clause head)
       skipping over `skip' arguments in cover instructions

       Invariants:
       G |- a @ S1[s1] : type
       G |- a @ S2[s2] : type
       G contains coverage variables,
       S1[s1] contains no EVars
       cover instructions ci matche S1 and S2
    *)
    (* unify spines, skipping output and ignore arguments in modeSpine *)
    (* fails, with no candidates since type families don't match *)
    (* this case can only arise in output coverage *)
    (* we do not match D1 and D2, since D1 is always an instance of D2 *)
    (* and no splittable variables should be suggested here *)
    (* Sat Dec 22 23:53:44 2001 -fp !!! *)
    (* an argument that must be covered (Match) *)
    (* an argument that need not be covered (Skip) *)
    (* matchClause (G, (a @ S1, s1), V, ci) = cands
       as in matchTop, but r is clause
       NOTE: Simply use constant type for more robustness (see below)
    *)
    (* changed to use subordination and strengthening here *)
    (* Sun Dec 16 10:39:34 2001 -fp *)
    (* val X1 = createEVar (G, I.EClo (V1, s)) *)
    (* changed back --- no effect *)
    (* was val X1 = I.newEVar (G, I.EClo (V1, s)) Mon Feb 28 14:37:22 2011 -cs *)
    (* was: I.Null instead of G in line above Wed Nov 21 16:40:40 2001 *)
    (* matchSig (G, (a @ S, s), ccs, ci, klist) = klist'
       match coverage goal {{G}} a @ S[s]
       against each coverage clause V in ccs,
       adding one new list cand for each V to klist to obtain klist'

       Invariants:
       G |- a @ S[s] : type
       V consists of clauses with target type a @ S'
       ci matches S
       klist <> Covered
    *)
    (* matchSig' (G, (a @ S, s), ccs, ci, klist) = klist'
       as matchSig, but check if coverage goal {{G}} a @ S[s] is already matched
    *)
    (* already covered: return *)
    (* not yet covered: continue to search *)
    (* matchBlocks (G, s', piDecs, V, k, i, ci, klist) = klist'
       Invariants:
       G |- s' : Gsome
       Gsome |- piDecs : ctx
       G |- V : type
       G_k = (Gsome, D1...D(i-1) piDecs)
     *)
    (* klist <> Covered *)
    (* matchCtx (G, s', G', V, k, ci, klist) = klist'
       Invariants:
       G |- s' : G'
       G |- V : type
       s' o ^ = ^k
       ci matches for for V = a @ S
       klist <> Covered accumulates mode spines
    *)
    (* will always fail for input coverage *)
    (*  G'', V' |- ^ : G''
              G |- s' : G'', V'
          *)
    (*  G |- ^ o s' : G'' *)
    (* G'' |- s : Gsome,
             G |- s'' : G''
             G |- s o s'' : Gsome
             Gsome |- piDecs : ctx
          *)
    (* as matchClause *)
    (* p > 0 *)
    (* was val X1 = I.newEVar (G, I.EClo (V1', s')) Mon Feb 28 14:38:21 2011 -cs *)
    (* match (., V, p, ci, I/O(ccs)) = klist
       matching coverage goal {{G}} V against coverage clauses Vi in ccs
       yields candidates klist
       no local assumptions
       Invariants:
       V = {{G}} {{L}} a @ S where |G| = p
       cover instructions ci match S
       G |- V : type
    *)
    (************************************)
    (*** Selecting Splitting Variable ***)
    (************************************)
    (* insert (k, ksn) = ksn'
       ksn is ordered list of ks (smallest index first) with multiplicities
    *)
    (* join (ks, ksn) = ksn'
       ksn is as in function insert
    *)
    (* selectCand (klist) = ksnOpt
       where ksOpt is an indication of coverage (NONE)
       or a list of candidates with multiplicities

       Simple heuristic: select last splitting candidate from last clause tried
       This will never pick an index variable unless necessary.
    *)
    (* success: case is covered! *)
    (* failure: case G,V is not covered! *)
    (* local failure (clash) and no candidates *)
    (* local failure but no candidates *)
    (* found candidates ks <> nil *)
    (*****************)
    (*** Splitting ***)
    (*****************)
    (* In a coverage goal {{G}} {{L}} a @ S we instantiate each
       declaration in G with a new EVar, then split one of these variables,
       then abstract to obtain a new coverage goal {{G'}} {{L'}} a @ S'
    *)
    (* instEVars ({x1:V1}...{xp:Vp} V, p, nil) = (V[s], [X1,...,Xn])
       where . |- s : {x1:V1}...{xp:Vp}
       and s = Xp...X1.id, all Xi are new EVars
    *)
    (* p > 0 *)
    (* all EVars are global *)
    (* was  val X1 = I.newEVar (I.Null, I.EClo (V1, s))  all EVars are global *)
    (* G0 |- t : Gsome *)
    (* . |- s : G0 *)
    (* p > 0 *)
    (* new -fp Sun Dec  1 20:58:06 2002 *)
    (* new -cs  Sun Dec  1 06:27:57 2002 *)
    (* caseList is a list of possibilities for a variables
       to be split.  Maintained as a mutable reference so it
       can be updated in the success continuation.
    *)
    (* createEVarSpine (G, (V, s)) = (S', (V', s'))

       Invariant:
       If   G |- s : G1   and  G1 |- V = Pi {V1 .. Vn}. W : L
       and  G1, V1 .. Vn |- W atomic
       then G |- s' : G2  and  G2 |- V' : L
       and  S = X1; ...; Xn; Nil
       and  G |- W [1.2...n. s o ^n] = V' [sjfh']
       and  G |- S : V [s] >  V' [s']
    *)
    (* changed to use createEVar? *)
    (* Sun Dec 16 10:36:59 2001 -fp *)
    (* s = id *)
    (* G |- V1[s] : L *)
    (* Uni or other cases should be impossible *)
    (* createAtomConst (G, c) = (U', (V', s'))

       Invariant:
       If   S |- c : Pi {V1 .. Vn}. V
       then . |- U' = c @ (X1; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
    (* mod: m2/metasyn.fun allows skolem constants *)
    (* createAtomBVar (G, k) = (U', (V', s'))

       Invariant:
       If   G |- k : Pi {V1 .. Vn}. V
       then . |- U' = k @ (Xn; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
    (* end m2/metasyn.fun *)
    (* createAtomProj (G, #i(l), (V, s)) = (U', (V', s'))

       Invariant:
       If   G |- #i(l) : Pi {V1 .. Vn}. Va
       and  G |- Pi {V1..Vn}. Va = V[s] : type
       then . |- U' = #i(l) @ (X1; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
    (* createEVarSub G' = s

       Invariant:
       If   . |- G' ctx
       then . |- s : G' and s instantiates each x:A with an EVar . |- X : A

       Update: Always use empty context. Sat Dec  8 13:19:58 2001 -fp
    *)
    (* was   val V' = I.EClo (V, s)
                   val X = I.newEVar (I.Null, V') Mon Feb 28 15:32:09 2011 --cs *)
    (* hack *)
    (* blockCases (G, Vs, B, (Gsome, piDecs), sc) =

       If G |- V[s] : type
          . |- Gsome ctx and Gsome |- piDecs decList
       then sc is called for any x:A in piDecs such thtat
            G |- V[s] = A[t] : type
            where t instantiates variable in Gsome with new EVars
    *)
    (* . |- t : Gsome *)
    (* was: the above, using t' for t below *)
    (*  BUG. Breach in the invariant:
                         G |- sk : .
                         . |- t: Gsome
                         G <> .

                         replace t by t' in I.newLVar (sk, (cid, t))
                      --cs Fri Jan  3 11:07:41 2003 *)
    (* G |- t' : Gsome *)
    (* G |- t : G' and G' |- ({_:V'},piDecs) decList *)
    (* so G |- V'[t'] : type *)
    (* will trail *)
    (* will trail *)
    (* will trail *)
    (* splitEVar (X, W, sc) = ()

       calls sc () for all cases, after instantiation of X
       W are the currently possible worlds
    *)
    (* was
   fun lowerSplit (G, Vs, W, sc, print) = lowerSplitW (G, Whnf.whnf Vs, W, sc, print)
    and lowerSplitW (G, Vs as (I.Root (I.Const a, _), s), W, sc, pr) =
        let
        val _ = print ("Consider P cases for "  ^ Print.expToString (G, I.EClo Vs) ^ "\n")
val _ = pr () *)
    (* will trail *)
    (*        val _ = print ("Consider W cases for "  ^ Print.expToString (G, I.EClo Vs) ^ "\n")
val _ = pr () *)
    (* will trail *)
    (*        val _ = print ("Consider C cases for "  ^ Print.expToString (G, I.EClo Vs) ^ "\n") *)
    (* will trail *)
    (* GX = I.Null *)
    (* abstract (V, s) = V'
       where V' = {{G}} Vs' and G abstracts over all EVars in V[s]
       in arbitrary order respecting dependency

       Invariants: . |- V[s] : type
       Effect: may raise Constraints.Error (constrs)
     *)
    (* splitVar ({{G}} V, p, k, W) = SOME [{{G1}} V1 ,..., {{Gn}} Vn]
                                  or NONE
       where {{Gi}} Vi are new coverage goals obtained by
       splitting kth variable in G, counting right-to-left.

       returns NONE if splitting variable k fails because of constraints

       W are the worlds defined for current predicate

       Invariants:
       |G| = p
       k <= |G|
       G |- V : type
       {{Gi}} Vi cover {{G}} V
    *)
    (* split on k'th variable, counting from innermost *)
    (* may raise Constraints.Error *)
    (* Constraints.Error could be raised by abstract *)
    (**********************)
    (* Finitary Splitting *)
    (**********************)
    (*
       A splittable variable X : V is called finitary
       if there are finitely many alternatives for V.
       This means there are finitely many (including 0)
       constructors (possibly including local variables) such that
       all free variables in the argument are not recursive
       with the target type of V.

       Splitting such variables can never lead to non-termination.
    *)
    (* Stolen from abstract.fun *)
    (* foreign expression probably should not occur *)
    (* but if they do, variable occurrences don't count *)
    (* occursInExp (k, Whnf.normalize (#toInternal(ops) (), I.id)) *)
    (* no case for Redex, EVar, EClo *)
    (* no case for SClo *)
    (* occursInMatchPos (k, U, ci) = true
       if k occur in U in a matchable position according to the coverage
       instructions ci
    *)
    (* instEVarsSkip ({x1:V1}...{xp:Vp} V, p, nil, ci) = (V[s], [X1,...,Xn])
       where . |- s : {x1:V1}...{xp:Vp}
       and s = Xp...X1.id, all Xi are new EVars that actually occur in a "Match" argument
       and ci are the coverage instructions (Match or Skip) for the target type of V
    *)
    (* p > 0 *)
    (* all EVars are global *)
    (* was val X1 = I.newEVar (I.Null, I.EClo (V1, s))  all EVars are global *)
    (* G0 |- t : Gsome *)
    (* . |- s : G0 *)
    (* p > 0 *)
    (* -fp Sun Dec  1 21:09:38 2002 *)
    (* -cs Sun Dec  1 06:30:59 2002 *)
    (* if contraints remain, consider recursive and thereby unsplittable *)
    (* recursive X = true
       iff the instantiation of X : {{G}} a @ S contains an
           EVar Y : {{G'}} b @ S such that a <|= b

       This means there is no guarantee that X : {{G}} a @ S has only
       a finite number of instances
    *)
    (* GX = I.Null*)
    (* is this always true? --cs!!!*)
    (* LVars are ignored here.  OK because never splittable? *)
    (* Sat Dec 15 22:42:10 2001 -fp !!! *)
    (* finitary1 (X, k, W, f, cands)
        = ((k, n)::cands) if X is finitary with n possibilities
        = cands if X is not finitary
    *)
    (* The function f has been added to ensure that k is splittable without
       constraints.   In the previous version, this check was not performed.
       nat : type.
       z : nat.
       s : nat -> nat.

       eqz :  nat -> type.
       eqz_z : eqz z.

       unit : type.
       * : unit.

       test : {f : unit -> nat} eqz (f * ) -> type.
       %worlds () (test _ _).
       %covers test +F +Q.  %% loops!
        Counterexample due to Andrzej.  Fix due to Adam.
        Mon Oct 15 15:08:25 2007 --cs
    *)
    (* was Mon Feb 28 15:29:36 2011 -cs
    fun finitary1 (X as I.EVar(r, I.Null, VX, _), k, W, f, cands, print) =
        ( resetCount () ;
          chatter 7 (fn () => "Trying " ^ Print.expToString (I.Null, X) ^ " : "
                     ^ Print.expToString (I.Null, VX) ^ ".\n") ;
          ( splitEVar (X, W, fn () => (f (); if recursive X
                                        then raise NotFinitary
                                      else incCount ()), print) ;
            chatter 7 (fn () => "Finitary with " ^ Int.toString (getCount ()) ^ " candidates.\n");

            (k, getCount ())::cands )
           handle NotFinitary => ( chatter 7 (fn () => "Not finitary.\n");
                                   cands )
                 | Constraints.Error (constrs) =>
                                 ( chatter 7 (fn () => "Inactive finitary split.\n");
                                   cands )
        )
    *)
    (* finitarySplits (XsRev, k, W, cands) = [(k1,n1),...,(km,nm)]@cands
       where all ki are finitary with ni possibilities for X(i+k)
    *)
    (* parameter blocks can never be split *)
    (* finitary ({{G}} V, p, W) = [(k1,n1),...,(km,nm)]
       where ki are indices of splittable variables in G with ni possibilities
       and |G| = p
       and ci are the coverage instructions for the target type of V
    *)
    (***********************************)
    (* Contraction based on uniqueness *)
    (***********************************)
    (* eqExp (U[s], U'[s']) = true iff G |- U[s] == U'[s'] : V
       Invariants:
         G |- U[s] : V
         G |- U'[s'] : V
         U[s], U'[s'] contain no EVars
       Note that the typing invariant is satisfied because
       input arguments can only depend on other input arguments,
       but not undetermined or output arguments.
       Similar remarks apply to functions below
    *)
    (* eqInpSpine (ms, S1[s1], S2[s2]) = true
       iff U1[s1] == U2[s2] for all input (+) arguments in S1, S2
       according to uniqueness mode spine ms
       Invariants: typing as in eqExp, ms ~ S1, ms ~ S2
    *)
    (* ignore Star, Minus, Minus1 *)
    (* other cases should be impossible since spines must match *)
    (* eqInp (G, k, a, S[s], ms) = [k1+k,...,kn+k]
       where k1,...,kn are the deBruijn indices of those declarations
       ki:a @ Si in such that G0 |- Si[^ki+k] == S[s] on all input arguments
       according to mode spine ms.
       Here G = ...kn:a @ Sn, ..., k1:a @ S1, ...
    *)
    (* defined type families disallowed here *)
    (* other cases should be impossible *)
    (* contractionCands (G, k) = [[k11,...,k1{n1}],...,[km1,...,km{nm}]]
       where each [kj1,...,kj{nj}] are deBruijn indices in G (counting from right)
       such that kji:aj @ Sji ... kj{nj}:aj @ Sj{nj} and
       Sji...Sj{nj} agree on their input arguments according to the
       uniqueness mode spine for aj
    *)
    (* defined type families disallowed here *)
    (* using only one uniqueness declaration per type family *)
    (* ignore Pi --- contraction cands unclear *)
    (* ignore blocks --- contraction cands unclear *)
    (* isolateSplittable ((G0, {{G1}}V, p) = ((G0@G1), V) where |G1| = p
       This isolates the splittable variable G1@G1 from an old-style
       coverage goal ({{G}}V, p)
    *)
    (* unifyUOutSpine (ms, S1[s1], S2[s2]) = true
       iff U1[s1] == U2[s2] for all unique output (-1) arguments in S1, S2
       according to uniqueness mode spine ms
       Invariants: the input arguments in S1[s1] and S2[s2] must be known
          to be equal, ms ~ S1, ms ~ S2
       Effect: EVars in S1[s1], S2[s2] are instantianted, both upon
          failure and success
    *)
    (* will have effect! *)
    (* if mode = + already equal by invariant; otherwise ignore *)
    (* Nil/App or App/Nil cannot occur by invariants *)
    (* unifyUOuttype (a @ S1, a @ S2) = true
       iff S1 and S2 unify on all unique output (-1) arguments in S1, S2
       according to uniqueness mode declaration for a (both args must have same a)
       Invariants: the input args in S1, S2 must be known to be equal
          and a must have a uniqueness mode
       Effect: Evars may be instantiated by unification
    *)
    (* a1 = a2 by invariant *)
    (* must succeed by invariant *)
    (* must be constant-headed roots by invariant *)
    (* unifyUOutEvars (X1, X2) = true
       iff . |- X1 : a @ S1, . |- X2 : a @ S2 and the unique output arguments
       in V1 and V2 unify
       Invariants: the input args in S1, S2, must be known to be equal
         Both types start with the same a, a must have a uniqueness mode
       Effect: Evars may be instantiated by unification
    *)
    (* G1 = G2 = Null *)
    (* unifyUOut2 ([X1,...,Xp], k1, k2) = (see unifyOutEvars (X{k1}, X{k2})) *)
    (* unifyOut1 ([X1,...,Xp], [k1, k2, ..., kn] = true
       if X{k1} "==" X{k2} "==" ... "==" X{kn} according to unifyOutEvars
    *)
    (* unifyOut ([X1,...,Xp], [[k11,...,k1{n1}],...,[km1,...,km{nm}]]) = true
       if unifyOut1 ([X1,...,Xp], [kj1,...,kj{nj}]) for each j
    *)
    (* contractAll ({{G}}V, p, ucands) = SOME(V',p')
       iff (V',p') is the result of contracting unique output arguments
           according to contraction candidates ucands
           of variables in G where all input arguments agree
       returns NONE if unique output arguments are non-unifiable
       may be the identity if output arguments are already identity
          or unsolvable constraints during contraction
       Invariants: p = |G| (G contains the splittable variables)
    *)
    (* as in splitVar *)
    (* as in splitVar, may raise Constraints.Error *)
    (* unique outputs not simultaneously unifiable *)
    (* contract ({{G}}V0, p, ci, lab) = SOME(V',p')
       iff (V',p') is the result of contracting unique output arguments
           of variables in G where all input arguments agree
       returns NONE if unique output arguments are non-unifiable
       may be the identity if output arguments are already identity
          or unsolvable constraints during contraction
       ci and lab are used for printing
       Invariants: p = |G| (G contains the splittable variables)
    *)
    (* ignore body of coverage goal *)
    (* no progress if constraints remain *)
    (* no candidates, no progress *)
    (*********************)
    (* Coverage Checking *)
    (*********************)
    (* findMin ((k1,n1),...,(km,nm)) = (ki,ni)
       where ni is the minimum among the n1,...,nm
       Invariant: m >= 1
    *)
    (* need to improve tracing with higher chatter levels *)
    (* ccs = covering clauses *)
    (* cover (V, p, (W, ci), ccs, lab, missing) = missing'
       covers ([(V1,p1),...,(Vi,pi)], (W, ci), ccs, missing) = missing'

       check if Match arguments (+ for input, - for output) in V or all Vi, respectively,
       are covered by clauses ccs, adding omitted cases to missing to yield missing'.

       V = {{G}} {{L}} a @ S where |G| = p and G contains the splittable
       variables while L contains the local parameters

       W are the worlds for type family a
       ci are the cover instructions matching S

       lab is the label for the current goal for tracing purposes
    *)
    (* V is covered by unique output inconsistency *)
    (* V is covered: return missing patterns from other cases *)
    (* no strong candidates: check for finitary splitting candidates *)
    (* some candidates: split first candidate, ignoring multiplicities *)
    (* candidates are in reverse order, so non-index candidates are split first *)
    (* splitVar shows splitting as it happens *)
    (* splitting variable k generated constraints *)
    (* try other candidates *)
    (* ksn <> nil *)
    (* commit to the minimal candidate, since no constraints can arise *)
    (******************)
    (* Input Coverage *)
    (******************)
    (* constsToTypes [c1,...,cn] = [V1,...,Vn] where ci:Vi.
       Generates coverage clauses from signature.
    *)
    (*******************)
    (* Output Coverage *)
    (*******************)
    (* createCoverClause (G, V, 0) = ({{G}} V, |G|)
       where {{G}} V is in NF
    *)
    (* createCoverGoal (., ({{G}} {{GL}} a @ S, s), p, ms) = V' with |G| = p
       createCoverGoal (GL, (a @ S, s), 0, ms) = a @ S'
       createCoverSpine ((S, s), (V', s'), ms) = S'

       where all variables in G are replaced by new EVars in V to yield V'
       and output arguments in S are replaced by new EVars in V to yield V'

       G are the externally quantified variables
       GL are the locally introduced parameter for the current subgoal a @ S

       Invariants: . |- ({{G}} {{GL}} a @ S)[s] : type
                   |G| = p
                   ms matches S
                   . | S[s] : V'[s'] > type
                   . |- V'[s'] : type
    *)
    (* p > 0, G = I.Null *)
    (* was  val X = I.newEVar (G, I.EClo (V1, s))  Mon Feb 28 15:33:52 2011 -cs *)
    (* s = id, p >= 0 *)
    (* replace output argument by new variable *)
    (* strengthen G based on subordination *)
    (* leave input ( + ) arguments as they are, ignore ( * ) impossible *)
    let rec checkNoDef a =
      match I.sgnLookup a with
      | ConDef _ ->
          raise
            (Error
               (((^) "Coverage checking " N.qidToString (N.constQid a)) ^
                  ":\ntype family must not be defined."))
      | _ -> ()
    (* checkCovers (a, ms) = ()
       checks coverage for type family a with respect to mode spine ms
       Effect: raises Error (msg) otherwise
    *)
    let rec checkCovers (a, ms) =
      let _ =
        chatter 4
          (function
           | () ->
               ((^) "Input coverage checking family " N.qidToString
                  (N.constQid a))
                 ^ "\n") in
      let _ = checkNoDef a in
      let _ =
        try Subordinate.checkNoDef a
        with
        | Error msg ->
            raise
              (Error
                 ((((^) "Coverage checking " N.qidToString (N.constQid a)) ^
                     ":\n")
                    ^ msg)) in
      let (V0, p) = initCGoal a in
      let _ =
        if !Global.doubleCheck
        then TypeCheck.typeCheck (I.Null, (V0, (I.Uni I.Type)))
        else () in
      let _ = CSManager.reset () in
      let cIn = inCoverInst ms in
      let cs = Index.lookup a in
      let ccs = constsToTypes cs in
      let W = W.lookup a in
      let V0 = createCoverGoal (I.Null, (V0, I.id), p, ms) in
      let (V0, p) = abstract (V0, I.id) in
      let missing = cover (V0, p, (W, cIn), (Input ccs), Top, nil) in
      let _ =
        ((match missing with
          | nil -> ()
          | _::_ ->
              raise
                (Error
                   (((^) "Coverage error --- missing cases:\n"
                       missingToString (missing, ms))
                      ^ "\n")))
        (* all cases covered *)) in
      ((())
        (* convert mode spine to cover instructions *)
        (* lookup constants defining a *)(* calculate covering clauses *)
        (* world declarations for a; must be defined *)
        (* replace output by new EVars *)(* abstract will double-check *))
    (* checkOut (G, (V, s)) = ()
       checks if the most general goal V' is locally output-covered by V
       Effect: raises Error (msg) otherwise
    *)
    let rec checkOut (G, (V, s)) =
      let a = I.targetFam V in
      let SOME ms = ModeTable.modeLookup a in
      let cOut = outCoverInst ms in
      let (V', q) = createCoverClause (G, (I.EClo (V, s)), 0) in
      let _ =
        if !Global.doubleCheck
        then TypeCheck.typeCheck (I.Null, (V', (I.Uni I.Type)))
        else () in
      let V0 = createCoverGoal (I.Null, (V', I.id), q, ms) in
      let (V0', p) = abstract (V0, I.id) in
      let W = W.lookup a in
      let missing = cover (V0', p, (W, cOut), (Output (V', q)), Top, nil) in
      let _ =
        match missing with
        | nil -> ()
        | _::_ ->
            raise
              (Error
                 (((^) "Output coverage error --- missing cases:\n"
                     missingToString (missing, ms))
                    ^ "\n")) in
      ((())
        (* must be defined and well-moded *)(* determine cover instructions *)
        (* abstract all variables in G *)(* replace output by new EVars *)
        (* abstract will double-check *))
    (**********************************************)
    (* New code for coverage checking of Tomega   *)
    (* Started Sun Nov 24 11:02:25 2002  -fp      *)
    (* First version Tue Nov 26 19:29:12 2002 -fp *)
    (**********************************************)
    (* cg = CGoal (G, S)  with G |- S : {{G'}} type *)
    type __CoverGoal =
      | CGoal of (I.dctx * I.__Spine) 
    (* cc = CClause (Gi, Si) with  Gi |- Si : {{G}} type *)
    type __CoverClause =
      | CClause of (I.dctx * I.__Spine) 
    let rec formatCGoal (CGoal (G, S)) =
      let _ = N.varReset I.Null in
      F.HVbox
        ((@) [Print.formatCtx (I.Null, G);
             F.Break;
             F.Break;
             F.String "|-";
             F.Space]
           Print.formatSpine (G, S))
    let rec showPendingCGoal (CGoal (G, S), lab) =
      F.makestring_fmt
        (F.Hbox
           [F.String (labToString lab);
           F.Space;
           F.String "?- ";
           formatCGoal (CGoal (G, S));
           F.String "."])
    let rec showCClause (CClause (G, S)) =
      let _ = N.varReset I.Null in
      F.makestring_fmt
        (F.HVbox ((@) [F.String "!- "] Print.formatSpine (G, S)))
    let rec showSplitVar (CGoal (G, S), k) =
      let _ = N.varReset I.Null in
      let Dec (SOME x, _) = I.ctxLookup (G, k) in
      (^) (("Split " ^ x) ^ " in ") F.makestring_fmt
        (F.HVbox (Print.formatSpine (G, S)))
    (* newEVarSubst (G, G') = s
       Invariant:   If G = xn:Vn,...,x1:V1
                  then s = X1...Xn.^k
                     G |- s : G'
    *)
    let rec newEVarSubst =
      function
      | (G, I.Null) -> I.Shift (I.ctxLength G)
      | (G, Decl (G', (Dec (_, V) as D))) ->
          let s' = newEVarSubst (G, G') in
          let X = Whnf.newLoweredEVar (G, (V, s')) in
          ((I.Dot ((I.Exp X), s'))
            (* was val V' = I.EClo (V, s')
                 val X = I.newEVar (G, V') Mon Feb 28 15:34:31 2011 -cs *))
      | (G, Decl (G', (NDec _ as D))) ->
          let s' = newEVarSubst (G, G') in I.Dot (I.Undef, s')
      | (G, Decl (G', (BDec (_, (b, t)) as D))) ->
          let s' = newEVarSubst (G, G') in
          let L1 = I.newLVar (s', (b, t)) in ((I.Dot ((I.Block L1), s'))
            (* was  val L1 = I.newLVar (I.Shift(0), (b, I.comp(t, s')))
             --cs Fri Jul 23 16:39:27 2010 *)
            (* -cs Fri Jul 23 16:35:04 2010  FPCHECK *)
            (* L : Delta[t][G'] *)(* G |- s : G'  G |- L[s'] : V[s]
             G |- (L[s'].s : G', V *)
            (* -fp Sun Dec  1 21:10:45 2002 *)(* -cs Sun Dec  1 06:31:23 2002 *))
    (* ADec should be impossible *)
    (* checkConstraints (G, Si[ti], cands) = cands'
       failure if constraints remain in Q[s] which indicates only partial match
       Q[s] is the clause head after matching the coverage goal.

       Invariants: if cands = Eqns (es) then es = nil.
    *)
    (* This ignores LVars, because collectEVars does *)
    (* Why is that OK?  Sun Dec 16 09:01:40 2001 -fp !!! *)
    let rec checkConstraints =
      function
      | (G, (Si, ti), Cands ks) -> Cands ks
      | (G, (Si, ti), Fail) -> Fail
      | (G, (Si, ti), Eqns _) ->
          let Xs = Abstract.collectEVarsSpine (G, (Si, ti), nil) in
          let constrs = collectConstraints Xs in
          (((match constrs with
             | nil -> Eqns nil
             | _ -> fail "Remaining constraints"))
            (* constraints remained: Fail without candidates *))
      (* _ = nil *)
    (* matchClause (cg, (Si, ti)) = klist
       matching coverage goal cg against instantiated coverage clause Si[ti]
       yields splitting candidates klist
    *)
    let rec matchClause (CGoal (G, S), (Si, ti)) =
      let cands1 = matchSpine (G, 0, (S, I.id), (Si, ti), (Eqns nil)) in
      let cands2 = resolveCands cands1 in
      let cands3 = checkConstraints (G, (Si, ti), cands2) in cands3
    (* matchClauses (cg, ccs, klist) = klist'
       as in match, with accumulator argument klist
    *)
    let rec matchClauses =
      function
      | (cg, nil, klist) -> klist
      | ((CGoal (G, S) as cg), (CClause (Gi, Si))::ccs, klist) ->
          let ti = newEVarSubst (G, Gi) in
          let cands =
            CSManager.trail (function | () -> matchClause (cg, (Si, ti))) in
          ((matchClauses' (cg, ccs, (addKs (cands, klist))))
            (* G |- ti : Gi *))
    let rec matchClauses' =
      function
      | (cg, ccs, Covered) -> Covered
      | (cg, ccs, (CandList _ as klist)) -> matchClauses (cg, ccs, klist)
    (* match (cg, ccs) = klist
       matching coverage goal cg against coverage clauses ccs
       yields candidates klist
    *)
    let rec match__ (CGoal (G, S), ccs) =
      matchClauses ((CGoal (G, S)), ccs, (CandList nil))
    (* abstractSpine (S, s) = CGoal (G, S')
       Invariant: G abstracts all EVars in S[s]
       G |- S' : {{G'}}type
    *)
    let rec abstractSpine (S, s) =
      let (G', S') = Abstract.abstractSpine (S, s) in
      let namedG' = N.ctxName G' in
      let _ =
        if !Global.doubleCheck
        then ((TypeCheck.typeCheckCtx namedG')
          (* TypeCheck.typeCheckSpine (namedG', S') *))
        else () in
      ((CGoal (namedG', S'))(* for printing purposes *))
    (* kthSub (X1...Xn.^0, k) = Xk
       Invariant: 1 <= k <= n
       Xi are either EVars or to be ignored
    *)
    let rec kthSub =
      function
      | (Dot (Exp (X), s), 1) -> X
      | (Dot (_, s), k) -> kthSub (s, (k - 1))
    (* subToXsRev (X1...Xn.^0) = [Xiopt,...,Xnopt]
       Invariant: Xi are either EVars (translate to SOME(Xi))
                  or not (translate to NONE)
    *)
    let rec subToXsRev =
      function
      | Shift 0 -> nil
      | Dot (Exp (X), s) -> (::) (SOME X) subToXsRev s
      | Dot (_, s) -> (::) NONE subToXsRev s(* n = 0 *)
    (* caseList is a list of possibilities for a variables
       to be split.  Maintained as a mutable reference so it
       can be updated in the success continuation.
    *)
    let (caseList : __CoverGoal list ref) = ref nil
    let rec resetCases () = caseList := nil
    let rec addCase cg = (!) ((::) (caseList := cg)) caseList
    let rec getCases () = !caseList
    (* splitVar (CGoal(G, S), k, w) = SOME [cg1,...,cgn]
                                  or NONE
       where cgi are new coverage goals obtained by
       splitting kth variable in G, counting right-to-left.

       returns NONE if splitting variable k fails because of constraints

       w are the worlds defined for current predicate

       Invariants:
       k <= |G|
       G |- S : {{G'}} type
       cgi cover cg
    *)
    let rec splitVar ((CGoal (G, S) as cg), k, w) =
      ((try
          let _ = chatter 6 (function | () -> (showSplitVar (cg, k)) ^ "\n") in
          let s = newEVarSubst (I.Null, G) in
          let X = kthSub (s, k) in
          let _ = resetCases () in
          let _ =
            splitEVar
              (X, w, (function | () -> addCase (abstractSpine (S, s)))) in
          ((SOME (getCases ()))
            (* for splitting, EVars are always global *)
            (* G = xn:V1,...,x1:Vn *)(* s = X1....Xn.^0, where . |- s : G *)
            (* starts with k = 1 (a la deBruijn) *))
        with
        | Error constrs ->
            (chatter 7
               (function
                | () ->
                    ((^) "Inactive split:\n" Print.cnstrsToString constrs) ^
                      "\n");
             NONE))
      (* Constraints.Error could be raised by abstract *))
    (* finitary (CGoal (G, S), W) = [(k1,n1),...,(km,nm)]
       where ki are indices of splittable variables in G with ni possibilities
    *)
    let rec finitary (CGoal (G, S), w) =
      let s = newEVarSubst (I.Null, G) in
      let XsRev = subToXsRev s in
      ((finitarySplits
          (XsRev, 1, w, (function | () -> abstractSpine (S, s)), nil))
        (* G = xn:Vn,...,x1:V1 *)(* for splitting, EVars are always global *)
        (* s = X1...Xn.^0,  . |- S : G *)(* XsRev = [SOME(X1),...,SOME(Xn)] *))
    (***************)
    (* Contraction *)
    (***************)
    (* for explanation, see contract and contractAll above *)
    let rec contractAll (CGoal (G, S), ucands) =
      let s = newEVarSubst (I.Null, G) in
      let XsRev = subToXsRev s in
      ((if unifyUOut (XsRev, ucands)
        then SOME (abstractSpine (S, s))
        else NONE)
        (* as in splitVar, may raise Constraints.Error *)
        (* for unif, EVars are always global *))
    let rec contract ((CGoal (G, S) as cg), lab) =
      let ucands = contractionCands (G, 1) in
      let n = List.length ucands in
      let _ =
        if n > 0
        then
          chatter 6
            (function
             | () ->
                 ((^) (((^) "Found " Int.toString n) ^ " contraction ")
                    pluralize (n, "candidate"))
                   ^ "\n")
        else () in
      let cgOpt' =
        ((if n > 0
          then
            try contractAll (cg, ucands)
            with
            | Error _ ->
                (chatter 6
                   (function
                    | () -> "Contraction failed due to constraints\n");
                 SOME cg)
          else SOME cg)
        (* no progress if constraints remain *)) in
      let _ =
        match cgOpt' with
        | NONE ->
            chatter 6
              (function
               | () -> "Case impossible: conflicting unique outputs\n")
        | SOME cg' ->
            chatter 6 (function | () -> (showPendingCGoal (cg', lab)) ^ "\n") in
      ((cgOpt')(* no candidates, no progress *))
    (* cover (cg, w, ccs, lab, missing) = missing'
       covers ([cg1,...,cgn], w, ccs, missing) = missing'

       Check if cover goal cg (or [cg1,..,cgn]) are covered by
       cover clauses ccs, adding missing cases to missing to yield missing'

       cg = CGoal (G, S) where G contains the splittable variables
       cci = CClause (Gi, Si) where Gi contains essentially existential variables

       w are the worlds for the principal type family

       lab is the label for the current goal for tracing purposes
    *)
    let rec cover (cg, w, ccs, lab, missing) =
      chatter 6 (function | () -> (showPendingCGoal (cg, lab)) ^ "\n");
      cover' ((contract (cg, lab)), w, ccs, lab, missing)
    let rec cover' =
      function
      | (SOME cg, w, ccs, lab, missing) ->
          let cands = match__ (cg, ccs) in
          let cand = selectCand cands in
          ((split (cg, cand, w, ccs, lab, missing))
            (* determine splitting candidates *)(* select one candidate *))
      | (NONE, w, ccs, lab, missing) ->
          (chatter 6 (function | () -> "Covered\n"); missing)(* cg is covered by unique output inconsistency *)
    let rec split =
      function
      | (cg, NONE, w, ccs, lab, missing) ->
          (chatter 6 (function | () -> "Covered\n"); missing)
      | (cg, SOME nil, w, ccs, lab, missing) ->
          (chatter 6
             (function
              | () ->
                  "No strong candidates --- calculating weak candidates\n");
           splitWeak (cg, (finitary (cg, w)), w, ccs, lab, missing))
      | (cg, SOME ((k, _)::ksn), w, ccs, lab, missing) ->
          (chatter 6
             (function | () -> ((^) "Splitting on " Int.toString k) ^ "\n");
           (match splitVar (cg, k, w) with
            | SOME cases -> covers (cases, w, ccs, lab, missing)
            | NONE ->
                (chatter 6
                   (function
                    | () -> "Splitting failed due to generated constraints\n");
                 split (cg, (SOME ksn), w, ccs, lab, missing))))(* splitVar shows splitting as it happens *)
      (* candidates are in reverse order, so non-index candidates are split first *)
      (* some candidates: split first candidate, ignoring multiplicities *)
      (* no strong candidates: check for finitary splitting candidates *)
      (* cg is covered: return missing patterns from other cases *)
    let rec splitWeak =
      function
      | (cg, nil, w, ccs, lab, missing) ->
          (chatter 6
             (function
              | () ->
                  ((^) "No weak candidates---case " labToString lab) ^
                    " not covered\n");
           cg :: missing)
      | (cg, ksn, w, ccs, lab, missing) ->
          split (cg, (SOME ((findMin ksn) :: nil)), w, ccs, lab, missing)
      (* ksn <> nil *)
    let rec covers (cases, w, ccs, lab, missing) =
      chatter 6
        (function
         | () ->
             ((^) ((^) "Found " Int.toString (List.length cases)) pluralize
                ((List.length cases), " case"))
               ^ "\n");
      covers' (cases, 1, w, ccs, lab, missing)
    let rec covers' =
      function
      | (nil, n, w, ccs, lab, missing) ->
          (chatter 6
             (function
              | () ->
                  ((^) "All subcases of " labToString lab) ^ " considered\n");
           missing)
      | (cg::cases', n, w, ccs, lab, missing) ->
          let missing1 = cover (cg, w, ccs, (Child (lab, n)), missing) in
          covers' (cases', (n + 1), w, ccs, lab, missing1)
    (* substToSpine' (s, G, T) = S @ T
       If   G' |- s : G
       then G' |- S : {{G}} a >> a  for arbitrary a
       {{G}} erases void declarations in G
    *)
    let rec substToSpine' =
      function
      | (Shift n, I.Null, T) -> T
      | (Shift n, (Decl _ as G), T) ->
          substToSpine' ((I.Dot ((I.Idx (n + 1)), (I.Shift (n + 1)))), G, T)
      | (Dot (_, s), Decl (G, NDec _), T) -> substToSpine' (s, G, T)
      | (Dot (Exp (U), s), Decl (G, V), T) ->
          substToSpine' (s, G, (I.App (U, T)))
      | (Dot (Idx n, s), Decl (G, Dec (_, V)), T) ->
          let (Us, _) =
            Whnf.whnfEta (((I.Root ((I.BVar n), I.Nil)), I.id), (V, I.id)) in
          substToSpine' (s, G, (I.App ((I.EClo Us), T)))
      | (Dot (_, s), Decl (G, BDec (_, (L, t))), T) ->
          substToSpine' (s, G, T)(* Attempted fix, didn't work because I don't know how you
             computed splitting candidates for Blocks
             --cs Sat Jan  4 22:38:01 2003
          *)
      (* Treat like I.NDec *)(* was: I.Idx in previous line, Sun Jan  5 11:02:19 2003 -fp *)
      (* Eta-expand *)(* Unusable meta-decs are eliminated here *)
      (* Skip over NDec's; must be either Undef or Idx [from eta-expansion] *)
    (* I.Axp, I.Block(B) or other I.Undef impossible *)
    (* substToSpine (s, G) = S
       If   G' |- s : G
       then G' |- S : {{G}} type

       Note: {{G}} erases void declarations in G
     *)
    let rec substToSpine (s, G) = substToSpine' (s, G, I.Nil)
    (* purify' G = (G', s) where all NDec's have been erased from G
       If    |- G ctx
       then  |- G ctx and  G' |- s : G
    *)
    let rec purify' =
      function
      | I.Null -> (I.Null, I.id)
      | Decl (G, NDec _) ->
          let (G', s) = purify' G in (((G', (I.Dot (I.Undef, s))))
            (* G' |- s : G *)(* G' |- _.s : G,_ *))
      | Decl (G, (Dec _ as D)) ->
          let (G', s) = purify' G in
          ((((I.Decl (G', (I.decSub (D, s)))), (I.dot1 s)))
            (* G' |- s : G *)(* G |- D : type *)
            (* G' |- D[s] : type *)(* G', D[s] |- 1 : D[s][^] *)
            (* G', D[s] |- s o ^ : G *)(* G', D[s] |- 1.s o ^ : G, D *))
      | Decl (G, (BDec _ as D)) ->
          let (G', s) = purify' G in (((G', (I.Dot (I.Undef, s))))
            (* G' |- s : G *)(* G' |- _.s : G,_ *))
      (* added a new case to throw out blocks
         -cs Sat Jan  4 22:55:12 2003
      *)
    (* purify G = G' where all NDec's have been erased from G
       If   |- G ctx
       then |- G' ctx
    *)
    let rec purify (G) = (fun r -> r.1) (purify' G)
    (* coverageCheckCases (W, Cs, G) = R

       Invariant:
       If   Cs = [(G1, s1) .... (Gn, sn)]
       and  Gi |- si : G
       and  for all worlds Phi
       and  instantiations Phi |- s : G
       there exists at least one index k and substitution   Phi |- t : Gk
       s.t.  sk o t = s
    *)
    let rec coverageCheckCases (w, Cs, G) =
      let _ = chatter 4 (function | () -> "[Tomega coverage checker...") in
      let _ = chatter 4 (function | () -> "\n") in
      let ccs =
        List.map
          (function | (Gi, si) -> CClause (Gi, (substToSpine (si, G)))) Cs in
      let _ = chatter 6 (function | () -> "[Begin covering clauses]\n") in
      let _ =
        List.app
          (function
           | cc -> chatter 6 (function | () -> (showCClause cc) ^ "\n")) ccs in
      let _ = chatter 6 (function | () -> "[End covering clauses]\n") in
      let pureG = purify G in
      let namedG = N.ctxLUName pureG in
      let R0 = substToSpine (I.id, namedG) in
      let cg0 = CGoal (namedG, R0) in
      let missing = cover (cg0, w, ccs, Top, nil) in
      let _ =
        ((match missing with
          | nil -> ()
          | _::_ -> raise (Error "Coverage error"))
        (* all cases covered *)) in
      let _ = chatter 4 (function | () -> "]\n") in ((())
        (* Question: are all the Gi's above named already? *))
  end ;;




module Cover =
  (Make_Cover)(struct
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
                 (*! structure Paths = Paths !*)
                 module Print = Print
                 module TypeCheck = TypeCheck
                 (*! structure CSManager = CSManager !*)
                 module Timers = Timers
               end)
module Total =
  (Make_Total)(struct
                 module Global = Global
                 module Table = IntRedBlackTree
                 (*! structure IntSyn' = IntSyn !*)
                 module Whnf = Whnf
                 module Names = Names
                 module ModeTable = ModeTable
                 module ModeCheck = ModeCheck
                 module Index = Index
                 module Subordinate = Subordinate
                 module Order = Order
                 module Reduces = Reduces
                 module Cover = Cover
                 (*! structure Paths = Paths !*)
                 module Origins = Origins
                 module Timers = Timers
               end);;
