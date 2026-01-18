
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
      | (Decl (__g', (Dec (name, __v) as __d)), a) ->
          let w' = weaken (__g', a) in
          if Subordinate.belowEq ((I.targetFam __v), a)
          then I.dot1 w'
          else I.comp (w', I.shift)
    let rec createEVar (__g, __v) =
      let w = weaken (__g, (I.targetFam __v)) in
      let iw = Whnf.invert w in
      let __g' = Whnf.strengthen (iw, __g) in
      let x' = Whnf.newLoweredEVar (__g', (__v, iw)) in
      let x = I.EClo (x', w) in x
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
      | (__g, __v, 0, ci) -> (__g, (abbrevCGoal' (__g, __v, ci)))
      | (__g, Pi ((__d, P), __v), p, ci) ->
          let __d' = N.decEName (__g, __d) in
          abbrevCGoal ((I.Decl (__g, __d')), __v, (p - 1), ci)
    let rec abbrevCGoal' =
      function
      | (__g, Pi ((__d, P), __v), ci) ->
          let __d' = N.decUName (__g, __d) in
          I.Pi ((__d', P), (abbrevCGoal' ((I.Decl (__g, __d')), __v, ci)))
      | (__g, Root (a, S), ci) -> I.Root (a, (abbrevCSpine (S, ci)))
    let rec formatCGoal (__v, p, ci) =
      let _ = N.varReset I.Null in
      let (__g, __v') = abbrevCGoal (I.Null, __v, p, ci) in
      F.hVbox
        [Print.formatCtx (I.Null, __g);
        F.Break;
        F.String "|-";
        F.space;
        Print.formatExp (__g, __v')]
    let rec formatCGoals =
      function
      | ((__v, p)::nil, ci) -> [formatCGoal (__v, p, ci)]
      | ((__v, p)::__Vs, ci) ->
          (::) (((::) (formatCGoal (__v, p, ci)) F.String ",") :: F.Break)
            formatCGoals (__Vs, ci)
    let rec missingToString (__Vs, ci) =
      F.makestring_fmt
        (F.hbox [F.Vbox0 0 1 (formatCGoals (__Vs, ci)); F.String "."])
    let rec showSplitVar (__v, p, k, ci) =
      let _ = N.varReset I.Null in
      let (__g, __v') = abbrevCGoal (I.Null, __v, p, ci) in
      let Dec (Some x, _) = I.ctxLookup (__g, k) in
      (^) (("Split " ^ x) ^ " in ") Print.expToString (__g, __v')
    let rec showPendingGoal (__v, p, ci, lab) =
      F.makestring_fmt
        (F.hbox
           [F.String (labToString lab);
           F.space;
           F.String "?- ";
           formatCGoal (__v, p, ci);
           F.String "."])
    let rec buildSpine =
      function
      | 0 -> I.Nil
      | n -> I.App ((I.Root ((I.BVar n), I.Nil)), (buildSpine (n - 1)))
    let rec initCGoal' =
      function
      | (a, k, __g, Pi ((__d, P), __v)) ->
          let __d' = N.decEName (__g, __d) in
          let (__v', p) = initCGoal' (a, (k + 1), (I.Decl (__g, __d')), __v) in
          ((I.Pi ((__d', I.Maybe), __v')), p)
      | (a, k, __g, Uni (I.Type)) -> ((I.Root (a, (buildSpine k))), k)
    let rec initCGoal a =
      initCGoal' ((I.Const a), 0, I.Null, (I.constType a))
    type __CoverClauses =
      | Input of I.__Exp list 
      | Output of (I.__Exp * int) 
    type __Equation =
      | Eqn of (I.dctx * I.eclo * I.eclo) 
    let rec equationToString (Eqn (__g, us1, us2)) =
      let __g' = Names.ctxLUName __g in
      let fmt =
        F.hVbox
          [Print.formatCtx (I.Null, __g');
          F.Break;
          F.String "|-";
          F.space;
          Print.formatExp (__g', (I.EClo us1));
          F.Break;
          F.String "=";
          F.space;
          Print.formatExp (__g', (I.EClo us2))] in
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
    let rec unifiable (__g, us1, us2) = Unify.unifiable (__g, us1, us2)
    let rec matchEqns =
      function
      | nil -> true__
      | (Eqn (__g, us1, ((__U2, s2) as us2)))::es ->
          (match Whnf.makePatSub s2 with
           | None -> unifiable (__g, us1, us2)
           | Some s2' -> unifiable (__g, us1, (__U2, s2'))) && (matchEqns es)
    let rec resolveCands =
      function
      | Eqns es -> if matchEqns (List.rev es) then Eqns nil else Fail
      | Cands ks -> Cands ks
      | Fail -> Fail
    let rec collectConstraints =
      function
      | nil -> nil
      | (EVar (_, _, _, ref nil))::__Xs -> collectConstraints __Xs
      | (EVar (_, _, _, ref constrs))::__Xs ->
          (@) constrs collectConstraints __Xs
    let rec checkConstraints =
      function
      | (__g, __Qs, Cands ks) -> Cands ks
      | (__g, __Qs, Fail) -> Fail
      | (__g, __Qs, Eqns _) ->
          let __Xs = Abstract.collectEVars (__g, __Qs, nil) in
          let constrs = collectConstraints __Xs in
          (match constrs with | nil -> Eqns nil | _ -> Fail)
    type __CandList =
      | Covered 
      | CandList of __Candidates list 
    let rec addKs =
      function
      | ((Cands ks as ccs), CandList klist) -> CandList (ccs :: klist)
      | ((Eqns nil as ces), CandList klist) -> Covered
      | ((Fail as cfl), CandList klist) -> CandList (cfl :: klist)
    let rec matchExp (__g, d, us1, us2, cands) =
      matchExpW (__g, d, (Whnf.whnf us1), (Whnf.whnf us2), cands)
    let rec matchExpW =
      function
      | (__g, d, ((Root (H1, S1), s1) as us1), ((Root (H2, S2), s2) as us2),
         cands) ->
          (match (H1, H2) with
           | (BVar k1, BVar k2) ->
               if k1 = k2
               then matchSpine (__g, d, (S1, s1), (S2, s2), cands)
               else
                 if k1 > d
                 then failAdd ((k1 - d), cands)
                 else fail "local variable / variable clash"
           | (Const c1, Const c2) ->
               if c1 = c2
               then matchSpine (__g, d, (S1, s1), (S2, s2), cands)
               else fail "constant / constant clash"
           | (Def d1, Def d2) ->
               if d1 = d2
               then matchSpine (__g, d, (S1, s1), (S2, s2), cands)
               else
                 matchExpW
                   (__g, d, (Whnf.expandDef us1), (Whnf.expandDef us2), cands)
           | (Def d1, _) ->
               matchExpW (__g, d, (Whnf.expandDef us1), us2, cands)
           | (_, Def d2) ->
               matchExpW (__g, d, us1, (Whnf.expandDef us2), cands)
           | (BVar k1, Const _) ->
               if k1 > d
               then failAdd ((k1 - d), cands)
               else fail "local variable / constant clash"
           | (Const _, BVar _) -> fail "constant / local variable clash"
           | (Proj (Bidx k1, i1), Proj (Bidx k2, i2)) ->
               if (k1 = k2) && (i1 = i2)
               then matchSpine (__g, d, (S1, s1), (S2, s2), cands)
               else fail "block index / block index clash"
           | (Proj (Bidx k1, i1), Proj (LVar (r2, Shift k2, (l2, t2)), i2))
               ->
               let BDec (bOpt, (l1, t1)) = I.ctxDec (__g, k1) in
               if (l1 <> l2) || (i1 <> i2)
               then fail "block index / block variable clash"
               else
                 (let cands2 =
                    matchSub (__g, d, t1, (I.comp (t2, (I.Shift k2))), cands) in
                  let _ = Unify.instantiateLVar (r2, (I.Bidx (k1 - k2))) in
                  matchSpine (__g, d, (S1, s1), (S2, s2), cands2))
           | (BVar k1, Proj _) ->
               if k1 > d
               then failAdd ((k1 - d), cands)
               else fail "local variable / block projection clash"
           | (Const _, Proj _) -> fail "constant / block projection clash"
           | (Proj _, Const _) -> fail "block projection / constant clash"
           | (Proj _, BVar _) ->
               fail "block projection / local variable clash")
      | (__g, d, (Lam (D1, __U1), s1), (Lam (D2, __U2), s2), cands) ->
          matchExp
            ((I.Decl (__g, (I.decSub (D1, s1)))), (d + 1), (__U1, (I.dot1 s1)),
              (__U2, (I.dot1 s2)), cands)
      | (__g, d, (Lam (D1, __U1), s1), (__U2, s2), cands) ->
          matchExp
            ((I.Decl (__g, (I.decSub (D1, s1)))), (d + 1), (__U1, (I.dot1 s1)),
              ((I.Redex
                  ((I.EClo (__U2, I.shift)),
                    (I.App ((I.Root ((I.BVar 1), I.Nil)), I.Nil)))),
                (I.dot1 s2)), cands)
      | (__g, d, (__U1, s1), (Lam (D2, __U2), s2), cands) ->
          matchExp
            ((I.Decl (__g, (I.decSub (D2, s2)))), (d + 1),
              ((I.Redex
                  ((I.EClo (__U1, I.shift)),
                    (I.App ((I.Root ((I.BVar 1), I.Nil)), I.Nil)))),
                (I.dot1 s1)), (__U2, (I.dot1 s2)), cands)
      | (__g, d, us1, ((EVar _, s2) as us2), cands) ->
          addEqn ((Eqn (__g, us1, us2)), cands)
    let rec matchSpine =
      function
      | (__g, d, (I.Nil, _), (I.Nil, _), cands) -> cands
      | (__g, d, (SClo (S1, s1'), s1), Ss2, cands) ->
          matchSpine (__g, d, (S1, (I.comp (s1', s1))), Ss2, cands)
      | (__g, d, Ss1, (SClo (S2, s2'), s2), cands) ->
          matchSpine (__g, d, Ss1, (S2, (I.comp (s2', s2))), cands)
      | (__g, d, (App (__U1, S1), s1), (App (__U2, S2), s2), cands) ->
          let cands' = matchExp (__g, d, (__U1, s1), (__U2, s2), cands) in
          matchSpine (__g, d, (S1, s1), (S2, s2), cands')
    let rec matchDec (__g, d, (Dec (_, V1), s1), (Dec (_, V2), s2), cands) =
      matchExp (__g, d, (V1, s1), (V2, s2), cands)
    let rec matchSub =
      function
      | (__g, d, Shift n1, Shift n2, cands) -> cands
      | (__g, d, Shift n, (Dot _ as s2), cands) ->
          matchSub
            (__g, d, (I.Dot ((I.Idx (n + 1)), (I.Shift (n + 1)))), s2, cands)
      | (__g, d, (Dot _ as s1), Shift m, cands) ->
          matchSub
            (__g, d, s1, (I.Dot ((I.Idx (m + 1)), (I.Shift (m + 1)))), cands)
      | (__g, d, Dot (Ft1, s1), Dot (Ft2, s2), cands) ->
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
            | (Exp (__U1), Exp (__U2)) ->
                matchExp (__g, d, (__U1, I.id), (__U2, I.id), cands)
            | (Exp (__U1), Idx n2) ->
                matchExp
                  (__g, d, (__U1, I.id), ((I.Root ((I.BVar n2), I.Nil)), I.id),
                    cands)
            | (Idx n1, Exp (__U2)) ->
                matchExp
                  (__g, d, ((I.Root ((I.BVar n1), I.Nil)), I.id), (__U2, I.id),
                    cands) in
          matchSub (__g, d, s1, s2, cands1)
    let rec matchTop (__g, d, us1, us2, ci, cands) =
      matchTopW (__g, d, (Whnf.whnf us1), (Whnf.whnf us2), ci, cands)
    let rec matchTopW =
      function
      | (__g, d, (Root (Const c1, S1), s1), (Root (Const c2, S2), s2), ci,
         cands) ->
          if c1 = c2
          then matchTopSpine (__g, d, (S1, s1), (S2, s2), ci, cands)
          else fail "type family clash"
      | (__g, d, (Pi ((D1, _), V1), s1), (Pi ((D2, _), V2), s2), ci, cands) ->
          matchTopW
            ((I.Decl (__g, D1)), (d + 1), (V1, (I.dot1 s1)), (V2, (I.dot1 s2)),
              ci, cands)
    let rec matchTopSpine =
      function
      | (__g, d, (I.Nil, _), (I.Nil, _), Cnil, cands) -> cands
      | (__g, d, (SClo (S1, s1'), s1), Ss2, ci, cands) ->
          matchTopSpine (__g, d, (S1, (I.comp (s1', s1))), Ss2, ci, cands)
      | (__g, d, Ss1, (SClo (S2, s2'), s2), ci, cands) ->
          matchTopSpine (__g, d, Ss1, (S2, (I.comp (s2', s2))), ci, cands)
      | (__g, d, (App (__U1, S1), s1), (App (__U2, S2), s2), Match ci', cands) ->
          let cands' = matchExp (__g, d, (__U1, s1), (__U2, s2), cands) in
          matchTopSpine (__g, d, (S1, s1), (S2, s2), ci', cands')
      | (__g, d, (App (__U1, S1), s1), (App (__U2, S2), s2), Skip ci', cands) ->
          matchTopSpine (__g, d, (S1, s1), (S2, s2), ci', cands)
    let rec matchClause =
      function
      | (__g, ps', ((Root (_, _), s) as qs), ci) ->
          checkConstraints
            (__g, qs,
              (resolveCands (matchTop (__g, 0, ps', qs, ci, (Eqns nil)))))
      | (__g, ps', (Pi ((Dec (_, V1), _), V2), s), ci) ->
          let X1 = Whnf.newLoweredEVar (__g, (V1, s)) in
          matchClause (__g, ps', (V2, (I.Dot ((I.Exp X1), s))), ci)
    let rec matchSig =
      function
      | (__g, ps', nil, ci, klist) -> klist
      | (__g, ps', (__v)::ccs', ci, klist) ->
          let cands =
            CSManager.trail
              (function | () -> matchClause (__g, ps', (__v, I.id), ci)) in
          matchSig' (__g, ps', ccs', ci, (addKs (cands, klist)))
    let rec matchSig' =
      function
      | (__g, ps', ccs, ci, Covered) -> Covered
      | (__g, ps', ccs, ci, CandList klist) ->
          matchSig (__g, ps', ccs, ci, (CandList klist))
    let rec matchBlocks =
      function
      | (__g, s', nil, __v, k, i, ci, klist) -> klist
      | (__g, s', (Dec (_, __v'))::piDecs, __v, k, i, ci, klist) ->
          let cands =
            CSManager.trail
              (function | () -> matchClause (__g, (__v, I.id), (__v', s'), ci)) in
          let s'' =
            I.Dot ((I.Exp (I.Root ((I.Proj ((I.Bidx k), i)), I.Nil))), s') in
          matchBlocks'
            (__g, s'', piDecs, __v, k, (i + 1), ci, (addKs (cands, klist)))
    let rec matchBlocks' =
      function
      | (__g, s', piDecs, __v, k, i, ci, Covered) -> Covered
      | (__g, s', piDecs, __v, k, i, ci, klist) ->
          matchBlocks (__g, s', piDecs, __v, k, i, ci, klist)
    let rec matchCtx =
      function
      | (__g, s', I.Null, __v, k, ci, klist) -> klist
      | (__g, s', Decl (__g'', Dec (_, __v')), __v, k, ci, klist) ->
          let s'' = I.comp (I.shift, s') in
          let cands =
            CSManager.trail
              (function | () -> matchClause (__g, (__v, I.id), (__v', s''), ci)) in
          matchCtx' (__g, s'', __g'', __v, (k + 1), ci, (addKs (cands, klist)))
      | (__g, s', Decl (__g'', BDec (_, (cid, s))), __v, k, ci, klist) ->
          let (Gsome, piDecs) = I.constBlock cid in
          let s'' = I.comp (I.shift, s') in
          let klist' =
            matchBlocks (__g, (I.comp (s, s'')), piDecs, __v, k, 1, ci, klist) in
          matchCtx' (__g, s'', __g'', __v, (k + 1), ci, klist')
    let rec matchCtx' =
      function
      | (__g, s', __g', __v, k, ci, Covered) -> Covered
      | (__g, s', __g', __v, k, ci, CandList klist) ->
          matchCtx (__g, s', __g', __v, k, ci, (CandList klist))
    let rec matchOut =
      function
      | (__g, __v, ci, (__v', s'), 0) ->
          let cands = matchTop (__g, 0, (__v, I.id), (__v', s'), ci, (Eqns nil)) in
          let cands' = resolveCands cands in
          let cands'' = checkConstraints (__g, (__v', s'), cands') in
          addKs (cands'', (CandList nil))
      | (__g, __v, ci, ((Pi ((Dec (_, V1'), _), V2') as __v'), s'), p) ->
          let X1 = Whnf.newLoweredEVar (__g, (V1', s')) in
          matchOut (__g, __v, ci, (V2', (I.Dot ((I.Exp X1), s'))), (p - 1))
    let rec match__ =
      function
      | (__g, (Root (Const a, S) as __v), 0, ci, Input ccs) ->
          matchCtx'
            (__g, I.id, __g, __v, 1, ci,
              (matchSig (__g, (__v, I.id), ccs, ci, (CandList nil))))
      | (__g, __v, 0, ci, Output (__v', q)) ->
          matchOut (__g, __v, ci, (__v', (I.Shift (I.ctxLength __g))), q)
      | (__g, Pi ((__d, _), __v'), p, ci, ccs) ->
          match__ ((I.Decl (__g, __d)), __v', (p - 1), ci, ccs)
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
      function | Covered -> None | CandList klist -> selectCand' (klist, nil)
    let rec selectCand' =
      function
      | (nil, ksn) -> Some ksn
      | ((Fail)::klist, ksn) -> selectCand' (klist, ksn)
      | ((Cands nil)::klist, ksn) -> selectCand' (klist, ksn)
      | ((Cands ks)::klist, ksn) -> selectCand' (klist, (join (ks, ksn)))
    let rec instEVars (__Vs, p, XsRev) = instEVarsW ((Whnf.whnf __Vs), p, XsRev)
    let rec instEVarsW =
      function
      | (__Vs, 0, XsRev) -> (__Vs, XsRev)
      | ((Pi ((Dec (xOpt, V1), _), V2), s), p, XsRev) ->
          let X1 = Whnf.newLoweredEVar (I.Null, (V1, s)) in
          instEVars
            ((V2, (I.Dot ((I.Exp X1), s))), (p - 1), ((Some X1) :: XsRev))
      | ((Pi ((BDec (_, (l, t)), _), V2), s), p, XsRev) ->
          let L1 = I.newLVar ((I.Shift 0), (l, (I.comp (t, s)))) in
          instEVars
            ((V2, (I.Dot ((I.Block L1), s))), (p - 1), (None :: XsRev))
    let (caseList : (I.__Exp * int) list ref) = ref nil
    let rec resetCases () = caseList := nil
    let rec addCase (__v, p) = (!) ((::) (caseList := (__v, p))) caseList
    let rec getCases () = !caseList
    let rec createEVarSpine (__g, __Vs) = createEVarSpineW (__g, (Whnf.whnf __Vs))
    let rec createEVarSpineW =
      function
      | (__g, ((Root _, s) as __Vs)) -> (I.Nil, __Vs)
      | (__g, (Pi (((Dec (_, V1) as __d), _), V2), s)) ->
          let x = createEVar (__g, (I.EClo (V1, s))) in
          let (S, __Vs) = createEVarSpine (__g, (V2, (I.Dot ((I.Exp x), s)))) in
          ((I.App (x, S)), __Vs)
    let rec createAtomConst (__g, (Const cid as H)) =
      let __v = I.constType cid in
      let (S, __Vs) = createEVarSpine (__g, (__v, I.id)) in ((I.Root (H, S)), __Vs)
    let rec createAtomBVar (__g, k) =
      let Dec (_, __v) = I.ctxDec (__g, k) in
      let (S, __Vs) = createEVarSpine (__g, (__v, I.id)) in
      ((I.Root ((I.BVar k), S)), __Vs)
    let rec createAtomProj (__g, H, (__v, s)) =
      let (S, __Vs') = createEVarSpine (__g, (__v, s)) in ((I.Root (H, S)), __Vs')
    let rec constCases =
      function
      | (__g, __Vs, nil, sc) -> ()
      | (__g, __Vs, (Const c)::sgn', sc) ->
          let (__u, __Vs') = createAtomConst (__g, (I.Const c)) in
          let _ =
            CSManager.trail
              (function
               | () -> if Unify.unifiable (__g, __Vs, __Vs') then sc __u else ()) in
          constCases (__g, __Vs, sgn', sc)
    let rec paramCases =
      function
      | (__g, __Vs, 0, sc) -> ()
      | (__g, __Vs, k, sc) ->
          let (__u, __Vs') = createAtomBVar (__g, k) in
          let _ =
            CSManager.trail
              (function
               | () -> if Unify.unifiable (__g, __Vs, __Vs') then sc __u else ()) in
          paramCases (__g, __Vs, (k - 1), sc)
    let rec createEVarSub =
      function
      | I.Null -> I.id
      | Decl (__g', (Dec (_, __v) as __d)) ->
          let s = createEVarSub __g' in
          let x = Whnf.newLoweredEVar (I.Null, (__v, s)) in
          I.Dot ((I.Exp x), s)
    let rec blockName cid = I.conDecName (I.sgnLookup cid)
    let rec blockCases (__g, __Vs, cid, (Gsome, piDecs), sc) =
      let t = createEVarSub Gsome in
      let sk = I.Shift (I.ctxLength __g) in
      let t' = I.comp (t, sk) in
      let lvar = I.newLVar (sk, (cid, t)) in
      blockCases' (__g, __Vs, (lvar, 1), (t', piDecs), sc)
    let rec blockCases' =
      function
      | (__g, __Vs, (lvar, i), (t, nil), sc) -> ()
      | (__g, __Vs, (lvar, i), (t, (Dec (_, __v'))::piDecs), sc) ->
          let (__u, __Vs') = createAtomProj (__g, (I.Proj (lvar, i)), (__v', t)) in
          let _ =
            CSManager.trail
              (function
               | () -> if Unify.unifiable (__g, __Vs, __Vs') then sc __u else ()) in
          let t' = I.Dot ((I.Exp (I.Root ((I.Proj (lvar, i)), I.Nil))), t) in
          blockCases' (__g, __Vs, (lvar, (i + 1)), (t', piDecs), sc)
    let rec worldCases =
      function
      | (__g, __Vs, Worlds nil, sc) -> ()
      | (__g, __Vs, Worlds (cid::cids), sc) ->
          (blockCases (__g, __Vs, cid, (I.constBlock cid), sc);
           worldCases (__g, __Vs, (T.Worlds cids), sc))
    let rec lowerSplitW =
      function
      | ((EVar (_, __g, __v, _) as x), W, sc) ->
          let sc' =
            function
            | __u ->
                if Unify.unifiable (__g, (x, I.id), (__u, I.id))
                then sc ()
                else () in
          let _ = paramCases (__g, (__v, I.id), (I.ctxLength __g), sc') in
          let _ = worldCases (__g, (__v, I.id), W, sc') in
          let _ =
            constCases (__g, (__v, I.id), (Index.lookup (I.targetFam __v)), sc') in
          ()
      | (Lam (__d, __u), W, sc) -> lowerSplitW (__u, W, sc)
    let rec splitEVar (x, W, sc) = lowerSplitW (x, W, sc)
    let rec abstract (__v, s) =
      let (i, __v') = Abstract.abstractDecImp (I.EClo (__v, s)) in
      let _ =
        if !Global.doubleCheck
        then TypeCheck.typeCheck (I.Null, (__v', (I.Uni I.Type)))
        else () in
      (__v', i)
    let rec splitVar (__v, p, k, (W, ci)) =
      try
        let _ =
          chatter 6 (function | () -> (showSplitVar (__v, p, k, ci)) ^ "\n") in
        let ((V1, s), XsRev) = instEVars ((__v, I.id), p, nil) in
        let Some (x) = List.nth (XsRev, (k - 1)) in
        let _ = resetCases () in
        let _ =
          splitEVar (x, W, (function | () -> addCase (abstract (V1, s)))) in
        Some (getCases ())
      with
      | Error constrs ->
          (chatter 7
             (function
              | () ->
                  ((^) "Inactive split:\n" Print.cnstrsToString constrs) ^
                    "\n");
           None)
    let rec occursInExp =
      function
      | (k, Uni _) -> false__
      | (k, Pi (DP, __v)) ->
          (occursInDecP (k, DP)) || (occursInExp ((k + 1), __v))
      | (k, Root (H, S)) -> (occursInHead (k, H)) || (occursInSpine (k, S))
      | (k, Lam (__d, __v)) -> (occursInDec (k, __d)) || (occursInExp ((k + 1), __v))
      | (k, FgnExp (cs, ops)) -> false__
    let rec occursInHead =
      function | (k, BVar k') -> k = k' | (k, _) -> false__
    let rec occursInSpine =
      function
      | (_, I.Nil) -> false__
      | (k, App (__u, S)) -> (occursInExp (k, __u)) || (occursInSpine (k, S))
    let rec occursInDec (k, Dec (_, __v)) = occursInExp (k, __v)
    let rec occursInDecP (k, (__d, _)) = occursInDec (k, __d)
    let rec occursInMatchPos =
      function
      | (k, Pi (DP, __v), ci) -> occursInMatchPos ((k + 1), __v, ci)
      | (k, Root (H, S), ci) -> occursInMatchPosSpine (k, S, ci)
    let rec occursInMatchPosSpine =
      function
      | (k, I.Nil, Cnil) -> false__
      | (k, App (__u, S), Match ci) ->
          (occursInExp (k, __u)) || (occursInMatchPosSpine (k, S, ci))
      | (k, App (__u, S), Skip ci) -> occursInMatchPosSpine (k, S, ci)
    let rec instEVarsSkip (__Vs, p, XsRev, ci) =
      InstEVarsSkipW ((Whnf.whnf __Vs), p, XsRev, ci)
    let rec InstEVarsSkipW =
      function
      | (__Vs, 0, XsRev, ci) -> (__Vs, XsRev)
      | ((Pi ((Dec (xOpt, V1), _), V2), s), p, XsRev, ci) ->
          let X1 = Whnf.newLoweredEVar (I.Null, (V1, s)) in
          let EVarOpt =
            if occursInMatchPos (1, V2, ci) then Some X1 else None in
          instEVarsSkip
            ((V2, (I.Dot ((I.Exp X1), s))), (p - 1), (EVarOpt :: XsRev), ci)
      | ((Pi ((BDec (_, (l, t)), _), V2), s), p, XsRev, ci) ->
          let L1 = I.newLVar ((I.Shift 0), (l, (I.comp (t, s)))) in
          instEVarsSkip
            ((V2, (I.Dot ((I.Block L1), s))), (p - 1), (None :: XsRev), ci)
    let rec targetBelowEq =
      function
      | (a, EVar (ref (None), GY, VY, ref nil)) ->
          Subordinate.belowEq (a, (I.targetFam VY))
      | (a, EVar (ref (None), GY, VY, ref (_::_))) -> true__
    let rec recursive =
      function
      | EVar (ref (Some (__u)), GX, VX, _) as x ->
          let a = I.targetFam VX in
          let __Ys = Abstract.collectEVars (GX, (x, I.id), nil) in
          let recp = List.exists (function | y -> targetBelowEq (a, y)) __Ys in
          recp
      | Lam (__d, __u) -> recursive __u
    let counter = ref 0
    let rec resetCount () = counter := 0
    let rec incCount () = ((!) ((:=) counter) counter) + 1
    let rec getCount () = !counter
    exception NotFinitary 
    let rec finitary1 (x, k, W, f, cands) =
      resetCount ();
      chatter 7
        (function
         | () ->
             (((^) "Trying " Print.expToString (I.Null, x)) ^ " : ") ^ ".\n");
      (try
         splitEVar
           (x, W,
             (function
              | () ->
                  (f ();
                   if recursive x then raise NotFinitary else incCount ())));
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
      | ((None)::__Xs, k, W, f, cands) ->
          finitarySplits (__Xs, (k + 1), W, f, cands)
      | ((Some (x))::__Xs, k, W, f, cands) ->
          finitarySplits
            (__Xs, (k + 1), W, f,
              (CSManager.trail
                 (function | () -> finitary1 (x, k, W, f, cands))))
    let rec finitary (__v, p, W, ci) =
      let _ =
        if !Global.doubleCheck
        then TypeCheck.typeCheck (I.Null, (__v, (I.Uni I.Type)))
        else () in
      let ((V1, s), XsRev) = instEVarsSkip ((__v, I.id), p, nil, ci) in
      finitarySplits (XsRev, 1, W, (function | () -> abstract (V1, s)), nil)
    let rec eqExp (__Us, __Us') = Conv.conv (__Us, __Us')
    let rec eqInpSpine =
      function
      | (ms, (SClo (S1, s1'), s1), Ss2) ->
          eqInpSpine (ms, (S1, (I.comp (s1', s1))), Ss2)
      | (ms, Ss1, (SClo (S2, s2'), s2)) ->
          eqInpSpine (ms, Ss1, (S2, (I.comp (s2', s2))))
      | (M.Mnil, (I.Nil, s), (I.Nil, s')) -> true__
      | (Mapp (Marg (M.Plus, _), ms'), (App (__u, S), s), (App (__u', S'), s'))
          ->
          (eqExp ((__u, s), (__u', s'))) && (eqInpSpine (ms', (S, s), (S', s')))
      | (Mapp (_, ms'), (App (__u, S), s), (App (__u', S'), s')) ->
          eqInpSpine (ms', (S, s), (S', s'))
    let rec eqInp =
      function
      | (I.Null, k, a, __Ss, ms) -> nil
      | (Decl (__g', Dec (_, Root (Const a', S'))), k, a, __Ss, ms) ->
          if (a = a') && (eqInpSpine (ms, (S', (I.Shift k)), __Ss))
          then (::) k eqInp (__g', (k + 1), a, __Ss, ms)
          else eqInp (__g', (k + 1), a, __Ss, ms)
      | (Decl (__g', Dec (_, Pi _)), k, a, __Ss, ms) ->
          eqInp (__g', (k + 1), a, __Ss, ms)
      | (Decl (__g', NDec _), k, a, __Ss, ms) -> eqInp (__g', (k + 1), a, __Ss, ms)
      | (Decl (__g', BDec (_, (b, t))), k, a, __Ss, ms) ->
          eqInp (__g', (k + 1), a, __Ss, ms)
    let rec contractionCands =
      function
      | (I.Null, k) -> nil
      | (Decl (__g', Dec (_, Root (Const a, S))), k) ->
          (match UniqueTable.modeLookup a with
           | None -> contractionCands (__g', (k + 1))
           | Some ms ->
               (match eqInp (__g', (k + 1), a, (S, (I.Shift k)), ms) with
                | nil -> contractionCands (__g', (k + 1))
                | ns -> (::) (k :: ns) contractionCands (__g', (k + 1))))
      | (Decl (__g', Dec (_, Pi _)), k) -> contractionCands (__g', (k + 1))
      | (Decl (__g', NDec _), k) -> contractionCands (__g', (k + 1))
      | (Decl (__g', BDec (_, (b, t))), k) -> contractionCands (__g', (k + 1))
    let rec isolateSplittable =
      function
      | (__g, __v, 0) -> (__g, __v)
      | (__g, Pi ((__d, _), __v'), p) ->
          isolateSplittable ((I.Decl (__g, __d)), __v', (p - 1))
    let rec unifyUOutSpine =
      function
      | (ms, (SClo (S1, s1'), s1), Ss2) ->
          unifyUOutSpine (ms, (S1, (I.comp (s1', s1))), Ss2)
      | (ms, Ss1, (SClo (S2, s2'), s2)) ->
          unifyUOutSpine (ms, Ss1, (S2, (I.comp (s2', s2))))
      | (M.Mnil, (I.Nil, s1), (I.Nil, s2)) -> true__
      | (Mapp (Marg (M.Minus1, _), ms'), (App (__U1, S1), s1),
         (App (__U2, S2), s2)) ->
          (Unify.unifiable (I.Null, (__U1, s1), (__U2, s2))) &&
            (unifyUOutSpine (ms', (S1, s1), (S2, s2)))
      | (Mapp (_, ms'), (App (__U1, S1), s1), (App (__U2, S2), s2)) ->
          unifyUOutSpine (ms', (S1, s1), (S2, s2))
    let rec unifyUOutType (V1, V2) =
      unifyUOutTypeW ((Whnf.whnf (V1, I.id)), (Whnf.whnf (V2, I.id)))
    let rec unifyUOutTypeW
      ((Root (Const a1, S1), s1), (Root (Const a2, S2), s2)) =
      let Some ms = UniqueTable.modeLookup a1 in
      unifyUOutSpine (ms, (S1, s1), (S2, s2))
    let rec unifyUOutEVars
      (Some (EVar (_, G1, V1, _)), Some (EVar (_, G2, V2, _))) =
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
    let rec contractAll (__v, p, ucands) =
      let ((V1, s), XsRev) = instEVars ((__v, I.id), p, nil) in
      if unifyUOut (XsRev, ucands) then Some (abstract (V1, s)) else None
    let rec contract (__v, p, ci, lab) =
      let (__g, _) = isolateSplittable (I.Null, __v, p) in
      let ucands = contractionCands (__g, 1) in
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
          try contractAll (__v, p, ucands)
          with
          | Error _ ->
              (chatter 6
                 (function | () -> "Contraction failed due to constraints\n");
               Some (__v, p))
        else Some (__v, p) in
      let _ =
        match VpOpt' with
        | None ->
            chatter 6
              (function
               | () -> "Case impossible: conflicting unique outputs\n")
        | Some (__v', p') ->
            chatter 6
              (function | () -> (showPendingGoal (__v', p', ci, lab)) ^ "\n") in
      VpOpt'
    let rec findMin ((k, n)::kns) = findMin' ((k, n), kns)
    let rec findMin' =
      function
      | ((k0, n0), nil) -> (k0, n0)
      | ((k0, n0), (k', n')::kns) ->
          if n' < n0
          then findMin' ((k', n'), kns)
          else findMin' ((k0, n0), kns)
    let rec cover (__v, p, ((W, ci) as wci), ccs, lab, missing) =
      chatter 6 (function | () -> (showPendingGoal (__v, p, ci, lab)) ^ "\n");
      cover' ((contract (__v, p, ci, lab)), wci, ccs, lab, missing)
    let rec cover' =
      function
      | (Some (__v, p), ((W, ci) as wci), ccs, lab, missing) ->
          split
            (__v, p, (selectCand (match__ (I.Null, __v, p, ci, ccs))), wci, ccs,
              lab, missing)
      | (None, wci, ccs, lab, missing) ->
          (chatter 6 (function | () -> "Covered\n"); missing)
    let rec split =
      function
      | (__v, p, None, wci, ccs, lab, missing) ->
          (chatter 6 (function | () -> "Covered\n"); missing)
      | (__v, p, Some nil, ((W, ci) as wci), ccs, lab, missing) ->
          (chatter 6
             (function
              | () -> "No strong candidates---calculating weak candidates\n");
           splitWeak (__v, p, (finitary (__v, p, W, ci)), wci, ccs, lab, missing))
      | (__v, p, Some ((k, _)::ksn), ((W, ci) as wci), ccs, lab, missing) ->
          (match splitVar (__v, p, k, wci) with
           | Some cases -> covers (cases, wci, ccs, lab, missing)
           | None -> split (__v, p, (Some ksn), wci, ccs, lab, missing))
    let rec splitWeak =
      function
      | (__v, p, nil, wci, ccs, lab, missing) ->
          (chatter 6
             (function
              | () ->
                  ((^) "No weak candidates---case " labToString lab) ^
                    " not covered\n");
           (__v, p) :: missing)
      | (__v, p, ksn, wci, ccs, lab, missing) ->
          split (__v, p, (Some ((findMin ksn) :: nil)), wci, ccs, lab, missing)
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
      | ((__v, p)::cases', n, wci, ccs, lab, missing) ->
          covers'
            (cases', (n + 1), wci, ccs, lab,
              (cover (__v, p, wci, ccs, (Child (lab, n)), missing)))
    let rec constsToTypes =
      function
      | nil -> nil
      | (Const c)::cs' -> (::) (I.constType c) constsToTypes cs'
      | (Def d)::cs' -> (::) (I.constType d) constsToTypes cs'
    let rec createCoverClause =
      function
      | (Decl (__g, __d), __v, p) ->
          createCoverClause (__g, (I.Pi ((__d, I.Maybe), __v)), (p + 1))
      | (I.Null, __v, p) -> ((Whnf.normalize (__v, I.id)), p)
    let rec createCoverGoal (__g, __Vs, p, ms) =
      createCoverGoalW (__g, (Whnf.whnf __Vs), p, ms)
    let rec createCoverGoalW =
      function
      | (__g, (Pi ((D1, __P1), V2), s), 0, ms) ->
          let D1' = I.decSub (D1, s) in
          let V2' =
            createCoverGoal ((I.Decl (__g, D1')), (V2, (I.dot1 s)), 0, ms) in
          I.Pi ((D1', __P1), V2')
      | (__g, (Pi (((Dec (_, V1) as __d), _), V2), s), p, ms) ->
          let x = Whnf.newLoweredEVar (__g, (V1, s)) in
          createCoverGoal (__g, (V2, (I.Dot ((I.Exp x), s))), (p - 1), ms)
      | (__g, (Root ((Const cid as a), S), s), p, ms) ->
          I.Root
            (a,
              (createCoverSpine (__g, (S, s), ((I.constType cid), I.id), ms)))
    let rec createCoverSpine =
      function
      | (__g, (I.Nil, s), _, M.Mnil) -> I.Nil
      | (__g, (App (__U1, S2), s), (Pi ((Dec (_, V1), _), V2), s'), Mapp
         (Marg (M.Minus, x), ms')) ->
          let x = createEVar (__g, (I.EClo (V1, s'))) in
          let S2' =
            createCoverSpine (__g, (S2, s), (V2, (I.Dot ((I.Exp x), s'))), ms') in
          I.App (x, S2')
      | (__g, (App (__U1, S2), s), (Pi (_, V2), s'), Mapp (_, ms')) ->
          I.App
            ((I.EClo (__U1, s)),
              (createCoverSpine
                 (__g, (S2, s),
                   (Whnf.whnf (V2, (I.Dot ((I.Exp (I.EClo (__U1, s))), s')))),
                   ms')))
      | (__g, (SClo (S, s'), s), __Vs, ms) ->
          createCoverSpine (__g, (S, (I.comp (s', s))), __Vs, ms)
    (*****************)
    (* Strengthening *)
    (*****************)
    (* next section adapted from m2/metasyn.fun *)
    (* weaken (__g, a) = w'

       Invariant:
       If   a is a type family
       then __g |- w' : __g'
       and  forall x:A in __g'  A subordinate to a
     *)
    (* added next case, probably should not arise *)
    (* Sun Dec 16 10:42:05 2001 -fp !!! *)
    (*
      | weaken (I.Decl (__g', __d as I.BDec _), a) =
           I.dot1 (weaken (__g', a))
      *)
    (* createEVar (__g, __v) = x[w] where __g |- x[w] : __v

       Invariant:
       If __g |- __v : __l
       then __g |- x[w] : __v
    *)
    (* __g |- __v : __l *)
    (* __g  |- w  : __g'    *)
    (* __g' |- iw : __g     *)
    (* __g' |- x' : __v[iw] *)
    (* was I.newEvar (__g', I.EClo (__v, iw))  Mon Feb 28 14:30:36 2011 --cs *)
    (* __g  |- x  : __v     *)
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
       Coverage goals have the form {{__g}} {{__l}} a @ S
       where __g are splittable variables
       and __l are local parameters (not splittable)
    *)
    (**********************************************)
    (* Creating the initial input coverage goal ***)
    (**********************************************)
    (* buildSpine n = n; n-1; ...; 1; Nil *)
    (* n > 0 *)
    (* Eta-long invariant violation -kw *)
    (* initCGoal' (a, 0, ., __v) = ({x1:V1}...{xn:Vn} a x1...xn, n)
       for |- a : __v and __v = {x1:V1}...{xn:Vn} type

       Invariants for initCGoal' (a, k, __g, __v):
       __g = {x1:V1}...{xk:Vk}
       __v = {xk+1:Vk+1}...{xn:Vn} type
       __g |- __v : type
    *)
    (* initCGoal (a) = {x1:V1}...{xn:Vn} a x1...xn
       where a : {x1:V1}...{xn:Vn} type
    *)
    (****************)
    (*** Matching ***)
    (****************)
    (* for now, no factoring --- singleton list *)
    (* Equation __g |- (__U1,s1) = (__U2,s2)
       Invariant:
       __g |- __U1[s1] : __v
       __g |- __U2[s2] : __v  for some __v

       __U1[s1] has no EVars (part of coverage goal)
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
    (* was: unifiable (__g, us1, us2) *)
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
    (* collectConstraints (__Xs) = constrs
       collect all the constraints that may be attached to EVars __Xs

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
    (* matchExp (__g, d, (__U1, s1), (__U2, s2), cands) = cands'
       matches __U1[s1] (part of coverage goal)
       against __U2[s2] (part of clause head)
       adds new candidates to cands to return cands'
         this could collapse to Fail,
         postponed equations Eqns(es),
         or candidates Cands(ks)
       d is depth, k <= d means local variable, k > d means coverage variable

       Invariants:
       __g |- __U1[s1] : __v
       __g |- __U2[s2] : __v  for some __v
       __g = Gc, Gl where d = |Gl|
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
                 matchSpine (__g, d, (S1, s1), (S2, s2),
                             matchBlock (__g, d, b1, b2, cands))
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
      | matchExpW (__g, d, (I.Pi ((D1, _), V1), s1), (I.Pi ((D2, _), V2), s2), cands) =
        let
          val cands' = matchDec (__g, d, (D1, s1), (D2, s2), cands)
        in
          matchExp (I.Decl (__g, D1), d+1, (V1, I.dot1 s1), (V2, I.dot1 s2), cands')
        end
      | matchExpW (__g, d, (I.Pi _, _), _, cands) = fail ()
      | matchExpW (__g, d, _, (I.Pi _, _), cands) = fail ()
      *)
    (* nothing else should be possible, by invariants *)
    (* No I.Uni, I.FgnExp, and no I.Redex by whnf *)
    (* BDec should be impossible here *)
    (* matchBlock now unfolded into the first case of matchExpW *)
    (* Sun Jan  5 12:02:49 2003 -fp *)
    (*
    and matchBlock (__g, d, I.Bidx(k), I.Bidx(k'), cands) =
        if (k = k') then cands
          else fail ("block index / block index clash")
      | matchBlock (__g, d, B1 as I.Bidx(k), I.LVar (r2, I.Shift(k'), (l2, t2)), cands) =
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
    (* matchTop (__g, (a @ S1, s1), (a @ S2, s2), ci) = cands
       matches S1[s1] (spine of coverage goal)
       against S2[s2] (spine of clause head)
       skipping over `skip' arguments in cover instructions

       Invariants:
       __g |- a @ S1[s1] : type
       __g |- a @ S2[s2] : type
       __g contains coverage variables,
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
    (* matchClause (__g, (a @ S1, s1), __v, ci) = cands
       as in matchTop, but r is clause
       NOTE: Simply use constant type for more robustness (see below)
    *)
    (* changed to use subordination and strengthening here *)
    (* Sun Dec 16 10:39:34 2001 -fp *)
    (* val X1 = createEVar (__g, I.EClo (V1, s)) *)
    (* changed back --- no effect *)
    (* was val X1 = I.newEVar (__g, I.EClo (V1, s)) Mon Feb 28 14:37:22 2011 -cs *)
    (* was: I.Null instead of __g in line above Wed Nov 21 16:40:40 2001 *)
    (* matchSig (__g, (a @ S, s), ccs, ci, klist) = klist'
       match coverage goal {{__g}} a @ S[s]
       against each coverage clause __v in ccs,
       adding one new list cand for each __v to klist to obtain klist'

       Invariants:
       __g |- a @ S[s] : type
       __v consists of clauses with target type a @ S'
       ci matches S
       klist <> Covered
    *)
    (* matchSig' (__g, (a @ S, s), ccs, ci, klist) = klist'
       as matchSig, but check if coverage goal {{__g}} a @ S[s] is already matched
    *)
    (* already covered: return *)
    (* not yet covered: continue to search *)
    (* matchBlocks (__g, s', piDecs, __v, k, i, ci, klist) = klist'
       Invariants:
       __g |- s' : Gsome
       Gsome |- piDecs : ctx
       __g |- __v : type
       G_k = (Gsome, D1...D(i-1) piDecs)
     *)
    (* klist <> Covered *)
    (* matchCtx (__g, s', __g', __v, k, ci, klist) = klist'
       Invariants:
       __g |- s' : __g'
       __g |- __v : type
       s' o ^ = ^k
       ci matches for for __v = a @ S
       klist <> Covered accumulates mode spines
    *)
    (* will always fail for input coverage *)
    (*  __g'', __v' |- ^ : __g''
              __g |- s' : __g'', __v'
          *)
    (*  __g |- ^ o s' : __g'' *)
    (* __g'' |- s : Gsome,
             __g |- s'' : __g''
             __g |- s o s'' : Gsome
             Gsome |- piDecs : ctx
          *)
    (* as matchClause *)
    (* p > 0 *)
    (* was val X1 = I.newEVar (__g, I.EClo (V1', s')) Mon Feb 28 14:38:21 2011 -cs *)
    (* match (., __v, p, ci, I/O(ccs)) = klist
       matching coverage goal {{__g}} __v against coverage clauses Vi in ccs
       yields candidates klist
       no local assumptions
       Invariants:
       __v = {{__g}} {{__l}} a @ S where |__g| = p
       cover instructions ci match S
       __g |- __v : type
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
       where ksOpt is an indication of coverage (None)
       or a list of candidates with multiplicities

       Simple heuristic: select last splitting candidate from last clause tried
       This will never pick an index variable unless necessary.
    *)
    (* success: case is covered! *)
    (* failure: case __g,__v is not covered! *)
    (* local failure (clash) and no candidates *)
    (* local failure but no candidates *)
    (* found candidates ks <> nil *)
    (*****************)
    (*** Splitting ***)
    (*****************)
    (* In a coverage goal {{__g}} {{__l}} a @ S we instantiate each
       declaration in __g with a new EVar, then split one of these variables,
       then abstract to obtain a new coverage goal {{__g'}} {{__l'}} a @ S'
    *)
    (* instEVars ({x1:V1}...{xp:Vp} __v, p, nil) = (__v[s], [X1,...,Xn])
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
    (* createEVarSpine (__g, (__v, s)) = (S', (__v', s'))

       Invariant:
       If   __g |- s : G1   and  G1 |- __v = Pi {V1 .. Vn}. W : __l
       and  G1, V1 .. Vn |- W atomic
       then __g |- s' : G2  and  G2 |- __v' : __l
       and  S = X1; ...; Xn; Nil
       and  __g |- W [1.2...n. s o ^n] = __v' [sjfh']
       and  __g |- S : __v [s] >  __v' [s']
    *)
    (* changed to use createEVar? *)
    (* Sun Dec 16 10:36:59 2001 -fp *)
    (* s = id *)
    (* __g |- V1[s] : __l *)
    (* Uni or other cases should be impossible *)
    (* createAtomConst (__g, c) = (__u', (__v', s'))

       Invariant:
       If   S |- c : Pi {V1 .. Vn}. __v
       then . |- __u' = c @ (X1; .. Xn; Nil)
       and  . |- __u' : __v' [s']
    *)
    (* mod: m2/metasyn.fun allows skolem constants *)
    (* createAtomBVar (__g, k) = (__u', (__v', s'))

       Invariant:
       If   __g |- k : Pi {V1 .. Vn}. __v
       then . |- __u' = k @ (Xn; .. Xn; Nil)
       and  . |- __u' : __v' [s']
    *)
    (* end m2/metasyn.fun *)
    (* createAtomProj (__g, #i(l), (__v, s)) = (__u', (__v', s'))

       Invariant:
       If   __g |- #i(l) : Pi {V1 .. Vn}. Va
       and  __g |- Pi {V1..Vn}. Va = __v[s] : type
       then . |- __u' = #i(l) @ (X1; .. Xn; Nil)
       and  . |- __u' : __v' [s']
    *)
    (* createEVarSub __g' = s

       Invariant:
       If   . |- __g' ctx
       then . |- s : __g' and s instantiates each x:A with an EVar . |- x : A

       Update: Always use empty context. Sat Dec  8 13:19:58 2001 -fp
    *)
    (* was   val __v' = I.EClo (__v, s)
                   val x = I.newEVar (I.Null, __v') Mon Feb 28 15:32:09 2011 --cs *)
    (* hack *)
    (* blockCases (__g, __Vs, B, (Gsome, piDecs), sc) =

       If __g |- __v[s] : type
          . |- Gsome ctx and Gsome |- piDecs decList
       then sc is called for any x:A in piDecs such thtat
            __g |- __v[s] = A[t] : type
            where t instantiates variable in Gsome with new EVars
    *)
    (* . |- t : Gsome *)
    (* was: the above, using t' for t below *)
    (*  BUG. Breach in the invariant:
                         __g |- sk : .
                         . |- t: Gsome
                         __g <> .

                         replace t by t' in I.newLVar (sk, (cid, t))
                      --cs Fri Jan  3 11:07:41 2003 *)
    (* __g |- t' : Gsome *)
    (* __g |- t : __g' and __g' |- ({_:__v'},piDecs) decList *)
    (* so __g |- __v'[t'] : type *)
    (* will trail *)
    (* will trail *)
    (* will trail *)
    (* splitEVar (x, W, sc) = ()

       calls sc () for all cases, after instantiation of x
       W are the currently possible worlds
    *)
    (* was
   fun lowerSplit (__g, __Vs, W, sc, print) = lowerSplitW (__g, Whnf.whnf __Vs, W, sc, print)
    and lowerSplitW (__g, __Vs as (I.Root (I.Const a, _), s), W, sc, pr) =
        let
        val _ = print ("Consider P cases for "  ^ Print.expToString (__g, I.EClo __Vs) ^ "\n")
val _ = pr () *)
    (* will trail *)
    (*        val _ = print ("Consider W cases for "  ^ Print.expToString (__g, I.EClo __Vs) ^ "\n")
val _ = pr () *)
    (* will trail *)
    (*        val _ = print ("Consider C cases for "  ^ Print.expToString (__g, I.EClo __Vs) ^ "\n") *)
    (* will trail *)
    (* GX = I.Null *)
    (* abstract (__v, s) = __v'
       where __v' = {{__g}} __Vs' and __g abstracts over all EVars in __v[s]
       in arbitrary order respecting dependency

       Invariants: . |- __v[s] : type
       Effect: may raise Constraints.Error (constrs)
     *)
    (* splitVar ({{__g}} __v, p, k, W) = Some [{{G1}} V1 ,..., {{Gn}} Vn]
                                  or None
       where {{Gi}} Vi are new coverage goals obtained by
       splitting kth variable in __g, counting right-to-left.

       returns None if splitting variable k fails because of constraints

       W are the worlds defined for current predicate

       Invariants:
       |__g| = p
       k <= |__g|
       __g |- __v : type
       {{Gi}} Vi cover {{__g}} __v
    *)
    (* split on k'th variable, counting from innermost *)
    (* may raise Constraints.Error *)
    (* Constraints.Error could be raised by abstract *)
    (**********************)
    (* Finitary Splitting *)
    (**********************)
    (*
       A splittable variable x : __v is called finitary
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
    (* occursInMatchPos (k, __u, ci) = true
       if k occur in __u in a matchable position according to the coverage
       instructions ci
    *)
    (* instEVarsSkip ({x1:V1}...{xp:Vp} __v, p, nil, ci) = (__v[s], [X1,...,Xn])
       where . |- s : {x1:V1}...{xp:Vp}
       and s = Xp...X1.id, all Xi are new EVars that actually occur in a "Match" argument
       and ci are the coverage instructions (Match or Skip) for the target type of __v
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
    (* recursive x = true
       iff the instantiation of x : {{__g}} a @ S contains an
           EVar y : {{__g'}} b @ S such that a <|= b

       This means there is no guarantee that x : {{__g}} a @ S has only
       a finite number of instances
    *)
    (* GX = I.Null*)
    (* is this always true? --cs!!!*)
    (* LVars are ignored here.  OK because never splittable? *)
    (* Sat Dec 15 22:42:10 2001 -fp !!! *)
    (* finitary1 (x, k, W, f, cands)
        = ((k, n)::cands) if x is finitary with n possibilities
        = cands if x is not finitary
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
    fun finitary1 (x as I.EVar(r, I.Null, VX, _), k, W, f, cands, print) =
        ( resetCount () ;
          chatter 7 (fn () => "Trying " ^ Print.expToString (I.Null, x) ^ " : "
                     ^ Print.expToString (I.Null, VX) ^ ".\n") ;
          ( splitEVar (x, W, fn () => (f (); if recursive x
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
       where all ki are finitary with ni possibilities for x(i+k)
    *)
    (* parameter blocks can never be split *)
    (* finitary ({{__g}} __v, p, W) = [(k1,n1),...,(km,nm)]
       where ki are indices of splittable variables in __g with ni possibilities
       and |__g| = p
       and ci are the coverage instructions for the target type of __v
    *)
    (***********************************)
    (* Contraction based on uniqueness *)
    (***********************************)
    (* eqExp (__u[s], __u'[s']) = true iff __g |- __u[s] == __u'[s'] : __v
       Invariants:
         __g |- __u[s] : __v
         __g |- __u'[s'] : __v
         __u[s], __u'[s'] contain no EVars
       Note that the typing invariant is satisfied because
       input arguments can only depend on other input arguments,
       but not undetermined or output arguments.
       Similar remarks apply to functions below
    *)
    (* eqInpSpine (ms, S1[s1], S2[s2]) = true
       iff __U1[s1] == __U2[s2] for all input (+) arguments in S1, S2
       according to uniqueness mode spine ms
       Invariants: typing as in eqExp, ms ~ S1, ms ~ S2
    *)
    (* ignore Star, Minus, Minus1 *)
    (* other cases should be impossible since spines must match *)
    (* eqInp (__g, k, a, S[s], ms) = [k1+k,...,kn+k]
       where k1,...,kn are the deBruijn indices of those declarations
       ki:a @ Si in such that G0 |- Si[^ki+k] == S[s] on all input arguments
       according to mode spine ms.
       Here __g = ...kn:a @ Sn, ..., k1:a @ S1, ...
    *)
    (* defined type families disallowed here *)
    (* other cases should be impossible *)
    (* contractionCands (__g, k) = [[k11,...,k1{n1}],...,[km1,...,km{nm}]]
       where each [kj1,...,kj{nj}] are deBruijn indices in __g (counting from right)
       such that kji:aj @ Sji ... kj{nj}:aj @ Sj{nj} and
       Sji...Sj{nj} agree on their input arguments according to the
       uniqueness mode spine for aj
    *)
    (* defined type families disallowed here *)
    (* using only one uniqueness declaration per type family *)
    (* ignore Pi --- contraction cands unclear *)
    (* ignore blocks --- contraction cands unclear *)
    (* isolateSplittable ((G0, {{G1}}__v, p) = ((G0@G1), __v) where |G1| = p
       This isolates the splittable variable G1@G1 from an old-style
       coverage goal ({{__g}}__v, p)
    *)
    (* unifyUOutSpine (ms, S1[s1], S2[s2]) = true
       iff __U1[s1] == __U2[s2] for all unique output (-1) arguments in S1, S2
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
    (* unifyUOut2 ([X1,...,Xp], k1, k2) = (see unifyOutEvars (x{k1}, x{k2})) *)
    (* unifyOut1 ([X1,...,Xp], [k1, k2, ..., kn] = true
       if x{k1} "==" x{k2} "==" ... "==" x{kn} according to unifyOutEvars
    *)
    (* unifyOut ([X1,...,Xp], [[k11,...,k1{n1}],...,[km1,...,km{nm}]]) = true
       if unifyOut1 ([X1,...,Xp], [kj1,...,kj{nj}]) for each j
    *)
    (* contractAll ({{__g}}__v, p, ucands) = Some(__v',p')
       iff (__v',p') is the result of contracting unique output arguments
           according to contraction candidates ucands
           of variables in __g where all input arguments agree
       returns None if unique output arguments are non-unifiable
       may be the identity if output arguments are already identity
          or unsolvable constraints during contraction
       Invariants: p = |__g| (__g contains the splittable variables)
    *)
    (* as in splitVar *)
    (* as in splitVar, may raise Constraints.Error *)
    (* unique outputs not simultaneously unifiable *)
    (* contract ({{__g}}V0, p, ci, lab) = Some(__v',p')
       iff (__v',p') is the result of contracting unique output arguments
           of variables in __g where all input arguments agree
       returns None if unique output arguments are non-unifiable
       may be the identity if output arguments are already identity
          or unsolvable constraints during contraction
       ci and lab are used for printing
       Invariants: p = |__g| (__g contains the splittable variables)
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
    (* cover (__v, p, (W, ci), ccs, lab, missing) = missing'
       covers ([(V1,p1),...,(Vi,pi)], (W, ci), ccs, missing) = missing'

       check if Match arguments (+ for input, - for output) in __v or all Vi, respectively,
       are covered by clauses ccs, adding omitted cases to missing to yield missing'.

       __v = {{__g}} {{__l}} a @ S where |__g| = p and __g contains the splittable
       variables while __l contains the local parameters

       W are the worlds for type family a
       ci are the cover instructions matching S

       lab is the label for the current goal for tracing purposes
    *)
    (* __v is covered by unique output inconsistency *)
    (* __v is covered: return missing patterns from other cases *)
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
    (* createCoverClause (__g, __v, 0) = ({{__g}} __v, |__g|)
       where {{__g}} __v is in NF
    *)
    (* createCoverGoal (., ({{__g}} {{GL}} a @ S, s), p, ms) = __v' with |__g| = p
       createCoverGoal (GL, (a @ S, s), 0, ms) = a @ S'
       createCoverSpine ((S, s), (__v', s'), ms) = S'

       where all variables in __g are replaced by new EVars in __v to yield __v'
       and output arguments in S are replaced by new EVars in __v to yield __v'

       __g are the externally quantified variables
       GL are the locally introduced parameter for the current subgoal a @ S

       Invariants: . |- ({{__g}} {{GL}} a @ S)[s] : type
                   |__g| = p
                   ms matches S
                   . | S[s] : __v'[s'] > type
                   . |- __v'[s'] : type
    *)
    (* p > 0, __g = I.Null *)
    (* was  val x = I.newEVar (__g, I.EClo (V1, s))  Mon Feb 28 15:33:52 2011 -cs *)
    (* s = id, p >= 0 *)
    (* replace output argument by new variable *)
    (* strengthen __g based on subordination *)
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
    (* checkOut (__g, (__v, s)) = ()
       checks if the most general goal __v' is locally output-covered by __v
       Effect: raises Error (msg) otherwise
    *)
    let rec checkOut (__g, (__v, s)) =
      let a = I.targetFam __v in
      let Some ms = ModeTable.modeLookup a in
      let cOut = outCoverInst ms in
      let (__v', q) = createCoverClause (__g, (I.EClo (__v, s)), 0) in
      let _ =
        if !Global.doubleCheck
        then TypeCheck.typeCheck (I.Null, (__v', (I.Uni I.Type)))
        else () in
      let V0 = createCoverGoal (I.Null, (__v', I.id), q, ms) in
      let (V0', p) = abstract (V0, I.id) in
      let W = W.lookup a in
      let missing = cover (V0', p, (W, cOut), (Output (__v', q)), Top, nil) in
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
        (* abstract all variables in __g *)(* replace output by new EVars *)
        (* abstract will double-check *))
    (**********************************************)
    (* New code for coverage checking of Tomega   *)
    (* Started Sun Nov 24 11:02:25 2002  -fp      *)
    (* First version Tue Nov 26 19:29:12 2002 -fp *)
    (**********************************************)
    (* cg = CGoal (__g, S)  with __g |- S : {{__g'}} type *)
    type __CoverGoal =
      | CGoal of (I.dctx * I.__Spine) 
    (* cc = CClause (Gi, Si) with  Gi |- Si : {{__g}} type *)
    type __CoverClause =
      | CClause of (I.dctx * I.__Spine) 
    let rec formatCGoal (CGoal (__g, S)) =
      let _ = N.varReset I.Null in
      F.hVbox
        ((@) [Print.formatCtx (I.Null, __g);
             F.Break;
             F.Break;
             F.String "|-";
             F.space]
           Print.formatSpine (__g, S))
    let rec showPendingCGoal (CGoal (__g, S), lab) =
      F.makestring_fmt
        (F.hbox
           [F.String (labToString lab);
           F.space;
           F.String "?- ";
           formatCGoal (CGoal (__g, S));
           F.String "."])
    let rec showCClause (CClause (__g, S)) =
      let _ = N.varReset I.Null in
      F.makestring_fmt
        (F.hVbox ((@) [F.String "!- "] Print.formatSpine (__g, S)))
    let rec showSplitVar (CGoal (__g, S), k) =
      let _ = N.varReset I.Null in
      let Dec (Some x, _) = I.ctxLookup (__g, k) in
      (^) (("Split " ^ x) ^ " in ") F.makestring_fmt
        (F.hVbox (Print.formatSpine (__g, S)))
    (* newEVarSubst (__g, __g') = s
       Invariant:   If __g = xn:Vn,...,x1:V1
                  then s = X1...Xn.^k
                     __g |- s : __g'
    *)
    let rec newEVarSubst =
      function
      | (__g, I.Null) -> I.Shift (I.ctxLength __g)
      | (__g, Decl (__g', (Dec (_, __v) as __d))) ->
          let s' = newEVarSubst (__g, __g') in
          let x = Whnf.newLoweredEVar (__g, (__v, s')) in
          ((I.Dot ((I.Exp x), s'))
            (* was val __v' = I.EClo (__v, s')
                 val x = I.newEVar (__g, __v') Mon Feb 28 15:34:31 2011 -cs *))
      | (__g, Decl (__g', (NDec _ as __d))) ->
          let s' = newEVarSubst (__g, __g') in I.Dot (I.Undef, s')
      | (__g, Decl (__g', (BDec (_, (b, t)) as __d))) ->
          let s' = newEVarSubst (__g, __g') in
          let L1 = I.newLVar (s', (b, t)) in ((I.Dot ((I.Block L1), s'))
            (* was  val L1 = I.newLVar (I.Shift(0), (b, I.comp(t, s')))
             --cs Fri Jul 23 16:39:27 2010 *)
            (* -cs Fri Jul 23 16:35:04 2010  FPCHECK *)
            (* __l : Delta[t][__g'] *)(* __g |- s : __g'  __g |- __l[s'] : __v[s]
             __g |- (__l[s'].s : __g', __v *)
            (* -fp Sun Dec  1 21:10:45 2002 *)(* -cs Sun Dec  1 06:31:23 2002 *))
    (* ADec should be impossible *)
    (* checkConstraints (__g, Si[ti], cands) = cands'
       failure if constraints remain in Q[s] which indicates only partial match
       Q[s] is the clause head after matching the coverage goal.

       Invariants: if cands = Eqns (es) then es = nil.
    *)
    (* This ignores LVars, because collectEVars does *)
    (* Why is that OK?  Sun Dec 16 09:01:40 2001 -fp !!! *)
    let rec checkConstraints =
      function
      | (__g, (Si, ti), Cands ks) -> Cands ks
      | (__g, (Si, ti), Fail) -> Fail
      | (__g, (Si, ti), Eqns _) ->
          let __Xs = Abstract.collectEVarsSpine (__g, (Si, ti), nil) in
          let constrs = collectConstraints __Xs in
          (((match constrs with
             | nil -> Eqns nil
             | _ -> fail "Remaining constraints"))
            (* constraints remained: Fail without candidates *))
      (* _ = nil *)
    (* matchClause (cg, (Si, ti)) = klist
       matching coverage goal cg against instantiated coverage clause Si[ti]
       yields splitting candidates klist
    *)
    let rec matchClause (CGoal (__g, S), (Si, ti)) =
      let cands1 = matchSpine (__g, 0, (S, I.id), (Si, ti), (Eqns nil)) in
      let cands2 = resolveCands cands1 in
      let cands3 = checkConstraints (__g, (Si, ti), cands2) in cands3
    (* matchClauses (cg, ccs, klist) = klist'
       as in match, with accumulator argument klist
    *)
    let rec matchClauses =
      function
      | (cg, nil, klist) -> klist
      | ((CGoal (__g, S) as cg), (CClause (Gi, Si))::ccs, klist) ->
          let ti = newEVarSubst (__g, Gi) in
          let cands =
            CSManager.trail (function | () -> matchClause (cg, (Si, ti))) in
          ((matchClauses' (cg, ccs, (addKs (cands, klist))))
            (* __g |- ti : Gi *))
    let rec matchClauses' =
      function
      | (cg, ccs, Covered) -> Covered
      | (cg, ccs, (CandList _ as klist)) -> matchClauses (cg, ccs, klist)
    (* match (cg, ccs) = klist
       matching coverage goal cg against coverage clauses ccs
       yields candidates klist
    *)
    let rec match__ (CGoal (__g, S), ccs) =
      matchClauses ((CGoal (__g, S)), ccs, (CandList nil))
    (* abstractSpine (S, s) = CGoal (__g, S')
       Invariant: __g abstracts all EVars in S[s]
       __g |- S' : {{__g'}}type
    *)
    let rec abstractSpine (S, s) =
      let (__g', S') = Abstract.abstractSpine (S, s) in
      let namedG' = N.ctxName __g' in
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
      | (Dot (Exp (x), s), 1) -> x
      | (Dot (_, s), k) -> kthSub (s, (k - 1))
    (* subToXsRev (X1...Xn.^0) = [Xiopt,...,Xnopt]
       Invariant: Xi are either EVars (translate to Some(Xi))
                  or not (translate to None)
    *)
    let rec subToXsRev =
      function
      | Shift 0 -> nil
      | Dot (Exp (x), s) -> (::) (Some x) subToXsRev s
      | Dot (_, s) -> (::) None subToXsRev s(* n = 0 *)
    (* caseList is a list of possibilities for a variables
       to be split.  Maintained as a mutable reference so it
       can be updated in the success continuation.
    *)
    let (caseList : __CoverGoal list ref) = ref nil
    let rec resetCases () = caseList := nil
    let rec addCase cg = (!) ((::) (caseList := cg)) caseList
    let rec getCases () = !caseList
    (* splitVar (CGoal(__g, S), k, w) = Some [cg1,...,cgn]
                                  or None
       where cgi are new coverage goals obtained by
       splitting kth variable in __g, counting right-to-left.

       returns None if splitting variable k fails because of constraints

       w are the worlds defined for current predicate

       Invariants:
       k <= |__g|
       __g |- S : {{__g'}} type
       cgi cover cg
    *)
    let rec splitVar ((CGoal (__g, S) as cg), k, w) =
      ((try
          let _ = chatter 6 (function | () -> (showSplitVar (cg, k)) ^ "\n") in
          let s = newEVarSubst (I.Null, __g) in
          let x = kthSub (s, k) in
          let _ = resetCases () in
          let _ =
            splitEVar
              (x, w, (function | () -> addCase (abstractSpine (S, s)))) in
          ((Some (getCases ()))
            (* for splitting, EVars are always global *)
            (* __g = xn:V1,...,x1:Vn *)(* s = X1....Xn.^0, where . |- s : __g *)
            (* starts with k = 1 (a la deBruijn) *))
        with
        | Error constrs ->
            (chatter 7
               (function
                | () ->
                    ((^) "Inactive split:\n" Print.cnstrsToString constrs) ^
                      "\n");
             None))
      (* Constraints.Error could be raised by abstract *))
    (* finitary (CGoal (__g, S), W) = [(k1,n1),...,(km,nm)]
       where ki are indices of splittable variables in __g with ni possibilities
    *)
    let rec finitary (CGoal (__g, S), w) =
      let s = newEVarSubst (I.Null, __g) in
      let XsRev = subToXsRev s in
      ((finitarySplits
          (XsRev, 1, w, (function | () -> abstractSpine (S, s)), nil))
        (* __g = xn:Vn,...,x1:V1 *)(* for splitting, EVars are always global *)
        (* s = X1...Xn.^0,  . |- S : __g *)(* XsRev = [Some(X1),...,Some(Xn)] *))
    (***************)
    (* Contraction *)
    (***************)
    (* for explanation, see contract and contractAll above *)
    let rec contractAll (CGoal (__g, S), ucands) =
      let s = newEVarSubst (I.Null, __g) in
      let XsRev = subToXsRev s in
      ((if unifyUOut (XsRev, ucands)
        then Some (abstractSpine (S, s))
        else None)
        (* as in splitVar, may raise Constraints.Error *)
        (* for unif, EVars are always global *))
    let rec contract ((CGoal (__g, S) as cg), lab) =
      let ucands = contractionCands (__g, 1) in
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
                 Some cg)
          else Some cg)
        (* no progress if constraints remain *)) in
      let _ =
        match cgOpt' with
        | None ->
            chatter 6
              (function
               | () -> "Case impossible: conflicting unique outputs\n")
        | Some cg' ->
            chatter 6 (function | () -> (showPendingCGoal (cg', lab)) ^ "\n") in
      ((cgOpt')(* no candidates, no progress *))
    (* cover (cg, w, ccs, lab, missing) = missing'
       covers ([cg1,...,cgn], w, ccs, missing) = missing'

       Check if cover goal cg (or [cg1,..,cgn]) are covered by
       cover clauses ccs, adding missing cases to missing to yield missing'

       cg = CGoal (__g, S) where __g contains the splittable variables
       cci = CClause (Gi, Si) where Gi contains essentially existential variables

       w are the worlds for the principal type family

       lab is the label for the current goal for tracing purposes
    *)
    let rec cover (cg, w, ccs, lab, missing) =
      chatter 6 (function | () -> (showPendingCGoal (cg, lab)) ^ "\n");
      cover' ((contract (cg, lab)), w, ccs, lab, missing)
    let rec cover' =
      function
      | (Some cg, w, ccs, lab, missing) ->
          let cands = match__ (cg, ccs) in
          let cand = selectCand cands in
          ((split (cg, cand, w, ccs, lab, missing))
            (* determine splitting candidates *)(* select one candidate *))
      | (None, w, ccs, lab, missing) ->
          (chatter 6 (function | () -> "Covered\n"); missing)(* cg is covered by unique output inconsistency *)
    let rec split =
      function
      | (cg, None, w, ccs, lab, missing) ->
          (chatter 6 (function | () -> "Covered\n"); missing)
      | (cg, Some nil, w, ccs, lab, missing) ->
          (chatter 6
             (function
              | () ->
                  "No strong candidates --- calculating weak candidates\n");
           splitWeak (cg, (finitary (cg, w)), w, ccs, lab, missing))
      | (cg, Some ((k, _)::ksn), w, ccs, lab, missing) ->
          (chatter 6
             (function | () -> ((^) "Splitting on " Int.toString k) ^ "\n");
           (match splitVar (cg, k, w) with
            | Some cases -> covers (cases, w, ccs, lab, missing)
            | None ->
                (chatter 6
                   (function
                    | () -> "Splitting failed due to generated constraints\n");
                 split (cg, (Some ksn), w, ccs, lab, missing))))(* splitVar shows splitting as it happens *)
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
          split (cg, (Some ((findMin ksn) :: nil)), w, ccs, lab, missing)
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
    (* substToSpine' (s, __g, T) = S @ T
       If   __g' |- s : __g
       then __g' |- S : {{__g}} a >> a  for arbitrary a
       {{__g}} erases void declarations in __g
    *)
    let rec substToSpine' =
      function
      | (Shift n, I.Null, T) -> T
      | (Shift n, (Decl _ as __g), T) ->
          substToSpine' ((I.Dot ((I.Idx (n + 1)), (I.Shift (n + 1)))), __g, T)
      | (Dot (_, s), Decl (__g, NDec _), T) -> substToSpine' (s, __g, T)
      | (Dot (Exp (__u), s), Decl (__g, __v), T) ->
          substToSpine' (s, __g, (I.App (__u, T)))
      | (Dot (Idx n, s), Decl (__g, Dec (_, __v)), T) ->
          let (__Us, _) =
            Whnf.whnfEta (((I.Root ((I.BVar n), I.Nil)), I.id), (__v, I.id)) in
          substToSpine' (s, __g, (I.App ((I.EClo __Us), T)))
      | (Dot (_, s), Decl (__g, BDec (_, (__l, t))), T) ->
          substToSpine' (s, __g, T)(* Attempted fix, didn't work because I don't know how you
             computed splitting candidates for Blocks
             --cs Sat Jan  4 22:38:01 2003
          *)
      (* Treat like I.NDec *)(* was: I.Idx in previous line, Sun Jan  5 11:02:19 2003 -fp *)
      (* Eta-expand *)(* Unusable meta-decs are eliminated here *)
      (* Skip over NDec's; must be either Undef or Idx [from eta-expansion] *)
    (* I.Axp, I.Block(B) or other I.Undef impossible *)
    (* substToSpine (s, __g) = S
       If   __g' |- s : __g
       then __g' |- S : {{__g}} type

       Note: {{__g}} erases void declarations in __g
     *)
    let rec substToSpine (s, __g) = substToSpine' (s, __g, I.Nil)
    (* purify' __g = (__g', s) where all NDec's have been erased from __g
       If    |- __g ctx
       then  |- __g ctx and  __g' |- s : __g
    *)
    let rec purify' =
      function
      | I.Null -> (I.Null, I.id)
      | Decl (__g, NDec _) ->
          let (__g', s) = purify' __g in (((__g', (I.Dot (I.Undef, s))))
            (* __g' |- s : __g *)(* __g' |- _.s : __g,_ *))
      | Decl (__g, (Dec _ as __d)) ->
          let (__g', s) = purify' __g in
          ((((I.Decl (__g', (I.decSub (__d, s)))), (I.dot1 s)))
            (* __g' |- s : __g *)(* __g |- __d : type *)
            (* __g' |- __d[s] : type *)(* __g', __d[s] |- 1 : __d[s][^] *)
            (* __g', __d[s] |- s o ^ : __g *)(* __g', __d[s] |- 1.s o ^ : __g, __d *))
      | Decl (__g, (BDec _ as __d)) ->
          let (__g', s) = purify' __g in (((__g', (I.Dot (I.Undef, s))))
            (* __g' |- s : __g *)(* __g' |- _.s : __g,_ *))
      (* added a new case to throw out blocks
         -cs Sat Jan  4 22:55:12 2003
      *)
    (* purify __g = __g' where all NDec's have been erased from __g
       If   |- __g ctx
       then |- __g' ctx
    *)
    let rec purify (__g) = (fun (r, _) -> r) (purify' __g)
    (* coverageCheckCases (W, __Cs, __g) = R

       Invariant:
       If   __Cs = [(G1, s1) .... (Gn, sn)]
       and  Gi |- si : __g
       and  for all worlds Phi
       and  instantiations Phi |- s : __g
       there exists at least one index k and substitution   Phi |- t : Gk
       s.t.  sk o t = s
    *)
    let rec coverageCheckCases (w, __Cs, __g) =
      let _ = chatter 4 (function | () -> "[Tomega coverage checker...") in
      let _ = chatter 4 (function | () -> "\n") in
      let ccs =
        List.map
          (function | (Gi, si) -> CClause (Gi, (substToSpine (si, __g)))) __Cs in
      let _ = chatter 6 (function | () -> "[Begin covering clauses]\n") in
      let _ =
        List.app
          (function
           | cc -> chatter 6 (function | () -> (showCClause cc) ^ "\n")) ccs in
      let _ = chatter 6 (function | () -> "[End covering clauses]\n") in
      let pureG = purify __g in
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
