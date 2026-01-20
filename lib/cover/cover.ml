
module type COVER  =
  sig
    exception Error of string 
    val checkNoDef : IntSyn.cid -> unit
    val checkOut : IntSyn.dctx -> IntSyn.eclo -> unit
    val checkCovers : IntSyn.cid -> ModeSyn.__ModeSpine -> unit
    val coverageCheckCases :
      Tomega.__Worlds ->
        (IntSyn.dctx * IntSyn.__Sub) list -> IntSyn.dctx -> unit
  end;;




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
    let rec weaken __39__ __40__ =
      match (__39__, __40__) with
      | (I.Null, a) -> I.id
      | (Decl (__G', (Dec (name, __V) as D)), a) ->
          let w' = weaken (__G', a) in
          if Subordinate.belowEq ((I.targetFam __V), a)
          then I.dot1 w'
          else I.comp (w', I.shift)
    let rec createEVar (__G) (__V) =
      let w = weaken (__G, (I.targetFam __V)) in
      let iw = Whnf.invert w in
      let __G' = Whnf.strengthen (iw, __G) in
      let __X' = Whnf.newLoweredEVar (__G', (__V, iw)) in
      let __X = I.EClo (__X', w) in ((__X)
        (* G |- V : L *)(* G  |- w  : G'    *)(* G' |- iw : G     *)
        (* G' |- X' : V[iw] *)(* was I.newEvar (G', I.EClo (V, iw))  Mon Feb 28 14:30:36 2011 --cs *)
        (* G  |- X  : V     *))
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
    let rec pluralize __41__ __42__ =
      match (__41__, __42__) with | (1, s) -> s | (n, s) -> s ^ "s"
    let rec abbrevCSpine (__S) ci = __S
    let rec abbrevCGoal __43__ __44__ __45__ __46__ =
      match (__43__, __44__, __45__, __46__) with
      | (__G, __V, 0, ci) -> (__G, (abbrevCGoal' (__G, __V, ci)))
      | (__G, Pi ((__D, __P), __V), p, ci) ->
          let __D' = N.decEName (__G, __D) in
          abbrevCGoal ((I.Decl (__G, __D')), __V, (p - 1), ci)(* p > 0 *)
    let rec abbrevCGoal' __47__ __48__ __49__ =
      match (__47__, __48__, __49__) with
      | (__G, Pi ((__D, __P), __V), ci) ->
          let __D' = N.decUName (__G, __D) in
          I.Pi ((__D', __P), (abbrevCGoal' ((I.Decl (__G, __D')), __V, ci)))
      | (__G, Root (a, __S), ci) -> I.Root (a, (abbrevCSpine (__S, ci)))
    let rec formatCGoal (__V) p ci =
      let _ = N.varReset I.Null in
      let (__G, __V') = abbrevCGoal (I.Null, __V, p, ci) in
      F.HVbox
        [Print.formatCtx (I.Null, __G);
        F.Break;
        F.String "|-";
        F.Space;
        Print.formatExp (__G, __V')]
    let rec formatCGoals __50__ __51__ =
      match (__50__, __51__) with
      | ((__V, p)::nil, ci) -> [formatCGoal (__V, p, ci)]
      | ((__V, p)::__Vs, ci) ->
          (::) (((::) (formatCGoal (__V, p, ci)) F.String ",") :: F.Break)
            formatCGoals (__Vs, ci)
    let rec missingToString (__Vs) ci =
      F.makestring_fmt
        (F.Hbox [F.Vbox0 0 1 (formatCGoals (__Vs, ci)); F.String "."])
    let rec showSplitVar (__V) p k ci =
      let _ = N.varReset I.Null in
      let (__G, __V') = abbrevCGoal (I.Null, __V, p, ci) in
      let Dec (Some x, _) = I.ctxLookup (__G, k) in
      (^) (("Split " ^ x) ^ " in ") Print.expToString (__G, __V')
    let rec showPendingGoal (__V) p ci lab =
      F.makestring_fmt
        (F.Hbox
           [F.String (labToString lab);
           F.Space;
           F.String "?- ";
           formatCGoal (__V, p, ci);
           F.String "."])
    let rec buildSpine =
      function
      | 0 -> I.Nil
      | n -> I.App ((I.Root ((I.BVar n), I.Nil)), (buildSpine (n - 1)))
      (* Eta-long invariant violation -kw *)(* n > 0 *)
    let rec initCGoal' __52__ __53__ __54__ __55__ =
      match (__52__, __53__, __54__, __55__) with
      | (a, k, __G, Pi ((__D, __P), __V)) ->
          let __D' = N.decEName (__G, __D) in
          let (__V', p) = initCGoal' (a, (k + 1), (I.Decl (__G, __D')), __V) in
          ((I.Pi ((__D', I.Maybe), __V')), p)
      | (a, k, __G, Uni (I.Type)) -> ((I.Root (a, (buildSpine k))), k)
    let rec initCGoal a =
      initCGoal' ((I.Const a), 0, I.Null, (I.constType a))
    type __CoverClauses =
      | Input of I.__Exp list 
      | Output of (I.__Exp * int) 
    type __Equation =
      | Eqn of (I.dctx * I.eclo * I.eclo) 
    let rec equationToString (Eqn (__G, __Us1, __Us2)) =
      let __G' = Names.ctxLUName __G in
      let fmt =
        F.HVbox
          [Print.formatCtx (I.Null, __G');
          F.Break;
          F.String "|-";
          F.Space;
          Print.formatExp (__G', (I.EClo __Us1));
          F.Break;
          F.String "=";
          F.Space;
          Print.formatExp (__G', (I.EClo __Us2))] in
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
            ((fun k -> fun str -> ((Int.toString k) ^ ",") ^ str)) "]" ks
      | Eqns eqns -> ((^) "Eqns [\n" eqnsToString eqns) ^ "]"
    let rec fail msg = chatter 7 (fun () -> msg ^ "\n"); Fail
    let rec failAdd __56__ __57__ =
      match (__56__, __57__) with
      | (k, Eqns _) -> Cands (k :: nil)
      | (k, Cands ks) -> Cands (k :: ks)
      | (k, Fail) -> Fail(* remove duplicates? *)(* no longer matches *)
    let rec addEqn __58__ __59__ =
      match (__58__, __59__) with
      | (e, Eqns es) -> Eqns (e :: es)
      | (e, (Cands ks as cands)) -> cands
      | (e, Fail) -> Fail(* already failed: ignore new constraints *)
      (* still may match: add equation *)
    let rec unifiable (__G) (__Us1) (__Us2) =
      Unify.unifiable (__G, __Us1, __Us2)
    let rec matchEqns =
      function
      | nil -> true__
      | (Eqn (__G, __Us1, ((__U2, s2) as Us2)))::es ->
          ((match Whnf.makePatSub s2 with
            | NONE -> unifiable (__G, __Us1, __Us2)
            | Some s2' -> unifiable (__G, __Us1, (__U2, s2')))
            (* constraints will be left in this case *)) &&
            (matchEqns es)(* was: unifiable (G, Us1, Us2) *)(* Sat Dec  7 20:59:46 2002 -fp *)
      (* explicitly convert if possible *)(* For some reason, s2 is sometimes not a patSub when it should be *)
    let rec resolveCands =
      function
      | Eqns es -> if matchEqns (List.rev es) then Eqns nil else Fail
      | Cands ks -> Cands ks
      | Fail -> Fail(* why is this important? --cs !!! *)
      (* reversed equations Fri Dec 28 09:39:55 2001 -fp !!! *)
    let rec collectConstraints =
      function
      | nil -> nil
      | (EVar (_, _, _, { contents = nil }))::__Xs -> collectConstraints __Xs
      | (EVar (_, _, _, { contents = constrs }))::__Xs ->
          (@) constrs collectConstraints __Xs(* at present, do not simplify -fp *)
      (* Constraints.simplify constrs @ *)(* constrs <> nil *)
    let rec checkConstraints __60__ __61__ __62__ =
      match (__60__, __61__, __62__) with
      | (__G, __Qs, Cands ks) -> Cands ks
      | (__G, __Qs, Fail) -> Fail
      | (__G, __Qs, Eqns _) ->
          let __Xs = Abstract.collectEVars (__G, __Qs, nil) in
          let constrs = collectConstraints __Xs in
          (((match constrs with | nil -> Eqns nil | _ -> Fail))
            (* constraints remained: Fail without candidates *))
      (* _ = nil *)
    type __CandList =
      | Covered 
      | CandList of __Candidates list 
    let rec addKs __63__ __64__ =
      match (__63__, __64__) with
      | ((Cands ks as ccs), CandList klist) -> CandList (ccs :: klist)
      | ((Eqns nil as ces), CandList klist) -> Covered
      | ((Fail as cfl), CandList klist) -> CandList (cfl :: klist)
    let rec matchExp (__G) d (__Us1) (__Us2) cands =
      matchExpW (__G, d, (Whnf.whnf __Us1), (Whnf.whnf __Us2), cands)
    let rec matchExpW __65__ __66__ __67__ __68__ __69__ =
      match (__65__, __66__, __67__, __68__, __69__) with
      | (__G, d, ((Root (__H1, __S1), s1) as Us1),
         ((Root (__H2, __S2), s2) as Us2), cands) ->
          (((match (__H1, __H2) with
             | (BVar k1, BVar k2) ->
                 if k1 = k2
                 then matchSpine (__G, d, (__S1, s1), (__S2, s2), cands)
                 else
                   ((if k1 > d
                     then failAdd ((k1 - d), cands)
                     else fail "local variable / variable clash")
                   (* k1 is coverage variable, new candidate *))
             | (Const c1, Const c2) ->
                 if c1 = c2
                 then matchSpine (__G, d, (__S1, s1), (__S2, s2), cands)
                 else fail "constant / constant clash"
             | (Def d1, Def d2) ->
                 ((if d1 = d2
                   then matchSpine (__G, d, (__S1, s1), (__S2, s2), cands)
                   else
                     matchExpW
                       (__G, d, (Whnf.expandDef __Us1),
                         (Whnf.expandDef __Us2), cands))
                 (* because of strictness *))
             | (Def d1, _) ->
                 matchExpW (__G, d, (Whnf.expandDef __Us1), __Us2, cands)
             | (_, Def d2) ->
                 matchExpW (__G, d, __Us1, (Whnf.expandDef __Us2), cands)
             | (BVar k1, Const _) ->
                 ((if k1 > d
                   then failAdd ((k1 - d), cands)
                   else fail "local variable / constant clash")
                 (* k1 is coverage variable, new candidate *))
             | (Const _, BVar _) -> fail "constant / local variable clash"
             | (Proj (Bidx k1, i1), Proj (Bidx k2, i2)) ->
                 if (k1 = k2) && (i1 = i2)
                 then matchSpine (__G, d, (__S1, s1), (__S2, s2), cands)
                 else fail "block index / block index clash"
             | (Proj (Bidx k1, i1), Proj (LVar (r2, Shift k2, (l2, t2)), i2))
                 ->
                 let BDec (bOpt, (l1, t1)) = I.ctxDec (__G, k1) in
                 if (l1 <> l2) || (i1 <> i2)
                 then fail "block index / block variable clash"
                 else
                   (let cands2 =
                      matchSub
                        (__G, d, t1, (I.comp (t2, (I.Shift k2))), cands) in
                    let _ = Unify.instantiateLVar (r2, (I.Bidx (k1 - k2))) in
                    ((matchSpine (__G, d, (__S1, s1), (__S2, s2), cands2))
                      (* was: t2 in prev line, July 22, 2010 -fp -cs *)
                      (* instantiate instead of postponing because LVars are *)
                      (* only instantiated to Bidx which are rigid *)
                      (* Sun Jan  5 12:03:13 2003 -fp *)))
             | (BVar k1, Proj _) ->
                 ((if k1 > d
                   then failAdd ((k1 - d), cands)
                   else fail "local variable / block projection clash")
                 (* k1 is splittable, new candidate *))
             | (Const _, Proj _) -> fail "constant / block projection clash"
             | (Proj _, Const _) -> fail "block projection / constant clash"
             | (Proj _, BVar _) ->
                 fail "block projection / local variable clash"))
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
      | (__G, d, (Lam (__D1, __U1), s1), (Lam (__D2, __U2), s2), cands) ->
          matchExp
            ((I.Decl (__G, (I.decSub (__D1, s1)))), (d + 1),
              (__U1, (I.dot1 s1)), (__U2, (I.dot1 s2)), cands)
      | (__G, d, (Lam (__D1, __U1), s1), (__U2, s2), cands) ->
          matchExp
            ((I.Decl (__G, (I.decSub (__D1, s1)))), (d + 1),
              (__U1, (I.dot1 s1)),
              ((I.Redex
                  ((I.EClo (__U2, I.shift)),
                    (I.App ((I.Root ((I.BVar 1), I.Nil)), I.Nil)))),
                (I.dot1 s2)), cands)
      | (__G, d, (__U1, s1), (Lam (__D2, __U2), s2), cands) ->
          matchExp
            ((I.Decl (__G, (I.decSub (__D2, s2)))), (d + 1),
              ((I.Redex
                  ((I.EClo (__U1, I.shift)),
                    (I.App ((I.Root ((I.BVar 1), I.Nil)), I.Nil)))),
                (I.dot1 s1)), (__U2, (I.dot1 s2)), cands)
      | (__G, d, __Us1, ((EVar _, s2) as Us2), cands) ->
          addEqn ((Eqn (__G, __Us1, __Us2)), cands)(* eta-expand *)
      (* eta-expand *)
    let rec matchSpine __70__ __71__ __72__ __73__ __74__ =
      match (__70__, __71__, __72__, __73__, __74__) with
      | (__G, d, (I.Nil, _), (I.Nil, _), cands) -> cands
      | (__G, d, (SClo (__S1, s1'), s1), __Ss2, cands) ->
          matchSpine (__G, d, (__S1, (I.comp (s1', s1))), __Ss2, cands)
      | (__G, d, __Ss1, (SClo (__S2, s2'), s2), cands) ->
          matchSpine (__G, d, __Ss1, (__S2, (I.comp (s2', s2))), cands)
      | (__G, d, (App (__U1, __S1), s1), (App (__U2, __S2), s2), cands) ->
          let cands' = matchExp (__G, d, (__U1, s1), (__U2, s2), cands) in
          matchSpine (__G, d, (__S1, s1), (__S2, s2), cands')
    let rec matchDec (__G) d (Dec (_, __V1), s1) (Dec (_, __V2), s2) cands =
      matchExp (__G, d, (__V1, s1), (__V2, s2), cands)
    let rec matchSub __75__ __76__ __77__ __78__ __79__ =
      match (__75__, __76__, __77__, __78__, __79__) with
      | (__G, d, Shift n1, Shift n2, cands) -> cands
      | (__G, d, Shift n, (Dot _ as s2), cands) ->
          matchSub
            (__G, d, (I.Dot ((I.Idx (n + 1)), (I.Shift (n + 1)))), s2, cands)
      | (__G, d, (Dot _ as s1), Shift m, cands) ->
          matchSub
            (__G, d, s1, (I.Dot ((I.Idx (m + 1)), (I.Shift (m + 1)))), cands)
      | (__G, d, Dot (Ft1, s1), Dot (Ft2, s2), cands) ->
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
                matchExp (__G, d, (__U1, I.id), (__U2, I.id), cands)
            | (Exp (__U1), Idx n2) ->
                matchExp
                  (__G, d, (__U1, I.id),
                    ((I.Root ((I.BVar n2), I.Nil)), I.id), cands)
            | (Idx n1, Exp (__U2)) ->
                matchExp
                  (__G, d, ((I.Root ((I.BVar n1), I.Nil)), I.id),
                    (__U2, I.id), cands) in
          matchSub (__G, d, s1, s2, cands1)(* by invariant *)
    let rec matchTop (__G) d (__Us1) (__Us2) ci cands =
      matchTopW (__G, d, (Whnf.whnf __Us1), (Whnf.whnf __Us2), ci, cands)
    let rec matchTopW __80__ __81__ __82__ __83__ __84__ __85__ =
      match (__80__, __81__, __82__, __83__, __84__, __85__) with
      | (__G, d, (Root (Const c1, __S1), s1), (Root (Const c2, __S2), s2),
         ci, cands) ->
          ((if c1 = c2
            then matchTopSpine (__G, d, (__S1, s1), (__S2, s2), ci, cands)
            else fail "type family clash")
          (* unify spines, skipping output and ignore arguments in modeSpine *))
      | (__G, d, (Pi ((__D1, _), __V1), s1), (Pi ((__D2, _), __V2), s2), ci,
         cands) ->
          matchTopW
            ((I.Decl (__G, __D1)), (d + 1), (__V1, (I.dot1 s1)),
              (__V2, (I.dot1 s2)), ci, cands)(* Sat Dec 22 23:53:44 2001 -fp !!! *)
      (* and no splittable variables should be suggested here *)
      (* we do not match D1 and D2, since D1 is always an instance of D2 *)
      (* this case can only arise in output coverage *)
      (* fails, with no candidates since type families don't match *)
    let rec matchTopSpine __86__ __87__ __88__ __89__ __90__ __91__ =
      match (__86__, __87__, __88__, __89__, __90__, __91__) with
      | (__G, d, (I.Nil, _), (I.Nil, _), Cnil, cands) -> cands
      | (__G, d, (SClo (__S1, s1'), s1), __Ss2, ci, cands) ->
          matchTopSpine
            (__G, d, (__S1, (I.comp (s1', s1))), __Ss2, ci, cands)
      | (__G, d, __Ss1, (SClo (__S2, s2'), s2), ci, cands) ->
          matchTopSpine
            (__G, d, __Ss1, (__S2, (I.comp (s2', s2))), ci, cands)
      | (__G, d, (App (__U1, __S1), s1), (App (__U2, __S2), s2), Match ci',
         cands) ->
          let cands' = matchExp (__G, d, (__U1, s1), (__U2, s2), cands) in
          matchTopSpine (__G, d, (__S1, s1), (__S2, s2), ci', cands')
      | (__G, d, (App (__U1, __S1), s1), (App (__U2, __S2), s2), Skip ci',
         cands) -> matchTopSpine (__G, d, (__S1, s1), (__S2, s2), ci', cands)
      (* an argument that need not be covered (Skip) *)
      (* an argument that must be covered (Match) *)
    let rec matchClause __92__ __93__ __94__ __95__ =
      match (__92__, __93__, __94__, __95__) with
      | (__G, ps', ((Root (_, _), s) as qs), ci) ->
          checkConstraints
            (__G, qs,
              (resolveCands (matchTop (__G, 0, ps', qs, ci, (Eqns nil)))))
      | (__G, ps', (Pi ((Dec (_, __V1), _), __V2), s), ci) ->
          let __X1 = Whnf.newLoweredEVar (__G, (__V1, s)) in
          ((matchClause (__G, ps', (__V2, (I.Dot ((I.Exp __X1), s))), ci))
            (* changed to use subordination and strengthening here *)
            (* Sun Dec 16 10:39:34 2001 -fp *)(* val X1 = createEVar (G, I.EClo (V1, s)) *)
            (* changed back --- no effect *)(* was val X1 = I.newEVar (G, I.EClo (V1, s)) Mon Feb 28 14:37:22 2011 -cs *)
            (* was: I.Null instead of G in line above Wed Nov 21 16:40:40 2001 *))
    let rec matchSig __96__ __97__ __98__ __99__ __100__ =
      match (__96__, __97__, __98__, __99__, __100__) with
      | (__G, ps', nil, ci, klist) -> klist
      | (__G, ps', (__V)::ccs', ci, klist) ->
          let cands =
            CSManager.trail
              (fun () -> matchClause (__G, ps', (__V, I.id), ci)) in
          matchSig' (__G, ps', ccs', ci, (addKs (cands, klist)))
    let rec matchSig' __101__ __102__ __103__ __104__ __105__ =
      match (__101__, __102__, __103__, __104__, __105__) with
      | (__G, ps', ccs, ci, Covered) -> Covered
      | (__G, ps', ccs, ci, CandList klist) ->
          matchSig (__G, ps', ccs, ci, (CandList klist))(* not yet covered: continue to search *)
      (* already covered: return *)
    let rec matchBlocks __106__ __107__ __108__ __109__ __110__ __111__
      __112__ __113__ =
      match (__106__, __107__, __108__, __109__, __110__, __111__, __112__,
              __113__)
      with
      | (__G, s', nil, __V, k, i, ci, klist) -> klist
      | (__G, s', (Dec (_, __V'))::piDecs, __V, k, i, ci, klist) ->
          let cands =
            CSManager.trail
              (fun () -> matchClause (__G, (__V, I.id), (__V', s'), ci)) in
          let s'' =
            I.Dot ((I.Exp (I.Root ((I.Proj ((I.Bidx k), i)), I.Nil))), s') in
          matchBlocks'
            (__G, s'', piDecs, __V, k, (i + 1), ci, (addKs (cands, klist)))
    let rec matchBlocks' __114__ __115__ __116__ __117__ __118__ __119__
      __120__ __121__ =
      match (__114__, __115__, __116__, __117__, __118__, __119__, __120__,
              __121__)
      with
      | (__G, s', piDecs, __V, k, i, ci, Covered) -> Covered
      | (__G, s', piDecs, __V, k, i, ci, klist) ->
          matchBlocks (__G, s', piDecs, __V, k, i, ci, klist)
    let rec matchCtx __122__ __123__ __124__ __125__ __126__ __127__ __128__
      =
      match (__122__, __123__, __124__, __125__, __126__, __127__, __128__)
      with
      | (__G, s', I.Null, __V, k, ci, klist) -> klist
      | (__G, s', Decl (G'', Dec (_, __V')), __V, k, ci, klist) ->
          let s'' = I.comp (I.shift, s') in
          let cands =
            CSManager.trail
              (fun () -> matchClause (__G, (__V, I.id), (__V', s''), ci)) in
          ((matchCtx'
              (__G, s'', G'', __V, (k + 1), ci, (addKs (cands, klist))))
            (*  G'', V' |- ^ : G''
              G |- s' : G'', V'
          *)
            (*  G |- ^ o s' : G'' *))
      | (__G, s', Decl (G'', BDec (_, (cid, s))), __V, k, ci, klist) ->
          let (Gsome, piDecs) = I.constBlock cid in
          let s'' = I.comp (I.shift, s') in
          let klist' =
            matchBlocks
              (__G, (I.comp (s, s'')), piDecs, __V, k, 1, ci, klist) in
          ((matchCtx' (__G, s'', G'', __V, (k + 1), ci, klist'))
            (* G'' |- s : Gsome,
             G |- s'' : G''
             G |- s o s'' : Gsome
             Gsome |- piDecs : ctx
          *))
      (* will always fail for input coverage *)
    let rec matchCtx' __129__ __130__ __131__ __132__ __133__ __134__ __135__
      =
      match (__129__, __130__, __131__, __132__, __133__, __134__, __135__)
      with
      | (__G, s', __G', __V, k, ci, Covered) -> Covered
      | (__G, s', __G', __V, k, ci, CandList klist) ->
          matchCtx (__G, s', __G', __V, k, ci, (CandList klist))
    let rec matchOut __136__ __137__ __138__ __139__ __140__ =
      match (__136__, __137__, __138__, __139__, __140__) with
      | (__G, __V, ci, (__V', s'), 0) ->
          let cands =
            matchTop (__G, 0, (__V, I.id), (__V', s'), ci, (Eqns nil)) in
          let cands' = resolveCands cands in
          let cands'' = checkConstraints (__G, (__V', s'), cands') in
          addKs (cands'', (CandList nil))
      | (__G, __V, ci, ((Pi ((Dec (_, V1'), _), V2') as V'), s'), p) ->
          let __X1 = Whnf.newLoweredEVar (__G, (V1', s')) in
          ((matchOut
              (__G, __V, ci, (V2', (I.Dot ((I.Exp __X1), s'))), (p - 1)))
            (* was val X1 = I.newEVar (G, I.EClo (V1', s')) Mon Feb 28 14:38:21 2011 -cs *))
      (* p > 0 *)
    let rec match__ __141__ __142__ __143__ __144__ __145__ =
      match (__141__, __142__, __143__, __144__, __145__) with
      | (__G, (Root (Const a, __S) as V), 0, ci, Input ccs) ->
          matchCtx'
            (__G, I.id, __G, __V, 1, ci,
              (matchSig (__G, (__V, I.id), ccs, ci, (CandList nil))))
      | (__G, __V, 0, ci, Output (__V', q)) ->
          matchOut (__G, __V, ci, (__V', (I.Shift (I.ctxLength __G))), q)
      | (__G, Pi ((__D, _), __V'), p, ci, ccs) ->
          match__ ((I.Decl (__G, __D)), __V', (p - 1), ci, ccs)
    let rec insert __146__ __147__ =
      match (__146__, __147__) with
      | (k, nil) -> (k, 1) :: nil
      | (k, ((k', n')::ksn' as ksn)) ->
          (match Int.compare (k, k') with
           | LESS -> (k, 1) :: ksn
           | EQUAL -> (k', (n' + 1)) :: ksn'
           | GREATER -> (::) (k', n') insert (k, ksn'))
    let rec join __148__ __149__ =
      match (__148__, __149__) with
      | (nil, ksn) -> ksn
      | (k::ks, ksn) -> join (ks, (insert (k, ksn)))
    let rec selectCand =
      function | Covered -> NONE | CandList klist -> selectCand' (klist, nil)
      (* success: case is covered! *)
    let rec selectCand' __150__ __151__ =
      match (__150__, __151__) with
      | (nil, ksn) -> Some ksn
      | ((Fail)::klist, ksn) -> selectCand' (klist, ksn)
      | ((Cands nil)::klist, ksn) -> selectCand' (klist, ksn)
      | ((Cands ks)::klist, ksn) -> selectCand' (klist, (join (ks, ksn)))
      (* found candidates ks <> nil *)(* local failure but no candidates *)
      (* local failure (clash) and no candidates *)
      (* failure: case G,V is not covered! *)
    let rec instEVars (__Vs) p (XsRev) =
      instEVarsW ((Whnf.whnf __Vs), p, XsRev)
    let rec instEVarsW __152__ __153__ __154__ =
      match (__152__, __153__, __154__) with
      | (__Vs, 0, XsRev) -> (__Vs, XsRev)
      | ((Pi ((Dec (xOpt, __V1), _), __V2), s), p, XsRev) ->
          let __X1 = Whnf.newLoweredEVar (I.Null, (__V1, s)) in
          ((instEVars
              ((__V2, (I.Dot ((I.Exp __X1), s))), (p - 1),
                ((Some __X1) :: XsRev)))
            (* p > 0 *)(* all EVars are global *)
            (* was  val X1 = I.newEVar (I.Null, I.EClo (V1, s))  all EVars are global *))
      | ((Pi ((BDec (_, (l, t)), _), __V2), s), p, XsRev) ->
          let __L1 = I.newLVar ((I.Shift 0), (l, (I.comp (t, s)))) in
          ((instEVars
              ((__V2, (I.Dot ((I.Block __L1), s))), (p - 1), (NONE :: XsRev)))
            (* p > 0 *)(* new -fp Sun Dec  1 20:58:06 2002 *)
            (* new -cs  Sun Dec  1 06:27:57 2002 *))
      (* . |- s : G0 *)(* G0 |- t : Gsome *)
    let (caseList : (I.__Exp * int) list ref) = ref nil
    let rec resetCases () = caseList := nil
    let rec addCase (__V) p = (!) ((::) (caseList := (__V, p))) caseList
    let rec getCases () = !caseList
    let rec createEVarSpine (__G) (__Vs) =
      createEVarSpineW (__G, (Whnf.whnf __Vs))
    let rec createEVarSpineW __155__ __156__ =
      match (__155__, __156__) with
      | (__G, ((Root _, s) as Vs)) -> (I.Nil, __Vs)
      | (__G, (Pi (((Dec (_, __V1) as D), _), __V2), s)) ->
          let __X = createEVar (__G, (I.EClo (__V1, s))) in
          let (__S, __Vs) =
            createEVarSpine (__G, (__V2, (I.Dot ((I.Exp __X), s)))) in
          ((((I.App (__X, __S)), __Vs))(* G |- V1[s] : L *))
      (* s = id *)
    let rec createAtomConst (__G) (Const cid as H) =
      let __V = I.constType cid in
      let (__S, __Vs) = createEVarSpine (__G, (__V, I.id)) in
      ((I.Root (__H, __S)), __Vs)
    let rec createAtomBVar (__G) k =
      let Dec (_, __V) = I.ctxDec (__G, k) in
      let (__S, __Vs) = createEVarSpine (__G, (__V, I.id)) in
      ((I.Root ((I.BVar k), __S)), __Vs)
    let rec createAtomProj (__G) (__H) (__V, s) =
      let (__S, __Vs') = createEVarSpine (__G, (__V, s)) in
      ((I.Root (__H, __S)), __Vs')
    let rec constCases __157__ __158__ __159__ __160__ =
      match (__157__, __158__, __159__, __160__) with
      | (__G, __Vs, nil, sc) -> ()
      | (__G, __Vs, (Const c)::sgn', sc) ->
          let (__U, __Vs') = createAtomConst (__G, (I.Const c)) in
          let _ =
            CSManager.trail
              (fun () ->
                 if Unify.unifiable (__G, __Vs, __Vs') then sc __U else ()) in
          constCases (__G, __Vs, sgn', sc)
    let rec paramCases __161__ __162__ __163__ __164__ =
      match (__161__, __162__, __163__, __164__) with
      | (__G, __Vs, 0, sc) -> ()
      | (__G, __Vs, k, sc) ->
          let (__U, __Vs') = createAtomBVar (__G, k) in
          let _ =
            CSManager.trail
              (fun () ->
                 if Unify.unifiable (__G, __Vs, __Vs') then sc __U else ()) in
          paramCases (__G, __Vs, (k - 1), sc)
    let rec createEVarSub =
      function
      | I.Null -> I.id
      | Decl (__G', (Dec (_, __V) as D)) ->
          let s = createEVarSub __G' in
          let __X = Whnf.newLoweredEVar (I.Null, (__V, s)) in
          ((I.Dot ((I.Exp __X), s))
            (* was   val V' = I.EClo (V, s)
                   val X = I.newEVar (I.Null, V') Mon Feb 28 15:32:09 2011 --cs *))
    let rec blockName cid = I.conDecName (I.sgnLookup cid)
    let rec blockCases (__G) (__Vs) cid (Gsome, piDecs) sc =
      let t = createEVarSub Gsome in
      let sk = I.Shift (I.ctxLength __G) in
      let t' = I.comp (t, sk) in
      let lvar = I.newLVar (sk, (cid, t)) in
      ((blockCases' (__G, __Vs, (lvar, 1), (t', piDecs), sc))
        (* . |- t : Gsome *)(* was: the above, using t' for t below *)
        (*  BUG. Breach in the invariant:
                         G |- sk : .
                         . |- t: Gsome
                         G <> .

                         replace t by t' in I.newLVar (sk, (cid, t))
                      --cs Fri Jan  3 11:07:41 2003 *)
        (* G |- t' : Gsome *))
    let rec blockCases' __165__ __166__ __167__ __168__ __169__ =
      match (__165__, __166__, __167__, __168__, __169__) with
      | (__G, __Vs, (lvar, i), (t, nil), sc) -> ()
      | (__G, __Vs, (lvar, i), (t, (Dec (_, __V'))::piDecs), sc) ->
          let (__U, __Vs') =
            createAtomProj (__G, (I.Proj (lvar, i)), (__V', t)) in
          let _ =
            CSManager.trail
              (fun () ->
                 if Unify.unifiable (__G, __Vs, __Vs') then sc __U else ()) in
          let t' = I.Dot ((I.Exp (I.Root ((I.Proj (lvar, i)), I.Nil))), t) in
          ((blockCases' (__G, __Vs, (lvar, (i + 1)), (t', piDecs), sc))
            (* G |- t : G' and G' |- ({_:V'},piDecs) decList *)(* so G |- V'[t'] : type *))
    let rec worldCases __170__ __171__ __172__ __173__ =
      match (__170__, __171__, __172__, __173__) with
      | (__G, __Vs, Worlds nil, sc) -> ()
      | (__G, __Vs, Worlds (cid::cids), sc) ->
          (blockCases (__G, __Vs, cid, (I.constBlock cid), sc);
           worldCases (__G, __Vs, (T.Worlds cids), sc))
    let rec lowerSplitW __174__ __175__ __176__ =
      match (__174__, __175__, __176__) with
      | ((EVar (_, __G, __V, _) as X), __W, sc) ->
          let sc' (__U) =
            if Unify.unifiable (__G, (__X, I.id), (__U, I.id))
            then sc ()
            else () in
          let _ = paramCases (__G, (__V, I.id), (I.ctxLength __G), sc') in
          let _ = worldCases (__G, (__V, I.id), __W, sc') in
          let _ =
            constCases
              (__G, (__V, I.id), (Index.lookup (I.targetFam __V)), sc') in
          ((())
            (* will trail *)(* will trail *)(* will trail *))
      | (Lam (__D, __U), __W, sc) -> lowerSplitW (__U, __W, sc)
    let rec splitEVar (__X) (__W) sc = lowerSplitW (__X, __W, sc)
    let rec abstract (__V) s =
      let (i, __V') = Abstract.abstractDecImp (I.EClo (__V, s)) in
      let _ =
        if !Global.doubleCheck
        then TypeCheck.typeCheck (I.Null, (__V', (I.Uni I.Type)))
        else () in
      (__V', i)
    let rec splitVar (__V) p k (__W, ci) =
      ((try
          let _ = chatter 6 (fun () -> (showSplitVar (__V, p, k, ci)) ^ "\n") in
          let ((__V1, s), XsRev) = instEVars ((__V, I.id), p, nil) in
          let Some (__X) = List.nth (XsRev, (k - 1)) in
          let _ = resetCases () in
          let _ =
            splitEVar (__X, __W, (fun () -> addCase (abstract (__V1, s)))) in
          ((Some (getCases ()))
            (* split on k'th variable, counting from innermost *)
            (* may raise Constraints.Error *))
        with
        | Error constrs ->
            (chatter 7
               (fun () ->
                  ((^) "Inactive split:\n" Print.cnstrsToString constrs) ^
                    "\n");
             NONE))
      (* Constraints.Error could be raised by abstract *))
    let rec occursInExp __177__ __178__ =
      match (__177__, __178__) with
      | (k, Uni _) -> false__
      | (k, Pi (DP, __V)) ->
          (occursInDecP (k, DP)) || (occursInExp ((k + 1), __V))
      | (k, Root (__H, __S)) ->
          (occursInHead (k, __H)) || (occursInSpine (k, __S))
      | (k, Lam (__D, __V)) ->
          (occursInDec (k, __D)) || (occursInExp ((k + 1), __V))
      | (k, FgnExp (cs, ops)) -> false__
    let rec occursInHead __179__ __180__ =
      match (__179__, __180__) with
      | (k, BVar k') -> k = k'
      | (k, _) -> false__
    let rec occursInSpine __181__ __182__ =
      match (__181__, __182__) with
      | (_, I.Nil) -> false__
      | (k, App (__U, __S)) ->
          (occursInExp (k, __U)) || (occursInSpine (k, __S))
    let rec occursInDec k (Dec (_, __V)) = occursInExp (k, __V)
    let rec occursInDecP k (__D, _) = occursInDec (k, __D)
    let rec occursInMatchPos __183__ __184__ __185__ =
      match (__183__, __184__, __185__) with
      | (k, Pi (DP, __V), ci) -> occursInMatchPos ((k + 1), __V, ci)
      | (k, Root (__H, __S), ci) -> occursInMatchPosSpine (k, __S, ci)
    let rec occursInMatchPosSpine __186__ __187__ __188__ =
      match (__186__, __187__, __188__) with
      | (k, I.Nil, Cnil) -> false__
      | (k, App (__U, __S), Match ci) ->
          (occursInExp (k, __U)) || (occursInMatchPosSpine (k, __S, ci))
      | (k, App (__U, __S), Skip ci) -> occursInMatchPosSpine (k, __S, ci)
    let rec instEVarsSkip (__Vs) p (XsRev) ci =
      InstEVarsSkipW ((Whnf.whnf __Vs), p, XsRev, ci)
    let rec InstEVarsSkipW __189__ __190__ __191__ __192__ =
      match (__189__, __190__, __191__, __192__) with
      | (__Vs, 0, XsRev, ci) -> (__Vs, XsRev)
      | ((Pi ((Dec (xOpt, __V1), _), __V2), s), p, XsRev, ci) ->
          let __X1 = Whnf.newLoweredEVar (I.Null, (__V1, s)) in
          let EVarOpt =
            if occursInMatchPos (1, __V2, ci) then Some __X1 else NONE in
          ((instEVarsSkip
              ((__V2, (I.Dot ((I.Exp __X1), s))), (p - 1),
                (EVarOpt :: XsRev), ci))
            (* p > 0 *)(* all EVars are global *)
            (* was val X1 = I.newEVar (I.Null, I.EClo (V1, s))  all EVars are global *))
      | ((Pi ((BDec (_, (l, t)), _), __V2), s), p, XsRev, ci) ->
          let __L1 = I.newLVar ((I.Shift 0), (l, (I.comp (t, s)))) in
          ((instEVarsSkip
              ((__V2, (I.Dot ((I.Block __L1), s))), (p - 1), (NONE :: XsRev),
                ci))
            (* p > 0 *)(* -fp Sun Dec  1 21:09:38 2002 *)
            (* -cs Sun Dec  1 06:30:59 2002 *))(* . |- s : G0 *)
      (* G0 |- t : Gsome *)
    let rec targetBelowEq __193__ __194__ =
      match (__193__, __194__) with
      | (a, EVar ({ contents = NONE }, GY, VY, { contents = nil })) ->
          Subordinate.belowEq (a, (I.targetFam VY))
      | (a, EVar ({ contents = NONE }, GY, VY, { contents = _::_ })) ->
          true__(* if contraints remain, consider recursive and thereby unsplittable *)
    let rec recursive =
      function
      | EVar ({ contents = Some (__U) }, GX, VX, _) as X ->
          let a = I.targetFam VX in
          let __Ys = Abstract.collectEVars (GX, (__X, I.id), nil) in
          let recp = List.exists (fun (__Y) -> targetBelowEq (a, __Y)) __Ys in
          ((recp)
            (* GX = I.Null*)(* is this always true? --cs!!!*)
            (* LVars are ignored here.  OK because never splittable? *)
            (* Sat Dec 15 22:42:10 2001 -fp !!! *))
      | Lam (__D, __U) -> recursive __U
    let counter = ref 0
    let rec resetCount () = counter := 0
    let rec incCount () = ((!) ((:=) counter) counter) + 1
    let rec getCount () = !counter
    exception NotFinitary 
    let rec finitary1 (__X) k (__W) f cands =
      resetCount ();
      chatter 7
        (fun () ->
           (((^) "Trying " Print.expToString (I.Null, __X)) ^ " : ") ^ ".\n");
      (try
         splitEVar
           (__X, __W,
             (fun () ->
                f ();
                if recursive __X then raise NotFinitary else incCount ()));
         chatter 7
           (fun () ->
              ((^) "Finitary with " Int.toString (getCount ())) ^
                " candidates.\n");
         (k, (getCount ())) :: cands
       with | NotFinitary -> (chatter 7 (fun () -> "Not finitary.\n"); cands)
       | Error constrs ->
           (chatter 7 (fun () -> "Inactive finitary split.\n"); cands))
    let rec finitarySplits __195__ __196__ __197__ __198__ __199__ =
      match (__195__, __196__, __197__, __198__, __199__) with
      | (nil, k, __W, f, cands) -> cands
      | ((NONE)::__Xs, k, __W, f, cands) ->
          finitarySplits (__Xs, (k + 1), __W, f, cands)
      | ((Some (__X))::__Xs, k, __W, f, cands) ->
          finitarySplits
            (__Xs, (k + 1), __W, f,
              (CSManager.trail (fun () -> finitary1 (__X, k, __W, f, cands))))
      (* parameter blocks can never be split *)
    let rec finitary (__V) p (__W) ci =
      let _ =
        if !Global.doubleCheck
        then TypeCheck.typeCheck (I.Null, (__V, (I.Uni I.Type)))
        else () in
      let ((__V1, s), XsRev) = instEVarsSkip ((__V, I.id), p, nil, ci) in
      finitarySplits (XsRev, 1, __W, (fun () -> abstract (__V1, s)), nil)
    let rec eqExp (__Us) (__Us') = Conv.conv (__Us, __Us')
    let rec eqInpSpine __200__ __201__ __202__ =
      match (__200__, __201__, __202__) with
      | (ms, (SClo (__S1, s1'), s1), __Ss2) ->
          eqInpSpine (ms, (__S1, (I.comp (s1', s1))), __Ss2)
      | (ms, __Ss1, (SClo (__S2, s2'), s2)) ->
          eqInpSpine (ms, __Ss1, (__S2, (I.comp (s2', s2))))
      | (M.Mnil, (I.Nil, s), (I.Nil, s')) -> true__
      | (Mapp (Marg (M.Plus, _), ms'), (App (__U, __S), s),
         (App (__U', __S'), s')) ->
          (eqExp ((__U, s), (__U', s'))) &&
            (eqInpSpine (ms', (__S, s), (__S', s')))
      | (Mapp (_, ms'), (App (__U, __S), s), (App (__U', __S'), s')) ->
          eqInpSpine (ms', (__S, s), (__S', s'))(* ignore Star, Minus, Minus1 *)
    let rec eqInp __203__ __204__ __205__ __206__ __207__ =
      match (__203__, __204__, __205__, __206__, __207__) with
      | (I.Null, k, a, __Ss, ms) -> nil
      | (Decl (__G', Dec (_, Root (Const a', __S'))), k, a, __Ss, ms) ->
          if (a = a') && (eqInpSpine (ms, (__S', (I.Shift k)), __Ss))
          then (::) k eqInp (__G', (k + 1), a, __Ss, ms)
          else eqInp (__G', (k + 1), a, __Ss, ms)
      | (Decl (__G', Dec (_, Pi _)), k, a, __Ss, ms) ->
          eqInp (__G', (k + 1), a, __Ss, ms)
      | (Decl (__G', NDec _), k, a, __Ss, ms) ->
          eqInp (__G', (k + 1), a, __Ss, ms)
      | (Decl (__G', BDec (_, (b, t))), k, a, __Ss, ms) ->
          eqInp (__G', (k + 1), a, __Ss, ms)(* defined type families disallowed here *)
    let rec contractionCands __208__ __209__ =
      match (__208__, __209__) with
      | (I.Null, k) -> nil
      | (Decl (__G', Dec (_, Root (Const a, __S))), k) ->
          (match UniqueTable.modeLookup a with
           | NONE -> contractionCands (__G', (k + 1))
           | Some ms ->
               (match eqInp (__G', (k + 1), a, (__S, (I.Shift k)), ms) with
                | nil -> contractionCands (__G', (k + 1))
                | ns -> (::) (k :: ns) contractionCands (__G', (k + 1))))
      | (Decl (__G', Dec (_, Pi _)), k) -> contractionCands (__G', (k + 1))
      | (Decl (__G', NDec _), k) -> contractionCands (__G', (k + 1))
      | (Decl (__G', BDec (_, (b, t))), k) ->
          contractionCands (__G', (k + 1))(* ignore blocks --- contraction cands unclear *)
      (* ignore Pi --- contraction cands unclear *)
      (* using only one uniqueness declaration per type family *)
      (* defined type families disallowed here *)
    let rec isolateSplittable __210__ __211__ __212__ =
      match (__210__, __211__, __212__) with
      | (__G, __V, 0) -> (__G, __V)
      | (__G, Pi ((__D, _), __V'), p) ->
          isolateSplittable ((I.Decl (__G, __D)), __V', (p - 1))
    let rec unifyUOutSpine __213__ __214__ __215__ =
      match (__213__, __214__, __215__) with
      | (ms, (SClo (__S1, s1'), s1), __Ss2) ->
          unifyUOutSpine (ms, (__S1, (I.comp (s1', s1))), __Ss2)
      | (ms, __Ss1, (SClo (__S2, s2'), s2)) ->
          unifyUOutSpine (ms, __Ss1, (__S2, (I.comp (s2', s2))))
      | (M.Mnil, (I.Nil, s1), (I.Nil, s2)) -> true__
      | (Mapp (Marg (M.Minus1, _), ms'), (App (__U1, __S1), s1),
         (App (__U2, __S2), s2)) ->
          (((Unify.unifiable (I.Null, (__U1, s1), (__U2, s2))) &&
              (unifyUOutSpine (ms', (__S1, s1), (__S2, s2))))
          (* will have effect! *))
      | (Mapp (_, ms'), (App (__U1, __S1), s1), (App (__U2, __S2), s2)) ->
          unifyUOutSpine (ms', (__S1, s1), (__S2, s2))(* if mode = + already equal by invariant; otherwise ignore *)
    let rec unifyUOutType (__V1) (__V2) =
      unifyUOutTypeW ((Whnf.whnf (__V1, I.id)), (Whnf.whnf (__V2, I.id)))
    let rec unifyUOutTypeW (Root (Const a1, __S1), s1)
      (Root (Const a2, __S2), s2) =
      let Some ms = UniqueTable.modeLookup a1 in
      ((unifyUOutSpine (ms, (__S1, s1), (__S2, s2)))
        (* must succeed by invariant *))(* a1 = a2 by invariant *)
    let rec unifyUOutEVars (Some (EVar (_, __G1, __V1, _))) (Some (EVar
      (_, __G2, __V2, _))) = unifyUOutType (__V1, __V2)(* G1 = G2 = Null *)
    let rec unifyUOut2 (XsRev) k1 k2 =
      unifyUOutEVars
        ((List.nth (XsRev, (k1 - 1))), (List.nth (XsRev, (k2 - 1))))
    let rec unifyUOut1 __216__ __217__ =
      match (__216__, __217__) with
      | (XsRev, nil) -> true__
      | (XsRev, k1::nil) -> true__
      | (XsRev, k1::k2::ks) ->
          (unifyUOut2 (XsRev, k1, k2)) && (unifyUOut1 (XsRev, (k2 :: ks)))
    let rec unifyUOut __218__ __219__ =
      match (__218__, __219__) with
      | (XsRev, nil) -> true__
      | (XsRev, ks::kss) ->
          (unifyUOut1 (XsRev, ks)) && (unifyUOut (XsRev, kss))
    let rec contractAll (__V) p ucands =
      let ((__V1, s), XsRev) = instEVars ((__V, I.id), p, nil) in
      ((if unifyUOut (XsRev, ucands) then Some (abstract (__V1, s)) else NONE)
        (* as in splitVar, may raise Constraints.Error *)
        (* as in splitVar *)(* unique outputs not simultaneously unifiable *))
    let rec contract (__V) p ci lab =
      let (__G, _) = isolateSplittable (I.Null, __V, p) in
      let ucands = contractionCands (__G, 1) in
      let n = List.length ucands in
      let _ =
        if n > 0
        then
          chatter 6
            (fun () ->
               ((^) (((^) "Found " Int.toString n) ^ " contraction ")
                  pluralize (n, "candidate"))
                 ^ "\n")
        else () in
      let VpOpt' =
        ((if n > 0
          then
            try contractAll (__V, p, ucands)
            with
            | Error _ ->
                (chatter 6
                   (fun () -> "Contraction failed due to constraints\n");
                 Some (__V, p))
          else Some (__V, p))
        (* no progress if constraints remain *)) in
      let _ =
        match VpOpt' with
        | NONE ->
            chatter 6
              (fun () -> "Case impossible: conflicting unique outputs\n")
        | Some (__V', p') ->
            chatter 6
              (fun () -> (showPendingGoal (__V', p', ci, lab)) ^ "\n") in
      ((VpOpt')
        (* ignore body of coverage goal *)(* no candidates, no progress *))
    let rec findMin ((k, n)::kns) = findMin' ((k, n), kns)
    let rec findMin' __220__ __221__ =
      match (__220__, __221__) with
      | ((k0, n0), nil) -> (k0, n0)
      | ((k0, n0), (k', n')::kns) ->
          if n' < n0
          then findMin' ((k', n'), kns)
          else findMin' ((k0, n0), kns)
    let rec cover (__V) p ((__W, ci) as wci) ccs lab missing =
      chatter 6 (fun () -> (showPendingGoal (__V, p, ci, lab)) ^ "\n");
      cover' ((contract (__V, p, ci, lab)), wci, ccs, lab, missing)
    let rec cover' __222__ __223__ __224__ __225__ __226__ =
      match (__222__, __223__, __224__, __225__, __226__) with
      | (Some (__V, p), ((__W, ci) as wci), ccs, lab, missing) ->
          split
            (__V, p, (selectCand (match__ (I.Null, __V, p, ci, ccs))), wci,
              ccs, lab, missing)
      | (NONE, wci, ccs, lab, missing) ->
          (chatter 6 (fun () -> "Covered\n"); missing)(* V is covered by unique output inconsistency *)
    let rec split __227__ __228__ __229__ __230__ __231__ __232__ __233__ =
      match (__227__, __228__, __229__, __230__, __231__, __232__, __233__)
      with
      | (__V, p, NONE, wci, ccs, lab, missing) ->
          (chatter 6 (fun () -> "Covered\n"); missing)
      | (__V, p, Some nil, ((__W, ci) as wci), ccs, lab, missing) ->
          (chatter 6
             (fun () ->
                "No strong candidates---calculating weak candidates\n");
           splitWeak
             (__V, p, (finitary (__V, p, __W, ci)), wci, ccs, lab, missing))
      | (__V, p, Some ((k, _)::ksn), ((__W, ci) as wci), ccs, lab, missing)
          ->
          (((match splitVar (__V, p, k, wci) with
             | Some cases -> covers (cases, wci, ccs, lab, missing)
             | NONE -> split (__V, p, (Some ksn), wci, ccs, lab, missing)))
          (* splitting variable k generated constraints *))
      (* splitVar shows splitting as it happens *)(* candidates are in reverse order, so non-index candidates are split first *)
      (* some candidates: split first candidate, ignoring multiplicities *)
      (* no strong candidates: check for finitary splitting candidates *)
      (* V is covered: return missing patterns from other cases *)
    let rec splitWeak __234__ __235__ __236__ __237__ __238__ __239__ __240__
      =
      match (__234__, __235__, __236__, __237__, __238__, __239__, __240__)
      with
      | (__V, p, nil, wci, ccs, lab, missing) ->
          (chatter 6
             (fun () ->
                ((^) "No weak candidates---case " labToString lab) ^
                  " not covered\n");
           (__V, p) :: missing)
      | (__V, p, ksn, wci, ccs, lab, missing) ->
          split
            (__V, p, (Some ((findMin ksn) :: nil)), wci, ccs, lab, missing)
      (* commit to the minimal candidate, since no constraints can arise *)
      (* ksn <> nil *)
    let rec covers cases wci ccs lab missing =
      chatter 6
        (fun () ->
           ((^) ((^) "Found " Int.toString (List.length cases)) pluralize
              ((List.length cases), " case"))
             ^ "\n");
      covers' (cases, 1, wci, ccs, lab, missing)
    let rec covers' __241__ __242__ __243__ __244__ __245__ __246__ =
      match (__241__, __242__, __243__, __244__, __245__, __246__) with
      | (nil, n, wci, ccs, lab, missing) ->
          (chatter 6
             (fun () ->
                ((^) "All subcases of " labToString lab) ^ " considered\n");
           missing)
      | ((__V, p)::cases', n, wci, ccs, lab, missing) ->
          covers'
            (cases', (n + 1), wci, ccs, lab,
              (cover (__V, p, wci, ccs, (Child (lab, n)), missing)))
    let rec constsToTypes =
      function
      | nil -> nil
      | (Const c)::cs' -> (::) (I.constType c) constsToTypes cs'
      | (Def d)::cs' -> (::) (I.constType d) constsToTypes cs'
    let rec createCoverClause __247__ __248__ __249__ =
      match (__247__, __248__, __249__) with
      | (Decl (__G, __D), __V, p) ->
          createCoverClause (__G, (I.Pi ((__D, I.Maybe), __V)), (p + 1))
      | (I.Null, __V, p) -> ((Whnf.normalize (__V, I.id)), p)
    let rec createCoverGoal (__G) (__Vs) p ms =
      createCoverGoalW (__G, (Whnf.whnf __Vs), p, ms)
    let rec createCoverGoalW __250__ __251__ __252__ __253__ =
      match (__250__, __251__, __252__, __253__) with
      | (__G, (Pi ((__D1, __P1), __V2), s), 0, ms) ->
          let D1' = I.decSub (__D1, s) in
          let V2' =
            createCoverGoal ((I.Decl (__G, D1')), (__V2, (I.dot1 s)), 0, ms) in
          I.Pi ((D1', __P1), V2')
      | (__G, (Pi (((Dec (_, __V1) as D), _), __V2), s), p, ms) ->
          let __X = Whnf.newLoweredEVar (__G, (__V1, s)) in
          ((createCoverGoal
              (__G, (__V2, (I.Dot ((I.Exp __X), s))), (p - 1), ms))
            (* p > 0, G = I.Null *)(* was  val X = I.newEVar (G, I.EClo (V1, s))  Mon Feb 28 15:33:52 2011 -cs *))
      | (__G, (Root ((Const cid as a), __S), s), p, ms) ->
          I.Root
            (a,
              (createCoverSpine
                 (__G, (__S, s), ((I.constType cid), I.id), ms)))(* s = id, p >= 0 *)
    let rec createCoverSpine __254__ __255__ __256__ __257__ =
      match (__254__, __255__, __256__, __257__) with
      | (__G, (I.Nil, s), _, M.Mnil) -> I.Nil
      | (__G, (App (__U1, __S2), s), (Pi ((Dec (_, __V1), _), __V2), s'),
         Mapp (Marg (M.Minus, x), ms')) ->
          let __X = createEVar (__G, (I.EClo (__V1, s'))) in
          let S2' =
            createCoverSpine
              (__G, (__S2, s), (__V2, (I.Dot ((I.Exp __X), s'))), ms') in
          ((I.App (__X, S2'))
            (* strengthen G based on subordination *))
      | (__G, (App (__U1, __S2), s), (Pi (_, __V2), s'), Mapp (_, ms')) ->
          I.App
            ((I.EClo (__U1, s)),
              (createCoverSpine
                 (__G, (__S2, s),
                   (Whnf.whnf
                      (__V2, (I.Dot ((I.Exp (I.EClo (__U1, s))), s')))), ms')))
      | (__G, (SClo (__S, s'), s), __Vs, ms) ->
          createCoverSpine (__G, (__S, (I.comp (s', s))), __Vs, ms)(* leave input ( + ) arguments as they are, ignore ( * ) impossible *)
      (* replace output argument by new variable *)
    let rec checkNoDef a =
      match I.sgnLookup a with
      | ConDef _ ->
          raise
            (Error
               (((^) "Coverage checking " N.qidToString (N.constQid a)) ^
                  ":\ntype family must not be defined."))
      | _ -> ()
    let rec checkCovers a ms =
      let _ =
        chatter 4
          (fun () ->
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
      let (__V0, p) = initCGoal a in
      let _ =
        if !Global.doubleCheck
        then TypeCheck.typeCheck (I.Null, (__V0, (I.Uni I.Type)))
        else () in
      let _ = CSManager.reset () in
      let cIn = inCoverInst ms in
      let cs = Index.lookup a in
      let ccs = constsToTypes cs in
      let __W = W.lookup a in
      let __V0 = createCoverGoal (I.Null, (__V0, I.id), p, ms) in
      let (__V0, p) = abstract (__V0, I.id) in
      let missing = cover (__V0, p, (__W, cIn), (Input ccs), Top, nil) in
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
    let rec checkOut (__G) (__V, s) =
      let a = I.targetFam __V in
      let Some ms = ModeTable.modeLookup a in
      let cOut = outCoverInst ms in
      let (__V', q) = createCoverClause (__G, (I.EClo (__V, s)), 0) in
      let _ =
        if !Global.doubleCheck
        then TypeCheck.typeCheck (I.Null, (__V', (I.Uni I.Type)))
        else () in
      let __V0 = createCoverGoal (I.Null, (__V', I.id), q, ms) in
      let (V0', p) = abstract (__V0, I.id) in
      let __W = W.lookup a in
      let missing = cover (V0', p, (__W, cOut), (Output (__V', q)), Top, nil) in
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
    type __CoverGoal =
      | CGoal of (I.dctx * I.__Spine) 
    type __CoverClause =
      | CClause of (I.dctx * I.__Spine) 
    let rec formatCGoal (CGoal (__G, __S)) =
      let _ = N.varReset I.Null in
      F.HVbox
        ((@) [Print.formatCtx (I.Null, __G);
             F.Break;
             F.Break;
             F.String "|-";
             F.Space]
           Print.formatSpine (__G, __S))
    let rec showPendingCGoal (CGoal (__G, __S)) lab =
      F.makestring_fmt
        (F.Hbox
           [F.String (labToString lab);
           F.Space;
           F.String "?- ";
           formatCGoal (CGoal (__G, __S));
           F.String "."])
    let rec showCClause (CClause (__G, __S)) =
      let _ = N.varReset I.Null in
      F.makestring_fmt
        (F.HVbox ((@) [F.String "!- "] Print.formatSpine (__G, __S)))
    let rec showSplitVar (CGoal (__G, __S)) k =
      let _ = N.varReset I.Null in
      let Dec (Some x, _) = I.ctxLookup (__G, k) in
      (^) (("Split " ^ x) ^ " in ") F.makestring_fmt
        (F.HVbox (Print.formatSpine (__G, __S)))
    let rec newEVarSubst __0__ __1__ =
      match (__0__, __1__) with
      | (__G, I.Null) -> I.Shift (I.ctxLength __G)
      | (__G, Decl (__G', (Dec (_, __V) as D))) ->
          let s' = newEVarSubst (__G, __G') in
          let __X = Whnf.newLoweredEVar (__G, (__V, s')) in
          ((I.Dot ((I.Exp __X), s'))
            (* was val V' = I.EClo (V, s')
                 val X = I.newEVar (G, V') Mon Feb 28 15:34:31 2011 -cs *))
      | (__G, Decl (__G', (NDec _ as D))) ->
          let s' = newEVarSubst (__G, __G') in I.Dot (I.Undef, s')
      | (__G, Decl (__G', (BDec (_, (b, t)) as D))) ->
          let s' = newEVarSubst (__G, __G') in
          let __L1 = I.newLVar (s', (b, t)) in ((I.Dot ((I.Block __L1), s'))
            (* was  val L1 = I.newLVar (I.Shift(0), (b, I.comp(t, s')))
             --cs Fri Jul 23 16:39:27 2010 *)
            (* -cs Fri Jul 23 16:35:04 2010  FPCHECK *)
            (* L : Delta[t][G'] *)(* G |- s : G'  G |- L[s'] : V[s]
             G |- (L[s'].s : G', V *)
            (* -fp Sun Dec  1 21:10:45 2002 *)(* -cs Sun Dec  1 06:31:23 2002 *))
    let rec checkConstraints __2__ __3__ __4__ =
      match (__2__, __3__, __4__) with
      | (__G, (Si, ti), Cands ks) -> Cands ks
      | (__G, (Si, ti), Fail) -> Fail
      | (__G, (Si, ti), Eqns _) ->
          let __Xs = Abstract.collectEVarsSpine (__G, (Si, ti), nil) in
          let constrs = collectConstraints __Xs in
          (((match constrs with
             | nil -> Eqns nil
             | _ -> fail "Remaining constraints"))
            (* constraints remained: Fail without candidates *))
      (* _ = nil *)
    let rec matchClause (CGoal (__G, __S)) (Si, ti) =
      let cands1 = matchSpine (__G, 0, (__S, I.id), (Si, ti), (Eqns nil)) in
      let cands2 = resolveCands cands1 in
      let cands3 = checkConstraints (__G, (Si, ti), cands2) in cands3
    let rec matchClauses __5__ __6__ __7__ =
      match (__5__, __6__, __7__) with
      | (cg, nil, klist) -> klist
      | ((CGoal (__G, __S) as cg), (CClause (Gi, Si))::ccs, klist) ->
          let ti = newEVarSubst (__G, Gi) in
          let cands = CSManager.trail (fun () -> matchClause (cg, (Si, ti))) in
          ((matchClauses' (cg, ccs, (addKs (cands, klist))))
            (* G |- ti : Gi *))
    let rec matchClauses' __8__ __9__ __10__ =
      match (__8__, __9__, __10__) with
      | (cg, ccs, Covered) -> Covered
      | (cg, ccs, (CandList _ as klist)) -> matchClauses (cg, ccs, klist)
    let rec match__ (CGoal (__G, __S)) ccs =
      matchClauses ((CGoal (__G, __S)), ccs, (CandList nil))
    let rec abstractSpine (__S) s =
      let (__G', __S') = Abstract.abstractSpine (__S, s) in
      let namedG' = N.ctxName __G' in
      let _ =
        if !Global.doubleCheck
        then ((TypeCheck.typeCheckCtx namedG')
          (* TypeCheck.typeCheckSpine (namedG', S') *))
        else () in
      ((CGoal (namedG', __S'))(* for printing purposes *))
    let rec kthSub __11__ __12__ =
      match (__11__, __12__) with
      | (Dot (Exp (__X), s), 1) -> __X
      | (Dot (_, s), k) -> kthSub (s, (k - 1))
    let rec subToXsRev =
      function
      | Shift 0 -> nil
      | Dot (Exp (__X), s) -> (::) (Some __X) subToXsRev s
      | Dot (_, s) -> (::) NONE subToXsRev s(* n = 0 *)
    let (caseList : __CoverGoal list ref) = ref nil
    let rec resetCases () = caseList := nil
    let rec addCase cg = (!) ((::) (caseList := cg)) caseList
    let rec getCases () = !caseList
    let rec splitVar (CGoal (__G, __S) as cg) k w =
      ((try
          let _ = chatter 6 (fun () -> (showSplitVar (cg, k)) ^ "\n") in
          let s = newEVarSubst (I.Null, __G) in
          let __X = kthSub (s, k) in
          let _ = resetCases () in
          let _ =
            splitEVar (__X, w, (fun () -> addCase (abstractSpine (__S, s)))) in
          ((Some (getCases ()))
            (* for splitting, EVars are always global *)
            (* G = xn:V1,...,x1:Vn *)(* s = X1....Xn.^0, where . |- s : G *)
            (* starts with k = 1 (a la deBruijn) *))
        with
        | Error constrs ->
            (chatter 7
               (fun () ->
                  ((^) "Inactive split:\n" Print.cnstrsToString constrs) ^
                    "\n");
             NONE))
      (* Constraints.Error could be raised by abstract *))
    let rec finitary (CGoal (__G, __S)) w =
      let s = newEVarSubst (I.Null, __G) in
      let XsRev = subToXsRev s in
      ((finitarySplits (XsRev, 1, w, (fun () -> abstractSpine (__S, s)), nil))
        (* G = xn:Vn,...,x1:V1 *)(* for splitting, EVars are always global *)
        (* s = X1...Xn.^0,  . |- S : G *)(* XsRev = [Some(X1),...,Some(Xn)] *))
    let rec contractAll (CGoal (__G, __S)) ucands =
      let s = newEVarSubst (I.Null, __G) in
      let XsRev = subToXsRev s in
      ((if unifyUOut (XsRev, ucands)
        then Some (abstractSpine (__S, s))
        else NONE)
        (* as in splitVar, may raise Constraints.Error *)
        (* for unif, EVars are always global *))
    let rec contract (CGoal (__G, __S) as cg) lab =
      let ucands = contractionCands (__G, 1) in
      let n = List.length ucands in
      let _ =
        if n > 0
        then
          chatter 6
            (fun () ->
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
                   (fun () -> "Contraction failed due to constraints\n");
                 Some cg)
          else Some cg)
        (* no progress if constraints remain *)) in
      let _ =
        match cgOpt' with
        | NONE ->
            chatter 6
              (fun () -> "Case impossible: conflicting unique outputs\n")
        | Some cg' ->
            chatter 6 (fun () -> (showPendingCGoal (cg', lab)) ^ "\n") in
      ((cgOpt')(* no candidates, no progress *))
    let rec cover cg w ccs lab missing =
      chatter 6 (fun () -> (showPendingCGoal (cg, lab)) ^ "\n");
      cover' ((contract (cg, lab)), w, ccs, lab, missing)
    let rec cover' __13__ __14__ __15__ __16__ __17__ =
      match (__13__, __14__, __15__, __16__, __17__) with
      | (Some cg, w, ccs, lab, missing) ->
          let cands = match__ (cg, ccs) in
          let cand = selectCand cands in
          ((split (cg, cand, w, ccs, lab, missing))
            (* determine splitting candidates *)(* select one candidate *))
      | (NONE, w, ccs, lab, missing) ->
          (chatter 6 (fun () -> "Covered\n"); missing)(* cg is covered by unique output inconsistency *)
    let rec split __18__ __19__ __20__ __21__ __22__ __23__ =
      match (__18__, __19__, __20__, __21__, __22__, __23__) with
      | (cg, NONE, w, ccs, lab, missing) ->
          (chatter 6 (fun () -> "Covered\n"); missing)
      | (cg, Some nil, w, ccs, lab, missing) ->
          (chatter 6
             (fun () ->
                "No strong candidates --- calculating weak candidates\n");
           splitWeak (cg, (finitary (cg, w)), w, ccs, lab, missing))
      | (cg, Some ((k, _)::ksn), w, ccs, lab, missing) ->
          (chatter 6 (fun () -> ((^) "Splitting on " Int.toString k) ^ "\n");
           (match splitVar (cg, k, w) with
            | Some cases -> covers (cases, w, ccs, lab, missing)
            | NONE ->
                (chatter 6
                   (fun () ->
                      "Splitting failed due to generated constraints\n");
                 split (cg, (Some ksn), w, ccs, lab, missing))))(* splitVar shows splitting as it happens *)
      (* candidates are in reverse order, so non-index candidates are split first *)
      (* some candidates: split first candidate, ignoring multiplicities *)
      (* no strong candidates: check for finitary splitting candidates *)
      (* cg is covered: return missing patterns from other cases *)
    let rec splitWeak __24__ __25__ __26__ __27__ __28__ __29__ =
      match (__24__, __25__, __26__, __27__, __28__, __29__) with
      | (cg, nil, w, ccs, lab, missing) ->
          (chatter 6
             (fun () ->
                ((^) "No weak candidates---case " labToString lab) ^
                  " not covered\n");
           cg :: missing)
      | (cg, ksn, w, ccs, lab, missing) ->
          split (cg, (Some ((findMin ksn) :: nil)), w, ccs, lab, missing)
      (* ksn <> nil *)
    let rec covers cases w ccs lab missing =
      chatter 6
        (fun () ->
           ((^) ((^) "Found " Int.toString (List.length cases)) pluralize
              ((List.length cases), " case"))
             ^ "\n");
      covers' (cases, 1, w, ccs, lab, missing)
    let rec covers' __30__ __31__ __32__ __33__ __34__ __35__ =
      match (__30__, __31__, __32__, __33__, __34__, __35__) with
      | (nil, n, w, ccs, lab, missing) ->
          (chatter 6
             (fun () ->
                ((^) "All subcases of " labToString lab) ^ " considered\n");
           missing)
      | (cg::cases', n, w, ccs, lab, missing) ->
          let missing1 = cover (cg, w, ccs, (Child (lab, n)), missing) in
          covers' (cases', (n + 1), w, ccs, lab, missing1)
    let rec substToSpine' __36__ __37__ __38__ =
      match (__36__, __37__, __38__) with
      | (Shift n, I.Null, __T) -> __T
      | (Shift n, (Decl _ as G), __T) ->
          substToSpine'
            ((I.Dot ((I.Idx (n + 1)), (I.Shift (n + 1)))), __G, __T)
      | (Dot (_, s), Decl (__G, NDec _), __T) -> substToSpine' (s, __G, __T)
      | (Dot (Exp (__U), s), Decl (__G, __V), __T) ->
          substToSpine' (s, __G, (I.App (__U, __T)))
      | (Dot (Idx n, s), Decl (__G, Dec (_, __V)), __T) ->
          let (__Us, _) =
            Whnf.whnfEta (((I.Root ((I.BVar n), I.Nil)), I.id), (__V, I.id)) in
          substToSpine' (s, __G, (I.App ((I.EClo __Us), __T)))
      | (Dot (_, s), Decl (__G, BDec (_, (__L, t))), __T) ->
          substToSpine' (s, __G, __T)(* Attempted fix, didn't work because I don't know how you
             computed splitting candidates for Blocks
             --cs Sat Jan  4 22:38:01 2003
          *)
      (* Treat like I.NDec *)(* was: I.Idx in previous line, Sun Jan  5 11:02:19 2003 -fp *)
      (* Eta-expand *)(* Unusable meta-decs are eliminated here *)
      (* Skip over NDec's; must be either Undef or Idx [from eta-expansion] *)
    let rec substToSpine s (__G) = substToSpine' (s, __G, I.Nil)
    let rec purify' =
      function
      | I.Null -> (I.Null, I.id)
      | Decl (__G, NDec _) ->
          let (__G', s) = purify' __G in (((__G', (I.Dot (I.Undef, s))))
            (* G' |- s : G *)(* G' |- _.s : G,_ *))
      | Decl (__G, (Dec _ as D)) ->
          let (__G', s) = purify' __G in
          ((((I.Decl (__G', (I.decSub (__D, s)))), (I.dot1 s)))
            (* G' |- s : G *)(* G |- D : type *)
            (* G' |- D[s] : type *)(* G', D[s] |- 1 : D[s][^] *)
            (* G', D[s] |- s o ^ : G *)(* G', D[s] |- 1.s o ^ : G, D *))
      | Decl (__G, (BDec _ as D)) ->
          let (__G', s) = purify' __G in (((__G', (I.Dot (I.Undef, s))))
            (* G' |- s : G *)(* G' |- _.s : G,_ *))
      (* added a new case to throw out blocks
         -cs Sat Jan  4 22:55:12 2003
      *)
    let rec purify (__G) = (fun r -> r.1) (purify' __G)
    let rec coverageCheckCases w (__Cs) (__G) =
      let _ = chatter 4 (fun () -> "[Tomega coverage checker...") in
      let _ = chatter 4 (fun () -> "\n") in
      let ccs =
        List.map
          (fun (Gi) -> fun si -> CClause (Gi, (substToSpine (si, __G)))) __Cs in
      let _ = chatter 6 (fun () -> "[Begin covering clauses]\n") in
      let _ =
        List.app (fun cc -> chatter 6 (fun () -> (showCClause cc) ^ "\n"))
          ccs in
      let _ = chatter 6 (fun () -> "[End covering clauses]\n") in
      let pureG = purify __G in
      let namedG = N.ctxLUName pureG in
      let __R0 = substToSpine (I.id, namedG) in
      let cg0 = CGoal (namedG, __R0) in
      let missing = cover (cg0, w, ccs, Top, nil) in
      let _ =
        ((match missing with
          | nil -> ()
          | _::_ -> raise (Error "Coverage error"))
        (* all cases covered *)) in
      let _ = chatter 4 (fun () -> "]\n") in ((())
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
                 module Print = Print
                 module TypeCheck = TypeCheck
                 module Timers = Timers
               end)
module Total =
  (Make_Total)(struct
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
               end);;
