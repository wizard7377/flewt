
module type MODECHECK  =
  sig
    exception Error of string 
    val checkD : IntSyn.__ConDec -> string -> Paths.occConDec option -> unit
    val checkMode : IntSyn.cid -> ModeSyn.__ModeSpine -> unit
    val checkFreeOut : IntSyn.cid -> ModeSyn.__ModeSpine -> unit
  end;;




module ModeCheck(ModeCheck:sig
                             module ModeTable : MODETABLE
                             module Whnf : WHNF
                             module Index : INDEX
                             module Origins : ORIGINS
                           end) : MODECHECK =
  struct
    exception Error of string 
    module I = IntSyn
    module M = ModeSyn
    module P = Paths
    type __Uniqueness =
      | Unique 
      | Ambig 
    type __Info =
      | Free 
      | Unknown 
      | Ground of __Uniqueness 
    type __Status =
      | Existential of (__Info * string option) 
      | Universal 
    let checkFree = ref false
    let rec wrapMsg c occ msg =
      match Origins.originLookup c with
      | (fileName, None) -> (fileName ^ ":") ^ msg
      | (fileName, Some occDec) ->
          P.wrapLoc'
            ((P.Loc (fileName, (P.occToRegionClause occDec occ))),
              (Origins.linesInfoLookup fileName),
              ((((^) "Constant " Names.qidToString (Names.constQid c)) ^ "\n")
                 ^ msg))
    let rec wrapMsg' fileName r msg = P.wrapLoc ((P.Loc (fileName, r)), msg)
    exception ModeError of (P.occ * string) 
    exception Error' of (P.occ * string) 
    let rec lookup a occ =
      match ModeTable.mmodeLookup a with
      | nil ->
          raise
            (Error'
               (occ,
                 ((^) "No mode declaration for " I.conDecName (I.sgnLookup a))))
      | sMs -> sMs
    let rec nameOf =
      function
      | Existential (_, None) -> "?"
      | Existential (_, Some name) -> name
      | _ -> "?"
    let rec unique __0__ __1__ =
      match (__0__, __1__) with
      | (k, nil) -> true
      | (k, k'::ks) -> (k <> k') && (unique (k, ks))
    let rec isUniversal = function | Universal -> true | _ -> false
    let rec isGround =
      function | Existential (Ground _, _) -> true | _ -> false
    let rec uniqueness =
      function | Existential (Ground u, _) -> u | Universal -> Unique
    let rec ambiguate =
      function | M.Plus -> M.Plus | M.Minus -> M.Minus | M.Minus1 -> M.Minus
    let rec andUnique __2__ __3__ =
      match (__2__, __3__) with | (Unique, Unique) -> Unique | _ -> Ambig
    let rec isFree =
      function | Existential (Free, _) -> true | _ -> false
    exception Eta 
    let rec etaContract __4__ __5__ =
      match (__4__, __5__) with
      | (Root (BVar k, __S), n) ->
          if k > n then (etaSpine (__S, n); k - n) else raise Eta
      | (Lam (__D, __U), n) -> etaContract (__U, (n + 1))
      | _ -> raise Eta
    let rec etaSpine __6__ __7__ =
      match (__6__, __7__) with
      | (I.Nil, 0) -> ()
      | (App (__U, __S), n) ->
          if (etaContract (__U, 0)) = n
          then etaSpine (__S, (n - 1))
          else raise Eta
    let rec checkPattern __8__ __9__ __10__ __11__ =
      match (__8__, __9__, __10__, __11__) with
      | (__D, k, args, I.Nil) -> ()
      | (__D, k, args, App (__U, __S)) ->
          let k' = etaContract (__U, 0) in
          if
            (k > k') &&
              ((isUniversal (I.ctxLookup (__D, k'))) && (unique (k', args)))
          then checkPattern (__D, k, (k' :: args), __S)
          else raise Eta
    let rec isPattern (__D) k (__S) =
      try checkPattern (__D, k, nil, __S); true with | Eta -> false
    let rec strictExpN __12__ __13__ __14__ =
      match (__12__, __13__, __14__) with
      | (__D, _, Uni _) -> false
      | (__D, p, Lam (_, __U)) ->
          strictExpN ((I.Decl (__D, Universal)), (p + 1), __U)
      | (__D, p, Pi ((__D', _), __U)) ->
          (strictDecN (__D, p, __D')) ||
            (strictExpN ((I.Decl (__D, Universal)), (p + 1), __U))
      | (__D, p, Root (__H, __S)) ->
          (((match __H with
             | BVar k' ->
                 if k' = p
                 then isPattern (__D, k', __S)
                 else
                   if isUniversal (I.ctxLookup (__D, k'))
                   then strictSpineN (__D, p, __S)
                   else false
             | Const c -> strictSpineN (__D, p, __S)
             | Def d -> strictSpineN (__D, p, __S)
             | FgnConst (cs, conDec) -> strictSpineN (__D, p, __S)))
          (* equivalently: isUniversal .. andalso strictSpineN .. *))
      | (__D, p, FgnExp (cs, ops)) -> false(* no other cases possible *)
      (* strictDecN (D, p, D) orelse *)(* checking D in this case should be redundant -fp *)
    let rec strictSpineN __15__ __16__ __17__ =
      match (__15__, __16__, __17__) with
      | (_, _, I.Nil) -> false
      | (__D, p, App (__U, __S)) ->
          (strictExpN (__D, p, __U)) || (strictSpineN (__D, p, __S))
    let rec strictDecN (__D) p (Dec (_, __V)) = strictExpN (__D, p, __V)
    let rec freeExpN __18__ __19__ __20__ __21__ __22__ __23__ =
      match (__18__, __19__, __20__, __21__, __22__, __23__) with
      | (__D, d, mode, Root (BVar k, __S), occ, strictFun) ->
          (freeVar (__D, d, mode, k, (P.head occ), strictFun);
           freeSpineN (__D, d, mode, __S, (1, occ), strictFun))
      | (__D, d, mode, Root (Const _, __S), occ, strictFun) ->
          freeSpineN (__D, d, mode, __S, (1, occ), strictFun)
      | (__D, d, mode, Root (Def _, __S), occ, strictFun) ->
          freeSpineN (__D, d, mode, __S, (1, occ), strictFun)
      | (__D, d, mode, Root (FgnConst (cs, conDec), __S), occ, strictFun) ->
          freeSpineN (__D, d, mode, __S, (1, occ), strictFun)
      | (__D, d, mode, Lam (_, __U), occ, strictFun) ->
          freeExpN
            ((I.Decl (__D, Universal)), (d + 1), mode, __U, (P.body occ),
              strictFun)
      | (__D, d, mode, FgnExp csfe, occ, strictFun) ->
          I.FgnExpStd.App.apply csfe
            (fun (__U) ->
               freeExpN
                 (__D, d, mode, (Whnf.normalize (__U, I.id)), occ, strictFun))
    let rec freeSpineN __24__ __25__ __26__ __27__ __28__ __29__ =
      match (__24__, __25__, __26__, __27__, __28__, __29__) with
      | (__D, d, mode, I.Nil, _, strictFun) -> ()
      | (__D, d, mode, App (__U, __S), (p, occ), strictFun) ->
          (freeExpN (__D, d, mode, __U, (P.arg (p, occ)), strictFun);
           freeSpineN (__D, d, mode, __S, ((p + 1), occ), strictFun))
    let rec freeVar (__D) d mode k occ strictFun =
      let status = I.ctxLookup (__D, k) in
      if (isFree status) || ((isUniversal status) || (strictFun (k - d)))
      then ()
      else
        raise
          (ModeError
             (occ,
               (((("Occurrence of variable " ^ (nameOf status)) ^ " in ") ^
                   (M.modeToString mode))
                  ^ " argument not free")))
    let rec nonStrictExpN __30__ __31__ =
      match (__30__, __31__) with
      | (__D, Root (BVar k, __S)) ->
          nonStrictSpineN ((nonStrictVarD (__D, k)), __S)
      | (__D, Root (Const c, __S)) -> nonStrictSpineN (__D, __S)
      | (__D, Root (Def d, __S)) -> nonStrictSpineN (__D, __S)
      | (__D, Root (FgnConst (cs, conDec), __S)) ->
          nonStrictSpineN (__D, __S)
      | (__D, Lam (_, __U)) ->
          I.ctxPop (nonStrictExpN ((I.Decl (__D, Universal)), __U))
      | (__D, FgnExp _) ->
          raise
            (Error "Foreign expressions not permitted when checking freeness")
    let rec nonStrictSpineN __32__ __33__ =
      match (__32__, __33__) with
      | (__D, I.Nil) -> __D
      | (__D, App (__U, __S)) ->
          nonStrictSpineN ((nonStrictExpN (__D, __U)), __S)
    let rec nonStrictVarD __34__ __35__ =
      match (__34__, __35__) with
      | (Decl (__D, Existential (Free, name)), 1) ->
          I.Decl (__D, (Existential (Unknown, name)))
      | (__D, 1) -> __D
      | (Decl (__D, status), k) ->
          I.Decl ((nonStrictVarD (__D, (k - 1))), status)(* Universal, or already Unknown or Ground - leave unchanged *)
    let rec updateExpN __36__ __37__ __38__ =
      match (__36__, __37__, __38__) with
      | (__D, Root (BVar k, __S), u) ->
          if isUniversal (I.ctxLookup (__D, k))
          then updateSpineN (__D, __S, u)
          else
            if isPattern (__D, k, __S)
            then updateVarD (__D, k, u)
            else
              if !checkFree
              then nonStrictSpineN ((nonStrictVarD (__D, k)), __S)
              else __D
      | (__D, Root (Const c, __S), u) -> updateSpineN (__D, __S, u)
      | (__D, Root (Def d, __S), u) -> updateSpineN (__D, __S, u)
      | (__D, Root (FgnConst (cs, conDec), __S), u) ->
          updateSpineN (__D, __S, u)
      | (__D, Lam (_, __U), u) ->
          I.ctxPop (updateExpN ((I.Decl (__D, Universal)), __U, u))
      | (__D, FgnExp _, u) -> __D(* no occurrence inside a FgnExp is considered strict *)
    let rec updateSpineN __39__ __40__ __41__ =
      match (__39__, __40__, __41__) with
      | (__D, I.Nil, u) -> __D
      | (__D, App (__U, __S), u) ->
          updateSpineN ((updateExpN (__D, __U, u)), __S, u)
    let rec updateVarD __42__ __43__ __44__ =
      match (__42__, __43__, __44__) with
      | (Decl (__D, Existential (_, name)), 1, u) ->
          I.Decl (__D, (Existential ((Ground u), name)))
      | (Decl (__D, status), k, u) ->
          I.Decl ((updateVarD (__D, (k - 1), u)), status)
    let rec updateAtom' __45__ __46__ __47__ __48__ __49__ =
      match (__45__, __46__, __47__, __48__, __49__) with
      | (__D, mode, I.Nil, M.Mnil, _) -> __D
      | (__D, M.Plus, App (__U, __S), Mapp (Marg (M.Plus, _), mS), (p, occ))
          ->
          updateAtom'
            ((updateExpN (__D, __U, Unique)), M.Plus, __S, mS,
              ((p + 1), occ))
      | (__D, M.Minus, App (__U, __S), Mapp (Marg (M.Minus, _), mS),
         (p, occ)) ->
          updateAtom'
            ((updateExpN (__D, __U, Ambig)), M.Minus, __S, mS,
              ((p + 1), occ))
      | (__D, M.Minus, App (__U, __S), Mapp (Marg (M.Minus1, _), mS),
         (p, occ)) ->
          updateAtom'
            ((updateExpN (__D, __U, Ambig)), M.Minus, __S, mS,
              ((p + 1), occ))
      | (__D, M.Minus1, App (__U, __S), Mapp (Marg (M.Minus, _), mS),
         (p, occ)) ->
          updateAtom'
            ((updateExpN (__D, __U, Ambig)), M.Minus1, __S, mS,
              ((p + 1), occ))
      | (__D, M.Minus1, App (__U, __S), Mapp (Marg (M.Minus1, _), mS),
         (p, occ)) ->
          updateAtom'
            ((updateExpN (__D, __U, Unique)), M.Minus1, __S, mS,
              ((p + 1), occ))
      | (__D, mode, App (__U, __S), Mapp (_, mS), (p, occ)) ->
          updateAtom' (__D, mode, __S, mS, ((p + 1), occ))(* therefore, no case for M.Mapp (M.Marg (M.Minus, _), mS) is provided here *)
      (* when checking freeness, all arguments must be input (+) or output (-) *)
    let rec freeAtom __50__ __51__ __52__ __53__ __54__ __55__ =
      match (__50__, __51__, __52__, __53__, __54__, __55__) with
      | (__D, mode, I.Nil, __Vs, M.Mnil, _) -> ()
      | (__D, M.Minus, App (__U, __S), (Pi ((Dec (_, __V1), _), __V2), s),
         Mapp (Marg (M.Minus, _), mS), (p, occ)) ->
          (freeExpN
             (__D, 0, M.Minus, __U, (P.arg (p, occ)),
               (fun q -> strictExpN (__D, q, (Whnf.normalize (__V1, s)))));
           freeAtom
             (__D, M.Minus, __S,
               (Whnf.whnfExpandDef (__V2, (I.Dot ((I.Exp __U), s)))), mS,
               ((p + 1), occ)))
      | (__D, mode, App (__U, __S), (Pi (_, __V2), s), Mapp (_, mS),
         (p, occ)) ->
          freeAtom
            (__D, mode, __S,
              (Whnf.whnfExpandDef (__V2, (I.Dot ((I.Exp __U), s)))), mS,
              ((p + 1), occ))
    let rec updateAtom (__D) mode (__S) a mS (p, occ) =
      let _ =
        if !checkFree
        then
          freeAtom
            (__D, (ambiguate mode), __S, ((I.constType a), I.id), mS,
              (p, occ))
        else () in
      updateAtom' (__D, mode, __S, mS, (p, occ))
    let rec groundExpN __56__ __57__ __58__ __59__ =
      match (__56__, __57__, __58__, __59__) with
      | (__D, mode, Root (BVar k, __S), occ) ->
          andUnique
            ((groundVar (__D, mode, k, (P.head occ))),
              (groundSpineN (__D, mode, __S, (1, occ))))
      | (__D, mode, Root (Const c, __S), occ) ->
          groundSpineN (__D, mode, __S, (1, occ))
      | (__D, mode, Root (Def d, __S), occ) ->
          groundSpineN (__D, mode, __S, (1, occ))
      | (__D, mode, Root (FgnConst (cs, conDec), __S), occ) ->
          groundSpineN (__D, mode, __S, (1, occ))
      | (__D, mode, Lam (_, __U), occ) ->
          groundExpN ((I.Decl (__D, Universal)), mode, __U, (P.body occ))
      | (__D, mode, FgnExp csfe, occ) ->
          I.FgnExpStd.fold csfe
            (fun (__U) ->
               fun u ->
                 andUnique
                   ((groundExpN
                       (__D, mode, (Whnf.normalize (__U, I.id)), occ)), u))
            Unique
    let rec groundSpineN __60__ __61__ __62__ __63__ =
      match (__60__, __61__, __62__, __63__) with
      | (__D, mode, I.Nil, _) -> Unique
      | (__D, mode, App (__U, __S), (p, occ)) ->
          andUnique
            ((groundExpN (__D, mode, __U, (P.arg (p, occ)))),
              (groundSpineN (__D, mode, __S, ((p + 1), occ))))
    let rec groundVar __64__ __65__ __66__ __67__ =
      match (__64__, __65__, __66__, __67__) with
      | (__D, M.Minus1, k, occ) ->
          (((match I.ctxLookup (__D, k) with
             | Existential (Ground (Unique), _) -> Unique
             | Universal -> Unique
             | Existential (Ground (Ambig), x) as s ->
                 raise
                   (ModeError
                      (occ,
                        (((^) (((^) "Occurrence of variable " nameOf s) ^
                                 " in ")
                            M.modeToString M.Minus1)
                           ^ " argument not necessarily unique")))
             | s ->
                 raise
                   (ModeError
                      (occ,
                        (((("Occurrence of variable " ^ (nameOf s)) ^ " in ")
                            ^ (M.modeToString M.Minus1))
                           ^ " argument not necessarily ground")))))
          (* Existential (Free, _) or Existential (Unknown, _) *))
      | (__D, mode, k, occ) ->
          let status = I.ctxLookup (__D, k) in
          if (isGround status) || (isUniversal status)
          then uniqueness status
          else
            raise
              (ModeError
                 (occ,
                   (((("Occurrence of variable " ^ (nameOf status)) ^ " in ")
                       ^ (M.modeToString mode))
                      ^ " argument not necessarily ground")))
    let rec groundAtom __68__ __69__ __70__ __71__ __72__ =
      match (__68__, __69__, __70__, __71__, __72__) with
      | (__D, _, I.Nil, M.Mnil, _) -> Unique
      | (__D, M.Plus, App (__U, __S), Mapp (Marg (M.Plus, _), mS), (p, occ))
          ->
          andUnique
            ((groundExpN (__D, M.Plus, __U, (P.arg (p, occ)))),
              (groundAtom (__D, M.Plus, __S, mS, ((p + 1), occ))))
      | (__D, M.Minus, App (__U, __S), Mapp (Marg (M.Minus, _), mS),
         (p, occ)) ->
          (((groundExpN (__D, M.Minus, __U, (P.arg (p, occ)));
             groundAtom (__D, M.Minus, __S, mS, ((p + 1), occ))))
          (* ignore uniqueness result here *))
      | (__D, M.Minus, App (__U, __S), Mapp (Marg (M.Minus1, _), mS),
         (p, occ)) ->
          (((groundExpN (__D, M.Minus1, __U, (P.arg (p, occ)));
             groundAtom (__D, M.Minus, __S, mS, ((p + 1), occ))))
          (* ignore uniqueness result here *))
      | (__D, mode, App (__U, __S), Mapp (_, mS), (p, occ)) ->
          groundAtom (__D, mode, __S, mS, ((p + 1), occ))
    let rec ctxPush m (__Ds) = List.map (fun (__D) -> I.Decl (__D, m)) __Ds
    let rec ctxPop (__Ds) = List.map (fun (Decl (__D, m)) -> __D) __Ds
    let rec checkD1 __73__ __74__ __75__ __76__ =
      match (__73__, __74__, __75__, __76__) with
      | (__D, Pi ((Dec (name, _), I.Maybe), __V), occ, k) ->
          checkD1
            ((I.Decl (__D, (Existential (Free, name)))), __V, (P.body occ),
              (fun (Decl (__D', m)) -> ctxPush (m, (k __D'))))
      | (__D, Pi ((Dec (name, __V1), I.No), __V2), occ, k) ->
          checkD1
            ((I.Decl (__D, (Existential (Free, name)))), __V2, (P.body occ),
              (fun (Decl (__D', m)) ->
                 ctxPush (m, (checkG1 (__D', __V1, (P.label occ), k)))))
      | (__D, Root (Const a, __S), occ, k) ->
          let rec checkAll =
            function
            | nil -> ()
            | mS::mSs ->
                let rec checkSome =
                  function
                  | (__D')::[] ->
                      (((groundAtom (__D', M.Minus, __S, mS, (1, occ));
                         checkAll mSs))
                      (* ignore return *))
                  | (__D')::__Ds ->
                      ((((try
                            groundAtom (__D', M.Minus, __S, mS, (1, occ)); ()
                          with | ModeError _ -> checkSome __Ds))
                       (* ignore return *));
                       checkAll mSs)(* try D', if it doesn't work, try another context in the Ds *)
                  (* D' is the only (last) possibility; on failure, we raise ModeError *) in
                checkSome
                  (k (updateAtom (__D, M.Plus, __S, a, mS, (1, occ)))) in
          ((checkAll (lookup (a, occ)))
            (* for a declaration, all modes must be satisfied *))
      | (__D, Root (Def d, __S), occ, k) ->
          let rec checkAll =
            function
            | nil -> ()
            | mS::mSs ->
                let rec checkSome =
                  function
                  | (__D')::[] ->
                      (((groundAtom (__D', M.Minus, __S, mS, (1, occ));
                         checkAll mSs))
                      (* ignore return *))
                  | (__D')::__Ds ->
                      ((((try
                            groundAtom (__D', M.Minus, __S, mS, (1, occ)); ()
                          with | ModeError _ -> checkSome __Ds))
                       (* ignore return *));
                       checkAll mSs)(* try D', if it doesn't work, try another context in the Ds *)
                  (* D' is the only (last) possibility; on failure, we raise ModeError *) in
                checkSome
                  (k (updateAtom (__D, M.Plus, __S, d, mS, (1, occ)))) in
          ((checkAll (lookup (d, occ)))
            (* for a declaration, all modes must be satisfied *))
    let rec checkG1 __81__ __82__ __83__ __84__ =
      match (__81__, __82__, __83__, __84__) with
      | (__D, Pi ((_, I.Maybe), __V), occ, k) ->
          ctxPop
            (checkG1
               ((I.Decl (__D, Universal)), __V, (P.body occ),
                 (fun (Decl (__D', m)) -> ctxPush (m, (k __D')))))
      | (__D, Pi ((Dec (_, __V1), I.No), __V2), occ, k) ->
          ctxPop
            (checkD1 (__D, __V1, (P.label occ), (fun (__D') -> [__D']));
             checkG1
               ((I.Decl (__D, Universal)), __V2, (P.body occ),
                 (fun (Decl (__D', m)) -> ctxPush (m, (k __D')))))
      | (__D, Root (Const a, __S), occ, k) ->
          let rec checkList __77__ __78__ =
            match (__77__, __78__) with
            | (found, nil) -> nil
            | (false, mS::[]) ->
                (match groundAtom (__D, M.Plus, __S, mS, (1, occ)) with
                 | Unique ->
                     k (updateAtom (__D, M.Minus1, __S, a, mS, (1, occ)))
                 | Ambig ->
                     k (updateAtom (__D, M.Minus, __S, a, mS, (1, occ))))
            | (found, mS::mSs) ->
                let found' =
                  ((try groundAtom (__D, M.Plus, __S, mS, (1, occ)); true
                    with | ModeError _ -> false)
                  (* handler scope??? -fp *)) in
                let __Ds' = checkList (found || found') mSs in
                ((if found'
                  then
                    (k (updateAtom (__D, M.Minus, __S, a, mS, (1, occ)))) @
                      __Ds'
                  else __Ds')
                  (* found' is true iff D satisfies mS *)
                  (* compute all other mode contexts *))
            (* Wed Aug 20 21:52:31 2003 -fp *)(* uniqueness not permitted on multiple modes right now *)
            (* mS is the last possible mode to check;
                    if the check fails, we don't catch ModeError *)
            (* found = true *) in
          ((checkList false (lookup (a, occ)))
            (* for a goal, at least one mode must be satisfied *))
      | (__D, Root (Def d, __S), occ, k) ->
          let rec checkList __79__ __80__ =
            match (__79__, __80__) with
            | (found, nil) -> nil
            | (false, mS::[]) ->
                (match groundAtom (__D, M.Plus, __S, mS, (1, occ)) with
                 | Unique ->
                     k (updateAtom (__D, M.Minus1, __S, d, mS, (1, occ)))
                 | Ambig ->
                     k (updateAtom (__D, M.Minus, __S, d, mS, (1, occ))))
            | (found, mS::mSs) ->
                let found' =
                  try groundAtom (__D, M.Plus, __S, mS, (1, occ)); true
                  with | ModeError _ -> false in
                let __Ds' = checkList (found || found') mSs in
                ((if found'
                  then
                    (k (updateAtom (__D, M.Minus, __S, d, mS, (1, occ)))) @
                      __Ds'
                  else __Ds')
                  (* found' is true iff D satisfies mS *)
                  (* compute all other mode contexts *))
            (* Wed Aug 20 21:52:31 2003 -fp *)(* uniqueness not permitted on multiple modes right now *)
            (* mS is the last possible mode to check;
                    if the check fails, we don't catch ModeError *)
            (* found = true *) in
          ((checkList false (lookup (d, occ)))
            (* for a goal, at least one mode must be satisfied *))
    let rec checkDlocal (__D) (__V) occ =
      try checkD1 (__D, __V, occ, (fun (__D') -> [__D']))
      with | ModeError (occ, msg) -> raise (Error' (occ, msg))
    let rec cidFromHead = function | Const a -> a | Def a -> a
    let rec checkD conDec fileName occOpt =
      let _ = checkFree := false in
      let rec checkable =
        function
        | Root (Ha, _) ->
            (match ModeTable.mmodeLookup (cidFromHead Ha) with
             | nil -> false
             | _ -> true)
        | Uni _ -> false
        | Pi (_, __V) -> checkable __V in
      let __V = I.conDecType conDec in
      if checkable __V
      then
        try checkDlocal (I.Null, __V, P.top)
        with
        | Error' (occ, msg) ->
            (match occOpt with
             | None -> raise (Error msg)
             | Some occTree ->
                 raise
                   (Error
                      (wrapMsg'
                         (fileName, (P.occToRegionClause occTree occ), msg))))
      else ()
    let rec checkAll =
      function
      | nil -> ()
      | (Const c)::clist ->
          (if (!Global.chatter) > 3
           then print ((Names.qidToString (Names.constQid c)) ^ " ")
           else ();
           (try checkDlocal (I.Null, (I.constType c), P.top)
            with | Error' (occ, msg) -> raise (Error (wrapMsg (c, occ, msg))));
           checkAll clist)
      | (Def d)::clist ->
          (if (!Global.chatter) > 3
           then print ((Names.qidToString (Names.constQid d)) ^ " ")
           else ();
           (try checkDlocal (I.Null, (I.constType d), P.top)
            with | Error' (occ, msg) -> raise (Error (wrapMsg (d, occ, msg))));
           checkAll clist)
    let rec checkMode a ms =
      let _ =
        if (!Global.chatter) > 3
        then
          print
            (((^) "Mode checking family " Names.qidToString
                (Names.constQid a))
               ^ ":\n")
        else () in
      let clist = Index.lookup a in
      let _ = checkFree := false in
      let _ = checkAll clist in
      let _ = if (!Global.chatter) > 3 then print "\n" else () in ()
    let rec checkFreeOut a ms =
      let _ =
        if (!Global.chatter) > 3
        then
          print
            (((^) "Checking output freeness of " Names.qidToString
                (Names.constQid a))
               ^ ":\n")
        else () in
      let clist = Index.lookup a in
      let _ = checkFree := true in
      let _ = checkAll clist in
      let _ = if (!Global.chatter) > 3 then print "\n" else () in ()
    let checkD = checkD
    let checkMode = checkMode
    let checkFreeOut = checkFreeOut
  end ;;
