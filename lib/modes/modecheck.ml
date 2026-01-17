
module type MODECHECK  =
  sig
    exception Error of
      ((string)(* Modified: Frank Pfenning *)(* Author: Carsten Schuermann *)
      (* Mode Checking *)) 
    val checkD :
      (IntSyn.__ConDec * string * Paths.occConDec option) ->
        ((unit)(* for new declarations *))
    val checkMode :
      (IntSyn.cid * ModeSyn.__ModeSpine) ->
        ((unit)(* for prior declarations *)(* raises Error (msg) *))
    val checkFreeOut :
      (IntSyn.cid * ModeSyn.__ModeSpine) ->
        ((unit)(* for output coverage of prior declarations *)(* raises Error(msg) *))
  end;;




module ModeCheck(ModeCheck:sig
                             module ModeTable : MODETABLE
                             module Whnf : WHNF
                             module Index : INDEX
                             module Origins :
                             ((ORIGINS)(* Mode Checking *)
                             (* Author: Carsten Schuermann *)(* Modified: Frank Pfenning, Roberto Virga *)
                             (*! structure IntSyn : INTSYN !*)(*! sharing ModeSyn.IntSyn = IntSyn !*)
                             (*! sharing Whnf.IntSyn = IntSyn !*)
                             (*! sharing Index.IntSyn = IntSyn !*)
                             (*! structure Paths : PATHS !*))
                           end) : MODECHECK =
  struct
    exception Error of
      ((string)(*! structure Paths = Paths !*)(*! structure ModeSyn = ModeSyn !*)
      (*! structure IntSyn = IntSyn !*)(*! sharing Origins.IntSyn = IntSyn !*)
      (*! sharing Origins.Paths = Paths !*)) 
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
    let checkFree = ref false__
    let rec wrapMsg (c, occ, msg) =
      match Origins.originLookup c with
      | (fileName, NONE) -> (fileName ^ ":") ^ msg
      | (fileName, SOME occDec) ->
          P.wrapLoc'
            ((P.Loc (fileName, (P.occToRegionClause occDec occ))),
              (Origins.linesInfoLookup fileName),
              ((((^) "Constant " Names.qidToString (Names.constQid c)) ^ "\n")
                 ^ msg))
    let rec wrapMsg' (fileName, r, msg) =
      P.wrapLoc ((P.Loc (fileName, r)), msg)
    exception ModeError of (P.occ * string) 
    exception Error' of (P.occ * string) 
    let rec lookup (a, occ) =
      match ModeTable.mmodeLookup a with
      | nil ->
          raise
            (Error'
               (occ,
                 ((^) "No mode declaration for " I.conDecName (I.sgnLookup a))))
      | sMs -> sMs
    let rec nameOf =
      function
      | Existential (_, NONE) -> "?"
      | Existential (_, SOME name) -> name
      | _ -> "?"
    let rec unique =
      function
      | (k, nil) -> true__
      | (k, k'::ks) -> (k <> k') && (unique (k, ks))
    let rec isUniversal = function | Universal -> true__ | _ -> false__
    let rec isGround =
      function | Existential (Ground _, _) -> true__ | _ -> false__
    let rec uniqueness =
      function | Existential (Ground u, _) -> u | Universal -> Unique
    let rec ambiguate =
      function | M.Plus -> M.Plus | M.Minus -> M.Minus | M.Minus1 -> M.Minus
    let rec andUnique = function | (Unique, Unique) -> Unique | _ -> Ambig
    let rec isFree =
      function | Existential (Free, _) -> true__ | _ -> false__
    exception Eta 
    let rec etaContract =
      function
      | (Root (BVar k, S), n) ->
          if k > n then (etaSpine (S, n); k - n) else raise Eta
      | (Lam (D, U), n) -> etaContract (U, (n + 1))
      | _ -> raise Eta
    let rec etaSpine =
      function
      | (I.Nil, 0) -> ()
      | (App (U, S), n) ->
          if (etaContract (U, 0)) = n
          then etaSpine (S, (n - 1))
          else raise Eta
    let rec checkPattern =
      function
      | (D, k, args, I.Nil) -> ()
      | (D, k, args, App (U, S)) ->
          let k' = etaContract (U, 0) in
          if
            (k > k') &&
              ((isUniversal (I.ctxLookup (D, k'))) && (unique (k', args)))
          then checkPattern (D, k, (k' :: args), S)
          else raise Eta
    let rec isPattern (D, k, S) =
      try checkPattern (D, k, nil, S); true__ with | Eta -> false__
    let rec strictExpN =
      function
      | (D, _, Uni _) -> false__
      | (D, p, Lam (_, U)) ->
          strictExpN ((I.Decl (D, Universal)), (p + 1), U)
      | (D, p, Pi ((D', _), U)) ->
          (strictDecN (D, p, D')) ||
            (strictExpN ((I.Decl (D, Universal)), (p + 1), U))
      | (D, p, Root (H, S)) ->
          (match H with
           | BVar k' ->
               if k' = p
               then isPattern (D, k', S)
               else
                 if isUniversal (I.ctxLookup (D, k'))
                 then strictSpineN (D, p, S)
                 else false__
           | Const c -> strictSpineN (D, p, S)
           | Def d -> strictSpineN (D, p, S)
           | FgnConst (cs, conDec) -> strictSpineN (D, p, S))
      | (D, p, FgnExp (cs, ops)) -> false__
    let rec strictSpineN =
      function
      | (_, _, I.Nil) -> false__
      | (D, p, App (U, S)) ->
          (strictExpN (D, p, U)) || (strictSpineN (D, p, S))
    let rec strictDecN (D, p, Dec (_, V)) = strictExpN (D, p, V)
    let rec freeExpN =
      function
      | (D, d, mode, Root (BVar k, S), occ, strictFun) ->
          (freeVar (D, d, mode, k, (P.head occ), strictFun);
           freeSpineN (D, d, mode, S, (1, occ), strictFun))
      | (D, d, mode, Root (Const _, S), occ, strictFun) ->
          freeSpineN (D, d, mode, S, (1, occ), strictFun)
      | (D, d, mode, Root (Def _, S), occ, strictFun) ->
          freeSpineN (D, d, mode, S, (1, occ), strictFun)
      | (D, d, mode, Root (FgnConst (cs, conDec), S), occ, strictFun) ->
          freeSpineN (D, d, mode, S, (1, occ), strictFun)
      | (D, d, mode, Lam (_, U), occ, strictFun) ->
          freeExpN
            ((I.Decl (D, Universal)), (d + 1), mode, U, (P.body occ),
              strictFun)
      | (D, d, mode, FgnExp csfe, occ, strictFun) ->
          I.FgnExpStd.App.apply csfe
            (function
             | U ->
                 freeExpN
                   (D, d, mode, (Whnf.normalize (U, I.id)), occ, strictFun))
    let rec freeSpineN =
      function
      | (D, d, mode, I.Nil, _, strictFun) -> ()
      | (D, d, mode, App (U, S), (p, occ), strictFun) ->
          (freeExpN (D, d, mode, U, (P.arg (p, occ)), strictFun);
           freeSpineN (D, d, mode, S, ((p + 1), occ), strictFun))
    let rec freeVar (D, d, mode, k, occ, strictFun) =
      let status = I.ctxLookup (D, k) in
      if (isFree status) || ((isUniversal status) || (strictFun (k - d)))
      then ()
      else
        raise
          (ModeError
             (occ,
               (((("Occurrence of variable " ^ (nameOf status)) ^ " in ") ^
                   (M.modeToString mode))
                  ^ " argument not free")))
    let rec nonStrictExpN =
      function
      | (D, Root (BVar k, S)) -> nonStrictSpineN ((nonStrictVarD (D, k)), S)
      | (D, Root (Const c, S)) -> nonStrictSpineN (D, S)
      | (D, Root (Def d, S)) -> nonStrictSpineN (D, S)
      | (D, Root (FgnConst (cs, conDec), S)) -> nonStrictSpineN (D, S)
      | (D, Lam (_, U)) ->
          I.ctxPop (nonStrictExpN ((I.Decl (D, Universal)), U))
      | (D, FgnExp _) ->
          raise
            (Error "Foreign expressions not permitted when checking freeness")
    let rec nonStrictSpineN =
      function
      | (D, I.Nil) -> D
      | (D, App (U, S)) -> nonStrictSpineN ((nonStrictExpN (D, U)), S)
    let rec nonStrictVarD =
      function
      | (Decl (D, Existential (Free, name)), 1) ->
          I.Decl (D, (Existential (Unknown, name)))
      | (D, 1) -> D
      | (Decl (D, status), k) ->
          I.Decl ((nonStrictVarD (D, (k - 1))), status)
    let rec updateExpN =
      function
      | (D, Root (BVar k, S), u) ->
          if isUniversal (I.ctxLookup (D, k))
          then updateSpineN (D, S, u)
          else
            if isPattern (D, k, S)
            then updateVarD (D, k, u)
            else
              if !checkFree
              then nonStrictSpineN ((nonStrictVarD (D, k)), S)
              else D
      | (D, Root (Const c, S), u) -> updateSpineN (D, S, u)
      | (D, Root (Def d, S), u) -> updateSpineN (D, S, u)
      | (D, Root (FgnConst (cs, conDec), S), u) -> updateSpineN (D, S, u)
      | (D, Lam (_, U), u) ->
          I.ctxPop (updateExpN ((I.Decl (D, Universal)), U, u))
      | (D, FgnExp _, u) -> D
    let rec updateSpineN =
      function
      | (D, I.Nil, u) -> D
      | (D, App (U, S), u) -> updateSpineN ((updateExpN (D, U, u)), S, u)
    let rec updateVarD =
      function
      | (Decl (D, Existential (_, name)), 1, u) ->
          I.Decl (D, (Existential ((Ground u), name)))
      | (Decl (D, status), k, u) ->
          I.Decl ((updateVarD (D, (k - 1), u)), status)
    let rec updateAtom' =
      function
      | (D, mode, I.Nil, M.Mnil, _) -> D
      | (D, M.Plus, App (U, S), Mapp (Marg (M.Plus, _), mS), (p, occ)) ->
          updateAtom'
            ((updateExpN (D, U, Unique)), M.Plus, S, mS, ((p + 1), occ))
      | (D, M.Minus, App (U, S), Mapp (Marg (M.Minus, _), mS), (p, occ)) ->
          updateAtom'
            ((updateExpN (D, U, Ambig)), M.Minus, S, mS, ((p + 1), occ))
      | (D, M.Minus, App (U, S), Mapp (Marg (M.Minus1, _), mS), (p, occ)) ->
          updateAtom'
            ((updateExpN (D, U, Ambig)), M.Minus, S, mS, ((p + 1), occ))
      | (D, M.Minus1, App (U, S), Mapp (Marg (M.Minus, _), mS), (p, occ)) ->
          updateAtom'
            ((updateExpN (D, U, Ambig)), M.Minus1, S, mS, ((p + 1), occ))
      | (D, M.Minus1, App (U, S), Mapp (Marg (M.Minus1, _), mS), (p, occ)) ->
          updateAtom'
            ((updateExpN (D, U, Unique)), M.Minus1, S, mS, ((p + 1), occ))
      | (D, mode, App (U, S), Mapp (_, mS), (p, occ)) ->
          updateAtom' (D, mode, S, mS, ((p + 1), occ))
    let rec freeAtom =
      function
      | (D, mode, I.Nil, Vs, M.Mnil, _) -> ()
      | (D, M.Minus, App (U, S), (Pi ((Dec (_, V1), _), V2), s), Mapp
         (Marg (M.Minus, _), mS), (p, occ)) ->
          (freeExpN
             (D, 0, M.Minus, U, (P.arg (p, occ)),
               (function | q -> strictExpN (D, q, (Whnf.normalize (V1, s)))));
           freeAtom
             (D, M.Minus, S,
               (Whnf.whnfExpandDef (V2, (I.Dot ((I.Exp U), s)))), mS,
               ((p + 1), occ)))
      | (D, mode, App (U, S), (Pi (_, V2), s), Mapp (_, mS), (p, occ)) ->
          freeAtom
            (D, mode, S, (Whnf.whnfExpandDef (V2, (I.Dot ((I.Exp U), s)))),
              mS, ((p + 1), occ))
    let rec updateAtom (D, mode, S, a, mS, (p, occ)) =
      let _ =
        if !checkFree
        then
          freeAtom
            (D, (ambiguate mode), S, ((I.constType a), I.id), mS, (p, occ))
        else () in
      updateAtom' (D, mode, S, mS, (p, occ))
    let rec groundExpN =
      function
      | (D, mode, Root (BVar k, S), occ) ->
          andUnique
            ((groundVar (D, mode, k, (P.head occ))),
              (groundSpineN (D, mode, S, (1, occ))))
      | (D, mode, Root (Const c, S), occ) ->
          groundSpineN (D, mode, S, (1, occ))
      | (D, mode, Root (Def d, S), occ) ->
          groundSpineN (D, mode, S, (1, occ))
      | (D, mode, Root (FgnConst (cs, conDec), S), occ) ->
          groundSpineN (D, mode, S, (1, occ))
      | (D, mode, Lam (_, U), occ) ->
          groundExpN ((I.Decl (D, Universal)), mode, U, (P.body occ))
      | (D, mode, FgnExp csfe, occ) ->
          I.FgnExpStd.fold csfe
            (function
             | (U, u) ->
                 andUnique
                   ((groundExpN (D, mode, (Whnf.normalize (U, I.id)), occ)),
                     u)) Unique
    let rec groundSpineN =
      function
      | (D, mode, I.Nil, _) -> Unique
      | (D, mode, App (U, S), (p, occ)) ->
          andUnique
            ((groundExpN (D, mode, U, (P.arg (p, occ)))),
              (groundSpineN (D, mode, S, ((p + 1), occ))))
    let rec groundVar =
      function
      | (D, M.Minus1, k, occ) ->
          (match I.ctxLookup (D, k) with
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
                      (((("Occurrence of variable " ^ (nameOf s)) ^ " in ") ^
                          (M.modeToString M.Minus1))
                         ^ " argument not necessarily ground"))))
      | (D, mode, k, occ) ->
          let status = I.ctxLookup (D, k) in
          if (isGround status) || (isUniversal status)
          then uniqueness status
          else
            raise
              (ModeError
                 (occ,
                   (((("Occurrence of variable " ^ (nameOf status)) ^ " in ")
                       ^ (M.modeToString mode))
                      ^ " argument not necessarily ground")))
    let rec groundAtom =
      function
      | (D, _, I.Nil, M.Mnil, _) -> Unique
      | (D, M.Plus, App (U, S), Mapp (Marg (M.Plus, _), mS), (p, occ)) ->
          andUnique
            ((groundExpN (D, M.Plus, U, (P.arg (p, occ)))),
              (groundAtom (D, M.Plus, S, mS, ((p + 1), occ))))
      | (D, M.Minus, App (U, S), Mapp (Marg (M.Minus, _), mS), (p, occ)) ->
          (groundExpN (D, M.Minus, U, (P.arg (p, occ)));
           groundAtom (D, M.Minus, S, mS, ((p + 1), occ)))
      | (D, M.Minus, App (U, S), Mapp (Marg (M.Minus1, _), mS), (p, occ)) ->
          (groundExpN (D, M.Minus1, U, (P.arg (p, occ)));
           groundAtom (D, M.Minus, S, mS, ((p + 1), occ)))
      | (D, mode, App (U, S), Mapp (_, mS), (p, occ)) ->
          groundAtom (D, mode, S, mS, ((p + 1), occ))
    let rec ctxPush (m, Ds) = List.map (function | D -> I.Decl (D, m)) Ds
    let rec ctxPop (Ds) = List.map (function | Decl (D, m) -> D) Ds
    let rec checkD1 =
      function
      | (D, Pi ((Dec (name, _), I.Maybe), V), occ, k) ->
          checkD1
            ((I.Decl (D, (Existential (Free, name)))), V, (P.body occ),
              (function | Decl (D', m) -> ctxPush (m, (k D'))))
      | (D, Pi ((Dec (name, V1), I.No), V2), occ, k) ->
          checkD1
            ((I.Decl (D, (Existential (Free, name)))), V2, (P.body occ),
              (function
               | Decl (D', m) ->
                   ctxPush (m, (checkG1 (D', V1, (P.label occ), k)))))
      | (D, Root (Const a, S), occ, k) ->
          let checkAll =
            function
            | nil -> ()
            | mS::mSs ->
                let checkSome =
                  function
                  | (D')::[] ->
                      (groundAtom (D', M.Minus, S, mS, (1, occ));
                       checkAll mSs)
                  | (D')::Ds ->
                      ((try groundAtom (D', M.Minus, S, mS, (1, occ)); ()
                        with | ModeError _ -> checkSome Ds);
                       checkAll mSs) in
                checkSome (k (updateAtom (D, M.Plus, S, a, mS, (1, occ)))) in
          checkAll (lookup (a, occ))
      | (D, Root (Def d, S), occ, k) ->
          let checkAll =
            function
            | nil -> ()
            | mS::mSs ->
                let checkSome =
                  function
                  | (D')::[] ->
                      (groundAtom (D', M.Minus, S, mS, (1, occ));
                       checkAll mSs)
                  | (D')::Ds ->
                      ((try groundAtom (D', M.Minus, S, mS, (1, occ)); ()
                        with | ModeError _ -> checkSome Ds);
                       checkAll mSs) in
                checkSome (k (updateAtom (D, M.Plus, S, d, mS, (1, occ)))) in
          checkAll (lookup (d, occ))
    let rec checkG1 =
      function
      | (D, Pi ((_, I.Maybe), V), occ, k) ->
          ctxPop
            (checkG1
               ((I.Decl (D, Universal)), V, (P.body occ),
                 (function | Decl (D', m) -> ctxPush (m, (k D')))))
      | (D, Pi ((Dec (_, V1), I.No), V2), occ, k) ->
          ctxPop
            (checkD1 (D, V1, (P.label occ), (function | D' -> [D']));
             checkG1
               ((I.Decl (D, Universal)), V2, (P.body occ),
                 (function | Decl (D', m) -> ctxPush (m, (k D')))))
      | (D, Root (Const a, S), occ, k) ->
          let checkList arg__0 arg__1 =
            match (arg__0, arg__1) with
            | (found, nil) -> nil
            | (false__, mS::[]) ->
                (match groundAtom (D, M.Plus, S, mS, (1, occ)) with
                 | Unique -> k (updateAtom (D, M.Minus1, S, a, mS, (1, occ)))
                 | Ambig -> k (updateAtom (D, M.Minus, S, a, mS, (1, occ))))
            | (found, mS::mSs) ->
                let found' =
                  try groundAtom (D, M.Plus, S, mS, (1, occ)); true__
                  with | ModeError _ -> false__ in
                let Ds' = checkList (found || found') mSs in
                if found'
                then (k (updateAtom (D, M.Minus, S, a, mS, (1, occ)))) @ Ds'
                else Ds' in
          checkList false__ (lookup (a, occ))
      | (D, Root (Def d, S), occ, k) ->
          let checkList arg__0 arg__1 =
            match (arg__0, arg__1) with
            | (found, nil) -> nil
            | (false__, mS::[]) ->
                (match groundAtom (D, M.Plus, S, mS, (1, occ)) with
                 | Unique -> k (updateAtom (D, M.Minus1, S, d, mS, (1, occ)))
                 | Ambig -> k (updateAtom (D, M.Minus, S, d, mS, (1, occ))))
            | (found, mS::mSs) ->
                let found' =
                  try groundAtom (D, M.Plus, S, mS, (1, occ)); true__
                  with | ModeError _ -> false__ in
                let Ds' = checkList (found || found') mSs in
                if found'
                then (k (updateAtom (D, M.Minus, S, d, mS, (1, occ)))) @ Ds'
                else Ds' in
          checkList false__ (lookup (d, occ))
    let rec checkDlocal (D, V, occ) =
      try checkD1 (D, V, occ, (function | D' -> [D']))
      with | ModeError (occ, msg) -> raise (Error' (occ, msg))
    let rec cidFromHead = function | Const a -> a | Def a -> a
    let rec checkD (conDec, fileName, occOpt) =
      let _ = checkFree := false__ in
      let checkable =
        function
        | Root (Ha, _) ->
            (match ModeTable.mmodeLookup (cidFromHead Ha) with
             | nil -> false__
             | _ -> true__)
        | Uni _ -> false__
        | Pi (_, V) -> checkable V in
      let V = I.conDecType conDec in
      if checkable V
      then
        try checkDlocal (I.Null, V, P.top)
        with
        | Error' (occ, msg) ->
            (match occOpt with
             | NONE -> raise (Error msg)
             | SOME occTree ->
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
    let rec checkMode (a, ms) =
      let _ =
        if (!Global.chatter) > 3
        then
          print
            (((^) "Mode checking family " Names.qidToString
                (Names.constQid a))
               ^ ":\n")
        else () in
      let clist = Index.lookup a in
      let _ = checkFree := false__ in
      let _ = checkAll clist in
      let _ = if (!Global.chatter) > 3 then print "\n" else () in ()
    let rec checkFreeOut (a, ms) =
      let _ =
        if (!Global.chatter) > 3
        then
          print
            (((^) "Checking output freeness of " Names.qidToString
                (Names.constQid a))
               ^ ":\n")
        else () in
      let clist = Index.lookup a in
      let _ = checkFree := true__ in
      let _ = checkAll clist in
      let _ = if (!Global.chatter) > 3 then print "\n" else () in ()
    let ((checkD)(* Uniqueness information *)(* u ::= Unique           *)
      (*     | Ambig            *)(* Groundedness information   *)
      (* I ::= Free                 *)(*     | Unknown              *)
      (*     | Ground               *)(* Variable status             *)
      (* S ::= Existential (I, xOpt) *)(*     | Universal             *)
      (* hack: if true, check freeness of output arguments in subgoals *)
      (* Representation invariant:

       Groundness information:
       T stands for ground, B stands for unknown
       Ex  for a named existential variable
       Par for a parameter

       Mode context   D ::= . | D, S

       If D contains Status information for variables in
       a context G, we write G ~ D
       We write D' >= D if for all i
         D(i) par iff D'(i) par
         D(i) bot implies D'(i) bot or D'(i) top
         D(i) top implies D'(i) top
    *)
      (* copied from worldcheck/worldsyn.fun *)(* lookup (a, occ) = mSs

       Invariant: mS are the argument modes for a
       Raises an error if no mode for a has declared.
       (occ is used in error message)
    *)
      (* nameOf S, selects a name for S *)(* unique (k, ks) = B

       Invariant:
       B iff k does not occur in ks
    *)
      (* isUniversal S = B

       Invariant:
       B iff S = Par
    *)
      (* isGround S = B

       Invariant:
       B iff S = Ex (T x)
    *)
      (* uniqueness S = u
       where u is the uniqueness property of status S
    *)
      (* ambiguate (mode) = mode'
       where mode' forgets uniqueness properties
    *)
      (* andUnique (u1, u2) = Unique if u1 = u2 = Unique
       = Ambig otherwise
    *)
      (* isFree S = b

       Invariant:
       b iff S = Ex (B x)
    *)
      (* etaContract (U, n) = k

       if lam V1... lam Vn. U =eta*=> k
       otherwise raise exception Eta

       Invariant: G, V1,..., Vn |- U : V for some G, Vi, V.
                  U in NF
    *)
      (* etaSpine (S, n) = ()
       if S =eta*=> n ; n-1 ; ... ; 1 ; Nil
       otherwise raise exception Eta

       Invariant: G |- S : V1 >> V2 for some G, V1, V2
                  S in NF
    *)
      (* S[s] should be impossible *)(* isPattern (D, k, mS) = B

       Invariant:
       B iff k > k' for all k' in mS
         and for all k in mS: k is parameter
         and for all k', k'' in mS: k' <> k''
    *)
      (* ------------------------------------------- strictness check *)
      (* This repeats some code from ../typecheck/strict.fun *)(* Interface here is somewhat different *)
      (* strictExpN (D, p, U) = B

       Invariant:
       If  D |- U : V
       and U is in nf (normal form)
       then B iff U is strict in p
    *)
      (* checking D in this case should be redundant -fp *)
      (* strictDecN (D, p, D) orelse *)(* equivalently: isUniversal .. andalso strictSpineN .. *)
      (* no other cases possible *)(* this is a hack - until we investigate this further   -rv *)
      (* no other cases possible *)(* strictSpineN (D, S) = B

       Invariant:
       If  D |- S : V > W
       and S is in nf (normal form)
       then B iff S is strict in k
    *)
      (*
    fun strictAtom (D, p, mode, I.Nil, (V, s), M.Mnil) = false
      | strictAtom (D, p, M.Minus, I.App (U, S), (I.Pi ((I.Dec (_, V1), _), V2), s),
                     M.Mapp (M.Marg (M.Minus, _), mS)) =
          strictExpN (D, p, Whnf.normalize (V1, s))
          orelse strictAtom (D, p, M.Minus, S, Whnf.whnfExpandDef (V2, I.Dot (I.Exp U, s)), mS)
      | strictAtom (D, p, mode, I.App (U, S), (I.Pi (_, V2), s), M.Mapp(_, mS)) =
          strictAtom (D, p, mode, S, Whnf.whnfExpandDef (V2, I.Dot (I.Exp U, s)), mS)
    *)
      (* ------------------------------------------- freeness check *)
      (* freeExpN (D, mode, U, occ = ()

       If G |- U : V  (U in nf)
       and G ~ D
       then freeExpN terminates with () if D |- U free
       else exception ModeError is raised

       (occ and mode are used in error messages)
    *)
      (* punting on the occ here  - ak *)(* freeSpineN (D, mode, S, occ, strictFun)  = ()

       If   G |- S : V1  > V2   (S in nf)
       and  G ~ D
       then freeSpineN terminates with () if  D |- S free
       else exception ModeError is raised

       (occ and mode are used in error messages)
    *)
      (* freeVar (D, mode, k, occ, strictFun)  = ()

       If   G |- k : V1
       and  G ~ D
       then freeVar terminates with () if  D |- S free
       else exception ModeError is raised

       (occ and mode are used in error messages)
    *)
      (* -------------------------------- non-strict mode context update *)
      (* nonStrictExpN (D, U) = D'

       If   G |- U : V     (U in nf)
       and  D ~ G
       then D' >= D where D'(k) Unknown for all existential variables k
            in U that are free in D
    *)
      (* nonStrictSpineN (D, S) = D'

       If   G |- S : V1 > V2      (S in nf)
       and  D ~ G
       then D' >= D' where D'(k) Unkown for all existential variables k
            in S that are Free in D
    *)
      (* nonStrictVarD (D, k) = D'

       If   G |- k : V
       and  D ~ G
       and  k is an existential variable
       then D' >= D where k is nonStrictd as described in  nonStrictExpN
    *)
      (* Universal, or already Unknown or Ground - leave unchanged *)
      (* ------------------------------------------- mode context update *)
      (* updateExpN (D, U, u) = D'

       If   G |- U : V     (U in nf)
       and  D ~ G
       then D' >= D where D'(k) Ground for all existential variables k
            with a strict occurrence in U
            and D'(k) Unkown for all existential variable k
            with a non-strict occurrence, but no strict occurrence in U
            (if !checkFree is true)

       u is the uniqueness property for the new ground assumptions
    *)
      (* no occurrence inside a FgnExp is considered strict *)(* updateSpineN (D, S, u) = D'

       If   G |- S : V1 > V2      (S in nf)
       and  D ~ G
       then D' >= D' where D'(k) Ground for all existential variables k
            with a strict occurrence in S
    *)
      (* updateVarD (D, k, u) = D'

       If   G |- k : V
       and  D ~ G
       and  k is an existential variable
       then D' >= D where k is updated as described in  updateExpN
    *)
      (* ----------------------- mode context update by argument modes *)
      (* updateAtom (D, m, S, mS, (p,occ)) = D'

       If   G |- S : V > V'   ( S = U1 ; .. ; Un)
       and  D ~ G
       and  S ~ mS            (mS = m1 , .. , mn)
       and  m mode
       then D' >= D where
            all Ui are updated if mi = m (mod uniqueness)

       The new ground variables are marked Unique
         if m = (-1) and mi = (-1) (when updating from subgoals with unique inputs)
         or m = mi = (+) (when updating from the clause head)
       Otherwise they are marked Ambig.

       (p,occ) is used in error message if freeness is to be checked
    *)
      (* when checking freeness, all arguments must be input (+) or output (-) *)
      (* therefore, no case for M.Mapp (M.Marg (M.Minus, _), mS) is provided here *)
      (* freeAtom (D, m, S, (V,s), mS, (p, occ)) = ()

       checks if all output arguments in S according to mS are free.
       Invariant: G |- S : V[s] >> P for some G and P  (S in nf)
                  G ~ D
                  mode = (-) or (+); ( * ) or (-1) are excluded
    *)
      (* updateAtom (D, m, S, a, mS, (p, occ))
       see updateAtom', and performs additional freeness check if required
    *)
      (* ------------------------------------------- groundness check *)
      (* groundExpN (D, mode, U, occ)  = u

       If   G |- U : V    (U in nf)
       and  G ~ D
       then if mode = (+) or (-)
            then groundExpN terminates with u if  D |- U ground
                 else exception ModeError is raised
            if mode = (-1) then D |- U ground and U unique
                           else exception ModeError is raised

       u = Unique if all known variables in U are Unique
       u = Ambig otherwise

       (occ and mode are used in error messages)
    *)
      (* punting on occ here  - ak *)(* groundSpineN (D, mode, S, occ)  = u

       If   G |- S : V1  > V2   (S in nf)
       and  G ~ D
       then if mode = (+) or (-)
            then groundSpineN terminates with u if  D |- S ground
                 else exception ModeError is raised
            if mode = (-1) then D |- S ground and S unique
                           else exception ModeError is raised

       u = Unique if all known variables in S are Unique
       u = Ambig otherwise

       (occ and mode are used in error messages)
    *)
      (* groundVar (D, mode, k, occ)  = u

       If   G |- k : V1
       and  G ~ D
       then if mode = (+) or (-)
            then groundVar terminates with u if  D |- k ground
                 else exception ModeError is raised
            if mode = (-1) then D |- k ground and k unique
                           else exception ModeError is raised

       u = Unique if k is known to be unique, Ambig otherwise

       (occ and mode are used in error messages)
    *)
      (* Existential (Free, _) or Existential (Unknown, _) *)(* ------------------------------------------- groundness check by polarity *)
      (* groundAtom (D, m, S, mS, (p,occ))  = u

       If   G |- S : V > V'   ( S = U1 ; .. ; Un)
       and  D ~ G
       and  S ~ mS            (mS = m1 , .. , mn)
       and  m mode = (+) or (-1)
       then groundAtom returns u if  D |- Ui ground
            for all i s.t. mi = m (mod uniqueness)
            and checks that D |- Ui unique if mi = (-1) and m = (-)
       otherwise exception ModeError is raised

       u = Unique if all mi = m (mod uniqueness) are unique,
       u = Ambig otherwise

       ((p,occ) used in error messages)
    *)
      (* ignore uniqueness result here *)(* ignore uniqueness result here *)
      (* ------------------------------------------- mode checking first phase *)
      (* ctxPush (Ds, m) = Ds'
       raises the contexts Ds prepending m
    *)
      (* ctxPop Ds = Ds'
       lowers the contexts Ds
    *)(* checkD1 (D, V, occ, k) = ()

       Invariant:
         if G |- V : L
         and  V does not contain Skolem constants
         and  D ~ G
         then
            for each  mode mS of the head of V
              exists  some Di s.t. all (-) evars of mS are ground
                where  D' ~ G, D' >= D is obtained by updating D
                  and  k D' = [D1, ..., Di, ..., Dn]
                  and  Di ~ G, Di >= D' is obtained by mode checking on the subgoals of V

       exception ModeError is raised if the expression does not mode check
       exception Error' is raised if the expression contains type families
       that have no mode information associated with them
       (occ used in error messages)
    *)
      (* for a declaration, all modes must be satisfied *)
      (* D' is the only (last) possibility; on failure, we raise ModeError *)
      (* ignore return *)(* try D', if it doesn't work, try another context in the Ds *)
      (* ignore return *)(* for a declaration, all modes must be satisfied *)
      (* D' is the only (last) possibility; on failure, we raise ModeError *)
      (* ignore return *)(* try D', if it doesn't work, try another context in the Ds *)
      (* ignore return *)(* checkG1 (D, V, occ, k) = Ds

       Invariant:
         if G |- V : L
         and  V does not contain Skolem constants
         and  D ~ G
         then forall D' >= D that mode checks V, (k D') is a sublist of Ds
         and for each Di in Ds, Di ~ G and Di >= D'

       exception ModeError is raised if the expression does not mode check
       exception Error' is raised if the expression contains type families
       that have no mode information associated with them
       (occ used in error messages)
     *)
      (* for a goal, at least one mode must be satisfied *)
      (* found = true *)(* mS is the last possible mode to check;
                    if the check fails, we don't catch ModeError *)
      (* uniqueness not permitted on multiple modes right now *)
      (* Wed Aug 20 21:52:31 2003 -fp *)(* found' is true iff D satisfies mS *)
      (* handler scope??? -fp *)(* compute all other mode contexts *)
      (* for a goal, at least one mode must be satisfied *)
      (* found = true *)(* mS is the last possible mode to check;
                    if the check fails, we don't catch ModeError *)
      (* uniqueness not permitted on multiple modes right now *)
      (* Wed Aug 20 21:52:31 2003 -fp *)(* found' is true iff D satisfies mS *)
      (* compute all other mode contexts *)(* checkDlocal (D, V, occ) = ()

       Invariant:
       If   G |- V : L
       and  D ~ G
       then checkD terminates with ()  iff V is mode correct.

       otherwise exception ModeError is raised (occ used in error messages)
    *)
      (* --------------------------------------------------------- mode checking *)
      (* checkD (ConDec, occOpt)  = ()

       checkD terminates with () if ConDec is mode correct
       otherwise exception Error is raised

       (occOpt is used in error messages)
    *))
      = checkD
    let checkMode = checkMode
    let checkFreeOut = checkFreeOut
  end ;;
