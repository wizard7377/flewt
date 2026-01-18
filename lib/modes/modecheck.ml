
(* Mode Checking *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning *)
module type MODECHECK  =
  sig
    exception Error of string 
    (* for new declarations *)
    val checkD : (IntSyn.__ConDec * string * Paths.occConDec option) -> unit
    (* raises Error (msg) *)
    (* for prior declarations *)
    val checkMode : (IntSyn.cid * ModeSyn.__ModeSpine) -> unit
    (* raises Error(msg) *)
    (* for output coverage of prior declarations *)
    val checkFreeOut : (IntSyn.cid * ModeSyn.__ModeSpine) -> unit
  end;;




(* Mode Checking *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning, Roberto Virga *)
module ModeCheck(ModeCheck:sig
                             (*! structure IntSyn : INTSYN !*)
                             module ModeTable : MODETABLE
                             module Whnf : WHNF
                             module Index : INDEX
                             (*! sharing ModeSyn.IntSyn = IntSyn !*)
                             (*! sharing Whnf.IntSyn = IntSyn !*)
                             (*! sharing Index.IntSyn = IntSyn !*)
                             (*! structure Paths : PATHS !*)
                             module Origins : ORIGINS
                           end) : MODECHECK =
  struct
    (*! sharing Origins.Paths = Paths !*)
    (*! sharing Origins.IntSyn = IntSyn !*)
    (*! structure IntSyn = IntSyn !*)
    (*! structure ModeSyn = ModeSyn !*)
    (*! structure Paths = Paths !*)
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
    let checkFree = ref false__
    let rec wrapMsg (c, occ, msg) =
      match Origins.originLookup c with
      | (fileName, None) -> (fileName ^ ":") ^ msg
      | (fileName, Some occDec) ->
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
      | Existential (_, None) -> "?"
      | Existential (_, Some name) -> name
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
      | (Lam (__d, __u), n) -> etaContract (__u, (n + 1))
      | _ -> raise Eta
    let rec etaSpine =
      function
      | (I.Nil, 0) -> ()
      | (App (__u, S), n) ->
          if (etaContract (__u, 0)) = n
          then etaSpine (S, (n - 1))
          else raise Eta
    let rec checkPattern =
      function
      | (__d, k, args, I.Nil) -> ()
      | (__d, k, args, App (__u, S)) ->
          let k' = etaContract (__u, 0) in
          if
            (k > k') &&
              ((isUniversal (I.ctxLookup (__d, k'))) && (unique (k', args)))
          then checkPattern (__d, k, (k' :: args), S)
          else raise Eta
    let rec isPattern (__d, k, S) =
      try checkPattern (__d, k, nil, S); true__ with | Eta -> false__
    let rec strictExpN =
      function
      | (__d, _, Uni _) -> false__
      | (__d, p, Lam (_, __u)) ->
          strictExpN ((I.Decl (__d, Universal)), (p + 1), __u)
      | (__d, p, Pi ((__d', _), __u)) ->
          (strictDecN (__d, p, __d')) ||
            (strictExpN ((I.Decl (__d, Universal)), (p + 1), __u))
      | (__d, p, Root (H, S)) ->
          (match H with
           | BVar k' ->
               if k' = p
               then isPattern (__d, k', S)
               else
                 if isUniversal (I.ctxLookup (__d, k'))
                 then strictSpineN (__d, p, S)
                 else false__
           | Const c -> strictSpineN (__d, p, S)
           | Def d -> strictSpineN (__d, p, S)
           | FgnConst (cs, conDec) -> strictSpineN (__d, p, S))
      | (__d, p, FgnExp (cs, ops)) -> false__
    let rec strictSpineN =
      function
      | (_, _, I.Nil) -> false__
      | (__d, p, App (__u, S)) ->
          (strictExpN (__d, p, __u)) || (strictSpineN (__d, p, S))
    let rec strictDecN (__d, p, Dec (_, __v)) = strictExpN (__d, p, __v)
    let rec freeExpN =
      function
      | (__d, d, mode, Root (BVar k, S), occ, strictFun) ->
          (freeVar (__d, d, mode, k, (P.head occ), strictFun);
           freeSpineN (__d, d, mode, S, (1, occ), strictFun))
      | (__d, d, mode, Root (Const _, S), occ, strictFun) ->
          freeSpineN (__d, d, mode, S, (1, occ), strictFun)
      | (__d, d, mode, Root (Def _, S), occ, strictFun) ->
          freeSpineN (__d, d, mode, S, (1, occ), strictFun)
      | (__d, d, mode, Root (FgnConst (cs, conDec), S), occ, strictFun) ->
          freeSpineN (__d, d, mode, S, (1, occ), strictFun)
      | (__d, d, mode, Lam (_, __u), occ, strictFun) ->
          freeExpN
            ((I.Decl (__d, Universal)), (d + 1), mode, __u, (P.body occ),
              strictFun)
      | (__d, d, mode, FgnExp csfe, occ, strictFun) ->
          I.FgnExpStd.App.apply csfe
            (function
             | __u ->
                 freeExpN
                   (__d, d, mode, (Whnf.normalize (__u, I.id)), occ, strictFun))
    let rec freeSpineN =
      function
      | (__d, d, mode, I.Nil, _, strictFun) -> ()
      | (__d, d, mode, App (__u, S), (p, occ), strictFun) ->
          (freeExpN (__d, d, mode, __u, (P.arg (p, occ)), strictFun);
           freeSpineN (__d, d, mode, S, ((p + 1), occ), strictFun))
    let rec freeVar (__d, d, mode, k, occ, strictFun) =
      let status = I.ctxLookup (__d, k) in
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
      | (__d, Root (BVar k, S)) -> nonStrictSpineN ((nonStrictVarD (__d, k)), S)
      | (__d, Root (Const c, S)) -> nonStrictSpineN (__d, S)
      | (__d, Root (Def d, S)) -> nonStrictSpineN (__d, S)
      | (__d, Root (FgnConst (cs, conDec), S)) -> nonStrictSpineN (__d, S)
      | (__d, Lam (_, __u)) ->
          I.ctxPop (nonStrictExpN ((I.Decl (__d, Universal)), __u))
      | (__d, FgnExp _) ->
          raise
            (Error "Foreign expressions not permitted when checking freeness")
    let rec nonStrictSpineN =
      function
      | (__d, I.Nil) -> __d
      | (__d, App (__u, S)) -> nonStrictSpineN ((nonStrictExpN (__d, __u)), S)
    let rec nonStrictVarD =
      function
      | (Decl (__d, Existential (Free, name)), 1) ->
          I.Decl (__d, (Existential (Unknown, name)))
      | (__d, 1) -> __d
      | (Decl (__d, status), k) ->
          I.Decl ((nonStrictVarD (__d, (k - 1))), status)
    let rec updateExpN =
      function
      | (__d, Root (BVar k, S), u) ->
          if isUniversal (I.ctxLookup (__d, k))
          then updateSpineN (__d, S, u)
          else
            if isPattern (__d, k, S)
            then updateVarD (__d, k, u)
            else
              if !checkFree
              then nonStrictSpineN ((nonStrictVarD (__d, k)), S)
              else __d
      | (__d, Root (Const c, S), u) -> updateSpineN (__d, S, u)
      | (__d, Root (Def d, S), u) -> updateSpineN (__d, S, u)
      | (__d, Root (FgnConst (cs, conDec), S), u) -> updateSpineN (__d, S, u)
      | (__d, Lam (_, __u), u) ->
          I.ctxPop (updateExpN ((I.Decl (__d, Universal)), __u, u))
      | (__d, FgnExp _, u) -> __d
    let rec updateSpineN =
      function
      | (__d, I.Nil, u) -> __d
      | (__d, App (__u, S), u) -> updateSpineN ((updateExpN (__d, __u, u)), S, u)
    let rec updateVarD =
      function
      | (Decl (__d, Existential (_, name)), 1, u) ->
          I.Decl (__d, (Existential ((Ground u), name)))
      | (Decl (__d, status), k, u) ->
          I.Decl ((updateVarD (__d, (k - 1), u)), status)
    let rec updateAtom' =
      function
      | (__d, mode, I.Nil, M.Mnil, _) -> __d
      | (__d, M.Plus, App (__u, S), Mapp (Marg (M.Plus, _), mS), (p, occ)) ->
          updateAtom'
            ((updateExpN (__d, __u, Unique)), M.Plus, S, mS, ((p + 1), occ))
      | (__d, M.Minus, App (__u, S), Mapp (Marg (M.Minus, _), mS), (p, occ)) ->
          updateAtom'
            ((updateExpN (__d, __u, Ambig)), M.Minus, S, mS, ((p + 1), occ))
      | (__d, M.Minus, App (__u, S), Mapp (Marg (M.Minus1, _), mS), (p, occ)) ->
          updateAtom'
            ((updateExpN (__d, __u, Ambig)), M.Minus, S, mS, ((p + 1), occ))
      | (__d, M.Minus1, App (__u, S), Mapp (Marg (M.Minus, _), mS), (p, occ)) ->
          updateAtom'
            ((updateExpN (__d, __u, Ambig)), M.Minus1, S, mS, ((p + 1), occ))
      | (__d, M.Minus1, App (__u, S), Mapp (Marg (M.Minus1, _), mS), (p, occ)) ->
          updateAtom'
            ((updateExpN (__d, __u, Unique)), M.Minus1, S, mS, ((p + 1), occ))
      | (__d, mode, App (__u, S), Mapp (_, mS), (p, occ)) ->
          updateAtom' (__d, mode, S, mS, ((p + 1), occ))
    let rec freeAtom =
      function
      | (__d, mode, I.Nil, __Vs, M.Mnil, _) -> ()
      | (__d, M.Minus, App (__u, S), (Pi ((Dec (_, V1), _), V2), s), Mapp
         (Marg (M.Minus, _), mS), (p, occ)) ->
          (freeExpN
             (__d, 0, M.Minus, __u, (P.arg (p, occ)),
               (function | q -> strictExpN (__d, q, (Whnf.normalize (V1, s)))));
           freeAtom
             (__d, M.Minus, S,
               (Whnf.whnfExpandDef (V2, (I.Dot ((I.Exp __u), s)))), mS,
               ((p + 1), occ)))
      | (__d, mode, App (__u, S), (Pi (_, V2), s), Mapp (_, mS), (p, occ)) ->
          freeAtom
            (__d, mode, S, (Whnf.whnfExpandDef (V2, (I.Dot ((I.Exp __u), s)))),
              mS, ((p + 1), occ))
    let rec updateAtom (__d, mode, S, a, mS, (p, occ)) =
      let _ =
        if !checkFree
        then
          freeAtom
            (__d, (ambiguate mode), S, ((I.constType a), I.id), mS, (p, occ))
        else () in
      updateAtom' (__d, mode, S, mS, (p, occ))
    let rec groundExpN =
      function
      | (__d, mode, Root (BVar k, S), occ) ->
          andUnique
            ((groundVar (__d, mode, k, (P.head occ))),
              (groundSpineN (__d, mode, S, (1, occ))))
      | (__d, mode, Root (Const c, S), occ) ->
          groundSpineN (__d, mode, S, (1, occ))
      | (__d, mode, Root (Def d, S), occ) ->
          groundSpineN (__d, mode, S, (1, occ))
      | (__d, mode, Root (FgnConst (cs, conDec), S), occ) ->
          groundSpineN (__d, mode, S, (1, occ))
      | (__d, mode, Lam (_, __u), occ) ->
          groundExpN ((I.Decl (__d, Universal)), mode, __u, (P.body occ))
      | (__d, mode, FgnExp csfe, occ) ->
          I.FgnExpStd.fold csfe
            (function
             | (__u, u) ->
                 andUnique
                   ((groundExpN (__d, mode, (Whnf.normalize (__u, I.id)), occ)),
                     u)) Unique
    let rec groundSpineN =
      function
      | (__d, mode, I.Nil, _) -> Unique
      | (__d, mode, App (__u, S), (p, occ)) ->
          andUnique
            ((groundExpN (__d, mode, __u, (P.arg (p, occ)))),
              (groundSpineN (__d, mode, S, ((p + 1), occ))))
    let rec groundVar =
      function
      | (__d, M.Minus1, k, occ) ->
          (match I.ctxLookup (__d, k) with
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
      | (__d, mode, k, occ) ->
          let status = I.ctxLookup (__d, k) in
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
      | (__d, _, I.Nil, M.Mnil, _) -> Unique
      | (__d, M.Plus, App (__u, S), Mapp (Marg (M.Plus, _), mS), (p, occ)) ->
          andUnique
            ((groundExpN (__d, M.Plus, __u, (P.arg (p, occ)))),
              (groundAtom (__d, M.Plus, S, mS, ((p + 1), occ))))
      | (__d, M.Minus, App (__u, S), Mapp (Marg (M.Minus, _), mS), (p, occ)) ->
          (groundExpN (__d, M.Minus, __u, (P.arg (p, occ)));
           groundAtom (__d, M.Minus, S, mS, ((p + 1), occ)))
      | (__d, M.Minus, App (__u, S), Mapp (Marg (M.Minus1, _), mS), (p, occ)) ->
          (groundExpN (__d, M.Minus1, __u, (P.arg (p, occ)));
           groundAtom (__d, M.Minus, S, mS, ((p + 1), occ)))
      | (__d, mode, App (__u, S), Mapp (_, mS), (p, occ)) ->
          groundAtom (__d, mode, S, mS, ((p + 1), occ))
    let rec ctxPush (m, __Ds) = List.map (function | __d -> I.Decl (__d, m)) __Ds
    let rec ctxPop (__Ds) = List.map (function | Decl (__d, m) -> __d) __Ds
    let rec checkD1 =
      function
      | (__d, Pi ((Dec (name, _), I.Maybe), __v), occ, k) ->
          checkD1
            ((I.Decl (__d, (Existential (Free, name)))), __v, (P.body occ),
              (function | Decl (__d', m) -> ctxPush (m, (k __d'))))
      | (__d, Pi ((Dec (name, V1), I.No), V2), occ, k) ->
          checkD1
            ((I.Decl (__d, (Existential (Free, name)))), V2, (P.body occ),
              (function
               | Decl (__d', m) ->
                   ctxPush (m, (checkG1 (__d', V1, (P.label occ), k)))))
      | (__d, Root (Const a, S), occ, k) ->
          let rec checkAll =
            function
            | nil -> ()
            | mS::mSs ->
                let rec checkSome =
                  function
                  | (__d')::[] ->
                      (groundAtom (__d', M.Minus, S, mS, (1, occ));
                       checkAll mSs)
                  | (__d')::__Ds ->
                      ((try groundAtom (__d', M.Minus, S, mS, (1, occ)); ()
                        with | ModeError _ -> checkSome __Ds);
                       checkAll mSs) in
                checkSome (k (updateAtom (__d, M.Plus, S, a, mS, (1, occ)))) in
          checkAll (lookup (a, occ))
      | (__d, Root (Def d, S), occ, k) ->
          let rec checkAll =
            function
            | nil -> ()
            | mS::mSs ->
                let rec checkSome =
                  function
                  | (__d')::[] ->
                      (groundAtom (__d', M.Minus, S, mS, (1, occ));
                       checkAll mSs)
                  | (__d')::__Ds ->
                      ((try groundAtom (__d', M.Minus, S, mS, (1, occ)); ()
                        with | ModeError _ -> checkSome __Ds);
                       checkAll mSs) in
                checkSome (k (updateAtom (__d, M.Plus, S, d, mS, (1, occ)))) in
          checkAll (lookup (d, occ))
    let rec checkG1 =
      function
      | (__d, Pi ((_, I.Maybe), __v), occ, k) ->
          ctxPop
            (checkG1
               ((I.Decl (__d, Universal)), __v, (P.body occ),
                 (function | Decl (__d', m) -> ctxPush (m, (k __d')))))
      | (__d, Pi ((Dec (_, V1), I.No), V2), occ, k) ->
          ctxPop
            (checkD1 (__d, V1, (P.label occ), (function | __d' -> [__d']));
             checkG1
               ((I.Decl (__d, Universal)), V2, (P.body occ),
                 (function | Decl (__d', m) -> ctxPush (m, (k __d')))))
      | (__d, Root (Const a, S), occ, k) ->
          let rec checkList arg__0 arg__1 =
            match (arg__0, arg__1) with
            | (found, nil) -> nil
            | (false__, mS::[]) ->
                (match groundAtom (__d, M.Plus, S, mS, (1, occ)) with
                 | Unique -> k (updateAtom (__d, M.Minus1, S, a, mS, (1, occ)))
                 | Ambig -> k (updateAtom (__d, M.Minus, S, a, mS, (1, occ))))
            | (found, mS::mSs) ->
                let found' =
                  try groundAtom (__d, M.Plus, S, mS, (1, occ)); true__
                  with | ModeError _ -> false__ in
                let __Ds' = checkList (found || found') mSs in
                if found'
                then (k (updateAtom (__d, M.Minus, S, a, mS, (1, occ)))) @ __Ds'
                else __Ds' in
          checkList false__ (lookup (a, occ))
      | (__d, Root (Def d, S), occ, k) ->
          let rec checkList arg__0 arg__1 =
            match (arg__0, arg__1) with
            | (found, nil) -> nil
            | (false__, mS::[]) ->
                (match groundAtom (__d, M.Plus, S, mS, (1, occ)) with
                 | Unique -> k (updateAtom (__d, M.Minus1, S, d, mS, (1, occ)))
                 | Ambig -> k (updateAtom (__d, M.Minus, S, d, mS, (1, occ))))
            | (found, mS::mSs) ->
                let found' =
                  try groundAtom (__d, M.Plus, S, mS, (1, occ)); true__
                  with | ModeError _ -> false__ in
                let __Ds' = checkList (found || found') mSs in
                if found'
                then (k (updateAtom (__d, M.Minus, S, d, mS, (1, occ)))) @ __Ds'
                else __Ds' in
          checkList false__ (lookup (d, occ))
    let rec checkDlocal (__d, __v, occ) =
      try checkD1 (__d, __v, occ, (function | __d' -> [__d']))
      with | ModeError (occ, msg) -> raise (Error' (occ, msg))
    let rec cidFromHead = function | Const a -> a | Def a -> a
    let rec checkD (conDec, fileName, occOpt) =
      let _ = checkFree := false__ in
      let rec checkable =
        function
        | Root (Ha, _) ->
            (match ModeTable.mmodeLookup (cidFromHead Ha) with
             | nil -> false__
             | _ -> true__)
        | Uni _ -> false__
        | Pi (_, __v) -> checkable __v in
      let __v = I.conDecType conDec in
      if checkable __v
      then
        try checkDlocal (I.Null, __v, P.top)
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
    (* Uniqueness information *)
    (* u ::= Unique           *)
    (*     | Ambig            *)
    (* Groundedness information   *)
    (* I ::= Free                 *)
    (*     | Unknown              *)
    (*     | Ground               *)
    (* Variable status             *)
    (* S ::= Existential (I, xOpt) *)
    (*     | Universal             *)
    (* hack: if true, check freeness of output arguments in subgoals *)
    (* Representation invariant:

       Groundness information:
       T stands for ground, B stands for unknown
       Ex  for a named existential variable
       Par for a parameter

       Mode context   __d ::= . | __d, S

       If __d contains Status information for variables in
       a context __g, we write __g ~ __d
       We write __d' >= __d if for all i
         __d(i) par iff __d'(i) par
         __d(i) bot implies __d'(i) bot or __d'(i) top
         __d(i) top implies __d'(i) top
    *)
    (* copied from worldcheck/worldsyn.fun *)
    (* lookup (a, occ) = mSs

       Invariant: mS are the argument modes for a
       Raises an error if no mode for a has declared.
       (occ is used in error message)
    *)
    (* nameOf S, selects a name for S *)
    (* unique (k, ks) = B

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
    (* etaContract (__u, n) = k

       if lam V1... lam Vn. __u =eta*=> k
       otherwise raise exception Eta

       Invariant: __g, V1,..., Vn |- __u : __v for some __g, Vi, V.
                  __u in NF
    *)
    (* etaSpine (S, n) = ()
       if S =eta*=> n ; n-1 ; ... ; 1 ; Nil
       otherwise raise exception Eta

       Invariant: __g |- S : V1 >> V2 for some __g, V1, V2
                  S in NF
    *)
    (* S[s] should be impossible *)
    (* isPattern (__d, k, mS) = B

       Invariant:
       B iff k > k' for all k' in mS
         and for all k in mS: k is parameter
         and for all k', k'' in mS: k' <> k''
    *)
    (* ------------------------------------------- strictness check *)
    (* This repeats some code from ../typecheck/strict.fun *)
    (* Interface here is somewhat different *)
    (* strictExpN (__d, p, __u) = B

       Invariant:
       If  __d |- __u : __v
       and __u is in nf (normal form)
       then B iff __u is strict in p
    *)
    (* checking __d in this case should be redundant -fp *)
    (* strictDecN (__d, p, __d) orelse *)
    (* equivalently: isUniversal .. andalso strictSpineN .. *)
    (* no other cases possible *)
    (* this is a hack - until we investigate this further   -rv *)
    (* no other cases possible *)
    (* strictSpineN (__d, S) = B

       Invariant:
       If  __d |- S : __v > W
       and S is in nf (normal form)
       then B iff S is strict in k
    *)
    (*
    fun strictAtom (__d, p, mode, I.Nil, (__v, s), M.Mnil) = false
      | strictAtom (__d, p, M.Minus, I.App (__u, S), (I.Pi ((I.Dec (_, V1), _), V2), s),
                     M.Mapp (M.Marg (M.Minus, _), mS)) =
          strictExpN (__d, p, Whnf.normalize (V1, s))
          orelse strictAtom (__d, p, M.Minus, S, Whnf.whnfExpandDef (V2, I.Dot (I.Exp __u, s)), mS)
      | strictAtom (__d, p, mode, I.App (__u, S), (I.Pi (_, V2), s), M.Mapp(_, mS)) =
          strictAtom (__d, p, mode, S, Whnf.whnfExpandDef (V2, I.Dot (I.Exp __u, s)), mS)
    *)
    (* ------------------------------------------- freeness check *)
    (* freeExpN (__d, mode, __u, occ = ()

       If __g |- __u : __v  (__u in nf)
       and __g ~ __d
       then freeExpN terminates with () if __d |- __u free
       else exception ModeError is raised

       (occ and mode are used in error messages)
    *)
    (* punting on the occ here  - ak *)
    (* freeSpineN (__d, mode, S, occ, strictFun)  = ()

       If   __g |- S : V1  > V2   (S in nf)
       and  __g ~ __d
       then freeSpineN terminates with () if  __d |- S free
       else exception ModeError is raised

       (occ and mode are used in error messages)
    *)
    (* freeVar (__d, mode, k, occ, strictFun)  = ()

       If   __g |- k : V1
       and  __g ~ __d
       then freeVar terminates with () if  __d |- S free
       else exception ModeError is raised

       (occ and mode are used in error messages)
    *)
    (* -------------------------------- non-strict mode context update *)
    (* nonStrictExpN (__d, __u) = __d'

       If   __g |- __u : __v     (__u in nf)
       and  __d ~ __g
       then __d' >= __d where __d'(k) Unknown for all existential variables k
            in __u that are free in __d
    *)
    (* nonStrictSpineN (__d, S) = __d'

       If   __g |- S : V1 > V2      (S in nf)
       and  __d ~ __g
       then __d' >= __d' where __d'(k) Unkown for all existential variables k
            in S that are Free in __d
    *)
    (* nonStrictVarD (__d, k) = __d'

       If   __g |- k : __v
       and  __d ~ __g
       and  k is an existential variable
       then __d' >= __d where k is nonStrictd as described in  nonStrictExpN
    *)
    (* Universal, or already Unknown or Ground - leave unchanged *)
    (* ------------------------------------------- mode context update *)
    (* updateExpN (__d, __u, u) = __d'

       If   __g |- __u : __v     (__u in nf)
       and  __d ~ __g
       then __d' >= __d where __d'(k) Ground for all existential variables k
            with a strict occurrence in __u
            and __d'(k) Unkown for all existential variable k
            with a non-strict occurrence, but no strict occurrence in __u
            (if !checkFree is true)

       u is the uniqueness property for the new ground assumptions
    *)
    (* no occurrence inside a FgnExp is considered strict *)
    (* updateSpineN (__d, S, u) = __d'

       If   __g |- S : V1 > V2      (S in nf)
       and  __d ~ __g
       then __d' >= __d' where __d'(k) Ground for all existential variables k
            with a strict occurrence in S
    *)
    (* updateVarD (__d, k, u) = __d'

       If   __g |- k : __v
       and  __d ~ __g
       and  k is an existential variable
       then __d' >= __d where k is updated as described in  updateExpN
    *)
    (* ----------------------- mode context update by argument modes *)
    (* updateAtom (__d, m, S, mS, (p,occ)) = __d'

       If   __g |- S : __v > __v'   ( S = __U1 ; .. ; Un)
       and  __d ~ __g
       and  S ~ mS            (mS = m1 , .. , mn)
       and  m mode
       then __d' >= __d where
            all Ui are updated if mi = m (mod uniqueness)

       The new ground variables are marked Unique
         if m = (-1) and mi = (-1) (when updating from subgoals with unique inputs)
         or m = mi = (+) (when updating from the clause head)
       Otherwise they are marked Ambig.

       (p,occ) is used in error message if freeness is to be checked
    *)
    (* when checking freeness, all arguments must be input (+) or output (-) *)
    (* therefore, no case for M.Mapp (M.Marg (M.Minus, _), mS) is provided here *)
    (* freeAtom (__d, m, S, (__v,s), mS, (p, occ)) = ()

       checks if all output arguments in S according to mS are free.
       Invariant: __g |- S : __v[s] >> P for some __g and P  (S in nf)
                  __g ~ __d
                  mode = (-) or (+); ( * ) or (-1) are excluded
    *)
    (* updateAtom (__d, m, S, a, mS, (p, occ))
       see updateAtom', and performs additional freeness check if required
    *)
    (* ------------------------------------------- groundness check *)
    (* groundExpN (__d, mode, __u, occ)  = u

       If   __g |- __u : __v    (__u in nf)
       and  __g ~ __d
       then if mode = (+) or (-)
            then groundExpN terminates with u if  __d |- __u ground
                 else exception ModeError is raised
            if mode = (-1) then __d |- __u ground and __u unique
                           else exception ModeError is raised

       u = Unique if all known variables in __u are Unique
       u = Ambig otherwise

       (occ and mode are used in error messages)
    *)
    (* punting on occ here  - ak *)
    (* groundSpineN (__d, mode, S, occ)  = u

       If   __g |- S : V1  > V2   (S in nf)
       and  __g ~ __d
       then if mode = (+) or (-)
            then groundSpineN terminates with u if  __d |- S ground
                 else exception ModeError is raised
            if mode = (-1) then __d |- S ground and S unique
                           else exception ModeError is raised

       u = Unique if all known variables in S are Unique
       u = Ambig otherwise

       (occ and mode are used in error messages)
    *)
    (* groundVar (__d, mode, k, occ)  = u

       If   __g |- k : V1
       and  __g ~ __d
       then if mode = (+) or (-)
            then groundVar terminates with u if  __d |- k ground
                 else exception ModeError is raised
            if mode = (-1) then __d |- k ground and k unique
                           else exception ModeError is raised

       u = Unique if k is known to be unique, Ambig otherwise

       (occ and mode are used in error messages)
    *)
    (* Existential (Free, _) or Existential (Unknown, _) *)
    (* ------------------------------------------- groundness check by polarity *)
    (* groundAtom (__d, m, S, mS, (p,occ))  = u

       If   __g |- S : __v > __v'   ( S = __U1 ; .. ; Un)
       and  __d ~ __g
       and  S ~ mS            (mS = m1 , .. , mn)
       and  m mode = (+) or (-1)
       then groundAtom returns u if  __d |- Ui ground
            for all i s.t. mi = m (mod uniqueness)
            and checks that __d |- Ui unique if mi = (-1) and m = (-)
       otherwise exception ModeError is raised

       u = Unique if all mi = m (mod uniqueness) are unique,
       u = Ambig otherwise

       ((p,occ) used in error messages)
    *)
    (* ignore uniqueness result here *)
    (* ignore uniqueness result here *)
    (* ------------------------------------------- mode checking first phase *)
    (* ctxPush (__Ds, m) = __Ds'
       raises the contexts __Ds prepending m
    *)
    (* ctxPop __Ds = __Ds'
       lowers the contexts __Ds
    *)
    (* checkD1 (__d, __v, occ, k) = ()

       Invariant:
         if __g |- __v : __l
         and  __v does not contain Skolem constants
         and  __d ~ __g
         then
            for each  mode mS of the head of __v
              exists  some Di s.t. all (-) evars of mS are ground
                where  __d' ~ __g, __d' >= __d is obtained by updating __d
                  and  k __d' = [D1, ..., Di, ..., Dn]
                  and  Di ~ __g, Di >= __d' is obtained by mode checking on the subgoals of __v

       exception ModeError is raised if the expression does not mode check
       exception Error' is raised if the expression contains type families
       that have no mode information associated with them
       (occ used in error messages)
    *)
    (* for a declaration, all modes must be satisfied *)
    (* __d' is the only (last) possibility; on failure, we raise ModeError *)
    (* ignore return *)
    (* try __d', if it doesn't work, try another context in the __Ds *)
    (* ignore return *)
    (* for a declaration, all modes must be satisfied *)
    (* __d' is the only (last) possibility; on failure, we raise ModeError *)
    (* ignore return *)
    (* try __d', if it doesn't work, try another context in the __Ds *)
    (* ignore return *)
    (* checkG1 (__d, __v, occ, k) = __Ds

       Invariant:
         if __g |- __v : __l
         and  __v does not contain Skolem constants
         and  __d ~ __g
         then forall __d' >= __d that mode checks __v, (k __d') is a sublist of __Ds
         and for each Di in __Ds, Di ~ __g and Di >= __d'

       exception ModeError is raised if the expression does not mode check
       exception Error' is raised if the expression contains type families
       that have no mode information associated with them
       (occ used in error messages)
     *)
    (* for a goal, at least one mode must be satisfied *)
    (* found = true *)
    (* mS is the last possible mode to check;
                    if the check fails, we don't catch ModeError *)
    (* uniqueness not permitted on multiple modes right now *)
    (* Wed Aug 20 21:52:31 2003 -fp *)
    (* found' is true iff __d satisfies mS *)
    (* handler scope??? -fp *)
    (* compute all other mode contexts *)
    (* for a goal, at least one mode must be satisfied *)
    (* found = true *)
    (* mS is the last possible mode to check;
                    if the check fails, we don't catch ModeError *)
    (* uniqueness not permitted on multiple modes right now *)
    (* Wed Aug 20 21:52:31 2003 -fp *)
    (* found' is true iff __d satisfies mS *)
    (* compute all other mode contexts *)
    (* checkDlocal (__d, __v, occ) = ()

       Invariant:
       If   __g |- __v : __l
       and  __d ~ __g
       then checkD terminates with ()  iff __v is mode correct.

       otherwise exception ModeError is raised (occ used in error messages)
    *)
    (* --------------------------------------------------------- mode checking *)
    (* checkD (ConDec, occOpt)  = ()

       checkD terminates with () if ConDec is mode correct
       otherwise exception Error is raised

       (occOpt is used in error messages)
    *)
    let checkD = checkD
    let checkMode = checkMode
    let checkFreeOut = checkFreeOut
  end ;;
