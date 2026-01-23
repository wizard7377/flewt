module type MODECHECK  =
  sig
    exception Error of string 
    val checkD : (IntSyn.conDec_ * string * Paths.occConDec option) -> unit
    val checkMode : (IntSyn.cid * ModeSyn.modeSpine_) -> unit
    val checkFreeOut : (IntSyn.cid * ModeSyn.modeSpine_) -> unit
  end


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
    type uniqueness_ =
      | Unique 
      | Ambig 
    type info_ =
      | Free 
      | Unknown 
      | Ground of uniqueness_ 
    type status_ =
      | Existential of (info_ * string option) 
      | Universal 
    let checkFree = ref false
    let rec wrapMsg (c, occ, msg) =
      begin match Origins.originLookup c with
      | (fileName, None) -> (fileName ^ ":") ^ msg
      | (fileName, Some occDec) ->
          P.wrapLoc'
            ((P.Loc (fileName, (P.occToRegionClause occDec occ))),
              (Origins.linesInfoLookup fileName),
              ((((^) "Constant " Names.qidToString (Names.constQid c)) ^ "\n")
                 ^ msg)) end
    let rec wrapMsg' (fileName, r, msg) =
      P.wrapLoc ((P.Loc (fileName, r)), msg)
    exception ModeError of (P.occ * string) 
    exception Error' of (P.occ * string) 
    let rec lookup (a, occ) =
      begin match ModeTable.mmodeLookup a with
      | [] ->
          raise
            (Error'
               (occ,
                 ((^) "No mode declaration for " I.conDecName (I.sgnLookup a))))
      | sMs -> sMs end
  let rec nameOf =
    begin function
    | Existential (_, None) -> "?"
    | Existential (_, Some name) -> name
    | _ -> "?" end
let rec unique =
  begin function
  | (k, []) -> true
  | (k, k'::ks) -> (k <> k') && (unique (k, ks)) end
let rec isUniversal = begin function | Universal -> true | _ -> false end
let rec isGround =
  begin function | Existential (Ground _, _) -> true | _ -> false end
let rec uniqueness =
  begin function | Existential (Ground u, _) -> u | Universal -> Unique end
let rec ambiguate =
  begin function
  | M.Plus -> M.Plus
  | M.Minus -> M.Minus
  | M.Minus1 -> M.Minus end
let rec andUnique =
  begin function | (Unique, Unique) -> Unique | _ -> Ambig end
let rec isFree =
  begin function | Existential (Free, _) -> true | _ -> false end
exception Eta 
let rec etaContract =
  begin function
  | (Root (BVar k, s_), n) ->
      if k > n then begin (begin etaSpine (s_, n); k - n end) end
  else begin raise Eta end | (Lam (d_, u_), n) -> etaContract (u_, (n + 1))
| _ -> raise Eta end
let rec etaSpine =
  begin function
  | (I.Nil, 0) -> ()
  | (App (u_, s_), n) ->
      if (etaContract (u_, 0)) = n then begin etaSpine (s_, (n - 1)) end
      else begin raise Eta end end
let rec checkPattern =
  begin function
  | (d_, k, args, I.Nil) -> ()
  | (d_, k, args, App (u_, s_)) ->
      let k' = etaContract (u_, 0) in
      if
        (k > k') &&
          ((isUniversal (I.ctxLookup (d_, k'))) && (unique (k', args)))
      then begin checkPattern (d_, k, (k' :: args), s_) end
        else begin raise Eta end end
let rec isPattern (d_, k, s_) =
  begin try begin checkPattern (d_, k, [], s_); true end with | Eta -> false end
let rec strictExpN =
  begin function
  | (d_, _, Uni _) -> false
  | (d_, p, Lam (_, u_)) ->
      strictExpN ((I.Decl (d_, Universal)), (p + 1), u_)
  | (d_, p, Pi ((d'_, _), u_)) ->
      (strictDecN (d_, p, d'_)) ||
        (strictExpN ((I.Decl (d_, Universal)), (p + 1), u_))
  | (d_, p, Root (h_, s_)) ->
      (((begin match h_ with
         | BVar k' -> if k' = p then begin isPattern (d_, k', s_) end
             else begin
               if isUniversal (I.ctxLookup (d_, k'))
               then begin strictSpineN (d_, p, s_) end else begin false end end
  | Const c -> strictSpineN (d_, p, s_) | Def d -> strictSpineN (d_, p, s_)
  | FgnConst (cs, conDec) -> strictSpineN (d_, p, s_) end))
(* equivalently: isUniversal .. andalso strictSpineN .. *))
| (d_, p, FgnExp (cs, ops)) -> false end(* no other cases possible *)
(* strictDecN (D, p, D) orelse *)(* checking D in this case should be redundant -fp *)
let rec strictSpineN =
  begin function
  | (_, _, I.Nil) -> false
  | (d_, p, App (u_, s_)) ->
      (strictExpN (d_, p, u_)) || (strictSpineN (d_, p, s_)) end
let rec strictDecN (d_, p, Dec (_, v_)) = strictExpN (d_, p, v_)
let rec freeExpN =
  begin function
  | (d_, d, mode, Root (BVar k, s_), occ, strictFun) ->
      (begin freeVar (d_, d, mode, k, (P.head occ), strictFun);
       freeSpineN (d_, d, mode, s_, (1, occ), strictFun) end)
  | (d_, d, mode, Root (Const _, s_), occ, strictFun) ->
      freeSpineN (d_, d, mode, s_, (1, occ), strictFun)
  | (d_, d, mode, Root (Def _, s_), occ, strictFun) ->
      freeSpineN (d_, d, mode, s_, (1, occ), strictFun)
  | (d_, d, mode, Root (FgnConst (cs, conDec), s_), occ, strictFun) ->
      freeSpineN (d_, d, mode, s_, (1, occ), strictFun)
  | (d_, d, mode, Lam (_, u_), occ, strictFun) ->
      freeExpN
        ((I.Decl (d_, Universal)), (d + 1), mode, u_, (P.body occ),
          strictFun)
  | (d_, d, mode, FgnExp csfe, occ, strictFun) ->
      I.FgnExpStd.App.apply csfe
        (begin function
         | u_ ->
             freeExpN
               (d_, d, mode, (Whnf.normalize (u_, I.id)), occ, strictFun) end) end
let rec freeSpineN =
  begin function
  | (d_, d, mode, I.Nil, _, strictFun) -> ()
  | (d_, d, mode, App (u_, s_), (p, occ), strictFun) ->
      (begin freeExpN (d_, d, mode, u_, (P.arg (p, occ)), strictFun);
       freeSpineN (d_, d, mode, s_, ((p + 1), occ), strictFun) end) end
let rec freeVar (d_, d, mode, k, occ, strictFun) =
  let status = I.ctxLookup (d_, k) in
  if (isFree status) || ((isUniversal status) || (strictFun (k - d)))
  then begin () end
    else begin
      raise
        (ModeError
           (occ,
             (((("Occurrence of variable " ^ (nameOf status)) ^ " in ") ^
                 (M.modeToString mode))
                ^ " argument not free"))) end
let rec nonStrictExpN =
  begin function
  | (d_, Root (BVar k, s_)) -> nonStrictSpineN ((nonStrictVarD (d_, k)), s_)
  | (d_, Root (Const c, s_)) -> nonStrictSpineN (d_, s_)
  | (d_, Root (Def d, s_)) -> nonStrictSpineN (d_, s_)
  | (d_, Root (FgnConst (cs, conDec), s_)) -> nonStrictSpineN (d_, s_)
  | (d_, Lam (_, u_)) ->
      I.ctxPop (nonStrictExpN ((I.Decl (d_, Universal)), u_))
  | (d_, FgnExp _) ->
      raise
        (Error "Foreign expressions not permitted when checking freeness") end
let rec nonStrictSpineN =
  begin function
  | (d_, I.Nil) -> d_
  | (d_, App (u_, s_)) -> nonStrictSpineN ((nonStrictExpN (d_, u_)), s_) end
let rec nonStrictVarD =
  begin function
  | (Decl (d_, Existential (Free, name)), 1) ->
      I.Decl (d_, (Existential (Unknown, name)))
  | (d_, 1) -> d_
  | (Decl (d_, status), k) -> I.Decl ((nonStrictVarD (d_, (k - 1))), status) end
(* Universal, or already Unknown or Ground - leave unchanged *)
let rec updateExpN =
  begin function
  | (d_, Root (BVar k, s_), u) ->
      if isUniversal (I.ctxLookup (d_, k))
      then begin updateSpineN (d_, s_, u) end
      else begin
        if isPattern (d_, k, s_) then begin updateVarD (d_, k, u) end
        else begin
          if !checkFree
          then begin nonStrictSpineN ((nonStrictVarD (d_, k)), s_) end
          else begin d_ end end end
| (d_, Root (Const c, s_), u) -> updateSpineN (d_, s_, u)
| (d_, Root (Def d, s_), u) -> updateSpineN (d_, s_, u)
| (d_, Root (FgnConst (cs, conDec), s_), u) -> updateSpineN (d_, s_, u)
| (d_, Lam (_, u_), u) ->
    I.ctxPop (updateExpN ((I.Decl (d_, Universal)), u_, u))
| (d_, FgnExp _, u) -> d_ end(* no occurrence inside a FgnExp is considered strict *)
let rec updateSpineN =
  begin function
  | (d_, I.Nil, u) -> d_
  | (d_, App (u_, s_), u) -> updateSpineN ((updateExpN (d_, u_, u)), s_, u) end
let rec updateVarD =
  begin function
  | (Decl (d_, Existential (_, name)), 1, u) ->
      I.Decl (d_, (Existential ((Ground u), name)))
  | (Decl (d_, status), k, u) ->
      I.Decl ((updateVarD (d_, (k - 1), u)), status) end
let rec updateAtom' =
  begin function
  | (d_, mode, I.Nil, M.Mnil, _) -> d_
  | (d_, M.Plus, App (u_, s_), Mapp (Marg (M.Plus, _), mS), (p, occ)) ->
      updateAtom'
        ((updateExpN (d_, u_, Unique)), M.Plus, s_, mS, ((p + 1), occ))
  | (d_, M.Minus, App (u_, s_), Mapp (Marg (M.Minus, _), mS), (p, occ)) ->
      updateAtom'
        ((updateExpN (d_, u_, Ambig)), M.Minus, s_, mS, ((p + 1), occ))
  | (d_, M.Minus, App (u_, s_), Mapp (Marg (M.Minus1, _), mS), (p, occ)) ->
      updateAtom'
        ((updateExpN (d_, u_, Ambig)), M.Minus, s_, mS, ((p + 1), occ))
  | (d_, M.Minus1, App (u_, s_), Mapp (Marg (M.Minus, _), mS), (p, occ)) ->
      updateAtom'
        ((updateExpN (d_, u_, Ambig)), M.Minus1, s_, mS, ((p + 1), occ))
  | (d_, M.Minus1, App (u_, s_), Mapp (Marg (M.Minus1, _), mS), (p, occ)) ->
      updateAtom'
        ((updateExpN (d_, u_, Unique)), M.Minus1, s_, mS, ((p + 1), occ))
  | (d_, mode, App (u_, s_), Mapp (_, mS), (p, occ)) ->
      updateAtom' (d_, mode, s_, mS, ((p + 1), occ)) end(* therefore, no case for M.Mapp (M.Marg (M.Minus, _), mS) is provided here *)
(* when checking freeness, all arguments must be input (+) or output (-) *)
let rec freeAtom =
  begin function
  | (d_, mode, I.Nil, vs_, M.Mnil, _) -> ()
  | (d_, M.Minus, App (u_, s_), (Pi ((Dec (_, v1_), _), v2_), s), Mapp
     (Marg (M.Minus, _), mS), (p, occ)) ->
      (begin freeExpN
               (d_, 0, M.Minus, u_, (P.arg (p, occ)),
                 (begin function
                  | q -> strictExpN (d_, q, (Whnf.normalize (v1_, s))) end));
      freeAtom
        (d_, M.Minus, s_,
          (Whnf.whnfExpandDef (v2_, (I.Dot ((I.Exp u_), s)))), mS,
          ((p + 1), occ)) end)
  | (d_, mode, App (u_, s_), (Pi (_, v2_), s), Mapp (_, mS), (p, occ)) ->
      freeAtom
        (d_, mode, s_, (Whnf.whnfExpandDef (v2_, (I.Dot ((I.Exp u_), s)))),
          mS, ((p + 1), occ)) end
let rec updateAtom (d_, mode, s_, a, mS, (p, occ)) =
  let _ =
    if !checkFree
    then
      begin freeAtom
              (d_, (ambiguate mode), s_, ((I.constType a), I.id), mS,
                (p, occ)) end
    else begin () end in
updateAtom' (d_, mode, s_, mS, (p, occ))
let rec groundExpN =
  begin function
  | (d_, mode, Root (BVar k, s_), occ) ->
      andUnique
        ((groundVar (d_, mode, k, (P.head occ))),
          (groundSpineN (d_, mode, s_, (1, occ))))
  | (d_, mode, Root (Const c, s_), occ) ->
      groundSpineN (d_, mode, s_, (1, occ))
  | (d_, mode, Root (Def d, s_), occ) ->
      groundSpineN (d_, mode, s_, (1, occ))
  | (d_, mode, Root (FgnConst (cs, conDec), s_), occ) ->
      groundSpineN (d_, mode, s_, (1, occ))
  | (d_, mode, Lam (_, u_), occ) ->
      groundExpN ((I.Decl (d_, Universal)), mode, u_, (P.body occ))
  | (d_, mode, FgnExp csfe, occ) ->
      I.FgnExpStd.fold csfe
        (begin function
         | (u_, u) ->
             andUnique
               ((groundExpN (d_, mode, (Whnf.normalize (u_, I.id)), occ)), u) end)
      Unique end
let rec groundSpineN =
  begin function
  | (d_, mode, I.Nil, _) -> Unique
  | (d_, mode, App (u_, s_), (p, occ)) ->
      andUnique
        ((groundExpN (d_, mode, u_, (P.arg (p, occ)))),
          (groundSpineN (d_, mode, s_, ((p + 1), occ)))) end
let rec groundVar =
  begin function
  | (d_, M.Minus1, k, occ) ->
      (((begin match I.ctxLookup (d_, k) with
         | Existential (Ground (Unique), _) -> Unique
         | Universal -> Unique
         | Existential (Ground (Ambig), x) as s ->
             raise
               (ModeError
                  (occ,
                    (((^) (((^) "Occurrence of variable " nameOf s) ^ " in ")
                        M.modeToString M.Minus1)
                       ^ " argument not necessarily unique")))
         | s ->
             raise
               (ModeError
                  (occ,
                    (((("Occurrence of variable " ^ (nameOf s)) ^ " in ") ^
                        (M.modeToString M.Minus1))
                       ^ " argument not necessarily ground"))) end))
  (* Existential (Free, _) or Existential (Unknown, _) *))
  | (d_, mode, k, occ) ->
      let status = I.ctxLookup (d_, k) in
      if (isGround status) || (isUniversal status)
      then begin uniqueness status end
        else begin
          raise
            (ModeError
               (occ,
                 (((("Occurrence of variable " ^ (nameOf status)) ^ " in ") ^
                     (M.modeToString mode))
                    ^ " argument not necessarily ground"))) end end
let rec groundAtom =
  begin function
  | (d_, _, I.Nil, M.Mnil, _) -> Unique
  | (d_, M.Plus, App (u_, s_), Mapp (Marg (M.Plus, _), mS), (p, occ)) ->
      andUnique
        ((groundExpN (d_, M.Plus, u_, (P.arg (p, occ)))),
          (groundAtom (d_, M.Plus, s_, mS, ((p + 1), occ))))
  | (d_, M.Minus, App (u_, s_), Mapp (Marg (M.Minus, _), mS), (p, occ)) ->
      (((begin groundExpN (d_, M.Minus, u_, (P.arg (p, occ)));
         groundAtom (d_, M.Minus, s_, mS, ((p + 1), occ)) end))
  (* ignore uniqueness result here *))
  | (d_, M.Minus, App (u_, s_), Mapp (Marg (M.Minus1, _), mS), (p, occ)) ->
      (((begin groundExpN (d_, M.Minus1, u_, (P.arg (p, occ)));
         groundAtom (d_, M.Minus, s_, mS, ((p + 1), occ)) end))
  (* ignore uniqueness result here *))
  | (d_, mode, App (u_, s_), Mapp (_, mS), (p, occ)) ->
      groundAtom (d_, mode, s_, mS, ((p + 1), occ)) end
let rec ctxPush (m, ds_) =
  List.map (begin function | d_ -> I.Decl (d_, m) end) ds_
let rec ctxPop (ds_) = List.map (begin function | Decl (d_, m) -> d_ end) ds_
let rec checkD1 =
  begin function
  | (d_, Pi ((Dec (name, _), I.Maybe), v_), occ, k) ->
      checkD1
        ((I.Decl (d_, (Existential (Free, name)))), v_, (P.body occ),
          (begin function | Decl (d'_, m) -> ctxPush (m, (k d'_)) end))
  | (d_, Pi ((Dec (name, v1_), I.No), v2_), occ, k) ->
      checkD1
        ((I.Decl (d_, (Existential (Free, name)))), v2_, (P.body occ),
          (begin function
           | Decl (d'_, m) ->
               ctxPush (m, (checkG1 (d'_, v1_, (P.label occ), k))) end))
  | (d_, Root (Const a, s_), occ, k) ->
      let rec checkAll =
        begin function
        | [] -> ()
        | mS::mSs ->
            let rec checkSome =
              begin function
              | (d'_)::[] ->
                  (((begin groundAtom (d'_, M.Minus, s_, mS, (1, occ));
                     checkAll mSs end))
              (* ignore return *))
              | (d'_)::ds_ ->
                  (begin (((begin try
                                    begin groundAtom
                                            (d'_, M.Minus, s_, mS, (1, occ));
                                    () end
                   with | ModeError _ -> checkSome ds_ end))
              (* ignore return *)); checkAll mSs end) end
      (* try D', if it doesn't work, try another context in the Ds *)
      (* D' is the only (last) possibility; on failure, we raise ModeError *) in
    checkSome (k (updateAtom (d_, M.Plus, s_, a, mS, (1, occ)))) end in
((checkAll (lookup (a, occ)))
(* for a declaration, all modes must be satisfied *))
| (d_, Root (Def d, s_), occ, k) ->
    let rec checkAll =
      begin function
      | [] -> ()
      | mS::mSs ->
          let rec checkSome =
            begin function
            | (d'_)::[] ->
                (((begin groundAtom (d'_, M.Minus, s_, mS, (1, occ));
                   checkAll mSs end))
            (* ignore return *))
            | (d'_)::ds_ ->
                (begin (((begin try
                                  begin groundAtom
                                          (d'_, M.Minus, s_, mS, (1, occ));
                                  () end
                 with | ModeError _ -> checkSome ds_ end))
            (* ignore return *)); checkAll mSs end) end
    (* try D', if it doesn't work, try another context in the Ds *)
    (* D' is the only (last) possibility; on failure, we raise ModeError *) in
  checkSome (k (updateAtom (d_, M.Plus, s_, d, mS, (1, occ)))) end in
((checkAll (lookup (d, occ)))
(* for a declaration, all modes must be satisfied *)) end
let rec checkG1 =
  begin function
  | (d_, Pi ((_, I.Maybe), v_), occ, k) ->
      ctxPop
        (checkG1
           ((I.Decl (d_, Universal)), v_, (P.body occ),
             (begin function | Decl (d'_, m) -> ctxPush (m, (k d'_)) end)))
  | (d_, Pi ((Dec (_, v1_), I.No), v2_), occ, k) ->
      ctxPop
        (begin checkD1
                 (d_, v1_, (P.label occ), (begin function | d'_ -> [d'_] end));
        checkG1
          ((I.Decl (d_, Universal)), v2_, (P.body occ),
            (begin function | Decl (d'_, m) -> ctxPush (m, (k d'_)) end)) end)
| (d_, Root (Const a, s_), occ, k) ->
    let rec checkList arg__0 arg__1 =
      begin match (arg__0, arg__1) with
      | (found, []) -> []
      | (false, mS::[]) ->
          (begin match groundAtom (d_, M.Plus, s_, mS, (1, occ)) with
           | Unique -> k (updateAtom (d_, M.Minus1, s_, a, mS, (1, occ)))
           | Ambig -> k (updateAtom (d_, M.Minus, s_, a, mS, (1, occ))) end)
      | (found, mS::mSs) ->
          let found' =
            ((begin try
                      begin groundAtom (d_, M.Plus, s_, mS, (1, occ)); true end
            with | ModeError _ -> false end)
          (* handler scope??? -fp *)) in
    let ds'_ = checkList (found || found') mSs in
    ((if found'
      then begin (k (updateAtom (d_, M.Minus, s_, a, mS, (1, occ)))) @ ds'_ end
      else begin ds'_ end)
      (* found' is true iff D satisfies mS *)(* compute all other mode contexts *)) end
(* Wed Aug 20 21:52:31 2003 -fp *)(* uniqueness not permitted on multiple modes right now *)
(* mS is the last possible mode to check;
                    if the check fails, we don't catch ModeError *)
(* found = true *) in ((checkList false (lookup (a, occ)))
(* for a goal, at least one mode must be satisfied *))
| (d_, Root (Def d, s_), occ, k) ->
    let rec checkList arg__2 arg__3 =
      begin match (arg__2, arg__3) with
      | (found, []) -> []
      | (false, mS::[]) ->
          (begin match groundAtom (d_, M.Plus, s_, mS, (1, occ)) with
           | Unique -> k (updateAtom (d_, M.Minus1, s_, d, mS, (1, occ)))
           | Ambig -> k (updateAtom (d_, M.Minus, s_, d, mS, (1, occ))) end)
      | (found, mS::mSs) ->
          let found' =
            begin try
                    begin groundAtom (d_, M.Plus, s_, mS, (1, occ)); true end
            with | ModeError _ -> false end in
    let ds'_ = checkList (found || found') mSs in
    ((if found'
      then begin (k (updateAtom (d_, M.Minus, s_, d, mS, (1, occ)))) @ ds'_ end
      else begin ds'_ end)
      (* found' is true iff D satisfies mS *)(* compute all other mode contexts *)) end
(* Wed Aug 20 21:52:31 2003 -fp *)(* uniqueness not permitted on multiple modes right now *)
(* mS is the last possible mode to check;
                    if the check fails, we don't catch ModeError *)
(* found = true *) in ((checkList false (lookup (d, occ)))
(* for a goal, at least one mode must be satisfied *)) end
let rec checkDlocal (d_, v_, occ) =
  begin try checkD1 (d_, v_, occ, (begin function | d'_ -> [d'_] end))
  with | ModeError (occ, msg) -> raise (Error' (occ, msg)) end
let rec cidFromHead = begin function | Const a -> a | Def a -> a end
let rec checkD (conDec, fileName, occOpt) =
  let _ = checkFree := false in
  let rec checkable =
    begin function
    | Root (Ha, _) ->
        (begin match ModeTable.mmodeLookup (cidFromHead Ha) with
         | [] -> false
         | _ -> true end)
    | Uni _ -> false | Pi (_, v_) -> checkable v_ end in
let v_ = I.conDecType conDec in
if checkable v_
then
  begin begin try checkDlocal (I.Null, v_, P.top)
        with
        | Error' (occ, msg) ->
            (begin match occOpt with
             | None -> raise (Error msg)
             | Some occTree ->
                 raise
                   (Error
                      (wrapMsg'
                         (fileName, (P.occToRegionClause occTree occ), msg))) end) end end
  else begin () end
let rec checkAll =
  begin function
  | [] -> ()
  | (Const c)::clist ->
      (begin if !Global.chatter > 3
             then begin print ((Names.qidToString (Names.constQid c)) ^ " ") end
       else begin () end;
  (begin try checkDlocal (I.Null, (I.constType c), P.top)
   with | Error' (occ, msg) -> raise (Error (wrapMsg (c, occ, msg))) end);
  checkAll clist end)
| (Def d)::clist ->
    (begin if !Global.chatter > 3
           then begin print ((Names.qidToString (Names.constQid d)) ^ " ") end
     else begin () end;
(begin try checkDlocal (I.Null, (I.constType d), P.top)
 with | Error' (occ, msg) -> raise (Error (wrapMsg (d, occ, msg))) end);
checkAll clist end) end
let rec checkMode (a, ms) =
  let _ =
    if !Global.chatter > 3
    then
      begin print
              (((^) "Mode checking family " Names.qidToString
                  (Names.constQid a))
                 ^ ":\n") end
    else begin () end in
let clist = Index.lookup a in
let _ = checkFree := false in
let _ = checkAll clist in
let _ = if !Global.chatter > 3 then begin print "\n" end else begin () end in
()
let rec checkFreeOut (a, ms) =
  let _ =
    if !Global.chatter > 3
    then
      begin print
              (((^) "Checking output freeness of " Names.qidToString
                  (Names.constQid a))
                 ^ ":\n") end
    else begin () end in
let clist = Index.lookup a in
let _ = checkFree := true in
let _ = checkAll clist in
let _ = if !Global.chatter > 3 then begin print "\n" end else begin () end in
()
let checkD = checkD
let checkMode = checkMode
let checkFreeOut = checkFreeOut end
