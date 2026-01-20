
module type STYLECHECK  =
  sig
    exception Error of string 
    val check : unit -> unit
    val checkConDec : IntSyn.cid -> unit
  end;;




module StyleCheck(StyleCheck:sig
                               module Whnf : WHNF
                               module Index : INDEX
                               module Origins : ORIGINS
                             end) : STYLECHECK =
  struct
    exception Error of string 
    module I = IntSyn
    module P = Paths
    type polarity =
      | Plus 
      | Minus 
    type info =
      | Correct 
      | Incorrect of (string list * string) 
    let rec toggle = function | Plus -> Minus | Minus -> Plus
    let rec wrapMsg c occ msg err =
      match Origins.originLookup c with
      | (fileName, NONE) -> (fileName ^ ":") ^ msg
      | (fileName, Some occDec) ->
          P.wrapLoc'
            ((P.Loc (fileName, (err occDec occ))),
              (Origins.linesInfoLookup fileName), msg)
    let rec denumber =
      function
      | [] -> []
      | c::l ->
          let x = ord c in
          let l' = denumber l in
          if ((x >= 65) && (x <= 90)) || ((x >= 97) && (x <= 122))
          then c :: l'
          else l'
    let rec options =
      function | n::nil -> n | n::l -> (n ^ ", ") ^ (options l)
    let rec error c prefNames n occ err =
      [wrapMsg
         (c, occ,
           (((((^) "Variable naming: expected " options prefNames) ^
                " found ")
               ^ n)
              ^ "\n")) err]
    let rec checkVariablename n prefNames =
      if
        List.exists
          (fun n' -> (=) (denumber (explode n)) denumber (explode n'))
          prefNames
      then Correct
      else Incorrect (prefNames, n)
    let rec checkVar __0__ __1__ =
      match (__0__, __1__) with
      | (Dec (Some n, __V), pol) ->
          (match Names.getNamePref (I.targetFam __V) with
           | NONE -> Correct
           | Some (prefENames, prefUNames) ->
               (match pol with
                | Plus -> checkVariablename (n, prefENames)
                | Minus -> checkVariablename (n, prefUNames)))
      | (Dec (NONE, __V), pol) -> Correct
    let rec implicitHead =
      function
      | BVar k -> 0
      | Const c -> I.constImp c
      | Skonst k -> 0
      | Def d -> I.constImp d
      | NSDef d -> I.constImp d
      | FgnConst _ -> 0
    let rec checkExp __2__ __3__ __4__ __5__ __6__ =
      match (__2__, __3__, __4__, __5__, __6__) with
      | (c, (__G, __P), Uni _, occ, err) -> []
      | (c, (__G, __P), Lam (__D, __U), occ, err) ->
          checkDec c ((__G, __P), __D, Minus, occ) err
            (fun (__G', __P') ->
               fun (__L') ->
                 (@) __L' checkExp c ((__G', __P'), __U, (P.body occ)) err)
      | (c, (__G, __P), Root (__H, __S), occ, err) ->
          (@) (checkHead c ((__G, __P), __H, (P.head occ)) err) checkSpine c
            ((__G, __P), 1, (implicitHead __H), __S, (P.body occ)) err
      | (c, (__G, __P), FgnExp (_, _), occ, err) -> []
    let rec checkType __7__ __8__ __9__ __10__ __11__ __12__ =
      match (__7__, __8__, __9__, __10__, __11__, __12__) with
      | (c, (__G, __P), Uni _, pol, occ, err) -> []
      | (c, (__G, __P), Pi ((__D, I.Maybe), __V), pol, occ, err) ->
          checkDec c ((__G, __P), __D, pol, occ) err
            (fun (__G', __P') ->
               fun (__L') ->
                 (@) __L' checkType c ((__G', __P'), __V, pol, (P.body occ))
                   err)
      | (c, (__G, __P), Pi ((__D, I.No), __V), pol, occ, err) ->
          checkDec c ((__G, __P), __D, pol, occ) err
            (fun (__G', __P') ->
               fun (__L') ->
                 (@) __L' checkType c ((__G', __P'), __V, pol, (P.body occ))
                   err)
      | (c, (__G, __P), Root (__H, __S), pol, occ, err) ->
          (@) (checkHead c ((__G, __P), __H, (P.head occ)) err) checkSpine c
            ((__G, __P), 1, (implicitHead __H), __S, (P.body occ)) err
      | (c, (__G, __P), FgnExp (_, _), pol, occ, err) -> []
    let rec checkDecImp (__G, __P) (Dec (_, __V) as D) pol k =
      let __I = checkVar (__D, pol) in
      k (((I.Decl (__G, __D)), (I.Decl (__P, __I))), [])
    let rec checkDec c (__G, __P) (Dec (_, __V) as D) pol occ err k =
      let __I = checkVar (__D, pol) in
      let __E1 =
        match __I with
        | Correct -> []
        | Incorrect (prefNames, n) -> error c (prefNames, n, occ) err in
      let __E2 =
        checkType c ((__G, __P), __V, (toggle pol), (P.label occ)) err in
      k (((I.Decl (__G, __D)), (I.Decl (__P, __I))), (__E1 @ __E2))
    let rec checkHead __13__ __14__ __15__ __16__ __17__ =
      match (__13__, __14__, __15__, __16__, __17__) with
      | (c, (__G, __P), BVar k, occ, err) ->
          (match I.ctxLookup (__P, k) with
           | Correct -> []
           | Incorrect (prefNames, n) -> error c (prefNames, n, occ) err)
      | (c, (__G, __P), Const _, occ, err) -> []
      | (c, (__G, __P), Skonst k, occ, err) -> []
      | (c, (__G, __P), Def d, occ, err) -> []
      | (c, (__G, __P), NSDef d, occ, err) -> []
      | (c, (__G, __P), FgnConst _, occ, err) -> []
    let rec checkSpine __18__ __19__ __20__ __21__ __22__ __23__ __24__ =
      match (__18__, __19__, __20__, __21__, __22__, __23__, __24__) with
      | (c, (__G, __P), n, 0, I.Nil, occ, err) -> []
      | (c, (__G, __P), n, 0, App (__U, __S), occ, err) ->
          (@) (checkExp c ((__G, __P), __U, (P.arg (n, occ))) err) checkSpine
            c ((__G, __P), (n + 1), 0, __S, occ) err
      | (c, (__G, __P), n, i, App (__U, __S), occ, err) ->
          checkSpine c ((__G, __P), (n + 1), (i - 1), __S, occ) err
    let rec checkType' __25__ __26__ __27__ __28__ __29__ __30__ =
      match (__25__, __26__, __27__, __28__, __29__, __30__) with
      | (c, (__G, __P), 0, __V, occ, err) ->
          checkType c ((__G, __P), __V, Plus, occ) err
      | (c, (__G, __P), n, Pi ((__D, I.Maybe), __V), occ, err) ->
          checkDecImp ((__G, __P), __D, Plus)
            (fun (__G', __P') ->
               fun (__L') ->
                 (@) __L' checkType' c
                   ((__G', __P'), (n - 1), __V, (P.body occ)) err)
    let rec checkExp' __31__ __32__ __33__ __34__ __35__ =
      match (__31__, __32__, __33__, __34__, __35__) with
      | (c, (__G, __P), Lam (__D, __U), occ, err) ->
          checkDec c ((__G, __P), __D, Plus, occ) err
            (fun (__G', __P') ->
               fun (__L') ->
                 (@) __L' checkExp' c ((__G', __P'), __U, (P.body occ)) err)
      | (c, (__G, __P), __U, occ, err) ->
          checkExp c ((__G, __P), __U, occ) err
    let rec checkDef __36__ __37__ __38__ __39__ __40__ __41__ =
      match (__36__, __37__, __38__, __39__, __40__, __41__) with
      | (c, (__G, __P), 0, __U, occ, err) ->
          checkExp' c ((__G, __P), __U, occ) err
      | (c, (__G, __P), n, Lam (__D, __U), occ, err) ->
          checkDecImp ((__G, __P), __D, Plus)
            (fun (__G', __P') ->
               fun (__L') ->
                 (@) __L' checkDef c
                   ((__G', __P'), (n - 1), __U, (P.body occ)) err)
    let rec checkConDec __42__ __43__ =
      match (__42__, __43__) with
      | (c, ConDec (_, _, implicit, _, __U, _)) ->
          (if (!Global.chatter) > 3
           then print ((Names.qidToString (Names.constQid c)) ^ " ")
           else ();
           checkType' c ((I.Null, I.Null), implicit, __U, P.top)
             P.occToRegionDec)
      | (c, ConDef (_, _, implicit, __U, __V, I.Type, _)) ->
          (if (!Global.chatter) > 3
           then print ((Names.qidToString (Names.constQid c)) ^ " ")
           else ();
           (@) (checkType' c ((I.Null, I.Null), implicit, __V, P.top)
                  P.occToRegionDef2)
             checkDef c ((I.Null, I.Null), implicit, __U, P.top)
             P.occToRegionDef1)
      | (c, AbbrevDef (_, _, implicit, __U, __V, I.Type)) ->
          (if (!Global.chatter) > 3
           then print ((Names.qidToString (Names.constQid c)) ^ " ")
           else ();
           checkType' c ((I.Null, I.Null), implicit, __V, P.top)
             P.occToRegionDef2;
           checkDef c ((I.Null, I.Null), implicit, __U, P.top)
             P.occToRegionDef1)
      | (c, _) -> [](* type level abbreviations ? *)
      (* type level definitions ? *)
    let rec checkAll c n =
      if c <= n
      then (@) (checkConDec c (I.sgnLookup c)) checkAll ((c + 1), n)
      else []
    let rec check () =
      let (n, _) = I.sgnSize () in map print (checkAll (0, n)); ()
    let checkConDec c = map print (checkConDec c (I.sgnLookup c)); ()
    let check = check
  end ;;




module StyleCheck =
  (Make_StyleCheck)(struct
                      module Whnf = Whnf
                      module Index = Index
                      module Origins = Origins
                    end);;
