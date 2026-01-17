
module type STYLECHECK  =
  sig
    exception Error of
      ((string)(* Author: Carsten Schuermann *)(* Style Checking *))
      
    val check : unit -> unit
    val checkConDec :
      IntSyn.cid -> ((unit)(* raises Error (msg) *))
  end;;




module StyleCheck(StyleCheck:sig
                               module Whnf : WHNF
                               module Index : INDEX
                               module Origins :
                               ((ORIGINS)(* Style Checking *)(* Author: Carsten Schuermann *))
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
    let rec wrapMsg (c, occ, msg) err =
      match Origins.originLookup c with
      | (fileName, NONE) -> (fileName ^ ":") ^ msg
      | (fileName, SOME occDec) ->
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
    let rec error c (prefNames, n, occ) err =
      [wrapMsg
         (c, occ,
           (((((^) "Variable naming: expected " options prefNames) ^
                " found ")
               ^ n)
              ^ "\n")) err]
    let rec checkVariablename (n, prefNames) =
      if
        List.exists
          (function | n' -> (=) (denumber (explode n)) denumber (explode n'))
          prefNames
      then Correct
      else Incorrect (prefNames, n)
    let rec checkVar =
      function
      | (Dec (SOME n, V), pol) ->
          (match Names.getNamePref (I.targetFam V) with
           | NONE -> Correct
           | SOME (prefENames, prefUNames) ->
               (match pol with
                | Plus -> checkVariablename (n, prefENames)
                | Minus -> checkVariablename (n, prefUNames)))
      | (Dec (NONE, V), pol) -> Correct
    let rec implicitHead =
      function
      | BVar k -> 0
      | Const c -> I.constImp c
      | Skonst k -> 0
      | Def d -> I.constImp d
      | NSDef d -> I.constImp d
      | FgnConst _ -> 0
    let rec checkExp arg__0 arg__1 arg__2 =
      match (arg__0, arg__1, arg__2) with
      | (c, ((G, P), Uni _, occ), err) -> []
      | (c, ((G, P), Lam (D, U), occ), err) ->
          checkDec c ((G, P), D, Minus, occ) err
            (function
             | ((G', P'), L') ->
                 (@) L' checkExp c ((G', P'), U, (P.body occ)) err)
      | (c, ((G, P), Root (H, S), occ), err) ->
          (@) (checkHead c ((G, P), H, (P.head occ)) err) checkSpine c
            ((G, P), 1, (implicitHead H), S, (P.body occ)) err
      | (c, ((G, P), FgnExp (_, _), occ), err) -> []
    let rec checkType arg__0 arg__1 arg__2 =
      match (arg__0, arg__1, arg__2) with
      | (c, ((G, P), Uni _, pol, occ), err) -> []
      | (c, ((G, P), Pi ((D, I.Maybe), V), pol, occ), err) ->
          checkDec c ((G, P), D, pol, occ) err
            (function
             | ((G', P'), L') ->
                 (@) L' checkType c ((G', P'), V, pol, (P.body occ)) err)
      | (c, ((G, P), Pi ((D, I.No), V), pol, occ), err) ->
          checkDec c ((G, P), D, pol, occ) err
            (function
             | ((G', P'), L') ->
                 (@) L' checkType c ((G', P'), V, pol, (P.body occ)) err)
      | (c, ((G, P), Root (H, S), pol, occ), err) ->
          (@) (checkHead c ((G, P), H, (P.head occ)) err) checkSpine c
            ((G, P), 1, (implicitHead H), S, (P.body occ)) err
      | (c, ((G, P), FgnExp (_, _), pol, occ), err) -> []
    let rec checkDecImp ((G, P), (Dec (_, V) as D), pol) k =
      let I = checkVar (D, pol) in k (((I.Decl (G, D)), (I.Decl (P, I))), [])
    let rec checkDec c ((G, P), (Dec (_, V) as D), pol, occ) err k =
      let I = checkVar (D, pol) in
      let E1 =
        match I with
        | Correct -> []
        | Incorrect (prefNames, n) -> error c (prefNames, n, occ) err in
      let E2 = checkType c ((G, P), V, (toggle pol), (P.label occ)) err in
      k (((I.Decl (G, D)), (I.Decl (P, I))), (E1 @ E2))
    let rec checkHead arg__0 arg__1 arg__2 =
      match (arg__0, arg__1, arg__2) with
      | (c, ((G, P), BVar k, occ), err) ->
          (match I.ctxLookup (P, k) with
           | Correct -> []
           | Incorrect (prefNames, n) -> error c (prefNames, n, occ) err)
      | (c, ((G, P), Const _, occ), err) -> []
      | (c, ((G, P), Skonst k, occ), err) -> []
      | (c, ((G, P), Def d, occ), err) -> []
      | (c, ((G, P), NSDef d, occ), err) -> []
      | (c, ((G, P), FgnConst _, occ), err) -> []
    let rec checkSpine arg__0 arg__1 arg__2 =
      match (arg__0, arg__1, arg__2) with
      | (c, ((G, P), n, 0, I.Nil, occ), err) -> []
      | (c, ((G, P), n, 0, App (U, S), occ), err) ->
          (@) (checkExp c ((G, P), U, (P.arg (n, occ))) err) checkSpine c
            ((G, P), (n + 1), 0, S, occ) err
      | (c, ((G, P), n, i, App (U, S), occ), err) ->
          checkSpine c ((G, P), (n + 1), (i - 1), S, occ) err
    let rec checkType' arg__0 arg__1 arg__2 =
      match (arg__0, arg__1, arg__2) with
      | (c, ((G, P), 0, V, occ), err) ->
          checkType c ((G, P), V, Plus, occ) err
      | (c, ((G, P), n, Pi ((D, I.Maybe), V), occ), err) ->
          checkDecImp ((G, P), D, Plus)
            (function
             | ((G', P'), L') ->
                 (@) L' checkType' c ((G', P'), (n - 1), V, (P.body occ)) err)
    let rec checkExp' arg__0 arg__1 arg__2 =
      match (arg__0, arg__1, arg__2) with
      | (c, ((G, P), Lam (D, U), occ), err) ->
          checkDec c ((G, P), D, Plus, occ) err
            (function
             | ((G', P'), L') ->
                 (@) L' checkExp' c ((G', P'), U, (P.body occ)) err)
      | (c, ((G, P), U, occ), err) -> checkExp c ((G, P), U, occ) err
    let rec checkDef arg__0 arg__1 arg__2 =
      match (arg__0, arg__1, arg__2) with
      | (c, ((G, P), 0, U, occ), err) -> checkExp' c ((G, P), U, occ) err
      | (c, ((G, P), n, Lam (D, U), occ), err) ->
          checkDecImp ((G, P), D, Plus)
            (function
             | ((G', P'), L') ->
                 (@) L' checkDef c ((G', P'), (n - 1), U, (P.body occ)) err)
    let rec checkConDec arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (c, ConDec (_, _, implicit, _, U, _)) ->
          (if (!Global.chatter) > 3
           then print ((Names.qidToString (Names.constQid c)) ^ " ")
           else ();
           checkType' c ((I.Null, I.Null), implicit, U, P.top)
             P.occToRegionDec)
      | (c, ConDef (_, _, implicit, U, V, I.Type, _)) ->
          (if (!Global.chatter) > 3
           then print ((Names.qidToString (Names.constQid c)) ^ " ")
           else ();
           (@) (checkType' c ((I.Null, I.Null), implicit, V, P.top)
                  P.occToRegionDef2)
             checkDef c ((I.Null, I.Null), implicit, U, P.top)
             P.occToRegionDef1)
      | (c, AbbrevDef (_, _, implicit, U, V, I.Type)) ->
          (if (!Global.chatter) > 3
           then print ((Names.qidToString (Names.constQid c)) ^ " ")
           else ();
           checkType' c ((I.Null, I.Null), implicit, V, P.top)
             P.occToRegionDef2;
           checkDef c ((I.Null, I.Null), implicit, U, P.top)
             P.occToRegionDef1)
      | (c, _) -> []
    let rec checkAll (c, n) =
      if c <= n
      then (@) (checkConDec c (I.sgnLookup c)) checkAll ((c + 1), n)
      else []
    let rec check () =
      let (n, _) = I.sgnSize () in map print (checkAll (0, n)); ()
    let ((checkConDec)(* indicates positivity *)(* distinguishes style correct
                                           from - incorrect declarations *)
      (* wrapMsg (c, occ, msg) err = s

       Invariant:
       Let c be a cid
       occ by an occurrence,
       msg an error message,
       and err a function that computes adequate region information for c
       then s is msg wrapped with location information
    *)
      (* denumber L = L'

       Invariant:
       L' = L without digits
    *)
      (* checkVariblename (n, prefNames) = I

       Invariant:
       If n occurs in prefNames then I = Correct otherwise Incorrect
    *)
      (* checkVar (D, pol) = I

       Invariant:
       If  D's name corresponds to the name choice for pol,
       then I is Correct else Incorrect
    *)
      (* implicitHead H = k

       Invariant:
       k = # implicit arguments associated with H
    *)
      (* checkExp c ((G, P), U, occ) err = L

       Invariant:
       Let   c be a cid
       and   |- G ctx
       and   |- P info for G
       and   G |- U : V
       and   occ an occurrence to the current location
       and   err an function mapping occ to regions
       then  L is a list of strings (error messages) computed from U
    *)
      (* checkType c ((G, P), V, pol, occ) err = L

       Invariant:
       Let   c be a cid
       and   |- G ctx
       and   |- P info for G
       and   G |-pol  V : type
       and   occ an occurrence to the current location
       and   err an function mapping occ to regions
       then  L is a list of strings (error messages) computed from V
    *)
      (* checkDecImp c ((G, P), D, pol) k = L

       Invariant:
       Let   c be a cid
       and   |- G ctx
       and   |- P info for G
       and   G |-pol  D declation
       and   k a continuation, that expects the extended context (G', P')
             and a list of already computed error messages L' as argument.
       then  L is a list of strings (error messages) computed D
       ( checkDecImp does not generate any error messages for D since omitted)
    *)
      (* checkDec c ((G, P), D, pol, occ) err k = L

       Invariant:
       Let   c be a cid
       and   |- G ctx
       and   |- P info for G
       and   G |-pol  D declation
       and   occ occurrence, err wrapper function
       and   k a continuation, that expects the extended context (G', P')
             and a list of already computed error messages L' as argument.
       then  L is a list of strings (error messages) computed from D
    *)
      (* checkHead c ((G, P), H, occ) err = L

       Invariant:
       Let   c be a cid
       and   |- G ctx
       and   |- P info for G
       and   G |-  H head
       and   occ occurrence, err wrapper function
       then  L is a list of at most one string (error message) computed from H
    *)
      (* checkSpine c ((G, P), S, n, i, occ) err = L

       Invariant:
       Let   c be a cid
       and   |- G ctx
       and   |- P info for G
       and   G |- S : V1 >> V2  for V1 V2, valid types
       and   n a running number of arguments considered
       and   i the number of remaining implicit arguments
       and   occ occurrence, err wrapper function
       then  L is a list of  strings (error messages) computed from S
    *)
      (* checkType' c ((G, P), n, V, occ) err = L

       Invariant:
       Let   c be a cid
       and   |- G ctx
       and   |- P info for G
       and   n a decreasing number of implicit arguments
       and   G |- V : type
       and   occ occurrence, err wrapper function
       then  L is a list of  strings (error messages) computed from V
       (omitted arguments generate error message where they are used not declared)
    *)
      (* checkExp' c ((G, P), U, occ) err = L

       Invariant:
       Let   c be a cid
       and   |- G ctx
       and   |- P info for G
       and   G |- U : V for some type V, body of a definition
       and   occ occurrence, err wrapper function
       then  L is a list of  strings (error messages) computed from U
       (top level negative occurrences exception.  Treated as pos occurrences)
    *)
      (* checkDef c ((G, P), n, U, occ) err = L

       Invariant:
       Let   c be a cid
       and   |- G ctx
       and   |- P info for G
       and   n a decreasing number of implicit arguments
       and   G |- U : V for some type V, body of a definition
       and   occ occurrence, err wrapper function
       then  L is a list of strings (error messages) computed from U
       (top level negative occurrences exception.  Treated as pos occurrences)
    *)
      (* checkConDec c C = L

       Invariant:
       Let   c be a cid
       and   . |- C : V for some type V, constant declaration
       then  L is a list of  strings (error messages) computed from C
    *)
      (* type level definitions ? *)(* type level abbreviations ? *)
      (* in all other cases *)(* checkAll (c, n) = L

       Invariant:
       Let   c be a cid
       and   n the max. number of cids
       then  L is a list of  strings (error messages) computed from the signature c<=n
    *)
      (* checkAll () = L

       Invariant:
       L is a list of  strings (error messages) computed from the entire Twelf signature
    *))
      = function | c -> (map print (checkConDec c (I.sgnLookup c)); ())
    let check = check
  end ;;




module StyleCheck =
  (Make_StyleCheck)(struct
                      module Whnf = Whnf
                      module Index = Index
                      module Origins = Origins
                    end);;
