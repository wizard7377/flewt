
(* Style Checking *)
(* Author: Carsten Schuermann *)
module type STYLECHECK  =
  sig
    exception Error of string 
    val check : unit -> unit
    (* raises Error (msg) *)
    val checkConDec : IntSyn.cid -> unit
  end;;




(* Style Checking *)
(* Author: Carsten Schuermann *)
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
    let rec wrapMsg (c, occ, msg) err =
      match Origins.originLookup c with
      | (fileName, None) -> (fileName ^ ":") ^ msg
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
      | (Dec (Some n, __v), pol) ->
          (match Names.getNamePref (I.targetFam __v) with
           | None -> Correct
           | Some (prefENames, prefUNames) ->
               (match pol with
                | Plus -> checkVariablename (n, prefENames)
                | Minus -> checkVariablename (n, prefUNames)))
      | (Dec (None, __v), pol) -> Correct
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
      | (c, ((__g, P), Uni _, occ), err) -> []
      | (c, ((__g, P), Lam (__d, __u), occ), err) ->
          checkDec c ((__g, P), __d, Minus, occ) err
            (function
             | ((__g', __P'), __l') ->
                 (@) __l' checkExp c ((__g', __P'), __u, (P.body occ)) err)
      | (c, ((__g, P), Root (H, S), occ), err) ->
          (@) (checkHead c ((__g, P), H, (P.head occ)) err) checkSpine c
            ((__g, P), 1, (implicitHead H), S, (P.body occ)) err
      | (c, ((__g, P), FgnExp (_, _), occ), err) -> []
    let rec checkType arg__0 arg__1 arg__2 =
      match (arg__0, arg__1, arg__2) with
      | (c, ((__g, P), Uni _, pol, occ), err) -> []
      | (c, ((__g, P), Pi ((__d, I.Maybe), __v), pol, occ), err) ->
          checkDec c ((__g, P), __d, pol, occ) err
            (function
             | ((__g', __P'), __l') ->
                 (@) __l' checkType c ((__g', __P'), __v, pol, (P.body occ)) err)
      | (c, ((__g, P), Pi ((__d, I.No), __v), pol, occ), err) ->
          checkDec c ((__g, P), __d, pol, occ) err
            (function
             | ((__g', __P'), __l') ->
                 (@) __l' checkType c ((__g', __P'), __v, pol, (P.body occ)) err)
      | (c, ((__g, P), Root (H, S), pol, occ), err) ->
          (@) (checkHead c ((__g, P), H, (P.head occ)) err) checkSpine c
            ((__g, P), 1, (implicitHead H), S, (P.body occ)) err
      | (c, ((__g, P), FgnExp (_, _), pol, occ), err) -> []
    let rec checkDecImp ((__g, P), (Dec (_, __v) as __d), pol) k =
      let I = checkVar (__d, pol) in k (((I.Decl (__g, __d)), (I.Decl (P, I))), [])
    let rec checkDec c ((__g, P), (Dec (_, __v) as __d), pol, occ) err k =
      let I = checkVar (__d, pol) in
      let E1 =
        match I with
        | Correct -> []
        | Incorrect (prefNames, n) -> error c (prefNames, n, occ) err in
      let E2 = checkType c ((__g, P), __v, (toggle pol), (P.label occ)) err in
      k (((I.Decl (__g, __d)), (I.Decl (P, I))), (E1 @ E2))
    let rec checkHead arg__0 arg__1 arg__2 =
      match (arg__0, arg__1, arg__2) with
      | (c, ((__g, P), BVar k, occ), err) ->
          (match I.ctxLookup (P, k) with
           | Correct -> []
           | Incorrect (prefNames, n) -> error c (prefNames, n, occ) err)
      | (c, ((__g, P), Const _, occ), err) -> []
      | (c, ((__g, P), Skonst k, occ), err) -> []
      | (c, ((__g, P), Def d, occ), err) -> []
      | (c, ((__g, P), NSDef d, occ), err) -> []
      | (c, ((__g, P), FgnConst _, occ), err) -> []
    let rec checkSpine arg__0 arg__1 arg__2 =
      match (arg__0, arg__1, arg__2) with
      | (c, ((__g, P), n, 0, I.Nil, occ), err) -> []
      | (c, ((__g, P), n, 0, App (__u, S), occ), err) ->
          (@) (checkExp c ((__g, P), __u, (P.arg (n, occ))) err) checkSpine c
            ((__g, P), (n + 1), 0, S, occ) err
      | (c, ((__g, P), n, i, App (__u, S), occ), err) ->
          checkSpine c ((__g, P), (n + 1), (i - 1), S, occ) err
    let rec checkType' arg__0 arg__1 arg__2 =
      match (arg__0, arg__1, arg__2) with
      | (c, ((__g, P), 0, __v, occ), err) ->
          checkType c ((__g, P), __v, Plus, occ) err
      | (c, ((__g, P), n, Pi ((__d, I.Maybe), __v), occ), err) ->
          checkDecImp ((__g, P), __d, Plus)
            (function
             | ((__g', __P'), __l') ->
                 (@) __l' checkType' c ((__g', __P'), (n - 1), __v, (P.body occ)) err)
    let rec checkExp' arg__0 arg__1 arg__2 =
      match (arg__0, arg__1, arg__2) with
      | (c, ((__g, P), Lam (__d, __u), occ), err) ->
          checkDec c ((__g, P), __d, Plus, occ) err
            (function
             | ((__g', __P'), __l') ->
                 (@) __l' checkExp' c ((__g', __P'), __u, (P.body occ)) err)
      | (c, ((__g, P), __u, occ), err) -> checkExp c ((__g, P), __u, occ) err
    let rec checkDef arg__0 arg__1 arg__2 =
      match (arg__0, arg__1, arg__2) with
      | (c, ((__g, P), 0, __u, occ), err) -> checkExp' c ((__g, P), __u, occ) err
      | (c, ((__g, P), n, Lam (__d, __u), occ), err) ->
          checkDecImp ((__g, P), __d, Plus)
            (function
             | ((__g', __P'), __l') ->
                 (@) __l' checkDef c ((__g', __P'), (n - 1), __u, (P.body occ)) err)
    let rec checkConDec arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (c, ConDec (_, _, implicit, _, __u, _)) ->
          (if (!Global.chatter) > 3
           then print ((Names.qidToString (Names.constQid c)) ^ " ")
           else ();
           checkType' c ((I.Null, I.Null), implicit, __u, P.top)
             P.occToRegionDec)
      | (c, ConDef (_, _, implicit, __u, __v, I.Type, _)) ->
          (if (!Global.chatter) > 3
           then print ((Names.qidToString (Names.constQid c)) ^ " ")
           else ();
           (@) (checkType' c ((I.Null, I.Null), implicit, __v, P.top)
                  P.occToRegionDef2)
             checkDef c ((I.Null, I.Null), implicit, __u, P.top)
             P.occToRegionDef1)
      | (c, AbbrevDef (_, _, implicit, __u, __v, I.Type)) ->
          (if (!Global.chatter) > 3
           then print ((Names.qidToString (Names.constQid c)) ^ " ")
           else ();
           checkType' c ((I.Null, I.Null), implicit, __v, P.top)
             P.occToRegionDef2;
           checkDef c ((I.Null, I.Null), implicit, __u, P.top)
             P.occToRegionDef1)
      | (c, _) -> []
    let rec checkAll (c, n) =
      if c <= n
      then (@) (checkConDec c (I.sgnLookup c)) checkAll ((c + 1), n)
      else []
    let rec check () =
      let (n, _) = I.sgnSize () in map print (checkAll (0, n)); ()
    (* indicates positivity *)
    (* distinguishes style correct
                                           from - incorrect declarations *)
    (* wrapMsg (c, occ, msg) err = s

       Invariant:
       Let c be a cid
       occ by an occurrence,
       msg an error message,
       and err a function that computes adequate region information for c
       then s is msg wrapped with location information
    *)
    (* denumber __l = __l'

       Invariant:
       __l' = __l without digits
    *)
    (* checkVariblename (n, prefNames) = I

       Invariant:
       If n occurs in prefNames then I = Correct otherwise Incorrect
    *)
    (* checkVar (__d, pol) = I

       Invariant:
       If  __d's name corresponds to the name choice for pol,
       then I is Correct else Incorrect
    *)
    (* implicitHead H = k

       Invariant:
       k = # implicit arguments associated with H
    *)
    (* checkExp c ((__g, P), __u, occ) err = __l

       Invariant:
       Let   c be a cid
       and   |- __g ctx
       and   |- P info for __g
       and   __g |- __u : __v
       and   occ an occurrence to the current location
       and   err an function mapping occ to regions
       then  __l is a list of strings (error messages) computed from __u
    *)
    (* checkType c ((__g, P), __v, pol, occ) err = __l

       Invariant:
       Let   c be a cid
       and   |- __g ctx
       and   |- P info for __g
       and   __g |-pol  __v : type
       and   occ an occurrence to the current location
       and   err an function mapping occ to regions
       then  __l is a list of strings (error messages) computed from __v
    *)
    (* checkDecImp c ((__g, P), __d, pol) k = __l

       Invariant:
       Let   c be a cid
       and   |- __g ctx
       and   |- P info for __g
       and   __g |-pol  __d declation
       and   k a continuation, that expects the extended context (__g', __P')
             and a list of already computed error messages __l' as argument.
       then  __l is a list of strings (error messages) computed __d
       ( checkDecImp does not generate any error messages for __d since omitted)
    *)
    (* checkDec c ((__g, P), __d, pol, occ) err k = __l

       Invariant:
       Let   c be a cid
       and   |- __g ctx
       and   |- P info for __g
       and   __g |-pol  __d declation
       and   occ occurrence, err wrapper function
       and   k a continuation, that expects the extended context (__g', __P')
             and a list of already computed error messages __l' as argument.
       then  __l is a list of strings (error messages) computed from __d
    *)
    (* checkHead c ((__g, P), H, occ) err = __l

       Invariant:
       Let   c be a cid
       and   |- __g ctx
       and   |- P info for __g
       and   __g |-  H head
       and   occ occurrence, err wrapper function
       then  __l is a list of at most one string (error message) computed from H
    *)
    (* checkSpine c ((__g, P), S, n, i, occ) err = __l

       Invariant:
       Let   c be a cid
       and   |- __g ctx
       and   |- P info for __g
       and   __g |- S : V1 >> V2  for V1 V2, valid types
       and   n a running number of arguments considered
       and   i the number of remaining implicit arguments
       and   occ occurrence, err wrapper function
       then  __l is a list of  strings (error messages) computed from S
    *)
    (* checkType' c ((__g, P), n, __v, occ) err = __l

       Invariant:
       Let   c be a cid
       and   |- __g ctx
       and   |- P info for __g
       and   n a decreasing number of implicit arguments
       and   __g |- __v : type
       and   occ occurrence, err wrapper function
       then  __l is a list of  strings (error messages) computed from __v
       (omitted arguments generate error message where they are used not declared)
    *)
    (* checkExp' c ((__g, P), __u, occ) err = __l

       Invariant:
       Let   c be a cid
       and   |- __g ctx
       and   |- P info for __g
       and   __g |- __u : __v for some type __v, body of a definition
       and   occ occurrence, err wrapper function
       then  __l is a list of  strings (error messages) computed from __u
       (top level negative occurrences exception.  Treated as pos occurrences)
    *)
    (* checkDef c ((__g, P), n, __u, occ) err = __l

       Invariant:
       Let   c be a cid
       and   |- __g ctx
       and   |- P info for __g
       and   n a decreasing number of implicit arguments
       and   __g |- __u : __v for some type __v, body of a definition
       and   occ occurrence, err wrapper function
       then  __l is a list of strings (error messages) computed from __u
       (top level negative occurrences exception.  Treated as pos occurrences)
    *)
    (* checkConDec c C = __l

       Invariant:
       Let   c be a cid
       and   . |- C : __v for some type __v, constant declaration
       then  __l is a list of  strings (error messages) computed from C
    *)
    (* type level definitions ? *)
    (* type level abbreviations ? *)
    (* in all other cases *)
    (* checkAll (c, n) = __l

       Invariant:
       Let   c be a cid
       and   n the max. number of cids
       then  __l is a list of  strings (error messages) computed from the signature c<=n
    *)
    (* checkAll () = __l

       Invariant:
       __l is a list of  strings (error messages) computed from the entire Twelf signature
    *)
    let checkConDec =
      function | c -> (map print (checkConDec c (I.sgnLookup c)); ())
    let check = check
  end ;;




module StyleCheck =
  (Make_StyleCheck)(struct
                      module Whnf = Whnf
                      module Index = Index
                      module Origins = Origins
                    end);;
