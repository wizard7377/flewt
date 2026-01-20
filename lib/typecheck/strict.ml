
module type STRICT  =
  sig
    exception Error of string 
    val check :
      (IntSyn.__Exp * IntSyn.__Exp) -> Paths.occConDec option -> unit
    val checkType : (int * IntSyn.__Exp) -> Paths.occConDec option -> unit
  end;;




module Strict(Strict:sig module Whnf : WHNF end) : STRICT =
  struct
    exception Error of string 
    module I = IntSyn
    let rec patSpine __0__ __1__ =
      match (__0__, __1__) with
      | (_, I.Nil) -> true
      | (k, App (Root (BVar k', I.Nil), __S)) ->
          let rec indexDistinct =
            function
            | I.Nil -> true
            | App (Root (BVar k'', I.Nil), __S) ->
                (k' <> k'') && (indexDistinct __S)
            | _ -> false in
          (k' <= k) && ((patSpine (k, __S)) && (indexDistinct __S))
      | _ -> false(* possibly eta-contract? -fp *)
    let rec strictExp __2__ __3__ __4__ =
      match (__2__, __3__, __4__) with
      | (_, _, Uni _) -> false
      | (k, p, Lam (__D, __U)) ->
          (strictDec (k, p, __D)) || (strictExp ((k + 1), (p + 1), __U))
      | (k, p, Pi ((__D, _), __U)) ->
          (strictDec (k, p, __D)) || (strictExp ((k + 1), (p + 1), __U))
      | (k, p, Root (__H, __S)) ->
          (match __H with
           | BVar k' ->
               if k' = p
               then patSpine (k, __S)
               else if k' <= k then strictSpine (k, p, __S) else false
           | Const c -> strictSpine (k, p, __S)
           | Def d -> strictSpine (k, p, __S)
           | FgnConst (cs, conDec) -> strictSpine (k, p, __S))
      | (k, p, FgnExp (cs, ops)) -> false(* no other cases possible *)
      (* checking D in this case might be redundant -fp *)
    let rec strictSpine __5__ __6__ __7__ =
      match (__5__, __6__, __7__) with
      | (_, _, I.Nil) -> false
      | (k, p, App (__U, __S)) ->
          (strictExp (k, p, __U)) || (strictSpine (k, p, __S))
    let rec strictDec k p (Dec (_, __V)) = strictExp (k, p, __V)
    let rec strictArgParm __8__ __9__ =
      match (__8__, __9__) with
      | (p, (Root _ as U)) -> strictExp (0, p, __U)
      | (p, (Pi _ as U)) -> strictExp (0, p, __U)
      | (p, (FgnExp _ as U)) -> strictExp (0, p, __U)
      | (p, Lam (__D, __U)) -> strictArgParm ((p + 1), __U)
    let rec occToString __10__ __11__ =
      match (__10__, __11__) with
      | (Some ocd, occ) -> Paths.wrap ((Paths.occToRegionDef1 ocd occ), "")
      | (None, occ) -> "Error: "
    let rec decToVarName =
      function
      | Dec (None, _) -> "implicit variable"
      | Dec (Some x, _) -> "variable " ^ x
    let rec strictTop (__U, __V) ocdOpt =
      let rec strictArgParms __12__ __13__ __14__ =
        match (__12__, __13__, __14__) with
        | (Root (BVar _, _), _, occ) ->
            raise
              (Error
                 ((occToString (ocdOpt, occ)) ^ "Head not rigid, use %abbrev"))
        | (Root _, _, _) -> ()
        | (Pi _, _, _) -> ()
        | (FgnExp _, _, _) -> ()
        | (Lam (__D, __U'), Pi (_, __V'), occ) ->
            if strictArgParm (1, __U')
            then strictArgParms (__U', __V', (Paths.body occ))
            else
              raise
                (Error
                   (((^) ((occToString (ocdOpt, occ)) ^
                            "No strict occurrence of ")
                       decToVarName __D)
                      ^ ", use %abbrev"))
        | ((Lam _ as U), (Root (Def _, _) as V), occ) ->
            strictArgParms
              (__U, (Whnf.normalize (Whnf.expandDef (__V, I.id))), occ)
        (* Wed Aug 25 16:39:57 2004 -fp *)(* may not be sound in general *) in
      strictArgParms (__U, __V, Paths.top)
    let rec occursInType (i, __V) ocdOpt =
      let rec oit __15__ __16__ =
        match (__15__, __16__) with
        | ((0, __V), occ) -> ()
        | ((i, Pi ((__D, __P), __V)), occ) ->
            (match Abstract.piDepend ((__D, __P), __V) with
             | Pi ((__D', I.Maybe), __V) ->
                 oit (((i - 1), __V), (Paths.body occ))
             | _ ->
                 raise
                   (Error
                      (((^) ((occToString (ocdOpt, occ)) ^
                               "No occurrence of ")
                          decToVarName __D)
                         ^ " in type, use %abbrev")))
        | _ -> () in
      oit ((i, __V), Paths.top)
    let check = strictTop
    let checkType = occursInType
  end ;;
