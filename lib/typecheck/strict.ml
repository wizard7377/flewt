
module type STRICT  =
  sig
    exception Error of
      ((string)(*! structure Paths : PATHS !*)(*! structure IntSyn : INTSYN !*)
      (* Author: Carsten Schuermann *)(* Checking Definitions for Strictness *))
      
    val check :
      ((IntSyn.__Exp * IntSyn.__Exp) * Paths.occConDec option) -> unit
    val checkType : ((int * IntSyn.__Exp) * Paths.occConDec option) -> unit
  end;;




module Strict(Strict:sig
                       module Whnf :
                       ((WHNF)(* Checking Definitions for Strict *)
                       (* Author: Carsten Schuermann *)
                       (*! structure IntSyn' : INTSYN !*))
                     end) : STRICT =
  struct
    exception Error of
      ((string)(*! structure Paths = Paths' !*)(*! structure IntSyn = IntSyn' !*)
      (*! structure Paths' : PATHS !*)(*! sharing Whnf.IntSyn = IntSyn' !*))
      
    module I = IntSyn
    let rec patSpine =
      function
      | (_, I.Nil) -> true__
      | (k, App (Root (BVar k', I.Nil), S)) ->
          let indexDistinct =
            function
            | I.Nil -> true__
            | App (Root (BVar k'', I.Nil), S) ->
                (k' <> k'') && (indexDistinct S)
            | _ -> false__ in
          (k' <= k) && ((patSpine (k, S)) && (indexDistinct S))
      | _ -> false__
    let rec strictExp =
      function
      | (_, _, Uni _) -> false__
      | (k, p, Lam (D, U)) ->
          (strictDec (k, p, D)) || (strictExp ((k + 1), (p + 1), U))
      | (k, p, Pi ((D, _), U)) ->
          (strictDec (k, p, D)) || (strictExp ((k + 1), (p + 1), U))
      | (k, p, Root (H, S)) ->
          (match H with
           | BVar k' ->
               if k' = p
               then patSpine (k, S)
               else if k' <= k then strictSpine (k, p, S) else false__
           | Const c -> strictSpine (k, p, S)
           | Def d -> strictSpine (k, p, S)
           | FgnConst (cs, conDec) -> strictSpine (k, p, S))
      | (k, p, FgnExp (cs, ops)) -> false__
    let rec strictSpine =
      function
      | (_, _, I.Nil) -> false__
      | (k, p, App (U, S)) ->
          (strictExp (k, p, U)) || (strictSpine (k, p, S))
    let rec strictDec (k, p, Dec (_, V)) = strictExp (k, p, V)
    let rec strictArgParm =
      function
      | (p, (Root _ as U)) -> strictExp (0, p, U)
      | (p, (Pi _ as U)) -> strictExp (0, p, U)
      | (p, (FgnExp _ as U)) -> strictExp (0, p, U)
      | (p, Lam (D, U)) -> strictArgParm ((p + 1), U)
    let rec occToString =
      function
      | (SOME ocd, occ) -> Paths.wrap ((Paths.occToRegionDef1 ocd occ), "")
      | (NONE, occ) -> "Error: "
    let rec decToVarName =
      function
      | Dec (NONE, _) -> "implicit variable"
      | Dec (SOME x, _) -> "variable " ^ x
    let rec strictTop ((U, V), ocdOpt) =
      let strictArgParms =
        function
        | (Root (BVar _, _), _, occ) ->
            raise
              (Error
                 ((occToString (ocdOpt, occ)) ^ "Head not rigid, use %abbrev"))
        | (Root _, _, _) -> ()
        | (Pi _, _, _) -> ()
        | (FgnExp _, _, _) -> ()
        | (Lam (D, U'), Pi (_, V'), occ) ->
            if strictArgParm (1, U')
            then strictArgParms (U', V', (Paths.body occ))
            else
              raise
                (Error
                   (((^) ((occToString (ocdOpt, occ)) ^
                            "No strict occurrence of ")
                       decToVarName D)
                      ^ ", use %abbrev"))
        | ((Lam _ as U), (Root (Def _, _) as V), occ) ->
            strictArgParms
              (U, (Whnf.normalize (Whnf.expandDef (V, I.id))), occ) in
      strictArgParms (U, V, Paths.top)
    let rec occursInType ((i, V), ocdOpt) =
      let oit =
        function
        | ((0, V), occ) -> ()
        | ((i, Pi ((D, P), V)), occ) ->
            (match Abstract.piDepend ((D, P), V) with
             | Pi ((D', I.Maybe), V) -> oit (((i - 1), V), (Paths.body occ))
             | _ ->
                 raise
                   (Error
                      (((^) ((occToString (ocdOpt, occ)) ^
                               "No occurrence of ")
                          decToVarName D)
                         ^ " in type, use %abbrev")))
        | _ -> () in
      oit ((i, V), Paths.top)
    let ((check)(* Definition of normal form (nf) --- see lambda/whnf.fun *)
      (* patSpine (k, S) = B

       Invariant:
       If  g, D |- S : V > V', S in nf
       and |D| = k
       then B iff S = (k1 ; k2 ;...; kn ; NIL), kn <= k, all ki pairwise distinct
    *)
      (* possibly eta-contract? -fp *)(* strictExp (k, p, U) = B

       Invariant:
       If  g, D |- U : V
       and U is in nf (normal form)
       and |D| = k
       then B iff U is strict in p
    *)
      (* checking D in this case might be redundant -fp *)
      (* no other cases possible *)(* this is a hack - until we investigate this further   -rv *)
      (* no other cases possible *)(* strictSpine (k, S) = B

       Invariant:
       If  g, D |- S : V > W
       and S is in nf (normal form)
       and |D| = k
       then B iff S is strict in k
    *)
      (* strictArgParm (p, U) = B

       Traverses the flexible abstractions in U.

       Invariant:
       If   g |- U : V
       and  g |- p : V'
       and  U is in nf
       then B iff argument parameter p occurs in strict position in U
                  which starts with argument parameters
    *)
      (* strictTop ((U, V), ocdOpt) = ()

       Invariant:
       condec has form c = U : V where . |- U : V
       and U is in nf (normal form)
       then function returns () if U every argument parameter of U
            has at least one strict and rigid occurrence in U
       raises Error otherwise

       ocdOpt is an optional occurrence tree for condec for error messages
    *)
      (* may not be sound in general *)(* Wed Aug 25 16:39:57 2004 -fp *))
      = strictTop
    let checkType = occursInType
  end ;;
