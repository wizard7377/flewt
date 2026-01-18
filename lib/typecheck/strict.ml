
(* Checking Definitions for Strictness *)
(* Author: Carsten Schuermann *)
module type STRICT  =
  sig
    (*! structure IntSyn : INTSYN !*)
    (*! structure Paths : PATHS !*)
    exception Error of string 
    val check :
      ((IntSyn.__Exp * IntSyn.__Exp) * Paths.occConDec option) -> unit
    val checkType : ((int * IntSyn.__Exp) * Paths.occConDec option) -> unit
  end;;




(* Checking Definitions for Strict *)
(* Author: Carsten Schuermann *)
module Strict(Strict:sig
                       (*! structure IntSyn' : INTSYN !*)
                       module Whnf : WHNF
                     end) : STRICT =
  struct
    (*! sharing Whnf.IntSyn = IntSyn' !*)
    (*! structure Paths' : PATHS !*)
    (*! structure IntSyn = IntSyn' !*)
    (*! structure Paths = Paths' !*)
    exception Error of string 
    module I = IntSyn
    let rec patSpine =
      function
      | (_, I.Nil) -> true__
      | (k, App (Root (BVar k', I.Nil), S)) ->
          let rec indexDistinct =
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
      | (k, p, Lam (__d, __u)) ->
          (strictDec (k, p, __d)) || (strictExp ((k + 1), (p + 1), __u))
      | (k, p, Pi ((__d, _), __u)) ->
          (strictDec (k, p, __d)) || (strictExp ((k + 1), (p + 1), __u))
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
      | (k, p, App (__u, S)) ->
          (strictExp (k, p, __u)) || (strictSpine (k, p, S))
    let rec strictDec (k, p, Dec (_, __v)) = strictExp (k, p, __v)
    let rec strictArgParm =
      function
      | (p, (Root _ as __u)) -> strictExp (0, p, __u)
      | (p, (Pi _ as __u)) -> strictExp (0, p, __u)
      | (p, (FgnExp _ as __u)) -> strictExp (0, p, __u)
      | (p, Lam (__d, __u)) -> strictArgParm ((p + 1), __u)
    let rec occToString =
      function
      | (Some ocd, occ) -> Paths.wrap ((Paths.occToRegionDef1 ocd occ), "")
      | (None, occ) -> "Error: "
    let rec decToVarName =
      function
      | Dec (None, _) -> "implicit variable"
      | Dec (Some x, _) -> "variable " ^ x
    let rec strictTop ((__u, __v), ocdOpt) =
      let rec strictArgParms =
        function
        | (Root (BVar _, _), _, occ) ->
            raise
              (Error
                 ((occToString (ocdOpt, occ)) ^ "Head not rigid, use %abbrev"))
        | (Root _, _, _) -> ()
        | (Pi _, _, _) -> ()
        | (FgnExp _, _, _) -> ()
        | (Lam (__d, __u'), Pi (_, __v'), occ) ->
            if strictArgParm (1, __u')
            then strictArgParms (__u', __v', (Paths.body occ))
            else
              raise
                (Error
                   (((^) ((occToString (ocdOpt, occ)) ^
                            "No strict occurrence of ")
                       decToVarName __d)
                      ^ ", use %abbrev"))
        | ((Lam _ as __u), (Root (Def _, _) as __v), occ) ->
            strictArgParms
              (__u, (Whnf.normalize (Whnf.expandDef (__v, I.id))), occ) in
      strictArgParms (__u, __v, Paths.top)
    let rec occursInType ((i, __v), ocdOpt) =
      let rec oit =
        function
        | ((0, __v), occ) -> ()
        | ((i, Pi ((__d, P), __v)), occ) ->
            (match Abstract.piDepend ((__d, P), __v) with
             | Pi ((__d', I.Maybe), __v) -> oit (((i - 1), __v), (Paths.body occ))
             | _ ->
                 raise
                   (Error
                      (((^) ((occToString (ocdOpt, occ)) ^
                               "No occurrence of ")
                          decToVarName __d)
                         ^ " in type, use %abbrev")))
        | _ -> () in
      oit ((i, __v), Paths.top)
    (* Definition of normal form (nf) --- see lambda/whnf.fun *)
    (* patSpine (k, S) = B

       Invariant:
       If  __g, __d |- S : __v > __v', S in nf
       and |__d| = k
       then B iff S = (k1 ; k2 ;...; kn ; NIL), kn <= k, all ki pairwise distinct
    *)
    (* possibly eta-contract? -fp *)
    (* strictExp (k, p, __u) = B

       Invariant:
       If  __g, __d |- __u : __v
       and __u is in nf (normal form)
       and |__d| = k
       then B iff __u is strict in p
    *)
    (* checking __d in this case might be redundant -fp *)
    (* no other cases possible *)
    (* this is a hack - until we investigate this further   -rv *)
    (* no other cases possible *)
    (* strictSpine (k, S) = B

       Invariant:
       If  __g, __d |- S : __v > W
       and S is in nf (normal form)
       and |__d| = k
       then B iff S is strict in k
    *)
    (* strictArgParm (p, __u) = B

       Traverses the flexible abstractions in U.

       Invariant:
       If   __g |- __u : __v
       and  __g |- p : __v'
       and  __u is in nf
       then B iff argument parameter p occurs in strict position in __u
                  which starts with argument parameters
    *)
    (* strictTop ((__u, __v), ocdOpt) = ()

       Invariant:
       condec has form c = __u : __v where . |- __u : __v
       and __u is in nf (normal form)
       then function returns () if __u every argument parameter of __u
            has at least one strict and rigid occurrence in __u
       raises Error otherwise

       ocdOpt is an optional occurrence tree for condec for error messages
    *)
    (* may not be sound in general *)
    (* Wed Aug 25 16:39:57 2004 -fp *)
    let check = strictTop
    let checkType = occursInType
  end ;;
