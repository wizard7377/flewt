module type STRICT  =
  sig
    exception Error of string 
    val check :
      ((IntSyn.exp_ * IntSyn.exp_) * Paths.occConDec option) -> unit
    val checkType : ((int * IntSyn.exp_) * Paths.occConDec option) -> unit
  end


module Strict(Strict:sig module Whnf : WHNF end) : STRICT =
  struct
    exception Error of string 
    module I = IntSyn
    let rec patSpine =
      begin function
      | (_, I.Nil) -> true
      | (k, App (Root (BVar k', I.Nil), s_)) ->
          let rec indexDistinct =
            begin function
            | I.Nil -> true
            | App (Root (BVar k'', I.Nil), s_) ->
                (k' <> k'') && (indexDistinct s_)
            | _ -> false end in
        (k' <= k) && ((patSpine (k, s_)) && (indexDistinct s_))
      | _ -> false end(* possibly eta-contract? -fp *)
  let rec strictExp =
    begin function
    | (_, _, Uni _) -> false
    | (k, p, Lam (d_, u_)) ->
        (strictDec (k, p, d_)) || (strictExp ((k + 1), (p + 1), u_))
    | (k, p, Pi ((d_, _), u_)) ->
        (strictDec (k, p, d_)) || (strictExp ((k + 1), (p + 1), u_))
    | (k, p, Root (h_, s_)) ->
        (begin match h_ with
         | BVar k' -> if k' = p then begin patSpine (k, s_) end
             else begin if k' <= k then begin strictSpine (k, p, s_) end
               else begin false end end
    | Const c -> strictSpine (k, p, s_) | Def d -> strictSpine (k, p, s_)
    | FgnConst (cs, conDec) -> strictSpine (k, p, s_) end)
| (k, p, FgnExp (cs, ops)) -> false end(* no other cases possible *)
(* checking D in this case might be redundant -fp *)
let rec strictSpine =
  begin function
  | (_, _, I.Nil) -> false
  | (k, p, App (u_, s_)) ->
      (strictExp (k, p, u_)) || (strictSpine (k, p, s_)) end
let rec strictDec (k, p, Dec (_, v_)) = strictExp (k, p, v_)
let rec strictArgParm =
  begin function
  | (p, (Root _ as u_)) -> strictExp (0, p, u_)
  | (p, (Pi _ as u_)) -> strictExp (0, p, u_)
  | (p, (FgnExp _ as u_)) -> strictExp (0, p, u_)
  | (p, Lam (d_, u_)) -> strictArgParm ((p + 1), u_) end
let rec occToString =
  begin function
  | (Some ocd, occ) -> Paths.wrap ((Paths.occToRegionDef1 ocd occ), "")
  | (None, occ) -> "Error: " end
let rec decToVarName =
  begin function
  | Dec (None, _) -> "implicit variable"
  | Dec (Some x, _) -> "variable " ^ x end
let rec strictTop ((u_, v_), ocdOpt) =
  let rec strictArgParms =
    begin function
    | (Root (BVar _, _), _, occ) ->
        raise
          (Error
             ((occToString (ocdOpt, occ)) ^ "Head not rigid, use %abbrev"))
    | (Root _, _, _) -> ()
    | (Pi _, _, _) -> ()
    | (FgnExp _, _, _) -> ()
    | (Lam (d_, u'_), Pi (_, v'_), occ) ->
        if strictArgParm (1, u'_)
        then begin strictArgParms (u'_, v'_, (Paths.body occ)) end
        else begin
          raise
            (Error
               (((^) ((occToString (ocdOpt, occ)) ^
                        "No strict occurrence of ")
                   decToVarName d_)
                  ^ ", use %abbrev")) end
    | ((Lam _ as u_), (Root (Def _, _) as v_), occ) ->
        strictArgParms
          (u_, (Whnf.normalize (Whnf.expandDef (v_, I.id))), occ) end
(* Wed Aug 25 16:39:57 2004 -fp *)(* may not be sound in general *) in
strictArgParms (u_, v_, Paths.top)
let rec occursInType ((i, v_), ocdOpt) =
  let rec oit =
    begin function
    | ((0, v_), occ) -> ()
    | ((i, Pi ((d_, p_), v_)), occ) ->
        (begin match Abstract.piDepend ((d_, p_), v_) with
         | Pi ((d'_, I.Maybe), v_) -> oit (((i - 1), v_), (Paths.body occ))
         | _ ->
             raise
               (Error
                  (((^) ((occToString (ocdOpt, occ)) ^ "No occurrence of ")
                      decToVarName d_)
                     ^ " in type, use %abbrev")) end)
    | _ -> () end in
oit ((i, v_), Paths.top)
let check = strictTop
let checkType = occursInType end
