module type APPROX  =
  sig
    type uni_ =
      | Level of int 
      | Next of uni_ 
      | LVar of uni_ option ref 
    type exp_ =
      | Uni of uni_ 
      | Arrow of (exp_ * exp_) 
      | Const of IntSyn.head_ 
      | CVar of exp_ option ref 
      | Undefined 
    val Type : uni_
    val Kind : uni_
    val Hyperkind : uni_
    val varReset : unit -> unit
    val newLVar : unit -> uni_
    val newCVar : unit -> exp_
    val whnfUni : uni_ -> uni_
    val whnf : exp_ -> exp_
    val uniToApx : IntSyn.uni_ -> uni_
    val classToApx : IntSyn.exp_ -> (exp_ * uni_)
    val exactToApx : (IntSyn.exp_ * IntSyn.exp_) -> (exp_ * exp_ * uni_)
    exception Ambiguous 
    val apxToUni : uni_ -> IntSyn.uni_
    val apxToClass : (IntSyn.dctx * exp_ * uni_ * bool) -> IntSyn.exp_
    val apxToExact : (IntSyn.dctx * exp_ * IntSyn.eclo * bool) -> IntSyn.exp_
    exception Unify of string 
    val matchUni : (uni_ * uni_) -> unit
    val match_ : (exp_ * exp_) -> unit
    val makeGroundUni : uni_ -> bool
  end


module Approx(Approx:sig module Whnf : WHNF end) : APPROX =
  struct
    module I = IntSyn
    let rec headConDec =
      begin function
      | Const c -> I.sgnLookup c
      | Skonst c -> I.sgnLookup c
      | Def d -> I.sgnLookup d
      | NSDef d -> I.sgnLookup d
      | FgnConst (_, cd) -> cd end
    type uni_ =
      | Level of int 
      | Next of uni_ 
      | LVar of uni_ option ref 
    type exp_ =
      | Uni of uni_ 
      | Arrow of (exp_ * exp_) 
      | Const of I.head_ 
      | CVar of exp_ option ref 
      | Undefined 
    let Type = Level 1
    let Kind = Level 2
    let Hyperkind = Level 3
    let rec newLVar () = LVar (ref None)
    let rec newCVar () = CVar (ref None)
    let rec whnfUni =
      begin function
      | Next (l_) ->
          (begin match whnfUni l_ with
           | Level i -> Level (i + 1)
           | l'_ -> Next l'_ end)
      | LVar { contents = Some (l_) } -> whnfUni l_ | l_ -> l_ end
let rec whnf =
  begin function | CVar { contents = Some (v_) } -> whnf v_ | v_ -> v_ end
type nonrec varEntry = ((exp_ * exp_ * uni_) * string)
let (varList : varEntry list ref) = ref []
let rec varReset () = varList := []
let rec varLookupRef r =
  List.find (begin function | ((CVar r', _, _), _) -> r = r' end) !varList
let rec varLookupName name =
  List.find (begin function | (_, name') -> name = name' end) !varList
let rec varInsert ((u_, v_, l_), name) =
  (varList := ((u_, v_, l_), name)) :: !varList
exception Ambiguous 
let rec getReplacementName ((CVar r as u_), v_, l_, allowed) =
  begin match varLookupRef r with
  | Some (_, name) -> name
  | None ->
      let _ = if allowed then begin () end else begin raise Ambiguous end in
let pref = begin match whnfUni l_ with | Level 2 -> "A" | Level 3 -> "K" end in
let rec try_ i =
  let name = ((^) ("%" ^ pref) Int.toString i) ^ "%" in
  begin match varLookupName name with
  | None -> (begin varInsert ((u_, v_, l_), name); name end)
    | Some _ -> try_ (i + 1) end in
((try_ 1)(* others impossible by invariant *)) end
let rec findByReplacementName name =
  ((begin match varLookupName name with | Some (UVL, _) -> UVL end)
  (* must be in list by invariant *))
let rec uniToApx = begin function | I.Type -> Type | I.Kind -> Kind end
let rec expToApx =
  begin function
  | Uni (l_) ->
      let l'_ = uniToApx l_ in ((Uni l'_), (Uni (whnfUni (Next l'_))))
  | Pi ((Dec (_, v1_), _), v2_) ->
      let (((V1', _))(* Type *)) = expToApx v1_ in
      let (V2', l'_) = expToApx v2_ in ((Arrow (V1', V2')), l'_)
  | Root (FVar (name, _, _), _) ->
      let (u_, v_, l_) = findByReplacementName name in (u_, v_)
  | Root (((h_, _))(* Const/Def/NSDef *)) ->
      ((Const h_), (Uni Type))
  | Redex (u_, _) -> expToApx u_
  | Lam (_, u_) -> expToApx u_
  | EClo (u_, _) -> expToApx u_ end(* are we sure Skonst/FgnConst are never types or kinds? *)
(* must have been created to represent a CVar *)
let rec classToApx (v_) =
  let (v'_, l'_) = expToApx v_ in let Uni (L'') = whnf l'_ in (v'_, L'')
let rec exactToApx (u_, v_) =
  let (v'_, l'_) = classToApx v_ in
  ((begin match whnfUni l'_ with
    | Level 1 -> (Undefined, v'_, l'_)
    | _ ->
        let (((u'_, _))(* V' *)) = expToApx u_ in
        (u'_, v'_, l'_) end)
  (* Type *)(* Kind/Hyperkind *))
let rec constDefApx d =
  begin match I.sgnLookup d with
  | ConDef (_, _, _, u_, _, _, _) ->
      let (((v'_, _))(* Uni Type *)) = expToApx u_ in v'_
  | AbbrevDef (_, _, _, u_, _, _) ->
      let (((v'_, _))(* Uni Type *)) = expToApx u_ in v'_ end
let rec apxToUniW =
  begin function | Level 1 -> I.Type | Level 2 -> I.Kind end
let rec apxToUni (l_) = apxToUniW (whnfUni l_)
let rec apxToClassW =
  begin function
  | (((g_, Uni (l_), _, allowed))(* Next L *)) ->
      I.Uni (apxToUni l_)
  | (g_, Arrow (v1_, v2_), l_, allowed) ->
      let V1' = apxToClass (g_, v1_, Type, allowed) in
      let d_ = I.Dec (None, V1') in
      let V2' = apxToClass ((I.Decl (g_, d_)), v2_, l_, allowed) in
      I.Pi ((d_, I.Maybe), V2')
  | (((g_, (CVar r as v_), l_, allowed))(* Type or Kind *))
      ->
      let name = getReplacementName (v_, (Uni l_), (Next l_), allowed) in
      let s = I.Shift (I.ctxLength g_) in
      I.Root ((I.FVar (name, (I.Uni (apxToUni l_)), s)), I.Nil)
  | (((g_, Const (h_), l_, allowed))(* Type *)) ->
      I.Root
        (h_, (Whnf.newSpineVar (g_, ((I.conDecType (headConDec h_)), I.id)))) end
(* convert undetermined CVars to FVars *)(* also, does the name of the bound variable here matter? *)
(* this is probably very bad -- it should be possible to infer
         more accurately which pis can be dependent *)
let rec apxToClass (g_, v_, l_, allowed) =
  apxToClassW (g_, (whnf v_), l_, allowed)
let rec apxToExactW =
  begin function
  | (g_, u_, (Pi ((d_, _), v_), s), allowed) ->
      let d'_ = I.decSub (d_, s) in
      I.Lam
        (d'_,
          (apxToExact ((I.Decl (g_, d'_)), u_, (v_, (I.dot1 s)), allowed)))
  | (g_, u_, (Uni (l_), s), allowed) ->
      apxToClass (g_, u_, (uniToApx l_), allowed)
  | (g_, u_, ((Root (FVar (name, _, _), _), s) as vs_), allowed) ->
      let (((v_, l_, _))(* Next L *)) =
        findByReplacementName name in
      let Uni (l_) = whnf l_ in
      (((begin match whnfUni l_ with
         | Level 1 -> I.newEVar (g_, (I.EClo vs_))
         | Level 2 ->
             let name' =
               getReplacementName ((whnf u_), v_, (Level 2), allowed) in
             let v'_ = apxToClass (I.Null, v_, (Level 2), allowed) in
             let s' = I.Shift (I.ctxLength g_) in
             ((I.Root ((I.FVar (name', v'_, s')), I.Nil))
               (* NOTE: V' differs from Vs by a Shift *)
               (* probably could avoid the following call by removing the
                  substitutions in Vs instead *)) end))
        (* U must be a CVar *))
  | (((g_, u_, vs_, allowed))(* an atomic type, not Def *))
      -> I.newEVar (g_, (I.EClo vs_)) end
let rec apxToExact (g_, u_, vs_, allowed) =
  apxToExactW (g_, u_, (Whnf.whnfExpandDef vs_), allowed)
exception Unify of string 
let rec occurUniW =
  begin function
  | (r, Next (l_)) -> occurUniW (r, l_)
  | (r, LVar r') ->
      if r = r' then begin raise (Unify "Level circularity") end
      else begin () end
  | (r, _) -> () end
let rec occurUni (r, l_) = occurUniW (r, (whnfUni l_))
let rec matchUniW =
  begin function
  | (Level i1, Level i2) -> if i1 = i2 then begin () end
      else begin raise (Unify "Level clash") end
  | (Level i1, Next (l2_)) ->
      if i1 > 1 then begin matchUniW ((Level (i1 - 1)), l2_) end
      else begin raise (Unify "Level clash") end
| (Next (l1_), Level i2) ->
    if i2 > 1 then begin matchUniW (l1_, (Level (i2 - 1))) end
    else begin raise (Unify "Level clash") end
| (Next (l1_), Next (l2_)) -> matchUniW (l1_, l2_)
| (LVar r1, (LVar r2 as l2_)) -> if r1 = r2 then begin () end
    else begin (:=) r1 Some l2_ end
| (LVar r1, l2_) -> (begin occurUniW (r1, l2_); (:=) r1 Some l2_ end)
| (l1_, LVar r2) -> (begin occurUniW (r2, l1_); (:=) r2 Some l1_ end) end
let rec matchUni (l1_, l2_) = matchUniW ((whnfUni l1_), (whnfUni l2_))
let rec occurW =
  begin function
  | (r, Arrow (v1_, v2_)) -> (begin occur (r, v1_); occur (r, v2_) end)
  | (r, CVar r') ->
      if r = r' then begin raise (Unify "Type/kind variable occurrence") end
      else begin () end
| (r, _) -> () end
let rec occur (r, u_) = occurW (r, (whnf u_))
let rec matchW =
  begin function
  | (Uni (l1_), Uni (l2_)) -> matchUni (l1_, l2_)
  | ((Const (h1_) as v1_), (Const (h2_) as v2_)) ->
      (((begin match (h1_, h2_) with
         | (Const c1, Const c2) -> if c1 = c2 then begin () end
             else begin raise (Unify "Type/kind constant clash") end
  | (Def d1, Def d2) -> if d1 = d2 then begin () end
      else begin match_ ((constDefApx d1), (constDefApx d2)) end
  | (Def d1, _) -> match_ ((constDefApx d1), v2_)
  | (_, Def d2) -> match_ (v1_, (constDefApx d2))
  | (NSDef d1, NSDef d2) -> if d1 = d2 then begin () end
      else begin match_ ((constDefApx d1), (constDefApx d2)) end
| (NSDef d1, _) -> match_ ((constDefApx d1), v2_)
| (_, NSDef d2) -> match_ (v1_, (constDefApx d2)) end))
(* strictness is irrelevant to matching on approximate types *)(* others cannot occur by invariant *))
| (Arrow (v1_, v2_), Arrow (v3_, v4_)) ->
    (begin (begin try match_ (v1_, v3_)
            with | e -> (begin match_ (v2_, v4_); raise e end) end);
match_ (v2_, v4_) end)
| ((Arrow _ as v1_), Const (Def d2)) -> match_ (v1_, (constDefApx d2))
| (Const (Def d1), (Arrow _ as v2_)) -> match_ ((constDefApx d1), v2_)
| ((Arrow _ as v1_), Const (NSDef d2)) -> match_ (v1_, (constDefApx d2))
| (Const (NSDef d1), (Arrow _ as v2_)) -> match_ ((constDefApx d1), v2_)
| (CVar r1, (CVar r2 as u2_)) -> if r1 = r2 then begin () end
    else begin (:=) r1 Some u2_ end
| (CVar r1, u2_) -> (begin occurW (r1, u2_); (:=) r1 Some u2_ end)
| (u1_, CVar r2) -> (begin occurW (r2, u1_); (:=) r2 Some u1_ end)
| _ -> raise (Unify "Type/kind expression clash") end
let rec match_ (u1_, u2_) = matchW ((whnf u1_), (whnf u2_))
let rec matchable (u1_, u2_) = begin try begin match_ (u1_, u2_); true end
  with | Unify _ -> false end
let rec makeGroundUni =
  begin function
  | Level _ -> false
  | Next (l_) -> makeGroundUni l_
  | LVar { contents = Some (l_) } -> makeGroundUni l_
  | LVar ({ contents = None } as r) -> (begin (:=) r Some (Level 1); true end) end
end
