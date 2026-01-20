
module type APPROX  =
  sig
    type __Uni =
      | Level of int 
      | Next of __Uni 
      | LVar of __Uni option ref 
    type __Exp =
      | Uni of __Uni 
      | Arrow of (__Exp * __Exp) 
      | Const of IntSyn.__Head 
      | CVar of __Exp option ref 
      | Undefined 
    val Type : __Uni
    val Kind : __Uni
    val Hyperkind : __Uni
    val varReset : unit -> unit
    val newLVar : unit -> __Uni
    val newCVar : unit -> __Exp
    val whnfUni : __Uni -> __Uni
    val whnf : __Exp -> __Exp
    val uniToApx : IntSyn.__Uni -> __Uni
    val classToApx : IntSyn.__Exp -> (__Exp * __Uni)
    val exactToApx : IntSyn.__Exp -> IntSyn.__Exp -> (__Exp * __Exp * __Uni)
    exception Ambiguous 
    val apxToUni : __Uni -> IntSyn.__Uni
    val apxToClass : IntSyn.dctx -> __Exp -> __Uni -> bool -> IntSyn.__Exp
    val apxToExact :
      IntSyn.dctx -> __Exp -> IntSyn.eclo -> bool -> IntSyn.__Exp
    exception Unify of string 
    val matchUni : __Uni -> __Uni -> unit
    val match__ : __Exp -> __Exp -> unit
    val makeGroundUni : __Uni -> bool
  end;;




module Approx(Approx:sig module Whnf : WHNF end) : APPROX =
  struct
    module I = IntSyn
    let rec headConDec =
      function
      | Const c -> I.sgnLookup c
      | Skonst c -> I.sgnLookup c
      | Def d -> I.sgnLookup d
      | NSDef d -> I.sgnLookup d
      | FgnConst (_, cd) -> cd
    type __Uni =
      | Level of int 
      | Next of __Uni 
      | LVar of __Uni option ref 
    type __Exp =
      | Uni of __Uni 
      | Arrow of (__Exp * __Exp) 
      | Const of I.__Head 
      | CVar of __Exp option ref 
      | Undefined 
    let Type = Level 1
    let Kind = Level 2
    let Hyperkind = Level 3
    let rec newLVar () = LVar (ref NONE)
    let rec newCVar () = CVar (ref NONE)
    let rec whnfUni =
      function
      | Next (__L) ->
          (match whnfUni __L with
           | Level i -> Level (i + 1)
           | __L' -> Next __L')
      | LVar { contents = Some (__L) } -> whnfUni __L
      | __L -> __L
    let rec whnf =
      function | CVar { contents = Some (__V) } -> whnf __V | __V -> __V
    type nonrec varEntry = ((__Exp * __Exp * __Uni) * string)
    let (varList : varEntry list ref) = ref nil
    let rec varReset () = varList := nil
    let rec varLookupRef r =
      List.find (fun (CVar r', _, _) -> fun _ -> r = r') (!varList)
    let rec varLookupName name =
      List.find (fun _ -> fun name' -> name = name') (!varList)
    let rec varInsert (__U, __V, __L) name =
      (varList := ((__U, __V, __L), name)) :: (!varList)
    exception Ambiguous 
    let rec getReplacementName (CVar r as U) (__V) (__L) allowed =
      match varLookupRef r with
      | Some (_, name) -> name
      | NONE ->
          let _ = if allowed then () else raise Ambiguous in
          let pref = match whnfUni __L with | Level 2 -> "A" | Level 3 -> "K" in
          let rec try__ i =
            let name = ((^) ("%" ^ pref) Int.toString i) ^ "%" in
            match varLookupName name with
            | NONE -> (varInsert ((__U, __V, __L), name); name)
            | Some _ -> try__ (i + 1) in
          ((try__ 1)(* others impossible by invariant *))
    let rec findByReplacementName name =
      ((match varLookupName name with | Some (UVL, _) -> UVL)
      (* must be in list by invariant *))
    let rec uniToApx = function | I.Type -> Type | I.Kind -> Kind
    let rec expToApx =
      function
      | Uni (__L) ->
          let __L' = uniToApx __L in
          ((Uni __L'), (Uni (whnfUni (Next __L'))))
      | Pi ((Dec (_, __V1), _), __V2) ->
          let (((V1', _))(* Type *)) = expToApx __V1 in
          let (V2', __L') = expToApx __V2 in ((Arrow (V1', V2')), __L')
      | Root (FVar (name, _, _), _) ->
          let (__U, __V, __L) = findByReplacementName name in (__U, __V)
      | Root (((__H, _))(* Const/Def/NSDef *)) ->
          ((Const __H), (Uni Type))
      | Redex (__U, _) -> expToApx __U
      | Lam (_, __U) -> expToApx __U
      | EClo (__U, _) -> expToApx __U(* are we sure Skonst/FgnConst are never types or kinds? *)
      (* must have been created to represent a CVar *)
    let rec classToApx (__V) =
      let (__V', __L') = expToApx __V in
      let Uni (L'') = whnf __L' in (__V', L'')
    let rec exactToApx (__U) (__V) =
      let (__V', __L') = classToApx __V in
      ((match whnfUni __L' with
        | Level 1 -> (Undefined, __V', __L')
        | _ ->
            let (((__U', _))(* V' *)) = expToApx __U in
            (__U', __V', __L'))
        (* Type *)(* Kind/Hyperkind *))
    let rec constDefApx d =
      match I.sgnLookup d with
      | ConDef (_, _, _, __U, _, _, _) ->
          let (((__V', _))(* Uni Type *)) = expToApx __U in
          __V'
      | AbbrevDef (_, _, _, __U, _, _) ->
          let (((__V', _))(* Uni Type *)) = expToApx __U in
          __V'
    let rec apxToUniW = function | Level 1 -> I.Type | Level 2 -> I.Kind
    let rec apxToUni (__L) = apxToUniW (whnfUni __L)
    let rec apxToClassW __0__ __1__ __2__ __3__ =
      match (__0__, __1__, __2__, __3__) with
      | (__G, Uni (__L), _, allowed) -> I.Uni (apxToUni __L)
      | (__G, Arrow (__V1, __V2), __L, allowed) ->
          let V1' = apxToClass (__G, __V1, Type, allowed) in
          let __D = I.Dec (NONE, V1') in
          let V2' = apxToClass ((I.Decl (__G, __D)), __V2, __L, allowed) in
          I.Pi ((__D, I.Maybe), V2')
      | (__G, (CVar r as V), __L, allowed) ->
          let name = getReplacementName (__V, (Uni __L), (Next __L), allowed) in
          let s = I.Shift (I.ctxLength __G) in
          I.Root ((I.FVar (name, (I.Uni (apxToUni __L)), s)), I.Nil)
      | (__G, Const (__H), __L, allowed) ->
          I.Root
            (__H,
              (Whnf.newSpineVar
                 (__G, ((I.conDecType (headConDec __H)), I.id))))(* Type *)
      (* convert undetermined CVars to FVars *)(* Type or Kind *)
      (* also, does the name of the bound variable here matter? *)
      (* this is probably very bad -- it should be possible to infer
         more accurately which pis can be dependent *)
      (* Next L *)
    let rec apxToClass (__G) (__V) (__L) allowed =
      apxToClassW (__G, (whnf __V), __L, allowed)
    let rec apxToExactW __4__ __5__ __6__ __7__ =
      match (__4__, __5__, __6__, __7__) with
      | (__G, __U, (Pi ((__D, _), __V), s), allowed) ->
          let __D' = I.decSub (__D, s) in
          I.Lam
            (__D',
              (apxToExact
                 ((I.Decl (__G, __D')), __U, (__V, (I.dot1 s)), allowed)))
      | (__G, __U, (Uni (__L), s), allowed) ->
          apxToClass (__G, __U, (uniToApx __L), allowed)
      | (__G, __U, ((Root (FVar (name, _, _), _), s) as Vs), allowed) ->
          let (((__V, __L, _))(* Next L *)) =
            findByReplacementName name in
          let Uni (__L) = whnf __L in
          (((match whnfUni __L with
             | Level 1 -> I.newEVar (__G, (I.EClo __Vs))
             | Level 2 ->
                 let name' =
                   getReplacementName ((whnf __U), __V, (Level 2), allowed) in
                 let __V' = apxToClass (I.Null, __V, (Level 2), allowed) in
                 let s' = I.Shift (I.ctxLength __G) in
                 ((I.Root ((I.FVar (name', __V', s')), I.Nil))
                   (* NOTE: V' differs from Vs by a Shift *)
                   (* probably could avoid the following call by removing the
                  substitutions in Vs instead *))))
            (* U must be a CVar *))
      | (__G, __U, __Vs, allowed) -> I.newEVar (__G, (I.EClo __Vs))(* an atomic type, not Def *)
    let rec apxToExact (__G) (__U) (__Vs) allowed =
      apxToExactW (__G, __U, (Whnf.whnfExpandDef __Vs), allowed)
    exception Unify of string 
    let rec occurUniW __8__ __9__ =
      match (__8__, __9__) with
      | (r, Next (__L)) -> occurUniW (r, __L)
      | (r, LVar r') ->
          if r = r' then raise (Unify "Level circularity") else ()
      | (r, _) -> ()
    let rec occurUni r (__L) = occurUniW (r, (whnfUni __L))
    let rec matchUniW __10__ __11__ =
      match (__10__, __11__) with
      | (Level i1, Level i2) ->
          if i1 = i2 then () else raise (Unify "Level clash")
      | (Level i1, Next (__L2)) ->
          if i1 > 1
          then matchUniW ((Level (i1 - 1)), __L2)
          else raise (Unify "Level clash")
      | (Next (__L1), Level i2) ->
          if i2 > 1
          then matchUniW (__L1, (Level (i2 - 1)))
          else raise (Unify "Level clash")
      | (Next (__L1), Next (__L2)) -> matchUniW (__L1, __L2)
      | (LVar r1, (LVar r2 as L2)) ->
          if r1 = r2 then () else (:=) r1 Some __L2
      | (LVar r1, __L2) -> (occurUniW (r1, __L2); (:=) r1 Some __L2)
      | (__L1, LVar r2) -> (occurUniW (r2, __L1); (:=) r2 Some __L1)
    let rec matchUni (__L1) (__L2) =
      matchUniW ((whnfUni __L1), (whnfUni __L2))
    let rec occurW __12__ __13__ =
      match (__12__, __13__) with
      | (r, Arrow (__V1, __V2)) -> (occur (r, __V1); occur (r, __V2))
      | (r, CVar r') ->
          if r = r'
          then raise (Unify "Type/kind variable occurrence")
          else ()
      | (r, _) -> ()
    let rec occur r (__U) = occurW (r, (whnf __U))
    let rec matchW __14__ __15__ =
      match (__14__, __15__) with
      | (Uni (__L1), Uni (__L2)) -> matchUni (__L1, __L2)
      | ((Const (__H1) as V1), (Const (__H2) as V2)) ->
          (((match (__H1, __H2) with
             | (Const c1, Const c2) ->
                 if c1 = c2
                 then ()
                 else raise (Unify "Type/kind constant clash")
             | (Def d1, Def d2) ->
                 if d1 = d2
                 then ()
                 else match__ ((constDefApx d1), (constDefApx d2))
             | (Def d1, _) -> match__ ((constDefApx d1), __V2)
             | (_, Def d2) -> match__ (__V1, (constDefApx d2))
             | (NSDef d1, NSDef d2) ->
                 if d1 = d2
                 then ()
                 else match__ ((constDefApx d1), (constDefApx d2))
             | (NSDef d1, _) -> match__ ((constDefApx d1), __V2)
             | (_, NSDef d2) -> match__ (__V1, (constDefApx d2))))
          (* strictness is irrelevant to matching on approximate types *)
          (* others cannot occur by invariant *))
      | (Arrow (__V1, __V2), Arrow (__V3, __V4)) ->
          ((try match__ (__V1, __V3)
            with | e -> (match__ (__V2, __V4); raise e));
           match__ (__V2, __V4))
      | ((Arrow _ as V1), Const (Def d2)) -> match__ (__V1, (constDefApx d2))
      | (Const (Def d1), (Arrow _ as V2)) -> match__ ((constDefApx d1), __V2)
      | ((Arrow _ as V1), Const (NSDef d2)) ->
          match__ (__V1, (constDefApx d2))
      | (Const (NSDef d1), (Arrow _ as V2)) ->
          match__ ((constDefApx d1), __V2)
      | (CVar r1, (CVar r2 as U2)) ->
          if r1 = r2 then () else (:=) r1 Some __U2
      | (CVar r1, __U2) -> (occurW (r1, __U2); (:=) r1 Some __U2)
      | (__U1, CVar r2) -> (occurW (r2, __U1); (:=) r2 Some __U1)
      | _ -> raise (Unify "Type/kind expression clash")
    let rec match__ (__U1) (__U2) = matchW ((whnf __U1), (whnf __U2))
    let rec matchable (__U1) (__U2) =
      try match__ (__U1, __U2); true__ with | Unify _ -> false__
    let rec makeGroundUni =
      function
      | Level _ -> false__
      | Next (__L) -> makeGroundUni __L
      | LVar { contents = Some (__L) } -> makeGroundUni __L
      | LVar ({ contents = NONE } as r) -> ((:=) r Some (Level 1); true__)
  end ;;
