
(* Approximate language for term reconstruction *)
(* Author: Kevin Watkins *)
module type APPROX  =
  sig
    (*! structure IntSyn : INTSYN !*)
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
    (* resets names of undetermined type/kind variables chosen for printing *)
    val varReset : unit -> unit
    val newLVar : unit -> __Uni
    val newCVar : unit -> __Exp
    val whnfUni : __Uni -> __Uni
    val whnf : __Exp -> __Exp
    val uniToApx : IntSyn.__Uni -> __Uni
    val classToApx : IntSyn.__Exp -> (__Exp * __Uni)
    val exactToApx : (IntSyn.__Exp * IntSyn.__Exp) -> (__Exp * __Exp * __Uni)
    exception Ambiguous 
    val apxToUni : __Uni -> IntSyn.__Uni
    val apxToClass : (IntSyn.dctx * __Exp * __Uni * bool) -> IntSyn.__Exp
    val apxToExact :
      (IntSyn.dctx * __Exp * IntSyn.eclo * bool) -> IntSyn.__Exp
    exception Unify of string 
    val matchUni : (__Uni * __Uni) -> unit
    val match__ : (__Exp * __Exp) -> unit
    val makeGroundUni : __Uni -> bool
  end;;




(* Approximate language for term reconstruction *)
(* Author: Kevin Watkins *)
module Approx(Approx:sig
                       (*! structure IntSyn' : INTSYN !*)
                       module Whnf : WHNF
                     end) : APPROX =
  struct
    (*! sharing Whnf.IntSyn = IntSyn' !*)
    (*! structure IntSyn = IntSyn' !*)
    module I = IntSyn
    let rec headConDec =
      function
      | Const c -> I.sgnLookup c
      | Skonst c -> I.sgnLookup c
      | Def d -> I.sgnLookup d
      | NSDef d -> I.sgnLookup d
      | FgnConst (_, cd) -> cd
    (* others impossible by invariant *)
    (* The approximate language is based on the idea of erasure.  The
     erasure of a term is defined as follows:

       c- = c
       d- = d
       type- = type
       kind- = kind
       ({x:A} B)- = A- -> B-
       ([x:A] M)- = M-    
       (M N)- = M-

       x- undefined
       X- undefined

     Note that erasure is always defined on well-typed terms at type
     family or kind level.  Also, if G |- U1 = U2 : V and U1,U2 are at
     type family or kind level, then U1- and U2- are defined and
     equal.  We can define the approximate typing judgment
             
       G |- U ~:~ V
                  
     by replacing appeals to equality in the usual presentation of the
     LF type theory with appeals to

       G |- U1 = U2 ~:~ V,

     which is defined to mean
           G |- U1 ~:~ V  and  G |- U2 ~:~ V  and  U1- = U2-
                                                         
     This is a mutual recursion between the two judgments, just as for
     the standard LF type theory.

     There is also a typing judgment on approximate terms

       |- u : v

     defined in the obvious way.  If |- u : v : l then for any
     well-formed G there are most general U, V such that G |- U : V
     and U- = u and V- = v.  *)
    (* The approximate language *)
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
    (* Because approximate type reconstruction uses the pattern G |- U
     ~:~ V ~:~ L and universe unification on L, if U is to be an
     arbitrary input expression, there must be an internal universe
     Hyperkind such that |- Type ~:~ Kind ~:~ Hyperkind.  The
     Hyperkind universe is used only during the approximate phase of
     reconstruction.  The invariants established by
     ReconTerm.filterLevel ensure that Hyperkind will never appear
     elsewhere. *)
    let Type = Level 1
    let Kind = Level 2
    let Hyperkind = Level 3
    let rec newLVar () = LVar (ref NONE)
    let rec newCVar () = CVar (ref NONE)
    (* whnfUni (l) = l'
       where l = l' and l' is in whnf *)
    let rec whnfUni =
      function
      | Next (L) ->
          (match whnfUni L with | Level i -> Level (i + 1) | L' -> Next L')
      | LVar (ref (SOME (L))) -> whnfUni L
      | L -> L
    (* whnf (u) = u'
       where u = u' and u' is in whnf *)
    let rec whnf = function | CVar (ref (SOME (V))) -> whnf V | V -> V
    (* just a little list since these are only for printing errors *)
    type nonrec varEntry = ((__Exp * __Exp * __Uni) * string)
    let (varList : varEntry list ref) = ref nil
    let rec varReset () = varList := nil
    let rec varLookupRef r =
      List.find (function | ((CVar r', _, _), _) -> r = r') (!varList)
    let rec varLookupName name =
      List.find (function | (_, name') -> name = name') (!varList)
    let rec varInsert ((U, V, L), name) =
      (varList := ((U, V, L), name)) :: (!varList)
    exception Ambiguous 
    (* getReplacementName (u, v, l, allowed) = name
         if u : v : l
         and u is a CVar at type family or kind level *)
    let rec getReplacementName ((CVar r as U), V, L, allowed) =
      match varLookupRef r with
      | SOME (_, name) -> name
      | NONE ->
          let _ = if allowed then () else raise Ambiguous in
          let pref = match whnfUni L with | Level 2 -> "A" | Level 3 -> "K" in
          let rec try__ i =
            let name = ((^) ("%" ^ pref) Int.toString i) ^ "%" in
            match varLookupName name with
            | NONE -> (varInsert ((U, V, L), name); name)
            | SOME _ -> try__ (i + 1) in
          ((try__ 1)(* others impossible by invariant *))
    (* findByReplacementName (name) = (u, v, l)
         if getReplacementName (u, v, l, allowed) = name was already called
         then u : v : l *)
    let rec findByReplacementName name =
      ((match varLookupName name with | SOME (UVL, _) -> UVL)
      (* must be in list by invariant *))
    (* converting exact terms to approximate terms *)
    (* uniToApx (L) = L- *)
    let rec uniToApx = function | I.Type -> Type | I.Kind -> Kind
    (* expToApx (U) = (U-, V-)
     if G |- U : V
     or G |- U ":" V = "hyperkind" *)
    let rec expToApx =
      function
      | Uni (L) ->
          let L' = uniToApx L in ((Uni L'), (Uni (whnfUni (Next L'))))
      | Pi ((Dec (_, V1), _), V2) ->
          let (((V1', _))(* Type *)) = expToApx V1 in
          let (V2', L') = expToApx V2 in ((Arrow (V1', V2')), L')
      | Root (FVar (name, _, _), _) ->
          let (U, V, L) = findByReplacementName name in (U, V)
      | Root (((H, _))(* Const/Def/NSDef *)) ->
          ((Const H), (Uni Type))
      | Redex (U, _) -> expToApx U
      | Lam (_, U) -> expToApx U
      | EClo (U, _) -> expToApx U(* are we sure Skonst/FgnConst are never types or kinds? *)
      (* must have been created to represent a CVar *)
    (* classToApx (V) = (V-, L-)
     if G |- V : L
     or G |- V ":" L = "hyperkind" *)
    let rec classToApx (V) =
      let (V', L') = expToApx V in let Uni (L'') = whnf L' in (V', L'')
    (* exactToApx (U, V) = (U-, V-)
     if G |- U : V *)
    let rec exactToApx (U, V) =
      let (V', L') = classToApx V in
      ((match whnfUni L' with
        | Level 1 -> (Undefined, V', L')
        | _ ->
            let (((U', _))(* V' *)) = expToApx U in
            (U', V', L'))
        (* Type *)(* Kind/Hyperkind *))
    (* constDefApx (d) = V-
     if |- d = V : type *)
    let rec constDefApx d =
      match I.sgnLookup d with
      | ConDef (_, _, _, U, _, _, _) -> let (V', _) = expToApx U in V'
      | AbbrevDef (_, _, _, U, _, _) ->
          let (((V', _))(* Uni Type *)) = expToApx U in V'
    (* Uni Type *)
    (* converting approximate terms to exact terms *)
    (* apxToUni (L-) = L *)
    let rec apxToUniW = function | Level 1 -> I.Type | Level 2 -> I.Kind
    (* others impossible by invariant *)
    let rec apxToUni (L) = apxToUniW (whnfUni L)
    (* apxToClass (G, v, L-, allowed) = V
     pre: L is ground and <= Hyperkind,
          and if L is Hyperkind then the target classifier
          of v is ground
          v : L-
     post: V is most general such that V- = v and G |- V : L *)
    let rec apxToClassW =
      function
      | (G, Uni (L), _, allowed) -> I.Uni (apxToUni L)
      | (G, Arrow (V1, V2), L, allowed) ->
          let V1' = apxToClass (G, V1, Type, allowed) in
          let D = I.Dec (NONE, V1') in
          let V2' = apxToClass ((I.Decl (G, D)), V2, L, allowed) in
          I.Pi ((D, I.Maybe), V2')
      | (((G, (CVar r as V), L, allowed))(* Type or Kind *))
          ->
          let name = getReplacementName (V, (Uni L), (Next L), allowed) in
          let s = I.Shift (I.ctxLength G) in
          I.Root ((I.FVar (name, (I.Uni (apxToUni L)), s)), I.Nil)
      | (((G, Const (H), L, allowed))(* Type *)) ->
          I.Root
            (H,
              (Whnf.newSpineVar (G, ((I.conDecType (headConDec H)), I.id))))
      (* convert undetermined CVars to FVars *)(* also, does the name of the bound variable here matter? *)
      (* this is probably very bad -- it should be possible to infer
         more accurately which pis can be dependent *)
    let rec apxToClass (G, V, L, allowed) =
      apxToClassW (G, (whnf V), L, allowed)
    (* Next L *)
    (* apxToExact (G, u, (V, s), allowed) = U
     if u : V-
     and G' |- V : L and G |- s : G'
     then U- = u and G |- U : V[s] and U is the most general such *)
    let rec apxToExactW =
      function
      | (G, U, (Pi ((D, _), V), s), allowed) ->
          let D' = I.decSub (D, s) in
          I.Lam
            (D',
              (apxToExact ((I.Decl (G, D')), U, (V, (I.dot1 s)), allowed)))
      | (G, U, (Uni (L), s), allowed) ->
          apxToClass (G, U, (uniToApx L), allowed)
      | (G, U, ((Root (FVar (name, _, _), _), s) as Vs), allowed) ->
          let (((V, L, _))(* Next L *)) =
            findByReplacementName name in
          let Uni (L) = whnf L in
          (((match whnfUni L with
             | Level 1 -> I.newEVar (G, (I.EClo Vs))
             | Level 2 ->
                 let name' =
                   getReplacementName ((whnf U), V, (Level 2), allowed) in
                 let V' = apxToClass (I.Null, V, (Level 2), allowed) in
                 let s' = I.Shift (I.ctxLength G) in
                 ((I.Root ((I.FVar (name', V', s')), I.Nil))
                   (* NOTE: V' differs from Vs by a Shift *)
                   (* probably could avoid the following call by removing the
                  substitutions in Vs instead *))))
            (* U must be a CVar *))
      | (((G, U, Vs, allowed))(* an atomic type, not Def *))
          -> I.newEVar (G, (I.EClo Vs))
    let rec apxToExact (G, U, Vs, allowed) =
      apxToExactW (G, U, (Whnf.whnfExpandDef Vs), allowed)
    (* matching for the approximate language *)
    exception Unify of string 
    (* occurUni (r, l) = ()
       iff r does not occur in l,
       otherwise raises Unify *)
    let rec occurUniW =
      function
      | (r, Next (L)) -> occurUniW (r, L)
      | (r, LVar r') ->
          if r = r' then raise (Unify "Level circularity") else ()
      | (r, _) -> ()
    let rec occurUni (r, L) = occurUniW (r, (whnfUni L))
    (* matchUni (l1, l2) = ()
       iff l1<I> = l2<I> for some most general instantiation I
       effect: applies I
       otherwise raises Unify *)
    let rec matchUniW =
      function
      | (Level i1, Level i2) ->
          if i1 = i2 then () else raise (Unify "Level clash")
      | (Level i1, Next (L2)) ->
          if i1 > 1
          then matchUniW ((Level (i1 - 1)), L2)
          else raise (Unify "Level clash")
      | (Next (L1), Level i2) ->
          if i2 > 1
          then matchUniW (L1, (Level (i2 - 1)))
          else raise (Unify "Level clash")
      | (Next (L1), Next (L2)) -> matchUniW (L1, L2)
      | (LVar r1, (LVar r2 as L2)) -> if r1 = r2 then () else (:=) r1 SOME L2
      | (LVar r1, L2) -> (occurUniW (r1, L2); (:=) r1 SOME L2)
      | (L1, LVar r2) -> (occurUniW (r2, L1); (:=) r2 SOME L1)
    let rec matchUni (L1, L2) = matchUniW ((whnfUni L1), (whnfUni L2))
    (* occur (r, u) = ()
       iff r does not occur in u,
       otherwise raises Unify *)
    let rec occurW =
      function
      | (r, Arrow (V1, V2)) -> (occur (r, V1); occur (r, V2))
      | (r, CVar r') ->
          if r = r'
          then raise (Unify "Type/kind variable occurrence")
          else ()
      | (r, _) -> ()
    let rec occur (r, U) = occurW (r, (whnf U))
    (* match (u1, u2) = ()
       iff u1<I> = u2<I> : v for some most general instantiation I
       effect: applies I
       otherwise raises Unify *)
    let rec matchW =
      function
      | (Uni (L1), Uni (L2)) -> matchUni (L1, L2)
      | ((Const (H1) as V1), (Const (H2) as V2)) ->
          (((match (H1, H2) with
             | (Const c1, Const c2) ->
                 if c1 = c2
                 then ()
                 else raise (Unify "Type/kind constant clash")
             | (Def d1, Def d2) ->
                 if d1 = d2
                 then ()
                 else match__ ((constDefApx d1), (constDefApx d2))
             | (Def d1, _) -> match__ ((constDefApx d1), V2)
             | (_, Def d2) -> match__ (V1, (constDefApx d2))
             | (NSDef d1, NSDef d2) ->
                 if d1 = d2
                 then ()
                 else match__ ((constDefApx d1), (constDefApx d2))
             | (NSDef d1, _) -> match__ ((constDefApx d1), V2)
             | (_, NSDef d2) -> match__ (V1, (constDefApx d2))))
          (* strictness is irrelevant to matching on approximate types *)
          (* others cannot occur by invariant *))
      | (Arrow (V1, V2), Arrow (V3, V4)) ->
          ((try match__ (V1, V3) with | e -> (match__ (V2, V4); raise e));
           match__ (V2, V4))
      | ((Arrow _ as V1), Const (Def d2)) -> match__ (V1, (constDefApx d2))
      | (Const (Def d1), (Arrow _ as V2)) -> match__ ((constDefApx d1), V2)
      | ((Arrow _ as V1), Const (NSDef d2)) -> match__ (V1, (constDefApx d2))
      | (Const (NSDef d1), (Arrow _ as V2)) -> match__ ((constDefApx d1), V2)
      | (CVar r1, (CVar r2 as U2)) -> if r1 = r2 then () else (:=) r1 SOME U2
      | (CVar r1, U2) -> (occurW (r1, U2); (:=) r1 SOME U2)
      | (U1, CVar r2) -> (occurW (r2, U1); (:=) r2 SOME U1)
      | _ -> raise (Unify "Type/kind expression clash")
    let rec match__ (U1, U2) = matchW ((whnf U1), (whnf U2))
    let rec matchable (U1, U2) =
      try match__ (U1, U2); true__ with | Unify _ -> false__
    let rec makeGroundUni =
      function
      | Level _ -> false__
      | Next (L) -> makeGroundUni L
      | LVar (ref (SOME (L))) -> makeGroundUni L
      | LVar (ref (NONE) as r) -> ((:=) r SOME (Level 1); true__)
  end ;;
