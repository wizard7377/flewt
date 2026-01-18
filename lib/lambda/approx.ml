
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
       x- undefined

     Note that erasure is always defined on well-typed terms at type
     family or kind level.  Also, if __g |- __U1 = __U2 : __v and __U1,__U2 are at
     type family or kind level, then __U1- and __U2- are defined and
     equal.  We can define the approximate typing judgment
             
       __g |- __u ~:~ __v
                  
     by replacing appeals to equality in the usual presentation of the
     LF type theory with appeals to

       __g |- __U1 = __U2 ~:~ __v,

     which is defined to mean
           __g |- __U1 ~:~ __v  and  __g |- __U2 ~:~ __v  and  __U1- = __U2-
                                                         
     This is a mutual recursion between the two judgments, just as for
     the standard LF type theory.

     There is also a typing judgment on approximate terms

       |- u : v

     defined in the obvious way.  If |- u : v : l then for any
     well-formed __g there are most general __u, __v such that __g |- __u : __v
     and __u- = u and __v- = v.  *)
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
    (* Because approximate type reconstruction uses the pattern __g |- __u
     ~:~ __v ~:~ __l and universe unification on __l, if __u is to be an
     arbitrary input expression, there must be an internal universe
     Hyperkind such that |- Type ~:~ Kind ~:~ Hyperkind.  The
     Hyperkind universe is used only during the approximate phase of
     reconstruction.  The invariants established by
     ReconTerm.filterLevel ensure that Hyperkind will never appear
     elsewhere. *)
    let Type = Level 1
    let Kind = Level 2
    let Hyperkind = Level 3
    let rec newLVar () = LVar (ref None)
    let rec newCVar () = CVar (ref None)
    (* whnfUni (l) = l'
       where l = l' and l' is in whnf *)
    let rec whnfUni =
      function
      | Next (__l) ->
          (match whnfUni __l with | Level i -> Level (i + 1) | __l' -> Next __l')
      | LVar (ref (Some (__l))) -> whnfUni __l
      | __l -> __l
    (* whnf (u) = u'
       where u = u' and u' is in whnf *)
    let rec whnf = function | CVar (ref (Some (__v))) -> whnf __v | __v -> __v
    (* just a little list since these are only for printing errors *)
    type nonrec varEntry = ((__Exp * __Exp * __Uni) * string)
    let (varList : varEntry list ref) = ref nil
    let rec varReset () = varList := nil
    let rec varLookupRef r =
      List.find (function | ((CVar r', _, _), _) -> r = r') (!varList)
    let rec varLookupName name =
      List.find (function | (_, name') -> name = name') (!varList)
    let rec varInsert ((__u, __v, __l), name) =
      (varList := ((__u, __v, __l), name)) :: (!varList)
    exception Ambiguous 
    (* getReplacementName (u, v, l, allowed) = name
         if u : v : l
         and u is a CVar at type family or kind level *)
    let rec getReplacementName ((CVar r as __u), __v, __l, allowed) =
      match varLookupRef r with
      | Some (_, name) -> name
      | None ->
          let _ = if allowed then () else raise Ambiguous in
          let pref = match whnfUni __l with | Level 2 -> "A" | Level 3 -> "K" in
          let rec try__ i =
            let name = ((^) ("%" ^ pref) Int.toString i) ^ "%" in
            match varLookupName name with
            | None -> (varInsert ((__u, __v, __l), name); name)
            | Some _ -> try__ (i + 1) in
          ((try__ 1)(* others impossible by invariant *))
    (* findByReplacementName (name) = (u, v, l)
         if getReplacementName (u, v, l, allowed) = name was already called
         then u : v : l *)
    let rec findByReplacementName name =
      ((match varLookupName name with | Some (UVL, _) -> UVL)
      (* must be in list by invariant *))
    (* converting exact terms to approximate terms *)
    (* uniToApx (__l) = __l- *)
    let rec uniToApx = function | I.Type -> Type | I.Kind -> Kind
    (* expToApx (__u) = (__u-, __v-)
     if __g |- __u : __v
     or __g |- __u ":" __v = "hyperkind" *)
    let rec expToApx =
      function
      | Uni (__l) ->
          let __l' = uniToApx __l in ((Uni __l'), (Uni (whnfUni (Next __l'))))
      | Pi ((Dec (_, V1), _), V2) ->
          let (((V1', _))(* Type *)) = expToApx V1 in
          let (V2', __l') = expToApx V2 in ((Arrow (V1', V2')), __l')
      | Root (FVar (name, _, _), _) ->
          let (__u, __v, __l) = findByReplacementName name in (__u, __v)
      | Root (((H, _))(* Const/Def/NSDef *)) ->
          ((Const H), (Uni Type))
      | Redex (__u, _) -> expToApx __u
      | Lam (_, __u) -> expToApx __u
      | EClo (__u, _) -> expToApx __u(* are we sure Skonst/FgnConst are never types or kinds? *)
      (* must have been created to represent a CVar *)
    (* classToApx (__v) = (__v-, __l-)
     if __g |- __v : __l
     or __g |- __v ":" __l = "hyperkind" *)
    let rec classToApx (__v) =
      let (__v', __l') = expToApx __v in let Uni (__l'') = whnf __l' in (__v', __l'')
    (* exactToApx (__u, __v) = (__u-, __v-)
     if __g |- __u : __v *)
    let rec exactToApx (__u, __v) =
      let (__v', __l') = classToApx __v in
      ((match whnfUni __l' with
        | Level 1 -> (Undefined, __v', __l')
        | _ ->
            let (((__u', _))(* __v' *)) = expToApx __u in
            (__u', __v', __l'))
        (* Type *)(* Kind/Hyperkind *))
    (* constDefApx (d) = __v-
     if |- d = __v : type *)
    let rec constDefApx d =
      match I.sgnLookup d with
      | ConDef (_, _, _, __u, _, _, _) -> let (__v', _) = expToApx __u in __v'
      | AbbrevDef (_, _, _, __u, _, _) ->
          let (((__v', _))(* Uni Type *)) = expToApx __u in __v'
    (* Uni Type *)
    (* converting approximate terms to exact terms *)
    (* apxToUni (__l-) = __l *)
    let rec apxToUniW = function | Level 1 -> I.Type | Level 2 -> I.Kind
    (* others impossible by invariant *)
    let rec apxToUni (__l) = apxToUniW (whnfUni __l)
    (* apxToClass (__g, v, __l-, allowed) = __v
     pre: __l is ground and <= Hyperkind,
          and if __l is Hyperkind then the target classifier
          of v is ground
          v : __l-
     post: __v is most general such that __v- = v and __g |- __v : __l *)
    let rec apxToClassW =
      function
      | (__g, Uni (__l), _, allowed) -> I.Uni (apxToUni __l)
      | (__g, Arrow (V1, V2), __l, allowed) ->
          let V1' = apxToClass (__g, V1, Type, allowed) in
          let __d = I.Dec (None, V1') in
          let V2' = apxToClass ((I.Decl (__g, __d)), V2, __l, allowed) in
          I.Pi ((__d, I.Maybe), V2')
      | (((__g, (CVar r as __v), __l, allowed))(* Type or Kind *))
          ->
          let name = getReplacementName (__v, (Uni __l), (Next __l), allowed) in
          let s = I.Shift (I.ctxLength __g) in
          I.Root ((I.FVar (name, (I.Uni (apxToUni __l)), s)), I.Nil)
      | (((__g, Const (H), __l, allowed))(* Type *)) ->
          I.Root
            (H,
              (Whnf.newSpineVar (__g, ((I.conDecType (headConDec H)), I.id))))
      (* convert undetermined CVars to FVars *)(* also, does the name of the bound variable here matter? *)
      (* this is probably very bad -- it should be possible to infer
         more accurately which pis can be dependent *)
    let rec apxToClass (__g, __v, __l, allowed) =
      apxToClassW (__g, (whnf __v), __l, allowed)
    (* Next __l *)
    (* apxToExact (__g, u, (__v, s), allowed) = __u
     if u : __v-
     and __g' |- __v : __l and __g |- s : __g'
     then __u- = u and __g |- __u : __v[s] and __u is the most general such *)
    let rec apxToExactW =
      function
      | (__g, __u, (Pi ((__d, _), __v), s), allowed) ->
          let __d' = I.decSub (__d, s) in
          I.Lam
            (__d',
              (apxToExact ((I.Decl (__g, __d')), __u, (__v, (I.dot1 s)), allowed)))
      | (__g, __u, (Uni (__l), s), allowed) ->
          apxToClass (__g, __u, (uniToApx __l), allowed)
      | (__g, __u, ((Root (FVar (name, _, _), _), s) as __Vs), allowed) ->
          let (((__v, __l, _))(* Next __l *)) =
            findByReplacementName name in
          let Uni (__l) = whnf __l in
          (((match whnfUni __l with
             | Level 1 -> I.newEVar (__g, (I.EClo __Vs))
             | Level 2 ->
                 let name' =
                   getReplacementName ((whnf __u), __v, (Level 2), allowed) in
                 let __v' = apxToClass (I.Null, __v, (Level 2), allowed) in
                 let s' = I.Shift (I.ctxLength __g) in
                 ((I.Root ((I.FVar (name', __v', s')), I.Nil))
                   (* NOTE: __v' differs from __Vs by a Shift *)
                   (* probably could avoid the following call by removing the
                  substitutions in __Vs instead *))))
            (* __u must be a CVar *))
      | (((__g, __u, __Vs, allowed))(* an atomic type, not Def *))
          -> I.newEVar (__g, (I.EClo __Vs))
    let rec apxToExact (__g, __u, __Vs, allowed) =
      apxToExactW (__g, __u, (Whnf.whnfExpandDef __Vs), allowed)
    (* matching for the approximate language *)
    exception Unify of string 
    (* occurUni (r, l) = ()
       iff r does not occur in l,
       otherwise raises Unify *)
    let rec occurUniW =
      function
      | (r, Next (__l)) -> occurUniW (r, __l)
      | (r, LVar r') ->
          if r = r' then raise (Unify "Level circularity") else ()
      | (r, _) -> ()
    let rec occurUni (r, __l) = occurUniW (r, (whnfUni __l))
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
      | (LVar r1, (LVar r2 as L2)) -> if r1 = r2 then () else (:=) r1 Some L2
      | (LVar r1, L2) -> (occurUniW (r1, L2); (:=) r1 Some L2)
      | (L1, LVar r2) -> (occurUniW (r2, L1); (:=) r2 Some L1)
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
    let rec occur (r, __u) = occurW (r, (whnf __u))
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
      | (CVar r1, (CVar r2 as __U2)) -> if r1 = r2 then () else (:=) r1 Some __U2
      | (CVar r1, __U2) -> (occurW (r1, __U2); (:=) r1 Some __U2)
      | (__U1, CVar r2) -> (occurW (r2, __U1); (:=) r2 Some __U1)
      | _ -> raise (Unify "Type/kind expression clash")
    let rec match__ (__U1, __U2) = matchW ((whnf __U1), (whnf __U2))
    let rec matchable (__U1, __U2) =
      try match__ (__U1, __U2); true__ with | Unify _ -> false__
    let rec makeGroundUni =
      function
      | Level _ -> false__
      | Next (__l) -> makeGroundUni __l
      | LVar (ref (Some (__l))) -> makeGroundUni __l
      | LVar (ref (None) as r) -> ((:=) r Some (Level 1); true__)
  end ;;
