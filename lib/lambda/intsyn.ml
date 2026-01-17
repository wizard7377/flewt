
module type INTSYN  =
  sig
    type nonrec cid =
      ((int)(* Modified: Roberto Virga *)(* Author: Frank Pfenning, Carsten Schuermann *)
      (* Internal Syntax *))
    type nonrec mid =
      ((int)(* Constant identifier        *))
    type nonrec csid =
      ((int)(* Structure identifier       *))
    type nonrec __FgnExp =
      ((exn)(* CS module identifier       *))
    exception UnexpectedFgnExp of
      ((__FgnExp)(* foreign expression representation *)) 
    type nonrec __FgnCnstr =
      ((exn)(* raised by a constraint solver
					   if passed an incorrect arg *))
    exception UnexpectedFgnCnstr of
      ((__FgnCnstr)(* foreign constraint representation *)) 
    type 'a __Ctx =
      | Null 
      | Decl of
      ((('a)(* g ::= .                    *)(* Contexts                   *)
      (* Contexts *)(* raised by a constraint solver
                                           if passed an incorrect arg *))
      __Ctx * 'a) 
    val ctxPop :
      'a __Ctx ->
        (('a)(*     | g, D                 *)) __Ctx
    val ctxLookup : ('a __Ctx * int) -> 'a
    val ctxLength : 'a __Ctx -> int
    type __Depend =
      | No 
      | Maybe 
      | Meta 
    type __Uni =
      | Kind 
      | Type (* expressions *)(*     | Meta                 *)
    (*     | Maybe                *)(* P ::= No                   *)
    (* Dependency information     *)
    type __Exp =
      | Uni of
      ((__Uni)(* Expressions:               *)(*     | Type                 *)
      (* L ::= Kind                 *)(* Universes:                 *))
      
      | Pi of ((((__Dec)(* U ::= L                    *)) *
      __Depend) * __Exp) 
      | Root of (((__Head)(*     | Pi (D, P). V         *))
      * __Spine) 
      | Redex of (((__Exp)(*     | H @ S                *))
      * __Spine) 
      | Lam of (((__Dec)(*     | U @ S                *)) *
      __Exp) 
      | EVar of (((__Exp)(*     | lam D. U             *))
      option ref * __Dec __Ctx * __Exp * __Cnstr ref list ref) 
      | EClo of (((__Exp)(*     | X<I> : g|-V, Cnstr   *)) *
      __Sub) 
      | AVar of ((__Exp)(*     | U[s]                 *))
      option ref 
      | FgnExp of (((csid)(*     | A<I>                 *))
      * __FgnExp) 
      | NVar of ((int)(*     | (foreign expression) *)) 
    and __Head =
      | BVar of
      ((int)(* Head:                      *)(*     | n (linear, 
                                               fully applied variable
                                               used in indexing       *))
      
      | Const of ((cid)(* H ::= k                    *)) 
      | Proj of (((__Block)(*     | c                    *))
      * int) 
      | Skonst of ((cid)(*     | #k(b)                *)) 
      | Def of ((cid)(*     | c#                   *)) 
      | NSDef of ((cid)(*     | d (strict)           *)) 
      | FVar of (((string)(*     | d (non strict)       *))
      * __Exp * __Sub) 
      | FgnConst of
      (((csid)(*     | F[s]                 *)) * __ConDec) 
    and __Spine =
      | Nil 
      | App of
      (((__Exp)(* S ::= Nil                  *)(* Spines:                    *)
      (*     | (foreign constant)   *)) * __Spine) 
      | SClo of (((__Spine)(*     | U ; S                *))
      * __Sub) 
    and __Sub =
      | Shift of
      ((int)(* Explicit substitutions:    *)(*     | S[s]                 *))
      
      | Dot of (((__Front)(* s ::= ^n                   *))
      * __Sub) 
    and __Front =
      | Idx of
      ((int)(* Fronts:                    *)(*     | Ft.s                 *))
      
      | Exp of ((__Exp)(* Ft ::= k                   *)) 
      | Axp of ((__Exp)(*     | U                    *)) 
      | Block of ((__Block)(*     | U                    *))
      
      | Undef 
    and __Dec =
      | Dec of
      (((string)(* Declarations:              *)(*     | _                    *)
      (*     | _x                   *)) option * __Exp) 
      | BDec of (((string)(* D ::= x:V                  *))
      option * (cid * __Sub)) 
      | ADec of (((string)(*     | v:l[s]               *))
      option * int) 
      | NDec of ((string)(*     | v[^-d]               *))
      option 
    and __Block =
      | Bidx of ((int)(* Blocks:                    *)) 
      | LVar of (((__Block)(* b ::= v                    *))
      option ref * __Sub * (cid * __Sub)) 
      | Inst of ((__Exp)(*     | L(l[^k],t)           *))
      list 
    and __Cnstr =
      | Solved 
      | Eqn of
      (((__Dec)(* Cnstr ::= solved           *)(* Constraint:                *)
      (* constraints *)(*  | BClo of Block * Sub                      | b[s]                 *)
      (* It would be better to consider having projections count
     like substitutions, then we could have Inst of Sub here, 
     which would simplify a lot of things.  

     I suggest however to wait until the next big overhaul 
     of the system -- cs *)
      (*     | u1, ..., Un          *)) __Ctx * __Exp *
      __Exp) 
      | FgnCnstr of
      (((csid)(*         | g|-(u1 == u2)    *)) *
      __FgnCnstr) 
    and __Status =
      | Normal 
      | Constraint of
      (((csid)(*   inert                    *)(* Status of a constant:      *)
      (*         | (foreign)        *)) *
      ((__Dec __Ctx * __Spine * int) -> __Exp option)) 
      | Foreign of (((csid)(*   acts as constraint       *))
      * (__Spine -> __Exp)) 
    and __FgnUnify =
      | Succeed of
      ((__FgnUnifyResidual)(* Result of foreign unify    *)
      (*   is converted to foreign  *)) list 
      | Fail 
    and __FgnUnifyResidual =
      | Assign of
      (((__Dec)(* succeed with a list of residual operations *))
      __Ctx * __Exp * __Exp * __Sub) 
      | Delay of
      (((__Exp)(* perform the assignment g |- X = U [ss] *))
      * __Cnstr ref) 
    and __ConDec =
      | ConDec of
      (((string)(* Constant declaration       *)(* Global signature *)
      (* delay cnstr, associating it with all the rigid EVars in U  *))
      * mid option * int * __Status *
      ((__Exp)(* a : K : kind  or           *)) * __Uni) 
      | ConDef of
      (((string)(* c : A : type               *)) * mid
      option * int *
      ((__Exp)(* a = A : K : kind  or       *)) * __Exp *
      __Uni *
      ((__Ancestor)(* d = M : A : type           *))) 
      | AbbrevDef of
      (((string)(* Ancestor info for d or a   *)) * mid
      option * int *
      ((__Exp)(* a = A : K : kind  or       *)) * __Exp *
      __Uni) 
      | BlockDec of
      (((string)(* d = M : A : type           *)) * mid
      option * ((__Dec)(* %block l : SOME G1 PI G2   *))
      __Ctx * __Dec list) 
      | BlockDef of (string * mid option * cid list) 
      | SkoDec of
      (((string)(* %block l = (l1 | ... | ln) *)) * mid
      option * int *
      ((__Exp)(* sa: K : kind  or           *)) * __Uni) 
    and __Ancestor =
      | Anc of
      (((cid)(* Ancestor of d or a         *)(* sc: A : type               *))
      option * int * cid option) 
    type __StrDec =
      | StrDec of
      (((string)(* Structure declaration      *)(* NONE means expands to {x:A}B *)
      (* head(expand(d)), height, head(expand[height](d)) *))
      * mid option) 
    type __ConDecForm =
      | FromCS 
      | Ordinary 
      | Clause (* Form of constant declaration *)
    type nonrec dctx =
      ((__Dec)(* Type abbreviations *)(* %clause declaration *)
        (* ordinary declaration *)(* from constraint domain *))
        __Ctx
    type nonrec eclo =
      (((__Exp)(* g = . | g,D                *)) * __Sub)
    type nonrec bclo =
      (((__Block)(* Us = U[s]                  *)) * __Sub)
    type nonrec cnstr =
      ((__Cnstr)(* Bs = B[s]                  *)) ref
    exception Error of string 
    module FgnExpStd :
    sig
      module ToInternal :
      ((FGN_OPN)(* raised if out of space     *)(* standard operations on foreign expressions *)
      (* convert to internal syntax *))
      module Map :
      ((FGN_OPN)(* apply function to subterms *))
      module App :
      ((FGN_OPN)(* apply function to subterms, for effect *))
      module EqualTo : ((FGN_OPN)(* test for equality *))
      module UnifyWith :
      ((FGN_OPN)(* unify with another term *))
      val fold :
        (csid * __FgnExp) ->
          ((__Exp * 'a) -> 'a) ->
            'a ->
              (('a)(* fold a function over the subterms *))
    end
    module FgnCnstrStd :
    sig
      module ToInternal :
      ((FGN_OPN)(* standard operations on foreign constraints *)
      (* convert to internal syntax *))
      module Awake : ((FGN_OPN)(* awake *))
      module Simplify : ((FGN_OPN)(* simplify *))
    end
    val conDecName : __ConDec -> string
    val conDecParent : __ConDec -> mid option
    val conDecImp : __ConDec -> int
    val conDecStatus : __ConDec -> __Status
    val conDecType : __ConDec -> __Exp
    val conDecBlock : __ConDec -> (dctx * __Dec list)
    val conDecUni : __ConDec -> __Uni
    val strDecName : __StrDec -> string
    val strDecParent : __StrDec -> mid option
    val sgnReset : unit -> unit
    val sgnSize : unit -> (cid * mid)
    val sgnAdd : __ConDec -> cid
    val sgnLookup : cid -> __ConDec
    val sgnApp : (cid -> unit) -> unit
    val sgnStructAdd : __StrDec -> mid
    val sgnStructLookup : mid -> __StrDec
    val constType : cid -> __Exp
    val constDef :
      cid -> ((__Exp)(* type of c or d             *))
    val constImp :
      cid -> ((int)(* definition of d            *))
    val constStatus : cid -> __Status
    val constUni : cid -> __Uni
    val constBlock : cid -> (dctx * __Dec list)
    val ctxDec :
      (dctx * int) -> ((__Dec)(* Declaration Contexts *))
    val blockDec :
      (dctx * __Block * int) ->
        ((__Dec)(* get variable declaration   *))
    val id : ((__Sub)(* Explicit substitutions *))
    val shift : ((__Sub)(* id                         *))
    val invShift : ((__Sub)(* ^                          *))
    val bvarSub :
      (int * __Sub) ->
        ((__Front)(* ^-1                        *))
    val frontSub :
      (__Front * __Sub) ->
        ((__Front)(* k[s]                       *))
    val decSub :
      (__Dec * __Sub) ->
        ((__Dec)(* H[s]                       *))
    val blockSub :
      (__Block * __Sub) ->
        ((__Block)(* x:V[s]                     *))
    val comp :
      (__Sub * __Sub) ->
        ((__Sub)(* B[s]                       *))
    val dot1 :
      __Sub -> ((__Sub)(* s o s'                     *))
    val invDot1 :
      __Sub -> ((__Sub)(* 1 . (s o ^)                *))
    val newEVar :
      (dctx * __Exp) ->
        ((__Exp)(* EVar related functions *)(* (^ o s) o ^-1)             *))
    val newAVar :
      unit -> ((__Exp)(* creates X:g|-V, []         *))
    val newTypeVar :
      dctx -> ((__Exp)(* creates A (bare)           *))
    val newLVar :
      (__Sub * (cid * __Sub)) ->
        ((__Block)(* creates X:g|-type, []      *))
    val headOpt :
      __Exp ->
        ((__Head)(* Definition related functions *)(* creates B:(l[^k],t)        *))
          option
    val ancestor : __Exp -> __Ancestor
    val defAncestor : cid -> __Ancestor
    val targetHeadOpt :
      __Exp ->
        ((__Head)(* Not expanding type definitions *)
          (* Type related functions *)) option
    val targetHead :
      __Exp -> ((__Head)(* target type family or NONE *))
    val targetFamOpt :
      __Exp ->
        ((cid)(* Expanding type definitions *)(* target type family         *))
          option
    val targetFam :
      __Exp -> ((cid)(* target type family or NONE *))
    val rename :
      (cid * string) ->
        ((unit)(* Used in Flit *)(* target type family         *))
  end;;




module IntSyn(IntSyn:sig module Global : GLOBAL end) : INTSYN =
  struct
    type nonrec cid = int
    type nonrec name = string
    type nonrec mid = int
    type nonrec csid = int
    type 'a __Ctx =
      | Null 
      | Decl of ('a __Ctx * 'a) 
    let rec ctxPop (Decl (g, D)) = g
    exception Error of string 
    let rec ctxLookup =
      function
      | (Decl (g', D), 1) -> D
      | (Decl (g', _), k') -> ctxLookup (g', (k' - 1))
    let rec ctxLength (g) =
      let ctxLength' =
        function
        | (Null, n) -> n
        | (Decl (g, _), n) -> ctxLength' (g, (n + 1)) in
      ctxLength' (g, 0)
    type nonrec __FgnExp = exn
    exception UnexpectedFgnExp of __FgnExp 
    type nonrec __FgnCnstr = exn
    exception UnexpectedFgnCnstr of __FgnCnstr 
    type __Depend =
      | No 
      | Maybe 
      | Meta 
    type __Uni =
      | Kind 
      | Type 
    type __Exp =
      | Uni of __Uni 
      | Pi of ((__Dec * __Depend) * __Exp) 
      | Root of (__Head * __Spine) 
      | Redex of (__Exp * __Spine) 
      | Lam of (__Dec * __Exp) 
      | EVar of (__Exp option ref * __Dec __Ctx * __Exp * __Cnstr ref list
      ref) 
      | EClo of (__Exp * __Sub) 
      | AVar of __Exp option ref 
      | NVar of int 
      | FgnExp of (csid * __FgnExp) 
    and __Head =
      | BVar of int 
      | Const of cid 
      | Proj of (__Block * int) 
      | Skonst of cid 
      | Def of cid 
      | NSDef of cid 
      | FVar of (name * __Exp * __Sub) 
      | FgnConst of (csid * __ConDec) 
    and __Spine =
      | Nil 
      | App of (__Exp * __Spine) 
      | SClo of (__Spine * __Sub) 
    and __Sub =
      | Shift of int 
      | Dot of (__Front * __Sub) 
    and __Front =
      | Idx of int 
      | Exp of __Exp 
      | Axp of __Exp 
      | Block of __Block 
      | Undef 
    and __Dec =
      | Dec of (name option * __Exp) 
      | BDec of (name option * (cid * __Sub)) 
      | ADec of (name option * int) 
      | NDec of name option 
    and __Block =
      | Bidx of int 
      | LVar of (__Block option ref * __Sub * (cid * __Sub)) 
      | Inst of __Exp list 
    and __Cnstr =
      | Solved 
      | Eqn of (__Dec __Ctx * __Exp * __Exp) 
      | FgnCnstr of (csid * __FgnCnstr) 
    and __Status =
      | Normal 
      | Constraint of (csid *
      ((__Dec __Ctx * __Spine * int) -> __Exp option)) 
      | Foreign of (csid * (__Spine -> __Exp)) 
    and __FgnUnify =
      | Succeed of __FgnUnifyResidual list 
      | Fail 
    and __FgnUnifyResidual =
      | Assign of (__Dec __Ctx * __Exp * __Exp * __Sub) 
      | Delay of (__Exp * __Cnstr ref) 
    and __ConDec =
      | ConDec of (string * mid option * int * __Status * __Exp * __Uni) 
      | ConDef of (string * mid option * int * __Exp * __Exp * __Uni *
      __Ancestor) 
      | AbbrevDef of (string * mid option * int * __Exp * __Exp * __Uni) 
      | BlockDec of (string * mid option * __Dec __Ctx * __Dec list) 
      | BlockDef of (string * mid option * cid list) 
      | SkoDec of (string * mid option * int * __Exp * __Uni) 
    and __Ancestor =
      | Anc of (cid option * int * cid option) 
    type __StrDec =
      | StrDec of (string * mid option) 
    type __ConDecForm =
      | FromCS 
      | Ordinary 
      | Clause 
    type nonrec dctx = __Dec __Ctx
    type nonrec eclo = (__Exp * __Sub)
    type nonrec bclo = (__Block * __Sub)
    type nonrec cnstr = __Cnstr ref
    module FgnExpStd =
      struct
        module ToInternal =
          (Make_FgnOpnTable)(struct
                               type nonrec arg = unit
                               type nonrec result = __Exp
                             end)
        module Map =
          (Make_FgnOpnTable)(struct
                               type nonrec arg = __Exp -> __Exp
                               type nonrec result = __Exp
                             end)
        module App =
          (Make_FgnOpnTable)(struct
                               type nonrec arg = __Exp -> unit
                               type nonrec result = unit
                             end)
        module EqualTo =
          (Make_FgnOpnTable)(struct
                               type nonrec arg = __Exp
                               type nonrec result = bool
                             end)
        module UnifyWith =
          (Make_FgnOpnTable)(struct
                               type nonrec arg = (__Dec __Ctx * __Exp)
                               type nonrec result = __FgnUnify
                             end)
        let rec fold csfe f b =
          let r = ref b in
          let g (U) = (:=) r f (U, (!r)) in App.apply csfe g; !r
      end
    module FgnCnstrStd =
      struct
        module ToInternal =
          (Make_FgnOpnTable)(struct
                               type nonrec arg = unit
                               type nonrec result =
                                 (__Dec __Ctx * __Exp) list
                             end)
        module Awake =
          (Make_FgnOpnTable)(struct
                               type nonrec arg = unit
                               type nonrec result = bool
                             end)
        module Simplify =
          (Make_FgnOpnTable)(struct
                               type nonrec arg = unit
                               type nonrec result = bool
                             end)
      end
    let rec conDecName =
      function
      | ConDec (name, _, _, _, _, _) -> name
      | ConDef (name, _, _, _, _, _, _) -> name
      | AbbrevDef (name, _, _, _, _, _) -> name
      | SkoDec (name, _, _, _, _) -> name
      | BlockDec (name, _, _, _) -> name
      | BlockDef (name, _, _) -> name
    let rec conDecParent =
      function
      | ConDec (_, parent, _, _, _, _) -> parent
      | ConDef (_, parent, _, _, _, _, _) -> parent
      | AbbrevDef (_, parent, _, _, _, _) -> parent
      | SkoDec (_, parent, _, _, _) -> parent
      | BlockDec (_, parent, _, _) -> parent
      | BlockDef (_, parent, _) -> parent
    let rec conDecImp =
      function
      | ConDec (_, _, i, _, _, _) -> i
      | ConDef (_, _, i, _, _, _, _) -> i
      | AbbrevDef (_, _, i, _, _, _) -> i
      | SkoDec (_, _, i, _, _) -> i
      | BlockDec (_, _, _, _) -> 0
    let rec conDecStatus =
      function | ConDec (_, _, _, status, _, _) -> status | _ -> Normal
    let rec conDecType =
      function
      | ConDec (_, _, _, _, V, _) -> V
      | ConDef (_, _, _, _, V, _, _) -> V
      | AbbrevDef (_, _, _, _, V, _) -> V
      | SkoDec (_, _, _, V, _) -> V
    let rec conDecBlock (BlockDec (_, _, Gsome, Lpi)) = (Gsome, Lpi)
    let rec conDecUni =
      function
      | ConDec (_, _, _, _, _, L) -> L
      | ConDef (_, _, _, _, _, L, _) -> L
      | AbbrevDef (_, _, _, _, _, L) -> L
      | SkoDec (_, _, _, _, L) -> L
    let rec strDecName (StrDec (name, _)) = name
    let rec strDecParent (StrDec (_, parent)) = parent
    let maxCid = Global.maxCid
    let dummyEntry = ConDec ("", NONE, 0, Normal, (Uni Kind), Kind)
    let sgnArray =
      (Array.array ((maxCid + 1), dummyEntry) : __ConDec Array.array)
    let nextCid = ref 0
    let maxMid = Global.maxMid
    let sgnStructArray =
      (Array.array ((maxMid + 1), (StrDec ("", NONE))) : __StrDec Array.array)
    let nextMid = ref 0
    let rec sgnClean i =
      if (!) ((>=) i) nextCid
      then ()
      else (Array.update (sgnArray, i, dummyEntry); sgnClean (i + 1))
    let rec sgnReset () = sgnClean 0; nextCid := 0; nextMid := 0
    let rec sgnSize () = ((!nextCid), (!nextMid))
    let rec sgnAdd conDec =
      let cid = !nextCid in
      if cid > maxCid
      then
        raise
          (Error
             (((^) "Global signature size " Int.toString (maxCid + 1)) ^
                " exceeded"))
      else (Array.update (sgnArray, cid, conDec); (nextCid := cid) + 1; cid)
    let rec sgnLookup cid = Array.sub (sgnArray, cid)
    let rec sgnApp f =
      let sgnApp' cid =
        if (!) ((=) cid) nextCid then () else (f cid; sgnApp' (cid + 1)) in
      sgnApp' 0
    let rec sgnStructAdd strDec =
      let mid = !nextMid in
      if mid > maxMid
      then
        raise
          (Error
             (((^) "Global signature size " Int.toString (maxMid + 1)) ^
                " exceeded"))
      else
        (Array.update (sgnStructArray, mid, strDec);
         (nextMid := mid) + 1;
         mid)
    let rec sgnStructLookup mid = Array.sub (sgnStructArray, mid)
    let rec rename (cid, new__) =
      let newConDec =
        match sgnLookup cid with
        | ConDec (n, m, i, s, e, u) -> ConDec (new__, m, i, s, e, u)
        | ConDef (n, m, i, e, e', u, a) -> ConDef (new__, m, i, e, e', u, a)
        | AbbrevDef (n, m, i, e, e', u) -> AbbrevDef (new__, m, i, e, e', u)
        | BlockDec (n, m, d, d') -> BlockDec (new__, m, d, d')
        | SkoDec (n, m, i, e, u) -> SkoDec (new__, m, i, e, u) in
      Array.update (sgnArray, cid, newConDec)
    let rec constDef d =
      match sgnLookup d with
      | ConDef (_, _, _, U, _, _, _) -> U
      | AbbrevDef (_, _, _, U, _, _) -> U
    let rec constType c = conDecType (sgnLookup c)
    let rec constImp c = conDecImp (sgnLookup c)
    let rec constUni c = conDecUni (sgnLookup c)
    let rec constBlock c = conDecBlock (sgnLookup c)
    let rec constStatus c =
      match sgnLookup c with
      | ConDec (_, _, _, status, _, _) -> status
      | _ -> Normal
    let id = Shift 0
    let shift = Shift 1
    let invShift = Dot (Undef, id)
    let rec comp =
      function
      | (Shift 0, s) -> s
      | (s, Shift 0) -> s
      | (Shift n, Dot (Ft, s)) -> comp ((Shift (n - 1)), s)
      | (Shift n, Shift m) -> Shift (n + m)
      | (Dot (Ft, s), s') -> Dot ((frontSub (Ft, s')), (comp (s, s')))
    let rec bvarSub =
      function
      | (1, Dot (Ft, s)) -> Ft
      | (n, Dot (Ft, s)) -> bvarSub ((n - 1), s)
      | (n, Shift k) -> Idx (n + k)
    let rec blockSub =
      function
      | (Bidx k, s) ->
          (match bvarSub (k, s) with | Idx k' -> Bidx k' | Block (B) -> B)
      | (LVar (ref (SOME (B)), sk, _), s) -> blockSub (B, (comp (sk, s)))
      | (LVar ((ref (NONE) as r), sk, (l, t)), s) ->
          LVar (r, (comp (sk, s)), (l, t))
      | ((Inst (ULs) as L), s') ->
          Inst (map (function | U -> EClo (U, s')) ULs)
    let rec frontSub =
      function
      | (Idx n, s) -> bvarSub (n, s)
      | (Exp (U), s) -> Exp (EClo (U, s))
      | (Undef, s) -> Undef
      | (Block (B), s) -> Block (blockSub (B, s))
    let rec decSub =
      function
      | (Dec (x, V), s) -> Dec (x, (EClo (V, s)))
      | (NDec x, s) -> NDec x
      | (BDec (n, (l, t)), s) -> BDec (n, (l, (comp (t, s))))
    let rec dot1 =
      function | Shift 0 as s -> s | s -> Dot ((Idx 1), (comp (s, shift)))
    let rec invDot1 s = comp ((comp (shift, s)), invShift)
    let rec ctxDec (g, k) =
      let ctxDec' =
        function
        | (Decl (g', Dec (x, V')), 1) -> Dec (x, (EClo (V', (Shift k))))
        | (Decl (g', BDec (n, (l, s))), 1) ->
            BDec (n, (l, (comp (s, (Shift k)))))
        | (Decl (g', _), k') -> ctxDec' (g', (k' - 1)) in
      ctxDec' (g, k)
    let rec blockDec (g, (Bidx k as v), i) =
      let BDec (_, (l, s)) = ctxDec (g, k) in
      let (Gsome, Lblock) = conDecBlock (sgnLookup l) in
      let blockDec' =
        function
        | (t, (D)::L, 1, j) -> decSub (D, t)
        | (t, _::L, n, j) ->
            blockDec'
              ((Dot ((Exp (Root ((Proj (v, j)), Nil))), t)), L, (n - 1),
                (j + 1)) in
      blockDec' (s, Lblock, i, 1)
    let rec newEVar (g, V) = EVar ((ref NONE), g, V, (ref nil))
    let rec newAVar () = AVar (ref NONE)
    let rec newTypeVar (g) = EVar ((ref NONE), g, (Uni Type), (ref nil))
    let rec newLVar (sk, (cid, t)) = LVar ((ref NONE), sk, (cid, t))
    let rec headOpt =
      function | Root (H, _) -> SOME H | Lam (_, U) -> headOpt U | _ -> NONE
    let rec ancestor' =
      function
      | NONE -> Anc (NONE, 0, NONE)
      | SOME (Const c) -> Anc ((SOME c), 1, (SOME c))
      | SOME (Def d) ->
          (match sgnLookup d with
           | ConDef (_, _, _, _, _, _, Anc (_, height, cOpt)) ->
               Anc ((SOME d), (height + 1), cOpt))
      | SOME _ -> Anc (NONE, 0, NONE)
    let rec ancestor (U) = ancestor' (headOpt U)
    let rec defAncestor d =
      match sgnLookup d with | ConDef (_, _, _, _, _, _, anc) -> anc
    let rec targetHeadOpt =
      function
      | Root (H, _) -> SOME H
      | Pi (_, V) -> targetHeadOpt V
      | Redex (V, S) -> targetHeadOpt V
      | Lam (_, V) -> targetHeadOpt V
      | EVar (ref (SOME (V)), _, _, _) -> targetHeadOpt V
      | EClo (V, s) -> targetHeadOpt V
      | _ -> NONE
    let rec targetHead (A) = valOf (targetHeadOpt A)
    let rec targetFamOpt =
      function
      | Root (Const cid, _) -> SOME cid
      | Pi (_, V) -> targetFamOpt V
      | Root (Def cid, _) -> targetFamOpt (constDef cid)
      | Redex (V, S) -> targetFamOpt V
      | Lam (_, V) -> targetFamOpt V
      | EVar (ref (SOME (V)), _, _, _) -> targetFamOpt V
      | EClo (V, s) -> targetFamOpt V
      | _ -> NONE
    let rec targetFam (A) = valOf (targetFamOpt A)
  end 
module IntSyn : INTSYN =
  (Make_IntSyn)(struct
                  module Global =
                    ((Global)(* Internal Syntax *)(* Author: Frank Pfenning, Carsten Schuermann *)
                    (* Modified: Roberto Virga *)(* Constant identifier        *)
                    (* Variable name              *)
                    (* Structure identifier       *)
                    (* CS module identifier       *)
                    (* Contexts *)(* Contexts                   *)
                    (* g ::= .                    *)
                    (*     | g, D                 *)
                    (* ctxPop (g) => g'
     Invariant: g = g',D
  *)
                    (* raised if out of space     *)
                    (* ctxLookup (g, k) = D, kth declaration in g from right to left
     Invariant: 1 <= k <= |g|, where |g| is length of g
  *)
                    (*    | ctxLookup (Null, k') = (print ("Looking up k' = " ^ Int.toString k' ^ "\n"); raise Error "Out of Bounce\n")*)
                    (* ctxLookup (Null, k')  should not occur by invariant *)
                    (* ctxLength g = |g|, the number of declarations in g *)
                    (* foreign expression representation *)
                    (* raised by a constraint solver
                                           if passed an incorrect arg *)
                    (* foreign unification constraint
                                           representation *)
                    (* raised by a constraint solver
                                           if passed an incorrect arg *)
                    (* Dependency information     *)
                    (* P ::= No                   *)
                    (*     | Maybe                *)
                    (*     | Meta                 *)
                    (* Expressions *)(* Universes:                 *)
                    (* L ::= Kind                 *)
                    (*     | Type                 *)
                    (* Expressions:               *)
                    (* U ::= L                    *)
                    (*     | bPi (D, P). V         *)
                    (*     | C @ S                *)
                    (*     | U @ S                *)
                    (*     | lam D. U             *)
                    (*     | X<I> : g|-V, Cnstr   *)
                    (*     | U[s]                 *)
                    (*     | A<I>                 *)
                    (*     | n (linear, fully applied) *)
                    (* grafting variable *)(*     | (foreign expression) *)
                    (* Heads:                     *)
                    (* H ::= k                    *)
                    (*     | c                    *)
                    (*     | #k(b)                *)
                    (*     | c#                   *)
                    (*     | d                    *)
                    (*     | d (non strict)       *)
                    (*     | F[s]                 *)
                    (*     | (foreign constant)   *)
                    (* Spines:                    *)
                    (* S ::= Nil                  *)
                    (*     | U ; S                *)
                    (*     | S[s]                 *)
                    (* Explicit substitutions:    *)
                    (* s ::= ^n                   *)
                    (*     | Ft.s                 *)
                    (* Fronts:                    *)
                    (* Ft ::= k                   *)
                    (*     | U                    *)
                    (*     | U (assignable)       *)
                    (*     | _x                   *)
                    (*     | _                    *)
                    (* Declarations:              *)
                    (* D ::= x:V                  *)
                    (*     | v:l[s]               *)
                    (*     | v[^-d]               *)
                    (* Blocks:                    *)
                    (* b ::= v                    *)
                    (*     | L(l[^k],t)           *)
                    (*     | u1, ..., Un          *)
                    (* Constraints *)(* Constraint:                *)
                    (* Cnstr ::= solved           *)
                    (*         | g|-(u1 == u2)    *)
                    (*         | (foreign)        *)
                    (* Status of a constant:      *)
                    (*   inert                    *)
                    (*   acts as constraint       *)
                    (*   is converted to foreign  *)
                    (* Result of foreign unify    *)
                    (* succeed with a list of residual operations *)
                    (* Residual of foreign unify  *)
                    (* perform the assignment g |- X = U [ss] *)
                    (* delay cnstr, associating it with all the rigid EVars in U  *)
                    (* Global signature *)(* Constant declaration       *)
                    (* a : K : kind  or           *)
                    (* c : A : type               *)
                    (* a = A : K : kind  or       *)
                    (* d = M : A : type           *)
                    (* Ancestor info for d or a   *)
                    (* a = A : K : kind  or       *)
                    (* d = M : A : type           *)
                    (* %block l : SOME G1 PI G2   *)
                    (* %block l = (l1 | ... | ln) *)
                    (* sa: K : kind  or           *)
                    (* sc: A : type               *)
                    (* Ancestor of d or a         *)
                    (* head(expand(d)), height, head(expand[height](d)) *)
                    (* NONE means expands to {x:A}B *)
                    (* Structure declaration      *)
                    (* Form of constant declaration *)
                    (* from constraint domain *)(* ordinary declaration *)
                    (* %clause declaration *)(* Type abbreviations *)
                    (* g = . | g,D                *)
                    (* Us = U[s]                  *)
                    (* Bs = B[s]                  *)
                    (*  exception Error of string              raised if out of space     *)
                    (* conDecImp (CD) = k

     Invariant:
     If   CD is either a declaration, definition, abbreviation, or
          a Skolem constant
     then k stands for the number of implicit elements.
  *)
                    (* watch out -- carsten *)(* conDecType (CD) =  V

     Invariant:
     If   CD is either a declaration, definition, abbreviation, or
          a Skolem constant
     then V is the respective type
  *)
                    (* conDecBlock (CD) =  (Gsome, Lpi)

     Invariant:
     If   CD is block definition
     then Gsome is the context of some variables
     and  Lpi is the list of pi variables
  *)
                    (* conDecUni (CD) =  L

     Invariant:
     If   CD is either a declaration, definition, abbreviation, or
          a Skolem constant
     then L is the respective universe
  *)
                    (* Invariants *)(* Constant declarations are all well-typed *)
                    (* Constant declarations are stored in beta-normal form *)
                    (* All definitions are strict in all their arguments *)
                    (* If Const(cid) is valid, then sgnArray(cid) = ConDec _ *)
                    (* If Def(cid) is valid, then sgnArray(cid) = ConDef _ *)
                    (* Fri Dec 20 12:04:24 2002 -fp *)
                    (* this circumvents a space leak *)
                    (* 0 <= cid < !nextCid *)(* 0 <= mid < !nextMid *)
                    (* A hack used in Flit - jcreed 6/05 *)
                    (* Explicit Substitutions *)(* id = ^0

     Invariant:
     g |- id : g        id is patsub
  *)
                    (* shift = ^1

     Invariant:
     g, V |- ^ : g       ^ is patsub
  *)
                    (* invShift = ^-1 = _.^0
     Invariant:
     g |- ^-1 : g, V     ^-1 is patsub
  *)
                    (* comp (s1, s2) = s'

     Invariant:
     If   g'  |- s1 : g
     and  g'' |- s2 : g'
     then s'  = s1 o s2
     and  g'' |- s1 o s2 : g

     If  s1, s2 patsub
     then s' patsub
   *)
                    (* next line is an optimization *)
                    (* roughly 15% on standard suite for Twelf 1.1 *)
                    (* Sat Feb 14 10:15:16 1998 -fp *)
                    (* bvarSub (n, s) = Ft'

      Invariant:
     If    g |- s : g'    g' |- n : V
     then  Ft' = Ftn         if  s = Ft1 .. Ftn .. ^k
       or  Ft' = ^(n+k)     if  s = Ft1 .. Ftm ^k   and m<n
     and   g |- Ft' : V [s]
  *)
                    (* blockSub (B, s) = B'

     Invariant:
     If   g |- s : g'
     and  g' |- B block
     then g |- B' block
     and  B [s] == B'
  *)
                    (* in front of substitutions, first case is irrelevant *)
                    (* Sun Dec  2 11:56:41 2001 -fp *)
                    (* -fp Sun Dec  1 21:18:30 2002 *)
                    (* --cs Sun Dec  1 11:25:41 2002 *)
                    (* Since always . |- t : Gsome, discard s *)
                    (* where is this needed? *)(* Thu Dec  6 20:30:26 2001 -fp !!! *)
                    (* was:
        LVar (r, comp(sk, s), (l, comp (t, s)))
        July 22, 2010 -fp -cs
       *)
                    (* comp(^k, s) = ^k' for some k' by invariant *)
                    (* this should be right but somebody should verify *)
                    (* frontSub (Ft, s) = Ft'

     Invariant:
     If   g |- s : g'     g' |- Ft : V
     then Ft' = Ft [s]
     and  g |- Ft' : V [s]

     NOTE: EClo (U, s) might be undefined, so if this is ever
     computed eagerly, we must introduce an "Undefined" exception,
     raise it in whnf and handle it here so Exp (EClo (U, s)) => Undef
  *)
                    (* decSub (x:V, s) = D'

     Invariant:
     If   g  |- s : g'    g' |- V : L
     then D' = x:V[s]
     and  g  |- V[s] : L
  *)
                    (* First line is an optimization suggested by cs *)
                    (* D[id] = D *)(* Sat Feb 14 18:37:44 1998 -fp *)
                    (* seems to have no statistically significant effect *)
                    (* undo for now Sat Feb 14 20:22:29 1998 -fp *)
                    (*
  fun decSub (D, Shift(0)) = D
    | decSub (Dec (x, V), s) = Dec (x, EClo (V, s))
  *)
                    (* dot1 (s) = s'

     Invariant:
     If   g |- s : g'
     then s' = 1. (s o ^)
     and  for all V s.t.  g' |- V : L
          g, V[s] |- s' : g', V

     If s patsub then s' patsub
  *)
                    (* first line is an optimization *)
                    (* roughly 15% on standard suite for Twelf 1.1 *)
                    (* Sat Feb 14 10:16:16 1998 -fp *)
                    (* invDot1 (s) = s'
     invDot1 (1. s' o ^) = s'

     Invariant:
     s = 1 . s' o ^
     If g' |- s' : g
     (so g',V[s] |- s : g,V)
  *)
                    (* Declaration Contexts *)(* ctxDec (g, k) = x:V
     Invariant:
     If      |g| >= k, where |g| is size of g,
     then    g |- k : V  and  g |- V : L
  *)
                    (* ctxDec' (g'', k') = x:V
             where g |- ^(k-k') : g'', 1 <= k' <= k
           *)
                    (* ctxDec' (Null, k')  should not occur by invariant *)
                    (* blockDec (g, v, i) = V

     Invariant:
     If   g (v) = l[s]
     and  Sigma (l) = SOME Gsome BLOCK Lblock
     and  g |- s : Gsome
     then g |- pi (v, i) : V
  *)
                    (* g |- s : Gsome *)(* EVar related functions *)
                    (* newEVar (g, V) = newEVarCnstr (g, V, nil) *)
                    (* newAVar g = new AVar (assignable variable) *)
                    (* AVars carry no type, ctx, or cnstr *)
                    (* newTypeVar (g) = X, X new
     where g |- X : type
  *)
                    (* newLVar (l, s) = (l[s]) *)(* Definition related functions *)
                    (* headOpt (U) = SOME(H) or NONE, U should be strict, normal *)
                    (* FgnConst possible, BVar impossible by strictness *)
                    (* ancestor(U) = ancestor info for d = U *)(* defAncestor(d) = ancestor of d, d must be defined *)
                    (* Type related functions *)(* targetHeadOpt (V) = SOME(H) or NONE
     where H is the head of the atomic target type of V,
     NONE if V is a kind or object or have variable type.
     Does not expand type definitions.
  *)
                    (* should there possibly be a FgnConst case? also targetFamOpt -kw *)
                    (* Root(Bvar _, _), Root(FVar _, _), Root(FgnConst _, _),
         EVar(ref NONE,..), Uni, FgnExp _
      *)
                    (* Root(Skonst _, _) can't occur *)
                    (* targetHead (A) = a
     as in targetHeadOpt, except V must be a valid type
  *)
                    (* targetFamOpt (V) = SOME(cid) or NONE
     where cid is the type family of the atomic target type of V,
     NONE if V is a kind or object or have variable type.
     Does expand type definitions.
  *)
                    (* Root(Bvar _, _), Root(FVar _, _), Root(FgnConst _, _),
         EVar(ref NONE,..), Uni, FgnExp _
      *)
                    (* Root(Skonst _, _) can't occur *)
                    (* targetFam (A) = a
     as in targetFamOpt, except V must be a valid type
  *)
                    (* functor IntSyn *))
                end) ;;
