
(* Internal Syntax *)
(* Author: Frank Pfenning, Carsten Schuermann *)
(* Modified: Roberto Virga *)
module type INTSYN  =
  sig
    type nonrec cid = int
    (* Constant identifier        *)
    type nonrec mid = int
    (* Structure identifier       *)
    type nonrec csid = int
    (* CS module identifier       *)
    type nonrec __FgnExp = exn
    (* foreign expression representation *)
    exception UnexpectedFgnExp of __FgnExp 
    (* raised by a constraint solver
					   if passed an incorrect arg *)
    type nonrec __FgnCnstr = exn
    (* foreign constraint representation *)
    exception UnexpectedFgnCnstr of __FgnCnstr 
    (* raised by a constraint solver
                                           if passed an incorrect arg *)
    (* Contexts *)
    type 'a __Ctx =
      | Null 
      | Decl of ('a __Ctx * 'a) 
    (*     | __g, __d                 *)
    val ctxPop : 'a __Ctx -> 'a __Ctx
    val ctxLookup : ('a __Ctx * int) -> 'a
    val ctxLength : 'a __Ctx -> int
    type __Depend =
      | No 
      | Maybe 
      | Meta 
    (*     | Meta                 *)
    (* expressions *)
    type __Uni =
      | Kind 
      | Type 
    (*     | Type                 *)
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
      | FgnExp of (csid * __FgnExp) 
      | NVar of int 
    and __Head =
      | BVar of int 
      | Const of cid 
      | Proj of (__Block * int) 
      | Skonst of cid 
      | Def of cid 
      | NSDef of cid 
      | FVar of (string * __Exp * __Sub) 
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
      | Dec of (string option * __Exp) 
      | BDec of (string option * (cid * __Sub)) 
      | ADec of (string option * int) 
      | NDec of string option 
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
    (* a : K : kind  or           *)
    (* a = A : K : kind  or       *)
    (* d = M : A : type           *)
    (* a = A : K : kind  or       *)
    (* %block l : Some G1 PI G2   *)
    (* sa: K : kind  or           *)
    (* head(expand(d)), height, head(expand[height](d)) *)
    (* None means expands to {x:A}B *)
    type __StrDec =
      | StrDec of (string * mid option) 
    (* Form of constant declaration *)
    type __ConDecForm =
      | FromCS 
      | Ordinary 
      | Clause 
    (* %clause declaration *)
    (* Type abbreviations *)
    type nonrec dctx = __Dec __Ctx
    (* __g = . | __g,__d                *)
    type nonrec eclo = (__Exp * __Sub)
    (* __Us = __u[s]                  *)
    type nonrec bclo = (__Block * __Sub)
    (* __Bs = B[s]                  *)
    type nonrec cnstr = __Cnstr ref
    exception Error of string 
    (* raised if out of space     *)
    (* standard operations on foreign expressions *)
    module FgnExpStd :
    sig
      (* Contexts                   *)
      (* __g ::= .                    *)
      (* Dependency information     *)
      (* P ::= No                   *)
      (*     | Maybe                *)
      (* Universes:                 *)
      (* __l ::= Kind                 *)
      (* Expressions:               *)
      (* __u ::= __l                    *)
      (*     | Pi (__d, P). __v         *)
      (*     | H @ S                *)
      (*     | __u @ S                *)
      (*     | lam D. __u             *)
      (*     | x<I> : __g|-__v, Cnstr   *)
      (*     | __u[s]                 *)
      (*     | A<I>                 *)
      (*     | (foreign expression) *)
      (*     | n (linear, 
                                               fully applied variable
                                               used in indexing       *)
      (* Head:                      *)
      (* H ::= k                    *)
      (*     | c                    *)
      (*     | #k(b)                *)
      (*     | c#                   *)
      (*     | d (strict)           *)
      (*     | d (non strict)       *)
      (*     | F[s]                 *)
      (*     | (foreign constant)   *)
      (* Spines:                    *)
      (* S ::= Nil                  *)
      (*     | __u ; S                *)
      (*     | S[s]                 *)
      (* Explicit substitutions:    *)
      (* s ::= ^n                   *)
      (*     | Ft.s                 *)
      (* Fronts:                    *)
      (* Ft ::= k                   *)
      (*     | __u                    *)
      (*     | __u                    *)
      (*     | _x                   *)
      (*     | _                    *)
      (* Declarations:              *)
      (* __d ::= x:__v                  *)
      (*     | v:l[s]               *)
      (*     | v[^-d]               *)
      (* Blocks:                    *)
      (* b ::= v                    *)
      (*     | __l(l[^k],t)           *)
      (*     | __U1, ..., Un          *)
      (* It would be better to consider having projections count
     like substitutions, then we could have Inst of Sub here, 
     which would simplify a lot of things.  

     I suggest however to wait until the next big overhaul 
     of the system -- cs *)
      (*  | BClo of Block * Sub                      | b[s]                 *)
      (* constraints *)
      (* Constraint:                *)
      (* Cnstr ::= solved           *)
      (*         | __g|-(__U1 == __U2)    *)
      (*         | (foreign)        *)
      (* Status of a constant:      *)
      (*   inert                    *)
      (*   acts as constraint       *)
      (*   is converted to foreign  *)
      (* Result of foreign unify    *)
      (* succeed with a list of residual operations *)
      (* perform the assignment __g |- x = __u [ss] *)
      (* delay cnstr, associating it with all the rigid EVars in __u  *)
      (* Global signature *)
      (* Constant declaration       *)
      (* c : A : type               *)
      (* Ancestor info for d or a   *)
      (* d = M : A : type           *)
      (* %block l = (l1 | ... | ln) *)
      (* sc: A : type               *)
      (* Ancestor of d or a         *)
      (* Structure declaration      *)
      (* from constraint domain *)
      (* ordinary declaration *)
      (* convert to internal syntax *)
      module ToInternal : FGN_OPN
      (* apply function to subterms *)
      module Map : FGN_OPN
      (* apply function to subterms, for effect *)
      module App : FGN_OPN
      (* test for equality *)
      module EqualTo : FGN_OPN
      (* unify with another term *)
      module UnifyWith : FGN_OPN
      (* fold a function over the subterms *)
      val fold : (csid * __FgnExp) -> ((__Exp * 'a) -> 'a) -> 'a -> 'a
    end
    (* standard operations on foreign constraints *)
    module FgnCnstrStd :
    sig
      (* convert to internal syntax *)
      module ToInternal : FGN_OPN
      (* awake *)
      module Awake : FGN_OPN
      (* simplify *)
      module Simplify : FGN_OPN
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
    (* type of c or d             *)
    val constDef : cid -> __Exp
    (* definition of d            *)
    val constImp : cid -> int
    val constStatus : cid -> __Status
    val constUni : cid -> __Uni
    val constBlock : cid -> (dctx * __Dec list)
    (* Declaration Contexts *)
    val ctxDec : (dctx * int) -> __Dec
    (* get variable declaration   *)
    val blockDec : (dctx * __Block * int) -> __Dec
    (* Explicit substitutions *)
    val id : __Sub
    (* id                         *)
    val shift : __Sub
    (* ^                          *)
    val invShift : __Sub
    (* ^-1                        *)
    val bvarSub : (int * __Sub) -> __Front
    (* k[s]                       *)
    val frontSub : (__Front * __Sub) -> __Front
    (* H[s]                       *)
    val decSub : (__Dec * __Sub) -> __Dec
    (* x:__v[s]                     *)
    val blockSub : (__Block * __Sub) -> __Block
    (* B[s]                       *)
    val comp : (__Sub * __Sub) -> __Sub
    (* s o s'                     *)
    val dot1 : __Sub -> __Sub
    (* 1 . (s o ^)                *)
    val invDot1 : __Sub -> __Sub
    (* (^ o s) o ^-1)             *)
    (* EVar related functions *)
    val newEVar : (dctx * __Exp) -> __Exp
    (* creates x:__g|-__v, []         *)
    val newAVar : unit -> __Exp
    (* creates A (bare)           *)
    val newTypeVar : dctx -> __Exp
    (* creates x:__g|-type, []      *)
    val newLVar : (__Sub * (cid * __Sub)) -> __Block
    (* creates B:(l[^k],t)        *)
    (* Definition related functions *)
    val headOpt : __Exp -> __Head option
    val ancestor : __Exp -> __Ancestor
    val defAncestor : cid -> __Ancestor
    (* Type related functions *)
    (* Not expanding type definitions *)
    val targetHeadOpt : __Exp -> __Head option
    (* target type family or None *)
    val targetHead : __Exp -> __Head
    (* target type family         *)
    (* Expanding type definitions *)
    val targetFamOpt : __Exp -> cid option
    (* target type family or None *)
    val targetFam : __Exp -> cid
    (* target type family         *)
    (* Used in Flit *)
    val rename : (cid * string) -> unit
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
    let rec ctxPop (Decl (__g, __d)) = __g
    exception Error of string 
    let rec ctxLookup =
      function
      | (Decl (__g', __d), 1) -> __d
      | (Decl (__g', _), k') -> ctxLookup (__g', (k' - 1))
    let rec ctxLength (__g) =
      let rec ctxLength' =
        function
        | (Null, n) -> n
        | (Decl (__g, _), n) -> ctxLength' (__g, (n + 1)) in
      ctxLength' (__g, 0)
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
          let rec g (__u) = (:=) r f (__u, (!r)) in App.apply csfe g; !r
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
      | ConDec (_, _, _, _, __v, _) -> __v
      | ConDef (_, _, _, _, __v, _, _) -> __v
      | AbbrevDef (_, _, _, _, __v, _) -> __v
      | SkoDec (_, _, _, __v, _) -> __v
    let rec conDecBlock (BlockDec (_, _, Gsome, Lpi)) = (Gsome, Lpi)
    let rec conDecUni =
      function
      | ConDec (_, _, _, _, _, __l) -> __l
      | ConDef (_, _, _, _, _, __l, _) -> __l
      | AbbrevDef (_, _, _, _, _, __l) -> __l
      | SkoDec (_, _, _, _, __l) -> __l
    let rec strDecName (StrDec (name, _)) = name
    let rec strDecParent (StrDec (_, parent)) = parent
    let maxCid = Global.maxCid
    let dummyEntry = ConDec ("", None, 0, Normal, (Uni Kind), Kind)
    let sgnArray =
      (Array.array ((maxCid + 1), dummyEntry) : __ConDec Array.array)
    let nextCid = ref 0
    let maxMid = Global.maxMid
    let sgnStructArray =
      (Array.array ((maxMid + 1), (StrDec ("", None))) : __StrDec Array.array)
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
      let rec sgnApp' cid =
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
      | ConDef (_, _, _, __u, _, _, _) -> __u
      | AbbrevDef (_, _, _, __u, _, _) -> __u
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
      | (LVar (ref (Some (B)), sk, _), s) -> blockSub (B, (comp (sk, s)))
      | (LVar ((ref (None) as r), sk, (l, t)), s) ->
          LVar (r, (comp (sk, s)), (l, t))
      | ((Inst (ULs) as __l), s') ->
          Inst (map (function | __u -> EClo (__u, s')) ULs)
    let rec frontSub =
      function
      | (Idx n, s) -> bvarSub (n, s)
      | (Exp (__u), s) -> Exp (EClo (__u, s))
      | (Undef, s) -> Undef
      | (Block (B), s) -> Block (blockSub (B, s))
    let rec decSub =
      function
      | (Dec (x, __v), s) -> Dec (x, (EClo (__v, s)))
      | (NDec x, s) -> NDec x
      | (BDec (n, (l, t)), s) -> BDec (n, (l, (comp (t, s))))
    let rec dot1 =
      function | Shift 0 as s -> s | s -> Dot ((Idx 1), (comp (s, shift)))
    let rec invDot1 s = comp ((comp (shift, s)), invShift)
    let rec ctxDec (__g, k) =
      let rec ctxDec' =
        function
        | (Decl (__g', Dec (x, __v')), 1) -> Dec (x, (EClo (__v', (Shift k))))
        | (Decl (__g', BDec (n, (l, s))), 1) ->
            BDec (n, (l, (comp (s, (Shift k)))))
        | (Decl (__g', _), k') -> ctxDec' (__g', (k' - 1)) in
      ctxDec' (__g, k)
    let rec blockDec (__g, (Bidx k as v), i) =
      let BDec (_, (l, s)) = ctxDec (__g, k) in
      let (Gsome, Lblock) = conDecBlock (sgnLookup l) in
      let rec blockDec' =
        function
        | (t, (__d)::__l, 1, j) -> decSub (__d, t)
        | (t, _::__l, n, j) ->
            blockDec'
              ((Dot ((Exp (Root ((Proj (v, j)), Nil))), t)), __l, (n - 1),
                (j + 1)) in
      blockDec' (s, Lblock, i, 1)
    let rec newEVar (__g, __v) = EVar ((ref None), __g, __v, (ref nil))
    let rec newAVar () = AVar (ref None)
    let rec newTypeVar (__g) = EVar ((ref None), __g, (Uni Type), (ref nil))
    let rec newLVar (sk, (cid, t)) = LVar ((ref None), sk, (cid, t))
    let rec headOpt =
      function | Root (H, _) -> Some H | Lam (_, __u) -> headOpt __u | _ -> None
    let rec ancestor' =
      function
      | None -> Anc (None, 0, None)
      | Some (Const c) -> Anc ((Some c), 1, (Some c))
      | Some (Def d) ->
          (match sgnLookup d with
           | ConDef (_, _, _, _, _, _, Anc (_, height, cOpt)) ->
               Anc ((Some d), (height + 1), cOpt))
      | Some _ -> Anc (None, 0, None)
    let rec ancestor (__u) = ancestor' (headOpt __u)
    let rec defAncestor d =
      match sgnLookup d with | ConDef (_, _, _, _, _, _, anc) -> anc
    let rec targetHeadOpt =
      function
      | Root (H, _) -> Some H
      | Pi (_, __v) -> targetHeadOpt __v
      | Redex (__v, S) -> targetHeadOpt __v
      | Lam (_, __v) -> targetHeadOpt __v
      | EVar (ref (Some (__v)), _, _, _) -> targetHeadOpt __v
      | EClo (__v, s) -> targetHeadOpt __v
      | _ -> None
    let rec targetHead (A) = valOf (targetHeadOpt A)
    let rec targetFamOpt =
      function
      | Root (Const cid, _) -> Some cid
      | Pi (_, __v) -> targetFamOpt __v
      | Root (Def cid, _) -> targetFamOpt (constDef cid)
      | Redex (__v, S) -> targetFamOpt __v
      | Lam (_, __v) -> targetFamOpt __v
      | EVar (ref (Some (__v)), _, _, _) -> targetFamOpt __v
      | EClo (__v, s) -> targetFamOpt __v
      | _ -> None
    let rec targetFam (A) = valOf (targetFamOpt A)
  end  (* Internal Syntax *)
(* Author: Frank Pfenning, Carsten Schuermann *)
(* Modified: Roberto Virga *)
(* Constant identifier        *)
(* Variable name              *)
(* Structure identifier       *)
(* CS module identifier       *)
(* Contexts *)
(* Contexts                   *)
(* __g ::= .                    *)
(*     | __g, __d                 *)
(* ctxPop (__g) => __g'
     Invariant: __g = __g',__d
  *)
(* raised if out of space     *)
(* ctxLookup (__g, k) = __d, kth declaration in __g from right to left
     Invariant: 1 <= k <= |__g|, where |__g| is length of __g
  *)
(*    | ctxLookup (Null, k') = (print ("Looking up k' = " ^ Int.toString k' ^ "\n"); raise Error "Out of Bounce\n")*)
(* ctxLookup (Null, k')  should not occur by invariant *)
(* ctxLength __g = |__g|, the number of declarations in __g *)
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
(* Expressions *)
(* Universes:                 *)
(* __l ::= Kind                 *)
(*     | Type                 *)
(* Expressions:               *)
(* __u ::= __l                    *)
(*     | bPi (__d, P). __v         *)
(*     | C @ S                *)
(*     | __u @ S                *)
(*     | lam D. __u             *)
(*     | x<I> : __g|-__v, Cnstr   *)
(*     | __u[s]                 *)
(*     | A<I>                 *)
(*     | n (linear, fully applied) *)
(* grafting variable *)
(*     | (foreign expression) *)
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
(*     | __u ; S                *)
(*     | S[s]                 *)
(* Explicit substitutions:    *)
(* s ::= ^n                   *)
(*     | Ft.s                 *)
(* Fronts:                    *)
(* Ft ::= k                   *)
(*     | __u                    *)
(*     | __u (assignable)       *)
(*     | _x                   *)
(*     | _                    *)
(* Declarations:              *)
(* __d ::= x:__v                  *)
(*     | v:l[s]               *)
(*     | v[^-d]               *)
(* Blocks:                    *)
(* b ::= v                    *)
(*     | __l(l[^k],t)           *)
(*     | u1, ..., Un          *)
(* Constraints *)
(* Constraint:                *)
(* Cnstr ::= solved           *)
(*         | __g|-(__U1 == __U2)    *)
(*         | (foreign)        *)
(* Status of a constant:      *)
(*   inert                    *)
(*   acts as constraint       *)
(*   is converted to foreign  *)
(* Result of foreign unify    *)
(* succeed with a list of residual operations *)
(* Residual of foreign unify  *)
(* perform the assignment __g |- x = __u [ss] *)
(* delay cnstr, associating it with all the rigid EVars in __u  *)
(* Global signature *)
(* Constant declaration       *)
(* a : K : kind  or           *)
(* c : A : type               *)
(* a = A : K : kind  or       *)
(* d = M : A : type           *)
(* Ancestor info for d or a   *)
(* a = A : K : kind  or       *)
(* d = M : A : type           *)
(* %block l : Some G1 PI G2   *)
(* %block l = (l1 | ... | ln) *)
(* sa: K : kind  or           *)
(* sc: A : type               *)
(* Ancestor of d or a         *)
(* head(expand(d)), height, head(expand[height](d)) *)
(* None means expands to {x:A}B *)
(* Structure declaration      *)
(* Form of constant declaration *)
(* from constraint domain *)
(* ordinary declaration *)
(* %clause declaration *)
(* Type abbreviations *)
(* __g = . | __g,__d                *)
(* __Us = __u[s]                  *)
(* __Bs = B[s]                  *)
(*  exception Error of string              raised if out of space     *)
(* conDecImp (CD) = k

     Invariant:
     If   CD is either a declaration, definition, abbreviation, or
          a Skolem constant
     then k stands for the number of implicit elements.
  *)
(* watch out -- carsten *)
(* conDecType (CD) =  __v

     Invariant:
     If   CD is either a declaration, definition, abbreviation, or
          a Skolem constant
     then __v is the respective type
  *)
(* conDecBlock (CD) =  (Gsome, Lpi)

     Invariant:
     If   CD is block definition
     then Gsome is the context of some variables
     and  Lpi is the list of pi variables
  *)
(* conDecUni (CD) =  __l

     Invariant:
     If   CD is either a declaration, definition, abbreviation, or
          a Skolem constant
     then __l is the respective universe
  *)
(* Invariants *)
(* Constant declarations are all well-typed *)
(* Constant declarations are stored in beta-normal form *)
(* All definitions are strict in all their arguments *)
(* If Const(cid) is valid, then sgnArray(cid) = ConDec _ *)
(* If Def(cid) is valid, then sgnArray(cid) = ConDef _ *)
(* Fri Dec 20 12:04:24 2002 -fp *)
(* this circumvents a space leak *)
(* 0 <= cid < !nextCid *)
(* 0 <= mid < !nextMid *)
(* A hack used in Flit - jcreed 6/05 *)
(* Explicit Substitutions *)
(* id = ^0

     Invariant:
     __g |- id : __g        id is patsub
  *)
(* shift = ^1

     Invariant:
     __g, __v |- ^ : __g       ^ is patsub
  *)
(* invShift = ^-1 = _.^0
     Invariant:
     __g |- ^-1 : __g, __v     ^-1 is patsub
  *)
(* comp (s1, s2) = s'

     Invariant:
     If   __g'  |- s1 : __g
     and  __g'' |- s2 : __g'
     then s'  = s1 o s2
     and  __g'' |- s1 o s2 : __g

     If  s1, s2 patsub
     then s' patsub
   *)
(* next line is an optimization *)
(* roughly 15% on standard suite for Twelf 1.1 *)
(* Sat Feb 14 10:15:16 1998 -fp *)
(* bvarSub (n, s) = Ft'

      Invariant:
     If    __g |- s : __g'    __g' |- n : __v
     then  Ft' = Ftn         if  s = Ft1 .. Ftn .. ^k
       or  Ft' = ^(n+k)     if  s = Ft1 .. Ftm ^k   and m<n
     and   __g |- Ft' : __v [s]
  *)
(* blockSub (B, s) = B'

     Invariant:
     If   __g |- s : __g'
     and  __g' |- B block
     then __g |- B' block
     and  B [s] == B'
  *)
(* in front of substitutions, first case is irrelevant *)
(* Sun Dec  2 11:56:41 2001 -fp *)
(* -fp Sun Dec  1 21:18:30 2002 *)
(* --cs Sun Dec  1 11:25:41 2002 *)
(* Since always . |- t : Gsome, discard s *)
(* where is this needed? *)
(* Thu Dec  6 20:30:26 2001 -fp !!! *)
(* was:
        LVar (r, comp(sk, s), (l, comp (t, s)))
        July 22, 2010 -fp -cs
       *)
(* comp(^k, s) = ^k' for some k' by invariant *)
(* this should be right but somebody should verify *)
(* frontSub (Ft, s) = Ft'

     Invariant:
     If   __g |- s : __g'     __g' |- Ft : __v
     then Ft' = Ft [s]
     and  __g |- Ft' : __v [s]

     NOTE: EClo (__u, s) might be undefined, so if this is ever
     computed eagerly, we must introduce an "Undefined" exception,
     raise it in whnf and handle it here so Exp (EClo (__u, s)) => Undef
  *)
(* decSub (x:__v, s) = __d'

     Invariant:
     If   __g  |- s : __g'    __g' |- __v : __l
     then __d' = x:__v[s]
     and  __g  |- __v[s] : __l
  *)
(* First line is an optimization suggested by cs *)
(* __d[id] = __d *)
(* Sat Feb 14 18:37:44 1998 -fp *)
(* seems to have no statistically significant effect *)
(* undo for now Sat Feb 14 20:22:29 1998 -fp *)
(*
  fun decSub (__d, Shift(0)) = __d
    | decSub (Dec (x, __v), s) = Dec (x, EClo (__v, s))
  *)
(* dot1 (s) = s'

     Invariant:
     If   __g |- s : __g'
     then s' = 1. (s o ^)
     and  for all __v s.t.  __g' |- __v : __l
          __g, __v[s] |- s' : __g', __v

     If s patsub then s' patsub
  *)
(* first line is an optimization *)
(* roughly 15% on standard suite for Twelf 1.1 *)
(* Sat Feb 14 10:16:16 1998 -fp *)
(* invDot1 (s) = s'
     invDot1 (1. s' o ^) = s'

     Invariant:
     s = 1 . s' o ^
     If __g' |- s' : __g
     (so __g',__v[s] |- s : __g,__v)
  *)
(* Declaration Contexts *)
(* ctxDec (__g, k) = x:__v
     Invariant:
     If      |__g| >= k, where |__g| is size of __g,
     then    __g |- k : __v  and  __g |- __v : __l
  *)
(* ctxDec' (__g'', k') = x:__v
             where __g |- ^(k-k') : __g'', 1 <= k' <= k
           *)
(* ctxDec' (Null, k')  should not occur by invariant *)
(* blockDec (__g, v, i) = __v

     Invariant:
     If   __g (v) = l[s]
     and  Sigma (l) = Some Gsome BLOCK Lblock
     and  __g |- s : Gsome
     then __g |- pi (v, i) : __v
  *)
(* __g |- s : Gsome *)
(* EVar related functions *)
(* newEVar (__g, __v) = newEVarCnstr (__g, __v, nil) *)
(* newAVar __g = new AVar (assignable variable) *)
(* AVars carry no type, ctx, or cnstr *)
(* newTypeVar (__g) = x, x new
     where __g |- x : type
  *)
(* newLVar (l, s) = (l[s]) *)
(* Definition related functions *)
(* headOpt (__u) = Some(H) or None, __u should be strict, normal *)
(* FgnConst possible, BVar impossible by strictness *)
(* ancestor(__u) = ancestor info for d = __u *)
(* defAncestor(d) = ancestor of d, d must be defined *)
(* Type related functions *)
(* targetHeadOpt (__v) = Some(H) or None
     where H is the head of the atomic target type of __v,
     None if __v is a kind or object or have variable type.
     Does not expand type definitions.
  *)
(* should there possibly be a FgnConst case? also targetFamOpt -kw *)
(* Root(Bvar _, _), Root(FVar _, _), Root(FgnConst _, _),
         EVar(ref None,..), Uni, FgnExp _
      *)
(* Root(Skonst _, _) can't occur *)
(* targetHead (A) = a
     as in targetHeadOpt, except __v must be a valid type
  *)
(* targetFamOpt (__v) = Some(cid) or None
     where cid is the type family of the atomic target type of __v,
     None if __v is a kind or object or have variable type.
     Does expand type definitions.
  *)
(* Root(Bvar _, _), Root(FVar _, _), Root(FgnConst _, _),
         EVar(ref None,..), Uni, FgnExp _
      *)
(* Root(Skonst _, _) can't occur *)
(* targetFam (A) = a
     as in targetFamOpt, except __v must be a valid type
  *)
(* functor IntSyn *)
module IntSyn : INTSYN = (Make_IntSyn)(struct module Global = Global end) ;;
