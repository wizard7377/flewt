
module type INTSYN  =
  sig
    type nonrec cid = int
    type nonrec mid = int
    type nonrec csid = int
    type nonrec __FgnExp = exn
    exception UnexpectedFgnExp of __FgnExp 
    type nonrec __FgnCnstr = exn
    exception UnexpectedFgnCnstr of __FgnCnstr 
    type 'a __Ctx =
      | Null 
      | Decl of ('a __Ctx * 'a) 
    val ctxPop : 'a __Ctx -> 'a __Ctx
    val ctxLookup : 'a __Ctx -> int -> 'a
    val ctxLength : 'a __Ctx -> int
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
      (__Dec __Ctx -> __Spine -> int -> __Exp option)) 
      | Foreign of (csid * (__Spine -> __Exp)) 
    and __FgnUnify =
      | Succeed of __FgnUnifyResidual list 
      | Fail 
    and __FgnUnifyResidual =
      | Assign of (__Dec __Ctx * __Exp * __Exp * __Sub) 
      | Delay of (__Exp * __Cnstr ref) 
    and __ConDec =
      | ConDec of
      (((string * mid option * int * __Status * __Exp * __Uni))(* a : K : kind  or           *))
      
      | ConDef of
      (((string * mid option * int * __Exp * __Exp * __Uni * __Ancestor))
      (* d = M : A : type           *)(* a = A : K : kind  or       *))
      
      | AbbrevDef of
      (((string * mid option * int * __Exp * __Exp * __Uni))(* a = A : K : kind  or       *))
      
      | BlockDec of
      (((string * mid option * __Dec __Ctx * __Dec list))(* %block l : Some G1 PI G2   *))
      
      | BlockDef of (string * mid option * cid list) 
      | SkoDec of
      (((string * mid option * int * __Exp * __Uni))(* sa: K : kind  or           *))
      
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
    exception Error of string 
    module FgnExpStd :
    sig
      module ToInternal : FGN_OPN
      module Map : FGN_OPN
      module App : FGN_OPN
      module EqualTo : FGN_OPN
      module UnifyWith : FGN_OPN
      val fold : csid -> __FgnExp -> (__Exp -> 'a -> 'a) -> 'a -> 'a
    end
    module FgnCnstrStd :
    sig
      module ToInternal : FGN_OPN
      module Awake : FGN_OPN
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
    val constDef : cid -> __Exp
    val constImp : cid -> int
    val constStatus : cid -> __Status
    val constUni : cid -> __Uni
    val constBlock : cid -> (dctx * __Dec list)
    val ctxDec : dctx -> int -> __Dec
    val blockDec : dctx -> __Block -> int -> __Dec
    val id : __Sub
    val shift : __Sub
    val invShift : __Sub
    val bvarSub : int -> __Sub -> __Front
    val frontSub : __Front -> __Sub -> __Front
    val decSub : __Dec -> __Sub -> __Dec
    val blockSub : __Block -> __Sub -> __Block
    val comp : __Sub -> __Sub -> __Sub
    val dot1 : __Sub -> __Sub
    val invDot1 : __Sub -> __Sub
    val newEVar : dctx -> __Exp -> __Exp
    val newAVar : unit -> __Exp
    val newTypeVar : dctx -> __Exp
    val newLVar : __Sub -> (cid * __Sub) -> __Block
    val headOpt : __Exp -> __Head option
    val ancestor : __Exp -> __Ancestor
    val defAncestor : cid -> __Ancestor
    val targetHeadOpt : __Exp -> __Head option
    val targetHead : __Exp -> __Head
    val targetFamOpt : __Exp -> cid option
    val targetFam : __Exp -> cid
    val rename : cid -> string -> unit
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
    let rec ctxPop (Decl (__G, __D)) = __G
    exception Error of string 
    let rec ctxLookup __0__ __1__ =
      match (__0__, __1__) with
      | (Decl (__G', __D), 1) -> __D
      | (Decl (__G', _), k') -> ctxLookup (__G', (k' - 1))
    let rec ctxLength (__G) =
      let rec ctxLength' __2__ __3__ =
        match (__2__, __3__) with
        | (Null, n) -> n
        | (Decl (__G, _), n) -> ctxLength' (__G, (n + 1)) in
      ctxLength' (__G, 0)
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
      (__Dec __Ctx -> __Spine -> int -> __Exp option)) 
      | Foreign of (csid * (__Spine -> __Exp)) 
    and __FgnUnify =
      | Succeed of __FgnUnifyResidual list 
      | Fail 
    and __FgnUnifyResidual =
      | Assign of (__Dec __Ctx * __Exp * __Exp * __Sub) 
      | Delay of (__Exp * __Cnstr ref) 
    and __ConDec =
      | ConDec of
      (((string * mid option * int * __Status * __Exp * __Uni))(* a : K : kind  or           *))
      
      | ConDef of
      (((string * mid option * int * __Exp * __Exp * __Uni * __Ancestor))
      (* d = M : A : type           *)(* a = A : K : kind  or       *))
      
      | AbbrevDef of
      (((string * mid option * int * __Exp * __Exp * __Uni))(* a = A : K : kind  or       *))
      
      | BlockDec of
      (((string * mid option * __Dec __Ctx * __Dec list))(* %block l : Some G1 PI G2   *))
      
      | BlockDef of (string * mid option * cid list) 
      | SkoDec of
      (((string * mid option * int * __Exp * __Uni))(* sa: K : kind  or           *))
      
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
          let rec g (__U) = (:=) r f (__U, (!r)) in App.apply csfe g; !r
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
      | ConDec (_, _, _, _, __V, _) -> __V
      | ConDef (_, _, _, _, __V, _, _) -> __V
      | AbbrevDef (_, _, _, _, __V, _) -> __V
      | SkoDec (_, _, _, __V, _) -> __V
    let rec conDecBlock (BlockDec (_, _, Gsome, Lpi)) = (Gsome, Lpi)
    let rec conDecUni =
      function
      | ConDec (_, _, _, _, _, __L) -> __L
      | ConDef (_, _, _, _, _, __L, _) -> __L
      | AbbrevDef (_, _, _, _, _, __L) -> __L
      | SkoDec (_, _, _, _, __L) -> __L
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
    let rec sgnReset () = ((sgnClean 0; nextCid := 0; nextMid := 0)
      (* Fri Dec 20 12:04:24 2002 -fp *)(* this circumvents a space leak *))
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
    let rec rename cid new__ =
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
      | ConDef (_, _, _, __U, _, _, _) -> __U
      | AbbrevDef (_, _, _, __U, _, _) -> __U
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
    let rec comp __4__ __5__ =
      match (__4__, __5__) with
      | (Shift 0, s) -> s
      | (s, Shift 0) -> s
      | (Shift n, Dot (Ft, s)) -> comp ((Shift (n - 1)), s)
      | (Shift n, Shift m) -> Shift (n + m)
      | (Dot (Ft, s), s') -> Dot ((frontSub (Ft, s')), (comp (s, s')))
      (* Sat Feb 14 10:15:16 1998 -fp *)(* roughly 15% on standard suite for Twelf 1.1 *)
      (* next line is an optimization *)
    let rec bvarSub __6__ __7__ =
      match (__6__, __7__) with
      | (1, Dot (Ft, s)) -> Ft
      | (n, Dot (Ft, s)) -> bvarSub ((n - 1), s)
      | (n, Shift k) -> Idx (n + k)
    let rec blockSub __8__ __9__ =
      match (__8__, __9__) with
      | (Bidx k, s) ->
          (match bvarSub (k, s) with | Idx k' -> Bidx k' | Block (__B) -> __B)
      | (LVar ({ contents = Some (__B) }, sk, _), s) ->
          blockSub (__B, (comp (sk, s)))
      | (LVar (({ contents = None } as r), sk, (l, t)), s) ->
          LVar (r, (comp (sk, s)), (l, t))
      | ((Inst (ULs) as L), s') ->
          Inst (map (fun (__U) -> EClo (__U, s')) ULs)(* comp(^k, s) = ^k' for some k' by invariant *)
      (* was:
        LVar (r, comp(sk, s), (l, comp (t, s)))
        July 22, 2010 -fp -cs
       *)
      (* Thu Dec  6 20:30:26 2001 -fp !!! *)(* where is this needed? *)
      (* Since always . |- t : Gsome, discard s *)(* --cs Sun Dec  1 11:25:41 2002 *)
      (* -fp Sun Dec  1 21:18:30 2002 *)
    let rec frontSub __10__ __11__ =
      match (__10__, __11__) with
      | (Idx n, s) -> bvarSub (n, s)
      | (Exp (__U), s) -> Exp (EClo (__U, s))
      | (Undef, s) -> Undef
      | (Block (__B), s) -> Block (blockSub (__B, s))
    let rec decSub __12__ __13__ =
      match (__12__, __13__) with
      | (Dec (x, __V), s) -> Dec (x, (EClo (__V, s)))
      | (NDec x, s) -> NDec x
      | (BDec (n, (l, t)), s) -> BDec (n, (l, (comp (t, s))))
    let rec dot1 =
      function | Shift 0 as s -> s | s -> Dot ((Idx 1), (comp (s, shift)))
    let rec invDot1 s = comp ((comp (shift, s)), invShift)
    let rec ctxDec (__G) k =
      let rec ctxDec' __14__ __15__ =
        match (__14__, __15__) with
        | (Decl (__G', Dec (x, __V')), 1) ->
            Dec (x, (EClo (__V', (Shift k))))
        | (Decl (__G', BDec (n, (l, s))), 1) ->
            BDec (n, (l, (comp (s, (Shift k)))))
        | (Decl (__G', _), k') -> ctxDec' (__G', (k' - 1)) in
      ((ctxDec' (__G, k))
        (* ctxDec' (G'', k') = x:V
             where G |- ^(k-k') : G'', 1 <= k' <= k
           *)
        (* ctxDec' (Null, k')  should not occur by invariant *))
    let rec blockDec (__G) (Bidx k as v) i =
      let BDec (_, (l, s)) = ctxDec (__G, k) in
      let (Gsome, Lblock) = conDecBlock (sgnLookup l) in
      let rec blockDec' __16__ __17__ __18__ __19__ =
        match (__16__, __17__, __18__, __19__) with
        | (t, (__D)::__L, 1, j) -> decSub (__D, t)
        | (t, _::__L, n, j) ->
            blockDec'
              ((Dot ((Exp (Root ((Proj (v, j)), Nil))), t)), __L, (n - 1),
                (j + 1)) in
      ((blockDec' (s, Lblock, i, 1))(* G |- s : Gsome *))
    let rec newEVar (__G) (__V) = EVar ((ref None), __G, __V, (ref nil))
    let rec newAVar () = AVar (ref None)
    let rec newTypeVar (__G) = EVar ((ref None), __G, (Uni Type), (ref nil))
    let rec newLVar sk (cid, t) = LVar ((ref None), sk, (cid, t))
    let rec headOpt =
      function
      | Root (__H, _) -> Some __H
      | Lam (_, __U) -> headOpt __U
      | _ -> None
    let rec ancestor' =
      function
      | None -> Anc (None, 0, None)
      | Some (Const c) -> Anc ((Some c), 1, (Some c))
      | Some (Def d) ->
          (match sgnLookup d with
           | ConDef (_, _, _, _, _, _, Anc (_, height, cOpt)) ->
               Anc ((Some d), (height + 1), cOpt))
      | Some _ -> Anc (None, 0, None)(* FgnConst possible, BVar impossible by strictness *)
    let rec ancestor (__U) = ancestor' (headOpt __U)
    let rec defAncestor d =
      match sgnLookup d with | ConDef (_, _, _, _, _, _, anc) -> anc
    let rec targetHeadOpt =
      function
      | Root (__H, _) -> Some __H
      | Pi (_, __V) -> targetHeadOpt __V
      | Redex (__V, __S) -> targetHeadOpt __V
      | Lam (_, __V) -> targetHeadOpt __V
      | EVar ({ contents = Some (__V) }, _, _, _) -> targetHeadOpt __V
      | EClo (__V, s) -> targetHeadOpt __V
      | _ -> None
    let rec targetHead (__A) = valOf (targetHeadOpt __A)
    let rec targetFamOpt =
      function
      | Root (Const cid, _) -> Some cid
      | Pi (_, __V) -> targetFamOpt __V
      | Root (Def cid, _) -> targetFamOpt (constDef cid)
      | Redex (__V, __S) -> targetFamOpt __V
      | Lam (_, __V) -> targetFamOpt __V
      | EVar ({ contents = Some (__V) }, _, _, _) -> targetFamOpt __V
      | EClo (__V, s) -> targetFamOpt __V
      | _ -> None
    let rec targetFam (__A) = valOf (targetFamOpt __A)
  end 
module IntSyn : INTSYN = (Make_IntSyn)(struct module Global = Global end) ;;
