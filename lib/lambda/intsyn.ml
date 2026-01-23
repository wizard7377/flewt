module type INTSYN  =
  sig
    type nonrec cid = int
    type nonrec mid = int
    type nonrec csid = int
    type nonrec fgnExp_ = exn
    exception UnexpectedFgnExp of fgnExp_ 
    type nonrec fgnCnstr_ = exn
    exception UnexpectedFgnCnstr of fgnCnstr_ 
    type 'a ctx_ =
      | Null 
      | Decl of ('a ctx_ * 'a) 
    val ctxPop : 'a ctx_ -> 'a ctx_
    val ctxLookup : ('a ctx_ * int) -> 'a
    val ctxLength : 'a ctx_ -> int
    type depend_ =
      | No 
      | Maybe 
      | Meta 
    type uni_ =
      | Kind 
      | Type 
    type exp_ =
      | Uni of uni_ 
      | Pi of ((dec_ * depend_) * exp_) 
      | Root of (head_ * spine_) 
      | Redex of (exp_ * spine_) 
      | Lam of (dec_ * exp_) 
      | EVar of (exp_ option ref * dec_ ctx_ * exp_ * cnstr_ ref list ref) 
      | EClo of (exp_ * sub_) 
      | AVar of exp_ option ref 
      | FgnExp of (csid * fgnExp_) 
      | NVar of int 
    and head_ =
      | BVar of int 
      | Const of cid 
      | Proj of (block_ * int) 
      | Skonst of cid 
      | Def of cid 
      | NSDef of cid 
      | FVar of (string * exp_ * sub_) 
      | FgnConst of (csid * conDec_) 
    and spine_ =
      | Nil 
      | App of (exp_ * spine_) 
      | SClo of (spine_ * sub_) 
    and sub_ =
      | Shift of int 
      | Dot of (front_ * sub_) 
    and front_ =
      | Idx of int 
      | Exp of exp_ 
      | Axp of exp_ 
      | Block of block_ 
      | Undef 
    and dec_ =
      | Dec of (string option * exp_) 
      | BDec of (string option * (cid * sub_)) 
      | ADec of (string option * int) 
      | NDec of string option 
    and block_ =
      | Bidx of int 
      | LVar of (block_ option ref * sub_ * (cid * sub_)) 
      | Inst of exp_ list 
    and cnstr_ =
      | Solved 
      | Eqn of (dec_ ctx_ * exp_ * exp_) 
      | FgnCnstr of (csid * fgnCnstr_) 
    and status_ =
      | Normal 
      | Constraint of (csid * ((dec_ ctx_ * spine_ * int) -> exp_ option)) 
      | Foreign of (csid * (spine_ -> exp_)) 
    and fgnUnify_ =
      | Succeed of fgnUnifyResidual_ list 
      | Fail 
    and fgnUnifyResidual_ =
      | Assign of (dec_ ctx_ * exp_ * exp_ * sub_) 
      | Delay of (exp_ * cnstr_ ref) 
    and conDec_ =
      | ConDec of
      (((string * mid option * int * status_ * exp_ * uni_))(* a : K : kind  or           *))
      
      | ConDef of
      (((string * mid option * int * exp_ * exp_ * uni_ * ancestor_))
      (* d = M : A : type           *)(* a = A : K : kind  or       *))
      
      | AbbrevDef of
      (((string * mid option * int * exp_ * exp_ * uni_))(* a = A : K : kind  or       *))
      
      | BlockDec of
      (((string * mid option * dec_ ctx_ * dec_ list))(* %block l : SOME G1 PI G2   *))
      
      | BlockDef of (string * mid option * cid list) 
      | SkoDec of
      (((string * mid option * int * exp_ * uni_))(* sa: K : kind  or           *))
      
    and ancestor_ =
      | Anc of (cid option * int * cid option) 
    type strDec_ =
      | StrDec of (string * mid option) 
    type conDecForm_ =
      | FromCS 
      | Ordinary 
      | Clause 
    type nonrec dctx = dec_ ctx_
    type nonrec eclo = (exp_ * sub_)
    type nonrec bclo = (block_ * sub_)
    type nonrec cnstr = cnstr_ ref
    exception Error of string 
    module FgnExpStd :
    sig
      module ToInternal : FGN_OPN
      module Map : FGN_OPN
      module App : FGN_OPN
      module EqualTo : FGN_OPN
      module UnifyWith : FGN_OPN
      val fold : (csid * fgnExp_) -> ((exp_ * 'a) -> 'a) -> 'a -> 'a
    end
    module FgnCnstrStd :
    sig
      module ToInternal : FGN_OPN
      module Awake : FGN_OPN
      module Simplify : FGN_OPN
    end
    val conDecName : conDec_ -> string
    val conDecParent : conDec_ -> mid option
    val conDecImp : conDec_ -> int
    val conDecStatus : conDec_ -> status_
    val conDecType : conDec_ -> exp_
    val conDecBlock : conDec_ -> (dctx * dec_ list)
    val conDecUni : conDec_ -> uni_
    val strDecName : strDec_ -> string
    val strDecParent : strDec_ -> mid option
    val sgnReset : unit -> unit
    val sgnSize : unit -> (cid * mid)
    val sgnAdd : conDec_ -> cid
    val sgnLookup : cid -> conDec_
    val sgnApp : (cid -> unit) -> unit
    val sgnStructAdd : strDec_ -> mid
    val sgnStructLookup : mid -> strDec_
    val constType : cid -> exp_
    val constDef : cid -> exp_
    val constImp : cid -> int
    val constStatus : cid -> status_
    val constUni : cid -> uni_
    val constBlock : cid -> (dctx * dec_ list)
    val ctxDec : (dctx * int) -> dec_
    val blockDec : (dctx * block_ * int) -> dec_
    val id : sub_
    val shift : sub_
    val invShift : sub_
    val bvarSub : (int * sub_) -> front_
    val frontSub : (front_ * sub_) -> front_
    val decSub : (dec_ * sub_) -> dec_
    val blockSub : (block_ * sub_) -> block_
    val comp : (sub_ * sub_) -> sub_
    val dot1 : sub_ -> sub_
    val invDot1 : sub_ -> sub_
    val newEVar : (dctx * exp_) -> exp_
    val newAVar : unit -> exp_
    val newTypeVar : dctx -> exp_
    val newLVar : (sub_ * (cid * sub_)) -> block_
    val headOpt : exp_ -> head_ option
    val ancestor : exp_ -> ancestor_
    val defAncestor : cid -> ancestor_
    val targetHeadOpt : exp_ -> head_ option
    val targetHead : exp_ -> head_
    val targetFamOpt : exp_ -> cid option
    val targetFam : exp_ -> cid
    val rename : (cid * string) -> unit
  end


module IntSyn(IntSyn:sig module Global : GLOBAL end) : INTSYN =
  struct
    type nonrec cid = int
    type nonrec name = string
    type nonrec mid = int
    type nonrec csid = int
    type 'a ctx_ =
      | Null 
      | Decl of ('a ctx_ * 'a) 
    let rec ctxPop (Decl (g_, d_)) = g_
    exception Error of string 
    let rec ctxLookup =
      begin function
      | (Decl (g'_, d_), 1) -> d_
      | (Decl (g'_, _), k') -> ctxLookup (g'_, (k' - 1)) end
    let rec ctxLength (g_) =
      let rec ctxLength' =
        begin function
        | (Null, n) -> n
        | (Decl (g_, _), n) -> ctxLength' (g_, (n + 1)) end in
    ctxLength' (g_, 0)
  type nonrec fgnExp_ = exn
  exception UnexpectedFgnExp of fgnExp_ 
  type nonrec fgnCnstr_ = exn
  exception UnexpectedFgnCnstr of fgnCnstr_ 
  type depend_ =
    | No 
    | Maybe 
    | Meta 
  type uni_ =
    | Kind 
    | Type 
  type exp_ =
    | Uni of uni_ 
    | Pi of ((dec_ * depend_) * exp_) 
    | Root of (head_ * spine_) 
    | Redex of (exp_ * spine_) 
    | Lam of (dec_ * exp_) 
    | EVar of (exp_ option ref * dec_ ctx_ * exp_ * cnstr_ ref list ref) 
    | EClo of (exp_ * sub_) 
    | AVar of exp_ option ref 
    | NVar of int 
    | FgnExp of (csid * fgnExp_) 
  and head_ =
    | BVar of int 
    | Const of cid 
    | Proj of (block_ * int) 
    | Skonst of cid 
    | Def of cid 
    | NSDef of cid 
    | FVar of (name * exp_ * sub_) 
    | FgnConst of (csid * conDec_) 
  and spine_ =
    | Nil 
    | App of (exp_ * spine_) 
    | SClo of (spine_ * sub_) 
  and sub_ =
    | Shift of int 
    | Dot of (front_ * sub_) 
  and front_ =
    | Idx of int 
    | Exp of exp_ 
    | Axp of exp_ 
    | Block of block_ 
    | Undef 
  and dec_ =
    | Dec of (name option * exp_) 
    | BDec of (name option * (cid * sub_)) 
    | ADec of (name option * int) 
    | NDec of name option 
  and block_ =
    | Bidx of int 
    | LVar of (block_ option ref * sub_ * (cid * sub_)) 
    | Inst of exp_ list 
  and cnstr_ =
    | Solved 
    | Eqn of (dec_ ctx_ * exp_ * exp_) 
    | FgnCnstr of (csid * fgnCnstr_) 
  and status_ =
    | Normal 
    | Constraint of (csid * ((dec_ ctx_ * spine_ * int) -> exp_ option)) 
    | Foreign of (csid * (spine_ -> exp_)) 
  and fgnUnify_ =
    | Succeed of fgnUnifyResidual_ list 
    | Fail 
  and fgnUnifyResidual_ =
    | Assign of (dec_ ctx_ * exp_ * exp_ * sub_) 
    | Delay of (exp_ * cnstr_ ref) 
  and conDec_ =
    | ConDec of
    (((string * mid option * int * status_ * exp_ * uni_))(* a : K : kind  or           *))
    
    | ConDef of
    (((string * mid option * int * exp_ * exp_ * uni_ * ancestor_))(* d = M : A : type           *)
    (* a = A : K : kind  or       *)) 
    | AbbrevDef of
    (((string * mid option * int * exp_ * exp_ * uni_))(* a = A : K : kind  or       *))
    
    | BlockDec of
    (((string * mid option * dec_ ctx_ * dec_ list))(* %block l : SOME G1 PI G2   *))
    
    | BlockDef of (string * mid option * cid list) 
    | SkoDec of
    (((string * mid option * int * exp_ * uni_))(* sa: K : kind  or           *))
    
  and ancestor_ =
    | Anc of (cid option * int * cid option) 
  type strDec_ =
    | StrDec of (string * mid option) 
  type conDecForm_ =
    | FromCS 
    | Ordinary 
    | Clause 
  type nonrec dctx = dec_ ctx_
  type nonrec eclo = (exp_ * sub_)
  type nonrec bclo = (block_ * sub_)
  type nonrec cnstr = cnstr_ ref
  module FgnExpStd =
    struct
      module ToInternal =
        (FgnOpnTable)(struct
                             type nonrec arg = unit
                             type nonrec result = exp_
                           end)
      module Map =
        (FgnOpnTable)(struct
                             type nonrec arg = exp_ -> exp_
                             type nonrec result = exp_
                           end)
      module App =
        (FgnOpnTable)(struct
                             type nonrec arg = exp_ -> unit
                             type nonrec result = unit
                           end)
      module EqualTo =
        (FgnOpnTable)(struct
                             type nonrec arg = exp_
                             type nonrec result = bool
                           end)
      module UnifyWith =
        (FgnOpnTable)(struct
                             type nonrec arg = (dec_ ctx_ * exp_)
                             type nonrec result = fgnUnify_
                           end)
      let rec fold csfe f b =
        let r = ref b in
        let rec g (u_) = (:=) r f (u_, !r) in begin App.apply csfe g; !r end
  end
module FgnCnstrStd =
  struct
    module ToInternal =
      (FgnOpnTable)(struct
                           type nonrec arg = unit
                           type nonrec result = (dec_ ctx_ * exp_) list
                         end)
    module Awake =
      (FgnOpnTable)(struct
                           type nonrec arg = unit
                           type nonrec result = bool
                         end)
    module Simplify =
      (FgnOpnTable)(struct
                           type nonrec arg = unit
                           type nonrec result = bool
                         end)
  end
let rec conDecName =
  begin function
  | ConDec (name, _, _, _, _, _) -> name
  | ConDef (name, _, _, _, _, _, _) -> name
  | AbbrevDef (name, _, _, _, _, _) -> name
  | SkoDec (name, _, _, _, _) -> name
  | BlockDec (name, _, _, _) -> name
  | BlockDef (name, _, _) -> name end
let rec conDecParent =
  begin function
  | ConDec (_, parent, _, _, _, _) -> parent
  | ConDef (_, parent, _, _, _, _, _) -> parent
  | AbbrevDef (_, parent, _, _, _, _) -> parent
  | SkoDec (_, parent, _, _, _) -> parent
  | BlockDec (_, parent, _, _) -> parent
  | BlockDef (_, parent, _) -> parent end
let rec conDecImp =
  begin function
  | ConDec (_, _, i, _, _, _) -> i
  | ConDef (_, _, i, _, _, _, _) -> i
  | AbbrevDef (_, _, i, _, _, _) -> i
  | SkoDec (_, _, i, _, _) -> i
  | BlockDec (_, _, _, _) -> 0 end
let rec conDecStatus =
  begin function | ConDec (_, _, _, status, _, _) -> status | _ -> Normal end
let rec conDecType =
  begin function
  | ConDec (_, _, _, _, v_, _) -> v_
  | ConDef (_, _, _, _, v_, _, _) -> v_
  | AbbrevDef (_, _, _, _, v_, _) -> v_
  | SkoDec (_, _, _, v_, _) -> v_ end
let rec conDecBlock (BlockDec (_, _, Gsome, Lpi)) = (Gsome, Lpi)
let rec conDecUni =
  begin function
  | ConDec (_, _, _, _, _, l_) -> l_
  | ConDef (_, _, _, _, _, l_, _) -> l_
  | AbbrevDef (_, _, _, _, _, l_) -> l_
  | SkoDec (_, _, _, _, l_) -> l_ end
let rec strDecName (StrDec (name, _)) = name
let rec strDecParent (StrDec (_, parent)) = parent
let maxCid = Global.maxCid
let dummyEntry = ConDec ("", None, 0, Normal, (Uni Kind), Kind)
let sgnArray = (Array.array ((maxCid + 1), dummyEntry) : conDec_ Array.array)
let nextCid = ref 0
let maxMid = Global.maxMid
let sgnStructArray =
  (Array.array ((maxMid + 1), (StrDec ("", None))) : strDec_ Array.array)
let nextMid = ref 0
let rec sgnClean i = if (!) ((>=) i) nextCid then begin () end
  else begin
    (begin Array.update (sgnArray, i, dummyEntry); sgnClean (i + 1) end) end
let rec sgnReset () = ((begin sgnClean 0; nextCid := 0; nextMid := 0 end)
  (* Fri Dec 20 12:04:24 2002 -fp *)(* this circumvents a space leak *))
let rec sgnSize () = (!nextCid, !nextMid)
let rec sgnAdd conDec =
  let cid = !nextCid in
  if cid > maxCid
  then
    begin raise
            (Error
               (((^) "Global signature size " Int.toString (maxCid + 1)) ^
                  " exceeded")) end
    else begin
      (begin Array.update (sgnArray, cid, conDec); (nextCid := cid) + 1; cid end) end
let rec sgnLookup cid = Array.sub (sgnArray, cid)
let rec sgnApp f =
  let rec sgnApp' cid = if (!) ((=) cid) nextCid then begin () end
    else begin (begin f cid; sgnApp' (cid + 1) end) end in
sgnApp' 0
let rec sgnStructAdd strDec =
  let mid = !nextMid in
  if mid > maxMid
  then
    begin raise
            (Error
               (((^) "Global signature size " Int.toString (maxMid + 1)) ^
                  " exceeded")) end
    else begin
      (begin Array.update (sgnStructArray, mid, strDec);
       (nextMid := mid) + 1;
       mid end) end
let rec sgnStructLookup mid = Array.sub (sgnStructArray, mid)
let rec rename (cid, new_) =
  let newConDec =
    begin match sgnLookup cid with
    | ConDec (n, m, i, s, e, u) -> ConDec (new_, m, i, s, e, u)
    | ConDef (n, m, i, e, e', u, a) -> ConDef (new_, m, i, e, e', u, a)
    | AbbrevDef (n, m, i, e, e', u) -> AbbrevDef (new_, m, i, e, e', u)
    | BlockDec (n, m, d, d') -> BlockDec (new_, m, d, d')
    | SkoDec (n, m, i, e, u) -> SkoDec (new_, m, i, e, u) end in
Array.update (sgnArray, cid, newConDec)
let rec constDef d =
  begin match sgnLookup d with
  | ConDef (_, _, _, u_, _, _, _) -> u_
  | AbbrevDef (_, _, _, u_, _, _) -> u_ end
let rec constType c = conDecType (sgnLookup c)
let rec constImp c = conDecImp (sgnLookup c)
let rec constUni c = conDecUni (sgnLookup c)
let rec constBlock c = conDecBlock (sgnLookup c)
let rec constStatus c =
  begin match sgnLookup c with
  | ConDec (_, _, _, status, _, _) -> status
  | _ -> Normal end
let id = Shift 0
let shift = Shift 1
let invShift = Dot (Undef, id)
let rec comp =
  begin function
  | (Shift 0, s) -> s
  | (s, Shift 0) -> s
  | (Shift n, Dot (Ft, s)) -> comp ((Shift (n - 1)), s)
  | (Shift n, Shift m) -> Shift (n + m)
  | (Dot (Ft, s), s') -> Dot ((frontSub (Ft, s')), (comp (s, s'))) end
(* Sat Feb 14 10:15:16 1998 -fp *)(* roughly 15% on standard suite for Twelf 1.1 *)
(* next line is an optimization *)
let rec bvarSub =
  begin function
  | (1, Dot (Ft, s)) -> Ft
  | (n, Dot (Ft, s)) -> bvarSub ((n - 1), s)
  | (n, Shift k) -> Idx (n + k) end
let rec blockSub =
  begin function
  | (Bidx k, s) ->
      (begin match bvarSub (k, s) with | Idx k' -> Bidx k' | Block (b_) -> b_ end)
  | (LVar ({ contents = Some (b_) }, sk, _), s) ->
      blockSub (b_, (comp (sk, s)))
  | (LVar (({ contents = None } as r), sk, (l, t)), s) ->
      LVar (r, (comp (sk, s)), (l, t))
  | ((Inst (ULs) as l_), s') ->
      Inst (map (begin function | u_ -> EClo (u_, s') end) ULs) end(* comp(^k, s) = ^k' for some k' by invariant *)
(* was:
        LVar (r, comp(sk, s), (l, comp (t, s)))
        July 22, 2010 -fp -cs
       *)
(* Thu Dec  6 20:30:26 2001 -fp !!! *)(* where is this needed? *)
(* Since always . |- t : Gsome, discard s *)(* --cs Sun Dec  1 11:25:41 2002 *)
(* -fp Sun Dec  1 21:18:30 2002 *)
let rec frontSub =
  begin function
  | (Idx n, s) -> bvarSub (n, s)
  | (Exp (u_), s) -> Exp (EClo (u_, s))
  | (Undef, s) -> Undef
  | (Block (b_), s) -> Block (blockSub (b_, s)) end
let rec decSub =
  begin function
  | (Dec (x, v_), s) -> Dec (x, (EClo (v_, s)))
  | (NDec x, s) -> NDec x
  | (BDec (n, (l, t)), s) -> BDec (n, (l, (comp (t, s)))) end
let rec dot1 =
  begin function | Shift 0 as s -> s | s -> Dot ((Idx 1), (comp (s, shift))) end
let rec invDot1 s = comp ((comp (shift, s)), invShift)
let rec ctxDec (g_, k) =
  let rec ctxDec' =
    begin function
    | (Decl (g'_, Dec (x, v'_)), 1) -> Dec (x, (EClo (v'_, (Shift k))))
    | (Decl (g'_, BDec (n, (l, s))), 1) ->
        BDec (n, (l, (comp (s, (Shift k)))))
    | (Decl (g'_, _), k') -> ctxDec' (g'_, (k' - 1)) end in
((ctxDec' (g_, k))
  (* ctxDec' (G'', k') = x:V
             where G |- ^(k-k') : G'', 1 <= k' <= k
           *)
  (* ctxDec' (Null, k')  should not occur by invariant *))
let rec blockDec (g_, (Bidx k as v), i) =
  let BDec (_, (l, s)) = ctxDec (g_, k) in
  let (Gsome, Lblock) = conDecBlock (sgnLookup l) in
  let rec blockDec' =
    begin function
    | (t, (d_)::l_, 1, j) -> decSub (d_, t)
    | (t, _::l_, n, j) ->
        blockDec'
          ((Dot ((Exp (Root ((Proj (v, j)), Nil))), t)), l_, (n - 1),
            (j + 1)) end in
  ((blockDec' (s, Lblock, i, 1))(* G |- s : Gsome *))
let rec newEVar (g_, v_) = EVar ((ref None), g_, v_, (ref []))
let rec newAVar () = AVar (ref None)
let rec newTypeVar (g_) = EVar ((ref None), g_, (Uni Type), (ref []))
let rec newLVar (sk, (cid, t)) = LVar ((ref None), sk, (cid, t))
let rec headOpt =
  begin function
  | Root (h_, _) -> Some h_
  | Lam (_, u_) -> headOpt u_
  | _ -> None end
let rec ancestor' =
  begin function
  | None -> Anc (None, 0, None)
  | Some (Const c) -> Anc ((Some c), 1, (Some c))
  | Some (Def d) ->
      (begin match sgnLookup d with
       | ConDef (_, _, _, _, _, _, Anc (_, height, cOpt)) ->
           Anc ((Some d), (height + 1), cOpt) end)
  | Some _ -> Anc (None, 0, None) end(* FgnConst possible, BVar impossible by strictness *)
let rec ancestor (u_) = ancestor' (headOpt u_)
let rec defAncestor d =
  begin match sgnLookup d with | ConDef (_, _, _, _, _, _, anc) -> anc end
let rec targetHeadOpt =
  begin function
  | Root (h_, _) -> Some h_
  | Pi (_, v_) -> targetHeadOpt v_
  | Redex (v_, s_) -> targetHeadOpt v_
  | Lam (_, v_) -> targetHeadOpt v_
  | EVar ({ contents = Some (v_) }, _, _, _) -> targetHeadOpt v_
  | EClo (v_, s) -> targetHeadOpt v_
  | _ -> None end
let rec targetHead (a_) = valOf (targetHeadOpt a_)
let rec targetFamOpt =
  begin function
  | Root (Const cid, _) -> Some cid
  | Pi (_, v_) -> targetFamOpt v_
  | Root (Def cid, _) -> targetFamOpt (constDef cid)
  | Redex (v_, s_) -> targetFamOpt v_
  | Lam (_, v_) -> targetFamOpt v_
  | EVar ({ contents = Some (v_) }, _, _, _) -> targetFamOpt v_
  | EClo (v_, s) -> targetFamOpt v_
  | _ -> None end
let rec targetFam (a_) = valOf (targetFamOpt a_) end 
module IntSyn : INTSYN = (IntSyn)(struct module Global = Global end) 