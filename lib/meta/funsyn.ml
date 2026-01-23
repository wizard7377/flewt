module type FUNSYN  =
  sig
    type nonrec label = int
    type nonrec lemma = int
    type labelDec_ =
      | LabelDec of (string * IntSyn.dec_ list * IntSyn.dec_ list) 
    type ctxBlock_ =
      | CtxBlock of (label option * IntSyn.dctx) 
    type lFDec_ =
      | Prim of IntSyn.dec_ 
      | Block of ctxBlock_ 
    type nonrec lfctx = lFDec_ IntSyn.ctx_
    type for_ =
      | All of (lFDec_ * for_) 
      | Ex of (IntSyn.dec_ * for_) 
      | True 
      | And of (for_ * for_) 
    type pro_ =
      | Lam of (lFDec_ * pro_) 
      | Inx of (IntSyn.exp_ * pro_) 
      | Unit 
      | Rec of (mDec_ * pro_) 
      | Let of (decs_ * pro_) 
      | Case of opts_ 
      | Pair of (pro_ * pro_) 
    and opts_ =
      | Opts of (lfctx * IntSyn.sub_ * pro_) list 
    and mDec_ =
      | MDec of (string option * for_) 
    and decs_ =
      | Empty 
      | Split of (int * decs_) 
      | New of (ctxBlock_ * decs_) 
      | App of ((int * IntSyn.exp_) * decs_) 
      | PApp of ((int * int) * decs_) 
      | Lemma of (lemma * decs_) 
      | Left of (int * decs_) 
      | Right of (int * decs_) 
    type lemmaDec_ =
      | LemmaDec of (string list * pro_ * for_) 
    type nonrec mctx = mDec_ IntSyn.ctx_
    val labelLookup : label -> labelDec_
    val labelAdd : labelDec_ -> label
    val labelSize : unit -> int
    val labelReset : unit -> unit
    val lemmaLookup : lemma -> lemmaDec_
    val lemmaAdd : lemmaDec_ -> lemma
    val lemmaSize : unit -> int
    val mdecSub : (mDec_ * IntSyn.sub_) -> mDec_
    val makectx : lfctx -> IntSyn.dctx
    val lfctxLength : lfctx -> int
    val lfctxLFDec : (lfctx * int) -> (lFDec_ * IntSyn.sub_)
    val dot1n : (IntSyn.dctx * IntSyn.sub_) -> IntSyn.sub_
    val convFor : ((for_ * IntSyn.sub_) * (for_ * IntSyn.sub_)) -> bool
    val forSub : (for_ * IntSyn.sub_) -> for_
    val normalizeFor : (for_ * IntSyn.sub_) -> for_
    val listToCtx : IntSyn.dec_ list -> IntSyn.dctx
    val ctxToList : IntSyn.dctx -> IntSyn.dec_ list
  end


module FunSyn(FunSyn:sig module Whnf : WHNF module Conv : CONV end) : FUNSYN
  =
  struct
    exception Error of string 
    type nonrec label = int
    type nonrec name = string
    type nonrec lemma = int
    type nonrec dlist = IntSyn.dec_ list
    type labelDec_ =
      | LabelDec of (name * dlist * dlist) 
    type ctxBlock_ =
      | CtxBlock of (label option * IntSyn.dctx) 
    type lFDec_ =
      | Prim of IntSyn.dec_ 
      | Block of ctxBlock_ 
    type nonrec lfctx = lFDec_ IntSyn.ctx_
    type for_ =
      | All of (lFDec_ * for_) 
      | Ex of (IntSyn.dec_ * for_) 
      | True 
      | And of (for_ * for_) 
    type pro_ =
      | Lam of (lFDec_ * pro_) 
      | Inx of (IntSyn.exp_ * pro_) 
      | Unit 
      | Rec of (mDec_ * pro_) 
      | Let of (decs_ * pro_) 
      | Case of opts_ 
      | Pair of (pro_ * pro_) 
    and opts_ =
      | Opts of (lfctx * IntSyn.sub_ * pro_) list 
    and mDec_ =
      | MDec of (name option * for_) 
    and decs_ =
      | Empty 
      | Split of (int * decs_) 
      | New of (ctxBlock_ * decs_) 
      | App of ((int * IntSyn.exp_) * decs_) 
      | PApp of ((int * int) * decs_) 
      | Lemma of (lemma * decs_) 
      | Left of (int * decs_) 
      | Right of (int * decs_) 
    type lemmaDec_ =
      | LemmaDec of (name list * pro_ * for_) 
    type nonrec mctx = mDec_ IntSyn.ctx_
    module I = IntSyn
    let maxLabel = Global.maxCid
    let maxLemma = Global.maxCid
    let labelArray =
      (Array.array ((maxLabel + 1), (LabelDec ("", [], []))) : labelDec_
                                                                 Array.array)
    let nextLabel = ref 0
    let lemmaArray =
      (Array.array ((maxLemma + 1), (LemmaDec ([], Unit, True))) : lemmaDec_
                                                                    Array.array)
    let nextLemma = ref 0
    let rec labelLookup label = Array.sub (labelArray, label)
    let rec labelAdd labelDec =
      let label = !nextLabel in
      if label > maxLabel
      then
        begin raise
                (Error
                   (((^) "Global signature size " Int.toString (maxLabel + 1))
                      ^ " exceeded")) end
        else begin
          (begin Array.update (labelArray, label, labelDec);
           (nextLabel := label) + 1;
           label end) end
let rec labelSize () = !nextLabel
let rec labelReset () = nextLabel := 0
let rec lemmaLookup lemma = Array.sub (lemmaArray, lemma)
let rec lemmaAdd lemmaDec =
  let lemma = !nextLemma in
  if lemma > maxLemma
  then
    begin raise
            (Error
               (((^) "Global signature size " Int.toString (maxLemma + 1)) ^
                  " exceeded")) end
    else begin
      (begin Array.update (lemmaArray, lemma, lemmaDec);
       (nextLemma := lemma) + 1;
       lemma end) end
let rec lemmaSize () = !nextLemma
let rec listToCtx (Gin) =
  let rec listToCtx' =
    begin function
    | (g_, []) -> g_
    | (g_, (d_)::ds_) -> listToCtx' ((I.Decl (g_, d_)), ds_) end in
listToCtx' (I.Null, Gin)
let rec ctxToList (Gin) =
  let rec ctxToList' =
    begin function
    | (I.Null, g_) -> g_
    | (Decl (g_, d_), g'_) -> ctxToList' (g_, (d_ :: g'_)) end in
ctxToList' (Gin, [])
let rec union =
  begin function
  | (g_, I.Null) -> g_
  | (g_, Decl (g'_, d_)) -> I.Decl ((union (g_, g'_)), d_) end
let rec makectx =
  begin function
  | I.Null -> I.Null
  | Decl (g_, Prim (d_)) -> I.Decl ((makectx g_), d_)
  | Decl (g_, Block (CtxBlock (l, g'_))) -> union ((makectx g_), g'_) end
let rec lfctxLength =
  begin function
  | I.Null -> 0
  | Decl (Psi, Prim _) -> (lfctxLength Psi) + 1
  | Decl (Psi, Block (CtxBlock (_, g_))) ->
      (lfctxLength Psi) + (I.ctxLength g_) end
let rec lfctxLFDec (Psi, k) =
  let rec lfctxLFDec' =
    begin function
    | (Decl (Psi', (Prim (Dec (x, v'_)) as LD)), 1) -> (LD, (I.Shift k))
    | (Decl (Psi', Prim _), k') -> lfctxLFDec' (Psi', (k' - 1))
    | (Decl (Psi', (Block (CtxBlock (_, g_)) as LD)), k') ->
        let l = I.ctxLength g_ in
        if k' <= l then begin (LD, (I.Shift ((k - k') + 1))) end
          else begin lfctxLFDec' (Psi', (k' - l)) end end in
((lfctxLFDec' (Psi, k))
(* lfctxDec' (Null, k')  should not occur by invariant *))
let rec dot1n =
  begin function
  | (I.Null, s) -> s
  | (Decl (g_, _), s) -> I.dot1 (dot1n (g_, s)) end
let rec convFor =
  begin function
  | ((True, _), (True, _)) -> true
  | ((All (Prim (d1_), f1_), s1), (All (Prim (d2_), f2_), s2)) ->
      (Conv.convDec ((d1_, s1), (d2_, s2))) &&
        (convFor ((f1_, (I.dot1 s1)), (f2_, (I.dot1 s2))))
  | ((All (Block (CtxBlock (((_, g1_))(* SOME l1 *))), f1_),
      s1),
     (All (Block (CtxBlock (((_, g2_))(* SOME l2 *))), f2_),
      s2)) ->
      convForBlock (((ctxToList g1_), f1_, s1), ((ctxToList g1_), f2_, s2))
  | ((Ex (d1_, f1_), s1), (Ex (d2_, f2_), s2)) ->
      (Conv.convDec ((d1_, s1), (d2_, s2))) &&
        (convFor ((f1_, (I.dot1 s1)), (f2_, (I.dot1 s2))))
  | ((And (f1_, F1'), s1), (And (f2_, F2'), s2)) ->
      (convFor ((f1_, s1), (f2_, s2))) && (convFor ((F1', s1), (F2', s2)))
  | _ -> false end(* omission! check that the block numbers are the same!!!! *)
(* l1 = l2 andalso *)
let rec convForBlock =
  begin function
  | (([], f1_, s1), ([], f2_, s2)) -> convFor ((f1_, s1), (f2_, s2))
  | (((d1_)::g1_, f1_, s1), ((d2_)::g2_, f2_, s2)) ->
      (Conv.convDec ((d1_, s1), (d2_, s2))) &&
        (convForBlock ((g1_, f1_, (I.dot1 s1)), (g2_, f2_, (I.dot1 s2))))
  | _ -> false end
let rec ctxSub =
  begin function
  | (I.Null, s) -> (I.Null, s)
  | (Decl (g_, d_), s) ->
      let (g'_, s') = ctxSub (g_, s) in
      ((I.Decl (g'_, (I.decSub (d_, s')))), (I.dot1 s)) end
let rec forSub =
  begin function
  | (All (Prim (d_), f_), s) ->
      All ((Prim (I.decSub (d_, s))), (forSub (f_, (I.dot1 s))))
  | (All (Block (CtxBlock (name, g_)), f_), s) ->
      let (g'_, s') = ctxSub (g_, s) in
      All ((Block (CtxBlock (name, g'_))), (forSub (f_, s')))
  | (Ex (d_, f_), s) -> Ex ((I.decSub (d_, s)), (forSub (f_, (I.dot1 s))))
  | (True, s) -> True
  | (And (f1_, f2_), s) -> And ((forSub (f1_, s)), (forSub (f2_, s))) end
let rec mdecSub (MDec (name, f_), s) = MDec (name, (forSub (f_, s)))
let rec normalizeFor =
  begin function
  | (All (Prim (d_), f_), s) ->
      All
        ((Prim (Whnf.normalizeDec (d_, s))), (normalizeFor (f_, (I.dot1 s))))
  | (Ex (d_, f_), s) ->
      Ex ((Whnf.normalizeDec (d_, s)), (normalizeFor (f_, (I.dot1 s))))
  | (And (f1_, f2_), s) ->
      And ((normalizeFor (f1_, s)), (normalizeFor (f2_, s)))
  | (True, _) -> True end
let labelLookup = labelLookup
let labelAdd = labelAdd
let labelSize = labelSize
let labelReset = labelReset
let lemmaLookup = lemmaLookup
let lemmaAdd = lemmaAdd
let lemmaSize = lemmaSize
let mdecSub = mdecSub
let makectx = makectx
let lfctxLength = lfctxLength
let lfctxLFDec = lfctxLFDec
let dot1n = dot1n
let convFor = convFor
let forSub = forSub
let normalizeFor = normalizeFor
let ctxToList = ctxToList
let listToCtx = listToCtx end 
module FunSyn =
  (FunSyn)(struct module Whnf = Whnf
                       module Conv = Conv end)