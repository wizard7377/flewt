
module type FUNSYN  =
  sig
    type nonrec label = int
    type nonrec lemma = int
    type __LabelDec =
      | LabelDec of (string * IntSyn.__Dec list * IntSyn.__Dec list) 
    type __CtxBlock =
      | CtxBlock of (label option * IntSyn.dctx) 
    type __LFDec =
      | Prim of IntSyn.__Dec 
      | Block of __CtxBlock 
    type nonrec lfctx = __LFDec IntSyn.__Ctx
    type __For =
      | All of (__LFDec * __For) 
      | Ex of (IntSyn.__Dec * __For) 
      | True 
      | And of (__For * __For) 
    type __Pro =
      | Lam of (__LFDec * __Pro) 
      | Inx of (IntSyn.__Exp * __Pro) 
      | Unit 
      | Rec of (__MDec * __Pro) 
      | Let of (__Decs * __Pro) 
      | Case of __Opts 
      | Pair of (__Pro * __Pro) 
    and __Opts =
      | Opts of (lfctx * IntSyn.__Sub * __Pro) list 
    and __MDec =
      | MDec of (string option * __For) 
    and __Decs =
      | Empty 
      | Split of (int * __Decs) 
      | New of (__CtxBlock * __Decs) 
      | App of ((int * IntSyn.__Exp) * __Decs) 
      | PApp of ((int * int) * __Decs) 
      | Lemma of (lemma * __Decs) 
      | Left of (int * __Decs) 
      | Right of (int * __Decs) 
    type __LemmaDec =
      | LemmaDec of (string list * __Pro * __For) 
    type nonrec mctx = __MDec IntSyn.__Ctx
    val labelLookup : label -> __LabelDec
    val labelAdd : __LabelDec -> label
    val labelSize : unit -> int
    val labelReset : unit -> unit
    val lemmaLookup : lemma -> __LemmaDec
    val lemmaAdd : __LemmaDec -> lemma
    val lemmaSize : unit -> int
    val mdecSub : __MDec -> IntSyn.__Sub -> __MDec
    val makectx : lfctx -> IntSyn.dctx
    val lfctxLength : lfctx -> int
    val lfctxLFDec : lfctx -> int -> (__LFDec * IntSyn.__Sub)
    val dot1n : IntSyn.dctx -> IntSyn.__Sub -> IntSyn.__Sub
    val convFor : (__For * IntSyn.__Sub) -> (__For * IntSyn.__Sub) -> bool
    val forSub : __For -> IntSyn.__Sub -> __For
    val normalizeFor : __For -> IntSyn.__Sub -> __For
    val listToCtx : IntSyn.__Dec list -> IntSyn.dctx
    val ctxToList : IntSyn.dctx -> IntSyn.__Dec list
  end;;




module FunSyn(FunSyn:sig module Whnf : WHNF module Conv : CONV end) : FUNSYN
  =
  struct
    exception Error of string 
    type nonrec label = int
    type nonrec name = string
    type nonrec lemma = int
    type nonrec dlist = IntSyn.__Dec list
    type __LabelDec =
      | LabelDec of (name * dlist * dlist) 
    type __CtxBlock =
      | CtxBlock of (label option * IntSyn.dctx) 
    type __LFDec =
      | Prim of IntSyn.__Dec 
      | Block of __CtxBlock 
    type nonrec lfctx = __LFDec IntSyn.__Ctx
    type __For =
      | All of (__LFDec * __For) 
      | Ex of (IntSyn.__Dec * __For) 
      | True 
      | And of (__For * __For) 
    type __Pro =
      | Lam of (__LFDec * __Pro) 
      | Inx of (IntSyn.__Exp * __Pro) 
      | Unit 
      | Rec of (__MDec * __Pro) 
      | Let of (__Decs * __Pro) 
      | Case of __Opts 
      | Pair of (__Pro * __Pro) 
    and __Opts =
      | Opts of (lfctx * IntSyn.__Sub * __Pro) list 
    and __MDec =
      | MDec of (name option * __For) 
    and __Decs =
      | Empty 
      | Split of (int * __Decs) 
      | New of (__CtxBlock * __Decs) 
      | App of ((int * IntSyn.__Exp) * __Decs) 
      | PApp of ((int * int) * __Decs) 
      | Lemma of (lemma * __Decs) 
      | Left of (int * __Decs) 
      | Right of (int * __Decs) 
    type __LemmaDec =
      | LemmaDec of (name list * __Pro * __For) 
    type nonrec mctx = __MDec IntSyn.__Ctx
    module I = IntSyn
    let maxLabel = Global.maxCid
    let maxLemma = Global.maxCid
    let labelArray =
      (Array.array ((maxLabel + 1), (LabelDec ("", nil, nil))) : __LabelDec
                                                                   Array.array)
    let nextLabel = ref 0
    let lemmaArray =
      (Array.array ((maxLemma + 1), (LemmaDec (nil, Unit, True))) : __LemmaDec
                                                                    Array.array)
    let nextLemma = ref 0
    let rec labelLookup label = Array.sub (labelArray, label)
    let rec labelAdd labelDec =
      let label = !nextLabel in
      if label > maxLabel
      then
        raise
          (Error
             (((^) "Global signature size " Int.toString (maxLabel + 1)) ^
                " exceeded"))
      else
        (Array.update (labelArray, label, labelDec);
         (nextLabel := label) + 1;
         label)
    let rec labelSize () = !nextLabel
    let rec labelReset () = nextLabel := 0
    let rec lemmaLookup lemma = Array.sub (lemmaArray, lemma)
    let rec lemmaAdd lemmaDec =
      let lemma = !nextLemma in
      if lemma > maxLemma
      then
        raise
          (Error
             (((^) "Global signature size " Int.toString (maxLemma + 1)) ^
                " exceeded"))
      else
        (Array.update (lemmaArray, lemma, lemmaDec);
         (nextLemma := lemma) + 1;
         lemma)
    let rec lemmaSize () = !nextLemma
    let rec listToCtx (Gin) =
      let rec listToCtx' __0__ __1__ =
        match (__0__, __1__) with
        | (__G, nil) -> __G
        | (__G, (__D)::__Ds) -> listToCtx' ((I.Decl (__G, __D)), __Ds) in
      listToCtx' (I.Null, Gin)
    let rec ctxToList (Gin) =
      let rec ctxToList' __2__ __3__ =
        match (__2__, __3__) with
        | (I.Null, __G) -> __G
        | (Decl (__G, __D), __G') -> ctxToList' (__G, (__D :: __G')) in
      ctxToList' (Gin, nil)
    let rec union __4__ __5__ =
      match (__4__, __5__) with
      | (__G, I.Null) -> __G
      | (__G, Decl (__G', __D)) -> I.Decl ((union (__G, __G')), __D)
    let rec makectx =
      function
      | I.Null -> I.Null
      | Decl (__G, Prim (__D)) -> I.Decl ((makectx __G), __D)
      | Decl (__G, Block (CtxBlock (l, __G'))) -> union ((makectx __G), __G')
    let rec lfctxLength =
      function
      | I.Null -> 0
      | Decl (Psi, Prim _) -> (lfctxLength Psi) + 1
      | Decl (Psi, Block (CtxBlock (_, __G))) ->
          (lfctxLength Psi) + (I.ctxLength __G)
    let rec lfctxLFDec (Psi) k =
      let rec lfctxLFDec' __6__ __7__ =
        match (__6__, __7__) with
        | (Decl (Psi', (Prim (Dec (x, __V')) as LD)), 1) -> (LD, (I.Shift k))
        | (Decl (Psi', Prim _), k') -> lfctxLFDec' (Psi', (k' - 1))
        | (Decl (Psi', (Block (CtxBlock (_, __G)) as LD)), k') ->
            let l = I.ctxLength __G in
            if k' <= l
            then (LD, (I.Shift ((k - k') + 1)))
            else lfctxLFDec' (Psi', (k' - l)) in
      ((lfctxLFDec' (Psi, k))
        (* lfctxDec' (Null, k')  should not occur by invariant *))
    let rec dot1n __8__ __9__ =
      match (__8__, __9__) with
      | (I.Null, s) -> s
      | (Decl (__G, _), s) -> I.dot1 (dot1n (__G, s))
    let rec convFor __10__ __11__ =
      match (__10__, __11__) with
      | ((True, _), (True, _)) -> true__
      | ((All (Prim (__D1), __F1), s1), (All (Prim (__D2), __F2), s2)) ->
          (Conv.convDec ((__D1, s1), (__D2, s2))) &&
            (convFor ((__F1, (I.dot1 s1)), (__F2, (I.dot1 s2))))
      | ((All
          (Block (CtxBlock (((_, __G1))(* Some l1 *))),
           __F1),
          s1),
         (All
          (Block (CtxBlock (((_, __G2))(* Some l2 *))),
           __F2),
          s2)) ->
          convForBlock
            (((ctxToList __G1), __F1, s1), ((ctxToList __G1), __F2, s2))
      | ((Ex (__D1, __F1), s1), (Ex (__D2, __F2), s2)) ->
          (Conv.convDec ((__D1, s1), (__D2, s2))) &&
            (convFor ((__F1, (I.dot1 s1)), (__F2, (I.dot1 s2))))
      | ((And (__F1, F1'), s1), (And (__F2, F2'), s2)) ->
          (convFor ((__F1, s1), (__F2, s2))) &&
            (convFor ((F1', s1), (F2', s2)))
      | _ -> false__(* omission! check that the block numbers are the same!!!! *)
      (* l1 = l2 andalso *)
    let rec convForBlock __12__ __13__ =
      match (__12__, __13__) with
      | ((nil, __F1, s1), (nil, __F2, s2)) ->
          convFor ((__F1, s1), (__F2, s2))
      | (((__D1)::__G1, __F1, s1), ((__D2)::__G2, __F2, s2)) ->
          (Conv.convDec ((__D1, s1), (__D2, s2))) &&
            (convForBlock
               ((__G1, __F1, (I.dot1 s1)), (__G2, __F2, (I.dot1 s2))))
      | _ -> false__
    let rec ctxSub __14__ __15__ =
      match (__14__, __15__) with
      | (I.Null, s) -> (I.Null, s)
      | (Decl (__G, __D), s) ->
          let (__G', s') = ctxSub (__G, s) in
          ((I.Decl (__G', (I.decSub (__D, s')))), (I.dot1 s))
    let rec forSub __16__ __17__ =
      match (__16__, __17__) with
      | (All (Prim (__D), __F), s) ->
          All ((Prim (I.decSub (__D, s))), (forSub (__F, (I.dot1 s))))
      | (All (Block (CtxBlock (name, __G)), __F), s) ->
          let (__G', s') = ctxSub (__G, s) in
          All ((Block (CtxBlock (name, __G'))), (forSub (__F, s')))
      | (Ex (__D, __F), s) ->
          Ex ((I.decSub (__D, s)), (forSub (__F, (I.dot1 s))))
      | (True, s) -> True
      | (And (__F1, __F2), s) -> And ((forSub (__F1, s)), (forSub (__F2, s)))
    let rec mdecSub (MDec (name, __F)) s = MDec (name, (forSub (__F, s)))
    let rec normalizeFor __18__ __19__ =
      match (__18__, __19__) with
      | (All (Prim (__D), __F), s) ->
          All
            ((Prim (Whnf.normalizeDec (__D, s))),
              (normalizeFor (__F, (I.dot1 s))))
      | (Ex (__D, __F), s) ->
          Ex ((Whnf.normalizeDec (__D, s)), (normalizeFor (__F, (I.dot1 s))))
      | (And (__F1, __F2), s) ->
          And ((normalizeFor (__F1, s)), (normalizeFor (__F2, s)))
      | (True, _) -> True
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
    let listToCtx = listToCtx
  end 
module FunSyn =
  (Make_FunSyn)(struct module Whnf = Whnf
                       module Conv = Conv end);;
