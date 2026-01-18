
(* Internal syntax for functional proof term calculus *)
(* Author: Carsten Schuermann *)
module type FUNSYN  =
  sig
    (*! structure IntSyn : INTSYN !*)
    (* make abstract *)
    type nonrec label = int
    type nonrec lemma = int
    type __LabelDec =
      | LabelDec of (string * IntSyn.__Dec list * IntSyn.__Dec list) 
    (* BB ::= l: Some Theta. Phi  *)
    type __CtxBlock =
      | CtxBlock of (label option * IntSyn.dctx) 
    (* B ::= l : Phi              *)
    type __LFDec =
      | Prim of IntSyn.__Dec 
      | Block of __CtxBlock 
    (*      | B                   *)
    (* ??? *)
    type nonrec lfctx = __LFDec IntSyn.__Ctx
    (* Psi ::= . | Psi, LD        *)
    type __For =
      | All of (__LFDec * __For) 
      | Ex of (IntSyn.__Dec * __For) 
      | True 
      | And of (__For * __For) 
    (*     | __F1 ^ __F2              *)
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
    (*      | xx = pi2 yy, __Ds     *)
    type __LemmaDec =
      | LemmaDec of (string list * __Pro * __For) 
    (* __l ::= c:F = P              *)
    (* ??? *)
    type nonrec mctx = __MDec IntSyn.__Ctx
    (* Delta ::= . | Delta, xx : F*)
    val labelLookup : label -> __LabelDec
    val labelAdd : __LabelDec -> label
    val labelSize : unit -> int
    val labelReset : unit -> unit
    val lemmaLookup : lemma -> __LemmaDec
    val lemmaAdd : __LemmaDec -> lemma
    val lemmaSize : unit -> int
    val mdecSub : (__MDec * IntSyn.__Sub) -> __MDec
    val makectx : lfctx -> IntSyn.dctx
    val lfctxLength : lfctx -> int
    val lfctxLFDec : (lfctx * int) -> (__LFDec * IntSyn.__Sub)
    val dot1n : (IntSyn.dctx * IntSyn.__Sub) -> IntSyn.__Sub
    val convFor : ((__For * IntSyn.__Sub) * (__For * IntSyn.__Sub)) -> bool
    val forSub : (__For * IntSyn.__Sub) -> __For
    val normalizeFor : (__For * IntSyn.__Sub) -> __For
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
      let rec listToCtx' =
        function
        | (__g, nil) -> __g
        | (__g, (__d)::__Ds) -> listToCtx' ((I.Decl (__g, __d)), __Ds) in
      listToCtx' (I.Null, Gin)
    let rec ctxToList (Gin) =
      let rec ctxToList' =
        function
        | (I.Null, __g) -> __g
        | (Decl (__g, __d), __g') -> ctxToList' (__g, (__d :: __g')) in
      ctxToList' (Gin, nil)
    let rec union =
      function
      | (__g, I.Null) -> __g
      | (__g, Decl (__g', __d)) -> I.Decl ((union (__g, __g')), __d)
    let rec makectx =
      function
      | I.Null -> I.Null
      | Decl (__g, Prim (__d)) -> I.Decl ((makectx __g), __d)
      | Decl (__g, Block (CtxBlock (l, __g'))) -> union ((makectx __g), __g')
    let rec lfctxLength =
      function
      | I.Null -> 0
      | Decl (Psi, Prim _) -> (lfctxLength Psi) + 1
      | Decl (Psi, Block (CtxBlock (_, __g))) ->
          (lfctxLength Psi) + (I.ctxLength __g)
    let rec lfctxLFDec (Psi, k) =
      let rec lfctxLFDec' =
        function
        | (Decl (Psi', (Prim (Dec (x, __v')) as LD)), 1) -> (LD, (I.Shift k))
        | (Decl (Psi', Prim _), k') -> lfctxLFDec' (Psi', (k' - 1))
        | (Decl (Psi', (Block (CtxBlock (_, __g)) as LD)), k') ->
            let l = I.ctxLength __g in
            if k' <= l
            then (LD, (I.Shift ((k - k') + 1)))
            else lfctxLFDec' (Psi', (k' - l)) in
      lfctxLFDec' (Psi, k)
    let rec dot1n =
      function | (I.Null, s) -> s | (Decl (__g, _), s) -> I.dot1 (dot1n (__g, s))
    let rec convFor =
      function
      | ((True, _), (True, _)) -> true__
      | ((All (Prim (D1), __F1), s1), (All (Prim (D2), __F2), s2)) ->
          (Conv.convDec ((D1, s1), (D2, s2))) &&
            (convFor ((__F1, (I.dot1 s1)), (__F2, (I.dot1 s2))))
      | ((All (Block (CtxBlock (_, G1)), __F1), s1),
         (All (Block (CtxBlock (_, G2)), __F2), s2)) ->
          convForBlock (((ctxToList G1), __F1, s1), ((ctxToList G1), __F2, s2))
      | ((Ex (D1, __F1), s1), (Ex (D2, __F2), s2)) ->
          (Conv.convDec ((D1, s1), (D2, s2))) &&
            (convFor ((__F1, (I.dot1 s1)), (__F2, (I.dot1 s2))))
      | ((And (__F1, __F1'), s1), (And (__F2, __F2'), s2)) ->
          (convFor ((__F1, s1), (__F2, s2))) && (convFor ((__F1', s1), (__F2', s2)))
      | _ -> false__
    let rec convForBlock =
      function
      | ((nil, __F1, s1), (nil, __F2, s2)) -> convFor ((__F1, s1), (__F2, s2))
      | (((D1)::G1, __F1, s1), ((D2)::G2, __F2, s2)) ->
          (Conv.convDec ((D1, s1), (D2, s2))) &&
            (convForBlock ((G1, __F1, (I.dot1 s1)), (G2, __F2, (I.dot1 s2))))
      | _ -> false__
    let rec ctxSub =
      function
      | (I.Null, s) -> (I.Null, s)
      | (Decl (__g, __d), s) ->
          let (__g', s') = ctxSub (__g, s) in
          ((I.Decl (__g', (I.decSub (__d, s')))), (I.dot1 s))
    let rec forSub =
      function
      | (All (Prim (__d), F), s) ->
          All ((Prim (I.decSub (__d, s))), (forSub (F, (I.dot1 s))))
      | (All (Block (CtxBlock (name, __g)), F), s) ->
          let (__g', s') = ctxSub (__g, s) in
          All ((Block (CtxBlock (name, __g'))), (forSub (F, s')))
      | (Ex (__d, F), s) -> Ex ((I.decSub (__d, s)), (forSub (F, (I.dot1 s))))
      | (True, s) -> True
      | (And (__F1, __F2), s) -> And ((forSub (__F1, s)), (forSub (__F2, s)))
    let rec mdecSub (MDec (name, F), s) = MDec (name, (forSub (F, s)))
    let rec normalizeFor =
      function
      | (All (Prim (__d), F), s) ->
          All
            ((Prim (Whnf.normalizeDec (__d, s))),
              (normalizeFor (F, (I.dot1 s))))
      | (Ex (__d, F), s) ->
          Ex ((Whnf.normalizeDec (__d, s)), (normalizeFor (F, (I.dot1 s))))
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
(* Internal syntax for functional proof term calculus *)
(* Author: Carsten Schuermann *)
(*! structure IntSyn' : INTSYN !*)
(*! sharing Whnf.IntSyn = IntSyn' !*)
(*! sharing Conv.IntSyn = IntSyn' !*)
(*! structure IntSyn = IntSyn' !*)
(* ContextBody                *)
(* BB ::= l: Some Theta. Phi  *)
(* ContextBlocks              *)
(* B ::= l : Phi              *)
(* Contexts                   *)
(* LD ::= x :: A              *)
(*      | B                   *)
(* Psi ::= . | Psi, LD        *)
(* Formulas                   *)
(* F ::= All LD. F            *)
(*     | Ex  D. F             *)
(*     | T                    *)
(*     | __F1 ^ __F2              *)
(* Programs                   *)
(* P ::= lam LD. P            *)
(*     | <M, P>               *)
(*     | <>                   *)
(*     | mu xx. P             *)
(*     | let __Ds in P          *)
(*     | case O               *)
(*     | <__P1, __P2>             *)
(* Option list                *)
(* O ::= (Psi' |> s |-> P     *)
(* Meta Declaration:          *)
(* DD ::= xx : F              *)
(* Declarations               *)
(* __Ds ::= .                   *)
(*      | <x, yy> = P, __Ds     *)
(*      | nu B. __Ds            *)
(*      | xx = yy M, __Ds       *)
(*      | xx = yy Phi, __Ds     *)
(*      | xx = cc, __Ds         *)
(*      | xx = pi1 yy, __Ds     *)
(*      | xx = pi2 yy, __Ds     *)
(* Lemmas                     *)
(* __l ::= c:F = P              *)
(* Delta ::= . | Delta, xx : F*)
(* hack!!! improve !!!! *)
(* union (__g, __g') = __g''

       Invariant:
       __g'' = __g, __g'
    *)
(* makectx Psi = __g

       Invariant:
       __g is Psi, where the Prim/Block information is discarded.
    *)
(* lfctxDec (Psi, k) = (LD', w')
       Invariant:
       If      |Psi| >= k, where |Psi| is size of Psi,
       and     Psi = Psi1, LD, Psi2
       then    Psi |- k = LD or Psi |- k in LD  (if LD is a contextblock
       then    LD' = LD
       and     Psi |- w' : Psi1, LD\1   (w' is a weakening substitution)
       and     LD\1 is LD if LD is prim, and LD\1 = x:A if LD = __g, x:A
   *)
(* lfctxDec' (Null, k')  should not occur by invariant *)
(* dot1n (__g, s) = s'

       Invariant:
       If   G1 |- s : G2
       then G1, __g |- s' : G2, __g
       where s' = 1.(1.  ...     s) o ^ ) o ^
                        |__g|-times
    *)
(* conv ((__F1, s1), (__F2, s2)) = B

       Invariant:
       If   __g |- s1 : G1
       and  G1 |- __F1 : formula
       and  __g |- s2 : G2
       and  G2 |- __F2 : formula
       and  (__F1, __F2 do not contain abstraction over contextblocks )
       then B holds iff __g |- __F1[s1] = __F2[s2] formula
    *)
(* Some l1 *) (* Some l2 *)
(* l1 = l2 andalso *)
(* omission! check that the block numbers are the same!!!! *)
(* functor FunSyn *)
module FunSyn =
  (Make_FunSyn)(struct
                  (*! structure IntSyn' = IntSyn !*)
                  module Whnf = Whnf
                  module Conv = Conv
                end);;
