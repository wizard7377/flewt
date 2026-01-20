
module type THMSYN  =
  sig
    module Names : NAMES
    exception Error of string 
    type __Order =
      | Varg of string list 
      | Lex of __Order list 
      | Simul of __Order list 
    type __Predicate =
      | Less 
      | Leq 
      | Eq 
    type __RedOrder =
      | RedOrder of (__Predicate * __Order * __Order) 
    type __Callpats =
      | Callpats of (IntSyn.cid * string option list) list 
    type __TDecl =
      | TDecl of (__Order * __Callpats) 
    type __RDecl =
      | RDecl of (__RedOrder * __Callpats) 
    type __TabledDecl =
      | TabledDecl of IntSyn.cid 
    type __KeepTableDecl =
      | KeepTableDecl of IntSyn.cid 
    type __ThDecl =
      | ThDecl of ((IntSyn.__Dec IntSyn.__Ctx * IntSyn.__Dec IntSyn.__Ctx)
      list * IntSyn.__Dec IntSyn.__Ctx * ModeSyn.__Mode IntSyn.__Ctx * int) 
    type __PDecl =
      | PDecl of (int * __TDecl) 
    type __WDecl =
      | WDecl of (Names.__Qid list * __Callpats) 
    val theoremDecToConDec :
      (string * __ThDecl) ->
        Paths.region ->
          ((IntSyn.__Dec IntSyn.__Ctx * IntSyn.__Dec IntSyn.__Ctx) list *
            IntSyn.__ConDec)
    val theoremDecToModeSpine :
      (string * __ThDecl) -> Paths.region -> ModeSyn.__ModeSpine
  end;;




module ThmSyn(ThmSyn:sig
                       module Abstract : ABSTRACT
                       module Whnf : WHNF
                       module Names' : NAMES
                     end) : THMSYN =
  struct
    module Names = Names'
    exception Error of string 
    let rec error r msg = raise (Error (Paths.wrap (r, msg)))
    type nonrec __Param = string option
    type __Order =
      | Varg of string list 
      | Lex of __Order list 
      | Simul of __Order list 
    type __Predicate =
      | Less 
      | Leq 
      | Eq 
    type __RedOrder =
      | RedOrder of (__Predicate * __Order * __Order) 
    type __Callpats =
      | Callpats of (IntSyn.cid * __Param list) list 
    type __TDecl =
      | TDecl of (__Order * __Callpats) 
    type __RDecl =
      | RDecl of (__RedOrder * __Callpats) 
    type __TabledDecl =
      | TabledDecl of IntSyn.cid 
    type __KeepTableDecl =
      | KeepTableDecl of IntSyn.cid 
    type __ThDecl =
      | ThDecl of ((IntSyn.__Dec IntSyn.__Ctx * IntSyn.__Dec IntSyn.__Ctx)
      list * IntSyn.__Dec IntSyn.__Ctx * ModeSyn.__Mode IntSyn.__Ctx * int) 
    type __PDecl =
      | PDecl of (int * __TDecl) 
    type __WDecl =
      | WDecl of (Names.__Qid list * __Callpats) 
    module I = IntSyn
    module M = ModeSyn
    let rec theoremDecToConDec (name, ThDecl (GBs, __G, MG, i)) r =
      let rec theoremToConDec' __0__ __1__ =
        match (__0__, __1__) with
        | (I.Null, __V) -> __V
        | (Decl (__G, __D), __V) ->
            if Abstract.closedDec (__G, (__D, I.id))
            then
              theoremToConDec'
                (__G,
                  (Abstract.piDepend
                     (((Whnf.normalizeDec (__D, I.id)), I.Maybe), __V)))
            else error (r, "Free variables in theorem declaration") in
      (((GBs,
          (I.ConDec
             (name, NONE, i, I.Normal,
               (theoremToConDec' (__G, (I.Uni I.Type))), I.Kind))))
        (* theoremToConDec' G V = V'

             Invariant:
             If   G = V1 .. Vn
             and  G |- V : kind
             then V' = {V1} .. {Vn} V
             and  . |-  V' : kind
          *))
    let rec theoremDecToModeSpine (name, ThDecl (GBs, __G, MG, i)) r =
      let rec theoremToModeSpine' __2__ __3__ __4__ =
        match (__2__, __3__, __4__) with
        | (I.Null, I.Null, mS) -> mS
        | (Decl (__G, Dec (x, _)), Decl (MG, m), mS) ->
            theoremToModeSpine' (__G, MG, (M.Mapp ((M.Marg (m, x)), mS))) in
      theoremToModeSpine' (__G, MG, M.Mnil)
    let theoremDecToConDec = theoremDecToConDec
    let theoremDecToModeSpine = theoremDecToModeSpine
  end ;;
