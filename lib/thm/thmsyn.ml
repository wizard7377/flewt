
module type THMSYN  =
  sig
    module Names :
    ((NAMES)(* Theorems *)(* Author: Carsten Schuermann *)
    (* Modified: Brigitte Pientka *))
    exception Error of string 
    type __Order =
      | Varg of ((string)(*! type Param = string option !*))
      list 
      | Lex of __Order list 
      | Simul of __Order list 
    type __Predicate =
      | Less 
      | Leq 
      | Eq (* -bp *)
    type __RedOrder =
      | RedOrder of (__Predicate * __Order * __Order) 
    type __Callpats =
      | Callpats of (IntSyn.cid * string option list) list 
    type __TDecl =
      | TDecl of (((__Order)(* Termination declaration *)) *
      __Callpats) 
    type __RDecl =
      | RDecl of
      (((__RedOrder)(* Reduction declaration *)(* -bp *))
      * __Callpats) 
    type __TabledDecl =
      | TabledDecl of ((IntSyn.cid)(* Tabled declaration *)) 
    type __KeepTableDecl =
      | KeepTableDecl of
      ((IntSyn.cid)(* KeepTable declaration *)) 
    type __ThDecl =
      | ThDecl of
      ((((IntSyn.__Dec)(* Theorem declaration  *))
      IntSyn.__Ctx * IntSyn.__Dec IntSyn.__Ctx) list * IntSyn.__Dec
      IntSyn.__Ctx * ModeSyn.__Mode IntSyn.__Ctx * int) 
    type __PDecl =
      | PDecl of (((int)(* Proof declaration *)) * __TDecl) 
    type __WDecl =
      | WDecl of
      (((Names.__Qid)(*  datatype WDecl = 
    WDecl of (IntSyn.Dec IntSyn.Ctx * 
	      IntSyn.Dec IntSyn.Ctx) list * Callpats
*)
      (* World declaration *)) list * __Callpats) 
    val theoremDecToConDec :
      ((string * __ThDecl) * Paths.region) ->
        ((IntSyn.__Dec IntSyn.__Ctx * IntSyn.__Dec IntSyn.__Ctx) list *
          IntSyn.__ConDec)
    val theoremDecToModeSpine :
      ((string * __ThDecl) * Paths.region) -> ModeSyn.__ModeSpine
  end;;




module ThmSyn(ThmSyn:sig
                       module Abstract : ABSTRACT
                       module Whnf : WHNF
                       module Names' :
                       ((NAMES)(* Theorems *)(* Author: Carsten Schuermann *)
                       (* Modified: Brigitte Pientka *)
                       (*! structure IntSyn : INTSYN !*)
                       (*! structure ModeSyn' : MODESYN !*)
                       (*! sharing ModeSyn'.IntSyn = IntSyn !*)(*! sharing Abstract.IntSyn = IntSyn !*)
                       (*! sharing Whnf.IntSyn = IntSyn !*)
                       (*! structure Paths' : PATHS !*))
                     end) : THMSYN =
  struct
    module Names =
      ((Names')(*! sharing Names'.IntSyn = IntSyn !*)
      (*! structure IntSyn = IntSyn !*)(*! structure ModeSyn = ModeSyn' *)
      (*! structure Paths = Paths' !*))
    exception Error of string 
    let rec error (r, msg) = raise (Error (Paths.wrap (r, msg)))
    type nonrec __Param = string option
    type __Order =
      | Varg of string list 
      | Lex of __Order list 
      | Simul of __Order list 
    type __Predicate =
      | Less 
      | Leq 
      | Eq (* -bp *)
    type __RedOrder =
      | RedOrder of (__Predicate * __Order * __Order) 
    type __Callpats =
      | Callpats of (IntSyn.cid * __Param list) list 
    type __TDecl =
      | TDecl of (((__Order)(* Termination declaration *)) *
      __Callpats) 
    type __RDecl =
      | RDecl of
      (((__RedOrder)(* Reduction declaration *)(* -bp *))
      * __Callpats) 
    type __TabledDecl =
      | TabledDecl of ((IntSyn.cid)(* Tabled declaration *)) 
    type __KeepTableDecl =
      | KeepTableDecl of
      ((IntSyn.cid)(* KeepTable declaration *)) 
    type __ThDecl =
      | ThDecl of
      ((((IntSyn.__Dec)(* Theorem declaration *))
      IntSyn.__Ctx * IntSyn.__Dec IntSyn.__Ctx) list * IntSyn.__Dec
      IntSyn.__Ctx * ModeSyn.__Mode IntSyn.__Ctx * int) 
    type __PDecl =
      | PDecl of (((int)(* Proof declaration *)) * __TDecl) 
    type __WDecl =
      | WDecl of
      (((Names.__Qid)(*  datatype WDecl =
    WDecl of (IntSyn.Dec IntSyn.Ctx *
              IntSyn.Dec IntSyn.Ctx) list * Callpats *)
      (* World declaration *)) list * __Callpats) 
    module I = IntSyn
    module M = ModeSyn
    let rec theoremDecToConDec ((name, ThDecl (GBs, g, MG, i)), r) =
      let theoremToConDec' =
        function
        | (I.Null, V) -> V
        | (Decl (g, D), V) ->
            if Abstract.closedDec (g, (D, I.id))
            then
              theoremToConDec'
                (g,
                  (Abstract.piDepend
                     (((Whnf.normalizeDec (D, I.id)), I.Maybe), V)))
            else error (r, "Free variables in theorem declaration") in
      (GBs,
        (I.ConDec
           (name, NONE, i, I.Normal, (theoremToConDec' (g, (I.Uni I.Type))),
             I.Kind)))
    let rec theoremDecToModeSpine ((name, ThDecl (GBs, g, MG, i)), r) =
      let theoremToModeSpine' =
        function
        | (I.Null, I.Null, mS) -> mS
        | (Decl (g, Dec (x, _)), Decl (MG, m), mS) ->
            theoremToModeSpine' (g, MG, (M.Mapp ((M.Marg (m, x)), mS))) in
      theoremToModeSpine' (g, MG, M.Mnil)
    let ((theoremDecToConDec)(* theoremDecToConDec (name, T) = D'

       Invariant:
       If   name is the name of a theorem
       and  T is the declaration of a theorem
       then D' is a constant type declaration of this theorem
    *)
      (* theoremToConDec' g V = V'

             Invariant:
             If   g = V1 .. Vn
             and  g |- V : kind
             then V' = {V1} .. {Vn} V
             and  . |-  V' : kind
          *)
      (* theoremDecToModeSpine (name, T) = mS'

       Invariant:
       If   name is the name of a theorem
       and  T is the declaration of a theorem
       then mS' is a mode spine reflecting the
         quantifier information for the theorem
    *))
      = theoremDecToConDec
    let theoremDecToModeSpine = theoremDecToModeSpine
  end ;;
