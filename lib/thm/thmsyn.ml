
(* Theorems *)
(* Author: Carsten Schuermann *)
(* Modified: Brigitte Pientka *)
module type THMSYN  =
  sig
    module Names : NAMES
    exception Error of string 
    (*! type Param = string option !*)
    type __Order =
      | Varg of string list 
      | Lex of __Order list 
      | Simul of __Order list 
    (* -bp *)
    type __Predicate =
      | Less 
      | Leq 
      | Eq 
    type __RedOrder =
      | RedOrder of (__Predicate * __Order * __Order) 
    type __Callpats =
      | Callpats of (IntSyn.cid * string option list) list 
    (* Termination declaration *)
    type __TDecl =
      | TDecl of (__Order * __Callpats) 
    (* -bp *)
    (* Reduction declaration *)
    type __RDecl =
      | RDecl of (__RedOrder * __Callpats) 
    (* Tabled declaration *)
    type __TabledDecl =
      | TabledDecl of IntSyn.cid 
    (* KeepTable declaration *)
    type __KeepTableDecl =
      | KeepTableDecl of IntSyn.cid 
    (* Theorem declaration  *)
    type __ThDecl =
      | ThDecl of ((IntSyn.__Dec IntSyn.__Ctx * IntSyn.__Dec IntSyn.__Ctx)
      list * IntSyn.__Dec IntSyn.__Ctx * ModeSyn.__Mode IntSyn.__Ctx * int) 
    (* Proof declaration *)
    type __PDecl =
      | PDecl of (int * __TDecl) 
    (* World declaration *)
    (*  datatype WDecl = 
    WDecl of (IntSyn.Dec IntSyn.Ctx * 
	      IntSyn.Dec IntSyn.Ctx) list * Callpats
*)
    type __WDecl =
      | WDecl of (Names.__Qid list * __Callpats) 
    val theoremDecToConDec :
      ((string * __ThDecl) * Paths.region) ->
        ((IntSyn.__Dec IntSyn.__Ctx * IntSyn.__Dec IntSyn.__Ctx) list *
          IntSyn.__ConDec)
    val theoremDecToModeSpine :
      ((string * __ThDecl) * Paths.region) -> ModeSyn.__ModeSpine
  end;;




(* Theorems *)
(* Author: Carsten Schuermann *)
(* Modified: Brigitte Pientka *)
module ThmSyn(ThmSyn:sig
                       (*! structure IntSyn : INTSYN !*)
                       (*! structure ModeSyn' : MODESYN !*)
                       (*! sharing ModeSyn'.IntSyn = IntSyn !*)
                       module Abstract : ABSTRACT
                       module Whnf : WHNF
                       (*! sharing Abstract.IntSyn = IntSyn !*)
                       (*! sharing Whnf.IntSyn = IntSyn !*)
                       (*! structure Paths' : PATHS !*)
                       module Names' : NAMES
                     end) : THMSYN =
  struct
    (*! sharing Names'.IntSyn = IntSyn !*)
    (*! structure IntSyn = IntSyn !*)
    (*! structure ModeSyn = ModeSyn' *)
    (*! structure Paths = Paths' !*)
    module Names = Names'
    exception Error of string 
    let rec error (r, msg) = raise (Error (Paths.wrap (r, msg)))
    type nonrec __Param = string option
    type __Order =
      | Varg of string list 
      | Lex of __Order list 
      | Simul of __Order list 
    (* -bp *)
    type __Predicate =
      | Less 
      | Leq 
      | Eq 
    type __RedOrder =
      | RedOrder of (__Predicate * __Order * __Order) 
    type __Callpats =
      | Callpats of (IntSyn.cid * __Param list) list 
    (* Termination declaration *)
    type __TDecl =
      | TDecl of (__Order * __Callpats) 
    (* -bp *)
    (* Reduction declaration *)
    type __RDecl =
      | RDecl of (__RedOrder * __Callpats) 
    (* Tabled declaration *)
    type __TabledDecl =
      | TabledDecl of IntSyn.cid 
    (* KeepTable declaration *)
    type __KeepTableDecl =
      | KeepTableDecl of IntSyn.cid 
    (* Theorem declaration *)
    type __ThDecl =
      | ThDecl of ((IntSyn.__Dec IntSyn.__Ctx * IntSyn.__Dec IntSyn.__Ctx)
      list * IntSyn.__Dec IntSyn.__Ctx * ModeSyn.__Mode IntSyn.__Ctx * int) 
    (* Proof declaration *)
    type __PDecl =
      | PDecl of (int * __TDecl) 
    (* World declaration *)
    (*  datatype WDecl =
    WDecl of (IntSyn.Dec IntSyn.Ctx *
              IntSyn.Dec IntSyn.Ctx) list * Callpats *)
    type __WDecl =
      | WDecl of (Names.__Qid list * __Callpats) 
    module I = IntSyn
    module M = ModeSyn
    let rec theoremDecToConDec ((name, ThDecl (GBs, __g, MG, i)), r) =
      let rec theoremToConDec' =
        function
        | (I.Null, __v) -> __v
        | (Decl (__g, __d), __v) ->
            if Abstract.closedDec (__g, (__d, I.id))
            then
              theoremToConDec'
                (__g,
                  (Abstract.piDepend
                     (((Whnf.normalizeDec (__d, I.id)), I.Maybe), __v)))
            else error (r, "Free variables in theorem declaration") in
      (GBs,
        (I.ConDec
           (name, None, i, I.Normal, (theoremToConDec' (__g, (I.Uni I.Type))),
             I.Kind)))
    let rec theoremDecToModeSpine ((name, ThDecl (GBs, __g, MG, i)), r) =
      let rec theoremToModeSpine' =
        function
        | (I.Null, I.Null, mS) -> mS
        | (Decl (__g, Dec (x, _)), Decl (MG, m), mS) ->
            theoremToModeSpine' (__g, MG, (M.Mapp ((M.Marg (m, x)), mS))) in
      theoremToModeSpine' (__g, MG, M.Mnil)
    (* theoremDecToConDec (name, T) = __d'

       Invariant:
       If   name is the name of a theorem
       and  T is the declaration of a theorem
       then __d' is a constant type declaration of this theorem
    *)
    (* theoremToConDec' __g __v = __v'

             Invariant:
             If   __g = V1 .. Vn
             and  __g |- __v : kind
             then __v' = {V1} .. {Vn} __v
             and  . |-  __v' : kind
          *)
    (* theoremDecToModeSpine (name, T) = mS'

       Invariant:
       If   name is the name of a theorem
       and  T is the declaration of a theorem
       then mS' is a mode spine reflecting the
         quantifier information for the theorem
    *)
    let theoremDecToConDec = theoremDecToConDec
    let theoremDecToModeSpine = theoremDecToModeSpine
  end ;;
