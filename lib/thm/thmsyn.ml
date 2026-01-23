module type THMSYN  =
  sig
    module Names : NAMES
    exception Error of string 
    type order_ =
      | Varg of string list 
      | Lex of order_ list 
      | Simul of order_ list 
    type predicate_ =
      | Less 
      | Leq 
      | Eq 
    type redOrder_ =
      | RedOrder of (predicate_ * order_ * order_) 
    type callpats_ =
      | Callpats of (IntSyn.cid * string option list) list 
    type tDecl_ =
      | TDecl of (order_ * callpats_) 
    type rDecl_ =
      | RDecl of (redOrder_ * callpats_) 
    type tabledDecl_ =
      | TabledDecl of IntSyn.cid 
    type keepTableDecl_ =
      | KeepTableDecl of IntSyn.cid 
    type thDecl_ =
      | ThDecl of ((IntSyn.dec_ IntSyn.ctx_ * IntSyn.dec_ IntSyn.ctx_) list *
      IntSyn.dec_ IntSyn.ctx_ * ModeSyn.mode_ IntSyn.ctx_ * int) 
    type pDecl_ =
      | PDecl of (int * tDecl_) 
    type wDecl_ =
      | WDecl of (Names.qid_ list * callpats_) 
    val theoremDecToConDec :
      ((string * thDecl_) * Paths.region) ->
        ((IntSyn.dec_ IntSyn.ctx_ * IntSyn.dec_ IntSyn.ctx_) list *
          IntSyn.conDec_)
    val theoremDecToModeSpine :
      ((string * thDecl_) * Paths.region) -> ModeSyn.modeSpine_
  end


module ThmSyn(ThmSyn:sig
                       module Abstract : ABSTRACT
                       module Whnf : WHNF
                       module Names' : NAMES
                     end) : THMSYN =
  struct
    module Names = Names'
    exception Error of string 
    let rec error (r, msg) = raise (Error (Paths.wrap (r, msg)))
    type nonrec param_ = string option
    type order_ =
      | Varg of string list 
      | Lex of order_ list 
      | Simul of order_ list 
    type predicate_ =
      | Less 
      | Leq 
      | Eq 
    type redOrder_ =
      | RedOrder of (predicate_ * order_ * order_) 
    type callpats_ =
      | Callpats of (IntSyn.cid * param_ list) list 
    type tDecl_ =
      | TDecl of (order_ * callpats_) 
    type rDecl_ =
      | RDecl of (redOrder_ * callpats_) 
    type tabledDecl_ =
      | TabledDecl of IntSyn.cid 
    type keepTableDecl_ =
      | KeepTableDecl of IntSyn.cid 
    type thDecl_ =
      | ThDecl of ((IntSyn.dec_ IntSyn.ctx_ * IntSyn.dec_ IntSyn.ctx_) list *
      IntSyn.dec_ IntSyn.ctx_ * ModeSyn.mode_ IntSyn.ctx_ * int) 
    type pDecl_ =
      | PDecl of (int * tDecl_) 
    type wDecl_ =
      | WDecl of (Names.qid_ list * callpats_) 
    module I = IntSyn
    module M = ModeSyn
    let rec theoremDecToConDec ((name, ThDecl (GBs, g_, MG, i)), r) =
      let rec theoremToConDec' =
        begin function
        | (I.Null, v_) -> v_
        | (Decl (g_, d_), v_) ->
            if Abstract.closedDec (g_, (d_, I.id))
            then
              begin theoremToConDec'
                      (g_,
                        (Abstract.piDepend
                           (((Whnf.normalizeDec (d_, I.id)), I.Maybe), v_))) end
            else begin error (r, "Free variables in theorem declaration") end end in
  (((GBs,
      (I.ConDec
         (name, None, i, I.Normal, (theoremToConDec' (g_, (I.Uni I.Type))),
           I.Kind))))
    (* theoremToConDec' G V = V'

             Invariant:
             If   G = V1 .. Vn
             and  G |- V : kind
             then V' = {V1} .. {Vn} V
             and  . |-  V' : kind
          *))
let rec theoremDecToModeSpine ((name, ThDecl (GBs, g_, MG, i)), r) =
  let rec theoremToModeSpine' =
    begin function
    | (I.Null, I.Null, mS) -> mS
    | (Decl (g_, Dec (x, _)), Decl (MG, m), mS) ->
        theoremToModeSpine' (g_, MG, (M.Mapp ((M.Marg (m, x)), mS))) end in
theoremToModeSpine' (g_, MG, M.Mnil)
let theoremDecToConDec = theoremDecToConDec
let theoremDecToModeSpine = theoremDecToModeSpine end
