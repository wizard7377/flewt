module type METASYN  =
  sig
    type mode_ =
      | Bot 
      | Top 
    type prefix_ =
      | Prefix of
      (((IntSyn.dctx * mode_ IntSyn.ctx_ * int IntSyn.ctx_))(* Mtx modes                  *)
      (* G   declarations           *)) 
    type state_ =
      | State of
      (((string * prefix_ * IntSyn.exp_))(*             G; Mtx; Btx    *)
      (*             [name]         *)) 
    type sgn_ =
      | SgnEmpty 
      | ConDec of (IntSyn.conDec_ * sgn_) 
    val createAtomConst :
      (IntSyn.dctx * IntSyn.head_) -> (IntSyn.exp_ * IntSyn.eclo)
    val createAtomBVar : (IntSyn.dctx * int) -> (IntSyn.exp_ * IntSyn.eclo)
  end


module MetaSyn(MetaSyn:sig module Whnf : WHNF end) : METASYN =
  struct
    exception Error of string 
    type nonrec var_ = int
    type mode_ =
      | Bot 
      | Top 
    type prefix_ =
      | Prefix of
      (((IntSyn.dctx * mode_ IntSyn.ctx_ * int IntSyn.ctx_))(* Mtx modes                  *)
      (* G   declarations           *)) 
    type state_ =
      | State of
      (((string * prefix_ * IntSyn.exp_))(*             G; Mtx; Btx    *)
      (*             [name]         *)) 
    type sgn_ =
      | SgnEmpty 
      | ConDec of (IntSyn.conDec_ * sgn_) 
    module I = IntSyn
    let rec createEVarSpine (g_, vs_) =
      createEVarSpineW (g_, (Whnf.whnf vs_))
    let rec createEVarSpineW =
      begin function
      | (g_, ((Uni (I.Type), s) as vs_)) -> (I.Nil, vs_)
      | (g_, ((Root _, s) as vs_)) -> (I.Nil, vs_)
      | (g_, (Pi (((Dec (_, v1_) as d_), _), v2_), s)) ->
          let x_ = I.newEVar (g_, (I.EClo (v1_, s))) in
          let (s_, vs_) =
            createEVarSpine (g_, (v2_, (I.Dot ((I.Exp x_), s)))) in
          ((I.App (x_, s_)), vs_) end(* s = id *)(* s = id *)
    let rec createAtomConst (g_, h_) =
      let cid =
        begin match h_ with | Const cid -> cid | Skonst cid -> cid end in
    let v_ = I.constType cid in
    let (s_, vs_) = createEVarSpine (g_, (v_, I.id)) in
    ((I.Root (h_, s_)), vs_)
  let rec createAtomBVar (g_, k) =
    let Dec (_, v_) = I.ctxDec (g_, k) in
    let (s_, vs_) = createEVarSpine (g_, (v_, I.id)) in
    ((I.Root ((I.BVar k), s_)), vs_)
  let createAtomConst = createAtomConst
  let createAtomBVar = createAtomBVar end
