
(* Meta syntax *)
(* Author: Carsten Schuermann *)
module type METASYN  =
  sig
    (*! structure IntSyn : INTSYN !*)
    type __Mode =
      | Bot 
      | Top 
    (*     | Top                  *)
    type __Prefix =
      | Prefix of (IntSyn.dctx * __Mode IntSyn.__Ctx * int IntSyn.__Ctx) 
    (* __g   declarations           *)
    (* Mtx modes                  *)
    (* Btx splitting depths       *)
    type __State =
      | State of (string * __Prefix * IntSyn.__Exp) 
    (*             [name]         *)
    (*             __g; Mtx; Btx    *)
    (*             |- __v           *)
    type __Sgn =
      | SgnEmpty 
      | ConDec of (IntSyn.__ConDec * __Sgn) 
    (*      | c:__v, IS             *)
    val createAtomConst :
      (IntSyn.dctx * IntSyn.__Head) -> (IntSyn.__Exp * IntSyn.eclo)
    val createAtomBVar : (IntSyn.dctx * int) -> (IntSyn.__Exp * IntSyn.eclo)
  end;;




(* Meta syntax *)
(* Author: Carsten Schuermann *)
module MetaSyn(MetaSyn:sig
                         (*! structure IntSyn' : INTSYN !*)
                         module Whnf : WHNF
                       end) : METASYN =
  struct
    (*! sharing Whnf.IntSyn = IntSyn' !*)
    (*! structure IntSyn = IntSyn' !*)
    exception Error of string 
    type nonrec __Var = int
    type __Mode =
      | Bot 
      | Top 
    (*     | Top                  *)
    type __Prefix =
      | Prefix of (IntSyn.dctx * __Mode IntSyn.__Ctx * int IntSyn.__Ctx) 
    (* __g   declarations           *)
    (* Mtx modes                  *)
    (* Btx splitting depths       *)
    type __State =
      | State of (string * __Prefix * IntSyn.__Exp) 
    (*             [name]         *)
    (*             __g; Mtx; Btx    *)
    (*             |- __v           *)
    type __Sgn =
      | SgnEmpty 
      | ConDec of (IntSyn.__ConDec * __Sgn) 
    (*      | c:__v, IS             *)
    module I = IntSyn
    let rec createEVarSpine (__g, __Vs) = createEVarSpineW (__g, (Whnf.whnf __Vs))
    let rec createEVarSpineW =
      function
      | (__g, ((Uni (I.Type), s) as __Vs)) -> (I.Nil, __Vs)
      | (__g, ((Root _, s) as __Vs)) -> (I.Nil, __Vs)
      | (__g, (Pi (((Dec (_, V1) as __d), _), V2), s)) ->
          let x = I.newEVar (__g, (I.EClo (V1, s))) in
          let (S, __Vs) = createEVarSpine (__g, (V2, (I.Dot ((I.Exp x), s)))) in
          ((I.App (x, S)), __Vs)
    let rec createAtomConst (__g, H) =
      let cid = match H with | Const cid -> cid | Skonst cid -> cid in
      let __v = I.constType cid in
      let (S, __Vs) = createEVarSpine (__g, (__v, I.id)) in ((I.Root (H, S)), __Vs)
    let rec createAtomBVar (__g, k) =
      let Dec (_, __v) = I.ctxDec (__g, k) in
      let (S, __Vs) = createEVarSpine (__g, (__v, I.id)) in
      ((I.Root ((I.BVar k), S)), __Vs)
    (* createEVarSpineW (__g, (__v, s)) = ((__v', s') , S')

       Invariant:
       If   __g |- s : G1   and  G1 |- __v = Pi {V1 .. Vn}. W : __l
       and  G1, V1 .. Vn |- W atomic
       then __g |- s' : G2  and  G2 |- __v' : __l
       and  S = X1; ...; Xn; Nil
       and  __g |- W [1.2...n. s o ^n] = __v' [s']
       and  __g |- S : __v [s] >  __v' [s']
    *)
    (* s = id *)
    (* s = id *)
    (* createAtomConst (__g, c) = (__u', (__v', s'))

       Invariant:
       If   S |- c : Pi {V1 .. Vn}. __v
       then . |- __u' = c @ (Xn; .. Xn; Nil)
       and  . |- __u' : __v' [s']
    *)
    (* createAtomBVar (__g, k) = (__u', (__v', s'))

       Invariant:
       If   __g |- k : Pi {V1 .. Vn}. __v
       then . |- __u' = k @ (Xn; .. Xn; Nil)
       and  . |- __u' : __v' [s']
    *)
    let createAtomConst = createAtomConst
    let createAtomBVar = createAtomBVar
  end ;;
