
module type METASYN  =
  sig
    type __Mode =
      | Bot 
      | Top (*! structure IntSyn : INTSYN !*)(* Author: Carsten Schuermann *)
    (* Meta syntax *)
    type __Prefix =
      | Prefix of
      (((IntSyn.dctx)(* Prefix P := *)(*     | Top                  *)
      (* M ::= Bot                  *)(* Mode                       *))
      * ((__Mode)(* G   declarations           *))
      IntSyn.__Ctx * ((int)(* Mtx modes                  *))
      IntSyn.__Ctx) 
    type __State =
      | State of
      (((string)(* State S :=                 *)(* Btx splitting depths       *))
      * ((__Prefix)(*             [name]         *)) *
      ((IntSyn.__Exp)(*             G; Mtx; Btx    *))) 
    type __Sgn =
      | SgnEmpty 
      | ConDec of
      (((IntSyn.__ConDec)(* IS ::= .                   *)
      (* Interface signature        *)(*             |- V           *))
      * __Sgn) 
    val createAtomConst :
      (IntSyn.dctx * IntSyn.__Head) ->
        (((IntSyn.__Exp)(*      | c:V, IS             *)) *
          IntSyn.eclo)
    val createAtomBVar : (IntSyn.dctx * int) -> (IntSyn.__Exp * IntSyn.eclo)
  end;;




module MetaSyn(MetaSyn:sig
                         module Whnf :
                         ((WHNF)(* Meta syntax *)(* Author: Carsten Schuermann *)
                         (*! structure IntSyn' : INTSYN !*))
                       end) : METASYN =
  struct
    exception Error of
      ((string)(*! structure IntSyn = IntSyn' !*)(*! sharing Whnf.IntSyn = IntSyn' !*))
      
    type nonrec __Var = int
    type __Mode =
      | Bot 
      | Top 
    type __Prefix =
      | Prefix of
      (((IntSyn.dctx)(* Prefix P := *)(*     | Top                  *)
      (* M ::= Bot                  *)(* Mode                       *))
      * ((__Mode)(* G   declarations           *))
      IntSyn.__Ctx * ((int)(* Mtx modes                  *))
      IntSyn.__Ctx) 
    type __State =
      | State of
      (((string)(* State S :=                 *)(* Btx splitting depths       *))
      * ((__Prefix)(*             [name]         *)) *
      ((IntSyn.__Exp)(*             G; Mtx; Btx    *))) 
    type __Sgn =
      | SgnEmpty 
      | ConDec of
      (((IntSyn.__ConDec)(* IS ::= .                   *)
      (* Interface signature        *)(*             |- V           *))
      * __Sgn) 
    module I = IntSyn
    let rec createEVarSpine (G, Vs) = createEVarSpineW (G, (Whnf.whnf Vs))
    let rec createEVarSpineW =
      function
      | (G, ((Uni (I.Type), s) as Vs)) -> (I.Nil, Vs)
      | (G, ((Root _, s) as Vs)) -> (I.Nil, Vs)
      | (G, (Pi (((Dec (_, V1) as D), _), V2), s)) ->
          let X = I.newEVar (G, (I.EClo (V1, s))) in
          let (S, Vs) = createEVarSpine (G, (V2, (I.Dot ((I.Exp X), s)))) in
          ((I.App (X, S)), Vs)
    let rec createAtomConst (G, H) =
      let cid = match H with | Const cid -> cid | Skonst cid -> cid in
      let V = I.constType cid in
      let (S, Vs) = createEVarSpine (G, (V, I.id)) in ((I.Root (H, S)), Vs)
    let rec createAtomBVar (G, k) =
      let Dec (_, V) = I.ctxDec (G, k) in
      let (S, Vs) = createEVarSpine (G, (V, I.id)) in
      ((I.Root ((I.BVar k), S)), Vs)
    let ((createAtomConst)(*      | c:V, IS             *)
      (* createEVarSpineW (G, (V, s)) = ((V', s') , S')

       Invariant:
       If   G |- s : G1   and  G1 |- V = Pi {V1 .. Vn}. W : L
       and  G1, V1 .. Vn |- W atomic
       then G |- s' : G2  and  G2 |- V' : L
       and  S = X1; ...; Xn; Nil
       and  G |- W [1.2...n. s o ^n] = V' [s']
       and  G |- S : V [s] >  V' [s']
    *)
      (* s = id *)(* s = id *)(* createAtomConst (G, c) = (U', (V', s'))

       Invariant:
       If   S |- c : Pi {V1 .. Vn}. V
       then . |- U' = c @ (Xn; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
      (* createAtomBVar (G, k) = (U', (V', s'))

       Invariant:
       If   G |- k : Pi {V1 .. Vn}. V
       then . |- U' = k @ (Xn; .. Xn; Nil)
       and  . |- U' : V' [s']
    *))
      = createAtomConst
    let createAtomBVar = createAtomBVar
  end ;;
