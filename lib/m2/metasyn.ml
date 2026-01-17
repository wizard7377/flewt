
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
      * ((__Mode)(* g   declarations           *))
      IntSyn.__Ctx * ((int)(* Mtx modes                  *))
      IntSyn.__Ctx) 
    type __State =
      | State of
      (((string)(* State S :=                 *)(* Btx splitting depths       *))
      * ((__Prefix)(*             [name]         *)) *
      ((IntSyn.__Exp)(*             g; Mtx; Btx    *))) 
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
      * ((__Mode)(* g   declarations           *))
      IntSyn.__Ctx * ((int)(* Mtx modes                  *))
      IntSyn.__Ctx) 
    type __State =
      | State of
      (((string)(* State S :=                 *)(* Btx splitting depths       *))
      * ((__Prefix)(*             [name]         *)) *
      ((IntSyn.__Exp)(*             g; Mtx; Btx    *))) 
    type __Sgn =
      | SgnEmpty 
      | ConDec of
      (((IntSyn.__ConDec)(* IS ::= .                   *)
      (* Interface signature        *)(*             |- V           *))
      * __Sgn) 
    module I = IntSyn
    let rec createEVarSpine (g, Vs) = createEVarSpineW (g, (Whnf.whnf Vs))
    let rec createEVarSpineW =
      function
      | (g, ((Uni (I.Type), s) as Vs)) -> (I.Nil, Vs)
      | (g, ((Root _, s) as Vs)) -> (I.Nil, Vs)
      | (g, (Pi (((Dec (_, V1) as D), _), V2), s)) ->
          let X = I.newEVar (g, (I.EClo (V1, s))) in
          let (S, Vs) = createEVarSpine (g, (V2, (I.Dot ((I.Exp X), s)))) in
          ((I.App (X, S)), Vs)
    let rec createAtomConst (g, H) =
      let cid = match H with | Const cid -> cid | Skonst cid -> cid in
      let V = I.constType cid in
      let (S, Vs) = createEVarSpine (g, (V, I.id)) in ((I.Root (H, S)), Vs)
    let rec createAtomBVar (g, k) =
      let Dec (_, V) = I.ctxDec (g, k) in
      let (S, Vs) = createEVarSpine (g, (V, I.id)) in
      ((I.Root ((I.BVar k), S)), Vs)
    let ((createAtomConst)(*      | c:V, IS             *)
      (* createEVarSpineW (g, (V, s)) = ((V', s') , S')

       Invariant:
       If   g |- s : G1   and  G1 |- V = Pi {V1 .. Vn}. W : L
       and  G1, V1 .. Vn |- W atomic
       then g |- s' : G2  and  G2 |- V' : L
       and  S = X1; ...; Xn; Nil
       and  g |- W [1.2...n. s o ^n] = V' [s']
       and  g |- S : V [s] >  V' [s']
    *)
      (* s = id *)(* s = id *)(* createAtomConst (g, c) = (U', (V', s'))

       Invariant:
       If   S |- c : Pi {V1 .. Vn}. V
       then . |- U' = c @ (Xn; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
      (* createAtomBVar (g, k) = (U', (V', s'))

       Invariant:
       If   g |- k : Pi {V1 .. Vn}. V
       then . |- U' = k @ (Xn; .. Xn; Nil)
       and  . |- U' : V' [s']
    *))
      = createAtomConst
    let createAtomBVar = createAtomBVar
  end ;;
