module type REDUNDANT  =
  sig exception Error of string  val convert : Tomega.prg_ -> Tomega.prg_ end


module Redundant(Redundant:sig module Opsem : OPSEM end) : REDUNDANT =
  struct
    exception Error of string 
    module T = Tomega
    module I = IntSyn
    let rec optionRefEqual (r1, r2, func) = if r1 = r2 then begin true end
      else begin
        (begin match (r1, r2) with
         | ({ contents = None }, { contents = None }) -> true
         | ({ contents = Some (p1_) }, { contents = Some (p2_) }) ->
             func (p1_, p2_)
         | _ -> false end) end
let rec convert =
  begin function
  | Lam (d_, p_) -> T.Lam (d_, (convert p_))
  | New (p_) -> T.New (convert p_)
  | Choose (p_) -> T.Choose (convert p_)
  | PairExp (m_, p_) -> T.PairExp (m_, (convert p_))
  | PairBlock (rho, p_) -> T.PairBlock (rho, (convert p_))
  | PairPrg (p1_, p2_) -> T.PairPrg ((convert p1_), (convert p2_))
  | T.Unit -> T.Unit
  | Var x -> T.Var x
  | Const x -> T.Const x
  | Redex (p_, s_) -> T.Redex ((convert p_), (convertSpine s_))
  | Rec (d_, p_) -> T.Rec (d_, (convert p_))
  | Case (Cases (o_)) -> T.Case (T.Cases (convertCases o_))
  | Let (d_, p1_, p2_) -> T.Let (d_, (convert p1_), (convert p2_)) end
let rec convertSpine =
  begin function
  | T.Nil -> T.Nil
  | AppExp (i_, s_) -> T.AppExp (i_, (convertSpine s_))
  | AppBlock (i_, s_) -> T.AppBlock (i_, (convertSpine s_))
  | AppPrg (p_, s_) -> T.AppPrg ((convert p_), (convertSpine s_))
  | SClo (s_, t) -> raise (Error "SClo should not exist") end
let rec expEqual (e1_, e2_) = Conv.conv ((e1_, I.id), (e2_, I.id))
let rec IsubEqual (sub1, sub2) = Conv.convSub (sub1, sub2)
let rec blockEqual =
  begin function
  | (Bidx x, Bidx x') -> x = x'
  | (LVar (r, sub1, (cid, sub2)), LVar (r', sub1', (cid', sub2'))) ->
      (optionRefEqual (r, r', blockEqual)) &&
        ((IsubEqual (sub1, sub1')) &&
           ((cid = cid') && (IsubEqual (sub1', sub2'))))
  | _ -> false end(* Should not occur -- ap 2/18/03 *)
let rec decEqual =
  begin function
  | (UDec (d1_), (UDec (d2_), t2)) ->
      Conv.convDec ((d1_, I.id), (d2_, (T.coerceSub t2)))
  | (PDec (_, f1_, _, _), (PDec (_, f2_, _, _), t2)) ->
      T.convFor ((f1_, T.id), (f2_, t2))
  | _ -> false end
let rec caseEqual =
  begin function
  | ((Psi1, t1, p1_)::o1_, ((Psi2, t2, p2_)::o2_, tAfter)) ->
      let t2' = T.comp ((T.invertSub tAfter), t2) in
      let t = Opsem.createVarSub (Psi1, Psi2) in
      let t' = T.comp (t2', t) in
      let doMatch = begin try begin Opsem.matchSub (Psi1, t1, t'); true end
        with | NoMatch -> false end in
      ((if doMatch
        then
          begin let newT = T.normalizeSub t in
                let stillMatch = IsSubRenamingOnly newT in
                stillMatch && (prgEqual (p1_, (p2_, (cleanSub newT)))) end
        else begin false end)
      (* Note:  (Psi1 |- t1: Psi0) *)(* Psi1 |- t: Psi2 *)
      (* Psi1 |- t' : Psi_0 *)) | ([], ([], t2)) -> true
| _ -> false end(* Recall that we (Psi2, t2, P2)[tAfter] = (Psi2, (tAfterInv \circ t2), P2) *)
let rec spineEqual =
  begin function
  | (T.Nil, (T.Nil, t2)) -> true
  | (AppExp (e1_, s1_), (AppExp (e2_, s2_), t2)) ->
      (Conv.conv ((e1_, I.id), (e2_, (T.coerceSub t2)))) &&
        (spineEqual (s1_, (s2_, t2)))
  | (AppBlock (b1_, s1_), (AppBlock (b2_, s2_), t2)) ->
      (blockEqual (b1_, (I.blockSub (b2_, (T.coerceSub t2))))) &&
        (spineEqual (s1_, (s2_, t2)))
  | (AppPrg (p1_, s1_), (AppPrg (p2_, s2_), t2)) ->
      (prgEqual (p1_, (p2_, t2))) && (spineEqual (s1_, (s2_, t2)))
  | (SClo (s_, t1), (SClo (s, t2a), t2)) ->
      raise (Error "SClo should not exist!")
  | _ -> false end(* there are no SClo created in converter *)
let rec prgEqual =
  begin function
  | (Lam (d1_, p1_), (Lam (d2_, p2_), t2)) ->
      (decEqual (d1_, (d2_, t2))) && (prgEqual (p1_, (p2_, (T.dot1 t2))))
  | (New (p1_), (New (p2_), t2)) -> prgEqual (p1_, (p2_, t2))
  | (Choose (p1_), (Choose (p2_), t2)) -> prgEqual (p1_, (p2_, t2))
  | (PairExp (u1_, p1_), (PairExp (u2_, p2_), t2)) ->
      (Conv.conv ((u1_, I.id), (u2_, (T.coerceSub t2)))) &&
        (prgEqual (p1_, (p2_, t2)))
  | (PairBlock (b1_, p1_), (PairBlock (b2_, p2_), t2)) ->
      (blockEqual (b1_, (I.blockSub (b2_, (T.coerceSub t2))))) &&
        (prgEqual (p1_, (p2_, t2)))
  | (PairPrg (P1a, P1b), (PairPrg (P2a, P2b), t2)) ->
      (prgEqual (P1a, (P2a, t2))) && (prgEqual (P1b, (P2b, t2)))
  | (T.Unit, (T.Unit, t2)) -> true
  | (Const lemma1, (Const lemma2, _)) -> lemma1 = lemma2
  | (Var x1, (Var x2, t2)) ->
      (begin match getFrontIndex (T.varSub (x2, t2)) with
       | None -> false
       | Some i -> x1 = i end)
  | (Redex (p1_, s1_), (Redex (p2_, s2_), t2)) ->
      (prgEqual (p1_, (p2_, t2))) && (spineEqual (s1_, (s2_, t2)))
  | (Rec (d1_, p1_), (Rec (d2_, p2_), t2)) ->
      (decEqual (d1_, (d2_, t2))) && (prgEqual (p1_, (p2_, (T.dot1 t2))))
  | (Case (Cases (o1_)), (Case (Cases (o2_)), t2)) ->
      caseEqual (o1_, (o2_, t2))
  | (Let (d1_, P1a, P1b), (Let (d2_, P2a, P2b), t2)) ->
      (decEqual (d1_, (d2_, t2))) && (prgEqual (P1a, (P2a, t2)))
  | (PClo (p1_, t1), (PClo (p2_, t2a), t2b)) ->
      raise (Error "PClo should not exist!")
  | (EVar (Psi1, P1optRef, f1_, _, _, _),
     (EVar (Psi2, P2optref, f2_, _, _, _), t2)) ->
      raise (Error "No EVARs should exist!")
  | _ -> false end(* there are no PClo created in converter *)(*      | prgEqual ((T.Root (H1, S1)), (T.Root (H2, S2), t2)) =
                (case (H1, H2)
                   of (T.Const lemma1, T.Const lemma2) => ((lemma1=lemma2) andalso (spineEqual(S1, (S2,t2))))
                 |  (T.Var x1, T.Var x2) =>
                           (case getFrontIndex(T.varSub(x2,t2)) of
                              NONE => false
                            | SOME i => ((x1 = i) andalso (spineEqual(S1, (S2,t2)))))
                 |  _ => false)
*)
let rec convertCases =
  begin function
  | (a_)::c_ ->
      let ((Psi, t, p_), c'_) = removeRedundancy (a_, c_) in
      (::) (Psi, t, (convert p_)) convertCases c'_
  | c_ -> c_ end
let rec removeRedundancy =
  begin function
  | (c_, []) -> (c_, [])
  | (c_, (c'_)::rest) ->
      let (C'')::cs_ = mergeIfNecessary (c_, c'_) in
      let (C''', rest') = removeRedundancy (C'', rest) in
      (C''', (cs_ @ rest')) end
let rec getFrontIndex =
  begin function
  | Idx k -> Some k
  | Prg (p_) -> getPrgIndex p_
  | Exp (u_) -> getExpIndex u_
  | Block (b_) -> getBlockIndex b_
  | T.Undef -> None end
let rec getPrgIndex =
  begin function
  | Var k -> Some k
  | Redex (p_, T.Nil) -> getPrgIndex p_
  | PClo (p_, t) ->
      (begin match getPrgIndex p_ with
       | None -> None
       | Some i -> getFrontIndex (T.varSub (i, t)) end)
  | _ -> None end(* it is possible in the matchSub that we will get PClo under a sub (usually id) *)
let rec getExpIndex =
  begin function
  | Root (BVar k, I.Nil) -> Some k
  | Redex (u_, I.Nil) -> getExpIndex u_
  | EClo (u_, t) ->
      (begin match getExpIndex u_ with
       | None -> None
       | Some i -> getFrontIndex (T.revCoerceFront (I.bvarSub (i, t))) end)
  | Lam (Dec (_, u1_), u2_) as u_ ->
      (begin try Some (Whnf.etaContract u_) with | Whnf.Eta -> None end)
  | _ -> None end
let rec getBlockIndex = begin function | Bidx k -> Some k | _ -> None end
let rec cleanSub =
  begin function
  | Shift _ as s_ -> s_
  | Dot (Ft1, s1) ->
      (begin match getFrontIndex Ft1 with
       | None -> T.Dot (Ft1, (cleanSub s1))
       | Some index -> T.Dot ((T.Idx index), (cleanSub s1)) end) end
let rec IsSubRenamingOnly =
  begin function
  | Shift n -> true
  | Dot (Ft1, s1) ->
      (begin match getFrontIndex Ft1 with | None -> false | Some _ -> true end)
      && (IsSubRenamingOnly s1) end
let rec mergeSpines =
  begin function
  | (T.Nil, (T.Nil, t2)) -> T.Nil
  | (AppExp (e1_, s1_), (AppExp (e2_, s2_), t2)) ->
      if Conv.conv ((e1_, I.id), (e2_, (T.coerceSub t2)))
      then begin T.AppExp (e1_, (mergeSpines (s1_, (s2_, t2)))) end
      else begin raise (Error "Spine not equal (AppExp)") end
  | (AppBlock (b1_, s1_), (AppBlock (b2_, s2_), t2)) ->
      if blockEqual (b1_, (I.blockSub (b2_, (T.coerceSub t2))))
      then begin T.AppBlock (b1_, (mergeSpines (s1_, (s2_, t2)))) end
      else begin raise (Error "Spine not equal (AppBlock)") end
| (AppPrg (p1_, s1_), (AppPrg (p2_, s2_), t2)) ->
    if prgEqual (p1_, (p2_, t2))
    then begin T.AppPrg (p1_, (mergeSpines (s1_, (s2_, t2)))) end
    else begin raise (Error "Prg (in App) not equal") end
| (SClo (s_, t1), (SClo (s, t2a), t2)) ->
    raise (Error "SClo should not exist!")
| _ -> raise (Error "Spine are not equivalent") end(* there are no SClo created in converter *)
let rec mergePrgs =
  begin function
  | (Lam (d1_, p1_), (Lam (d2_, p2_), t2)) ->
      if (decEqual (d1_, (d2_, t2))) && (prgEqual (p1_, (p2_, (T.dot1 t2))))
      then begin T.Lam (d1_, p1_) end
      else begin raise (Error "Lambda don't match") end
  | (New (p1_), (New (p2_), t2)) ->
      if prgEqual (p1_, (p2_, t2)) then begin T.New p1_ end
      else begin raise (Error "New don't match") end
| (Choose (p1_), (Choose (p2_), t2)) ->
    if prgEqual (p1_, (p2_, t2)) then begin T.Choose p1_ end
    else begin raise (Error "Choose don't match") end
| (PairExp (u1_, p1_), (PairExp (u2_, p2_), t2)) ->
    let t2' = T.coerceSub t2 in
    if Conv.conv ((u1_, I.id), (u2_, t2'))
    then begin T.PairExp (u1_, (mergePrgs (p1_, (p2_, t2)))) end
      else begin raise (Error "cannot merge PairExp") end
| (PairBlock (b1_, p1_), (PairBlock (b2_, p2_), t2)) ->
    let B2' = I.blockSub (b2_, (T.coerceSub t2)) in
    if blockEqual (b1_, B2')
    then begin T.PairBlock (b1_, (mergePrgs (p1_, (p2_, t2)))) end
      else begin raise (Error "cannot merge PairBlock") end
| (PairPrg (P1a, P1b), (PairPrg (P2a, P2b), t2)) ->
    if prgEqual (P1a, (P2a, t2))
    then begin T.PairPrg (P1a, (mergePrgs (P1b, (P2b, t2)))) end
    else begin raise (Error "cannot merge PairPrg") end
| (T.Unit, (T.Unit, t2)) -> T.Unit
| (Const lemma1, (Const lemma2, _)) ->
    if lemma1 = lemma2 then begin T.Const lemma1 end
    else begin raise (Error "Constants do not match.") end
| (Var x1, (Var x2, t2)) ->
    (begin match getFrontIndex (T.varSub (x2, t2)) with
     | None -> raise (Error "Variables do not match.")
     | Some i -> if x1 = i then begin T.Var x1 end
         else begin raise (Error "Variables do not match.") end end)
| (Redex (p1_, s1_), (Redex (p2_, s2_), t2)) ->
    let newS = mergeSpines (s1_, (s2_, t2)) in
    if prgEqual (p1_, (p2_, t2)) then begin T.Redex (p1_, newS) end
      else begin raise (Error "Redex Prgs don't match") end
| (Rec (d1_, p1_), (Rec (d2_, p2_), t2)) ->
    if (decEqual (d1_, (d2_, t2))) && (prgEqual (p1_, (p2_, (T.dot1 t2))))
    then begin T.Rec (d1_, p1_) end
    else begin raise (Error "Rec's don't match") end
| (Case (Cases (o1_)), (Case (Cases ((c_)::[])), t2)) ->
    T.Case (T.Cases (mergeCase (o1_, (c_, t2))))
| (Case (o1_), (Case (o2_), t2)) -> raise (Error "Invariant Violated")
| (PClo (p1_, t1), (PClo (p2_, t2a), t2b)) ->
    raise (Error "PClo should not exist!")
| (Let (d1_, P1a, P1b), (Let (d2_, P2a, P2b), t2)) ->
    if (decEqual (d1_, (d2_, t2))) && (prgEqual (P1a, (P2a, t2)))
    then begin T.Let (d1_, P1a, (mergePrgs (P1b, (P2b, (T.dot1 t2))))) end
    else begin raise (Error "Let don't match") end
| (EVar (Psi1, P1optRef, f1_, _, _, _),
   (EVar (Psi2, P2optref, f2_, _, _, _), t2)) ->
    raise (Error "No EVARs should exist!")
| _ ->
    raise (Error "Redundancy in cases could not automatically be removed.") end
(* there are no PClo created in converter *)(* By invariant the second case should be a list of one *)
(* three possible outcomes -
                   (1) We merge the cases together
                   (2) Cases are incompatible (duplicated)
                   (3) Cases are duplicate but all results are the same
                       which means we need to continue merging
                 *)
(* check the case now *)(*      | mergePrgs ((T.Root (H1, S1)), (T.Root (H2, S2), t2)) =
                (case (H1, H2)
                   of (T.Const lemma1, T.Const lemma2) =>
                     if (lemma1=lemma2) then
                        T.Root (H1, mergeSpines((S1),(S2,t2)))
                     else raise Error "Roots do not match"
                   |  (T.Var x1, T.Var x2) =>
                           (case getFrontIndex(T.varSub(x2,t2)) of
                              NONE => raise Error "Root does not match."
                            | SOME i =>
                                (if (x1 = i) then
                                   T.Root (T.Var x1, mergeSpines((S1),(S2,t2)))
                                 else
                                   raise Error "Root does not match."))
                   |  _ => raise Error "Root does not match.")
*)
let rec invertSub s =
  let rec lookup =
    begin function
    | (n, Shift _, p) -> None
    | (n, Dot (T.Undef, s'), p) -> lookup ((n + 1), s', p)
    | (n, Dot (Ft, s'), p) ->
        (begin match getFrontIndex Ft with
         | None -> lookup ((n + 1), s', p)
         | Some k -> if k = p then begin Some n end
             else begin lookup ((n + 1), s', p) end end) end in
let rec invertSub'' =
begin function
| (0, si) -> si
| (p, si) ->
    (begin match lookup (1, s, p) with
     | Some k -> invertSub'' ((p - 1), (T.Dot ((T.Idx k), si)))
     | None -> invertSub'' ((p - 1), (T.Dot (T.Undef, si))) end) end in
let rec invertSub' =
begin function
| (n, Shift p) -> invertSub'' (p, (T.Shift n))
| (n, Dot (_, s')) -> invertSub' ((n + 1), s') end in
invertSub' (0, s)
let rec printSub =
  begin function
  | Shift k -> print (((^) "Shift " Int.toString k) ^ "\n")
  | Dot (Idx k, s) ->
      (begin print (((^) "Idx " Int.toString k) ^ " (DOT) "); printSub s end)
  | Dot (Prg (EVar _), s) -> (begin print "PRG_EVAR (DOT) "; printSub s end)
  | Dot (Exp (EVar _), s) -> (begin print "EXP_EVAR (DOT) "; printSub s end)
| Dot (Prg (p_), s) -> (begin print "PRG (DOT) "; printSub s end)
| Dot (Exp (e_), s) -> (begin print "EXP (DOT) "; printSub s end)
| Dot (Block (b_), s) -> (begin print "BLOCK (DOT) "; printSub s end)
| Dot (T.Undef, s) -> (begin print "UNDEF. (DOT) "; printSub s end) end
let rec mergeCase =
  begin function
  | ([], c_) -> raise (Error "Case incompatible, cannot merge")
  | (((Psi1, t1, p1_)::o_ as l_), (((Psi2, t2, p2_), tAfter) as c_)) ->
      let tAfterInv = T.invertSub tAfter in
      let t3 = T.comp (tAfterInv, t2) in
      let t = Opsem.createVarSub (Psi1, Psi2) in
      let t' = T.comp (t3, t) in
      let doMatch = begin try begin Opsem.matchSub (Psi1, t1, t'); true end
        with | NoMatch -> false end in
      ((if doMatch
        then
          begin let newT = T.normalizeSub t in
                let stillMatch = IsSubRenamingOnly newT in
                (((if stillMatch
                   then
                     begin (Psi1, t1,
                             (mergePrgs (p1_, (p2_, (cleanSub newT))))) :: o_ end
                  else begin
                    ((if (length o_) = 0 then begin (Psi2, t3, p2_) :: l_ end
                    else begin (::) (Psi1, t1, p1_) mergeCase (o_, c_) end)
                  (* We tried all the cases, and we can now add it *)
                  (* Try other cases *)) end))
        (* Since the case matches, lets continue the merge on P1 and P2
           * Note that removing the redundancy of other case statements
           * is handled recursively ... see convertCases
           *)
        (* Note that tAfter and newT are both renaming substitutions *)) end
  else begin ((if (length o_) = 0 then begin (Psi2, t3, p2_) :: l_ end
    else begin (::) (Psi1, t1, p1_) mergeCase (o_, c_) end)
  (* We tried all the cases, and we can now add it *)
  (* Try other cases *)) end)
(*
        val _ = printCtx(Psi1)
        val _ = printCtx(Psi2)
          *)
(* Psi1 |- P1 : F[t1] *)(* Psi2 |- P2 : F[t2] *)
(* Psi1 |- t1 : Psi1' *)(* Psi2 |- t2 : Psi2' *)
(* By invariant,we assume *)(* Psi1' |- tAfter: Psi2' *)
(* Psi2' |- tAfterInv : Psi1' *)(* So now we have
         P1 makes sense in Psi1, t1 goes from Psi1' to Psi1.

         Psi1 |- t1 : Psi1'
         Psi2 |- t3 : Psi1'
         *)
(* Psi1 |- t : Psi2 *)(* Psi1 |- t' : Psi1' *)(* If we can get this to match, then Psi1 |- P2[t] *)) end
let rec mergeIfNecessary (((Psi1, s1, p1_) as c_), ((Psi2, s2, p2_) as c'_))
  =
  let t = Opsem.createVarSub (Psi1, Psi2) in
  let t' = T.comp (s2, t) in
  let doMatch = begin try begin Opsem.matchSub (Psi1, s1, t'); true end
    with | NoMatch -> false end in
  ((if not doMatch then begin [c_; c'_] end
    else begin
      (let newT = T.normalizeSub t in
       if IsSubRenamingOnly newT
       then
         begin ((begin try
                         [(Psi1, s1,
                            (mergePrgs (p1_, (p2_, (cleanSub newT)))))]
                 with
                 | Error s ->
                     raise
                       (Error
                          (("***WARNING*** -- redundant case automatically ANNIHILATED:  "
                              ^ s)
                             ^ "\n")) end)
       (* In this case, C' is redundant and cannot be fixed, so C' will never be called
               * [C,C']
               *)
       (* (print ("***WARNING*** -- redundant case automatically ANNIHILATED:  " ^ s ^ "\n") ; [C]) *)) end
      else begin [c_; c'_] end) end)
(* Note that s1 is a substitution s.t.  Psi1 |- s1: Psi0
        and s2 is a substitution s.t.         Psi2 |- s2: Psi0

        It is possible that this property is lost when the case is executed
        with a different Psi0 which can happen during recursive calls
        (as the context grows).

        In that case:
          Psi, Psi1 |- X1...Xn, id{Psi} : Psi, Psi2

        Therefore, the X's are not dependent on the extra Psi introduced
        by recursive calls, which is why they are ignored in matchSub as well.

        We will generate a substitution t s.t. Psi1 |- t: Psi2
        Therefore  Psi1 |- (s2 o t) : Psi0

        And we are trying to match it with
                   Psi1 |- s1 : Psi0

      *)
(* Psi1 |- t : Psi2 *)(* Now since s1 and t' go between the same contexts, we see
      * if we can unify them
      *))
end
