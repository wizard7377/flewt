
module type REDUNDANT  =
  sig exception Error of string  val convert : Tomega.__Prg -> Tomega.__Prg
  end;;




(* Redundancy remover (factoring) *)
(* Author: Adam Poswolsky (ABP) *)
module Redundant(Redundant:sig module Opsem : OPSEM end) : REDUNDANT =
  struct
    exception Error of string 
    (*
     convert:  Tomega.Prg -> Tomega.Prg
     Attempts to eliminate *redundant* cases.
     *)
    module T = Tomega
    module I = IntSyn
    let rec optionRefEqual (r1, r2, func) =
      if r1 = r2
      then true__
      else
        (match (r1, r2) with
         | (ref (NONE), ref (NONE)) -> true__
         | (ref (SOME (P1)), ref (SOME (P2))) -> func (P1, P2)
         | _ -> false__)
    let rec convert =
      function
      | Lam (D, P) -> T.Lam (D, (convert P))
      | New (P) -> T.New (convert P)
      | Choose (P) -> T.Choose (convert P)
      | PairExp (M, P) -> T.PairExp (M, (convert P))
      | PairBlock (rho, P) -> T.PairBlock (rho, (convert P))
      | PairPrg (P1, P2) -> T.PairPrg ((convert P1), (convert P2))
      | T.Unit -> T.Unit
      | Var x -> T.Var x
      | Const x -> T.Const x
      | Redex (P, S) -> T.Redex ((convert P), (convertSpine S))
      | Rec (D, P) -> T.Rec (D, (convert P))
      | Case (Cases (O)) -> T.Case (T.Cases (convertCases O))
      | Let (D, P1, P2) -> T.Let (D, (convert P1), (convert P2))
    let rec convertSpine =
      function
      | T.Nil -> T.Nil
      | AppExp (I, S) -> T.AppExp (I, (convertSpine S))
      | AppBlock (I, S) -> T.AppBlock (I, (convertSpine S))
      | AppPrg (P, S) -> T.AppPrg ((convert P), (convertSpine S))
      | SClo (S, t) -> raise (Error "SClo should not exist")
    let rec expEqual (E1, E2) = Conv.conv ((E1, I.id), (E2, I.id))
    let rec IsubEqual (sub1, sub2) = Conv.convSub (sub1, sub2)
    let rec blockEqual =
      function
      | (Bidx x, Bidx x') -> x = x'
      | (LVar (r, sub1, (cid, sub2)), LVar (r', sub1', (cid', sub2'))) ->
          (optionRefEqual (r, r', blockEqual)) &&
            ((IsubEqual (sub1, sub1')) &&
               ((cid = cid') && (IsubEqual (sub1', sub2'))))
      | _ -> false__(* Should not occur -- ap 2/18/03 *)
    let rec decEqual =
      function
      | (UDec (D1), (UDec (D2), t2)) ->
          Conv.convDec ((D1, I.id), (D2, (T.coerceSub t2)))
      | (PDec (_, F1, _, _), (PDec (_, F2, _, _), t2)) ->
          T.convFor ((F1, T.id), (F2, t2))
      | _ -> false__
    let rec caseEqual =
      function
      | ((Psi1, t1, P1)::O1, ((Psi2, t2, P2)::O2, tAfter)) ->
          let t2' = T.comp ((T.invertSub tAfter), t2) in
          let t = Opsem.createVarSub (Psi1, Psi2) in
          let t' = T.comp (t2', t) in
          let doMatch =
            try Opsem.matchSub (Psi1, t1, t'); true__
            with | NoMatch -> false__ in
          ((if doMatch
            then
              let newT = T.normalizeSub t in
              let stillMatch = IsSubRenamingOnly newT in
              stillMatch && (prgEqual (P1, (P2, (cleanSub newT))))
            else false__)
            (* Note:  (Psi1 |- t1: Psi0) *)(* Psi1 |- t: Psi2 *)
            (* Psi1 |- t' : Psi_0 *))
      | (nil, (nil, t2)) -> true__
      | _ -> false__(* Recall that we (Psi2, t2, P2)[tAfter] = (Psi2, (tAfterInv \circ t2), P2) *)
    let rec spineEqual =
      function
      | (T.Nil, (T.Nil, t2)) -> true__
      | (AppExp (E1, S1), (AppExp (E2, S2), t2)) ->
          (Conv.conv ((E1, I.id), (E2, (T.coerceSub t2)))) &&
            (spineEqual (S1, (S2, t2)))
      | (AppBlock (B1, S1), (AppBlock (B2, S2), t2)) ->
          (blockEqual (B1, (I.blockSub (B2, (T.coerceSub t2))))) &&
            (spineEqual (S1, (S2, t2)))
      | (AppPrg (P1, S1), (AppPrg (P2, S2), t2)) ->
          (prgEqual (P1, (P2, t2))) && (spineEqual (S1, (S2, t2)))
      | (SClo (S, t1), (SClo (s, t2a), t2)) ->
          raise (Error "SClo should not exist!")
      | _ -> false__(* there are no SClo created in converter *)
    let rec prgEqual =
      function
      | (Lam (D1, P1), (Lam (D2, P2), t2)) ->
          (decEqual (D1, (D2, t2))) && (prgEqual (P1, (P2, (T.dot1 t2))))
      | (New (P1), (New (P2), t2)) -> prgEqual (P1, (P2, t2))
      | (Choose (P1), (Choose (P2), t2)) -> prgEqual (P1, (P2, t2))
      | (PairExp (U1, P1), (PairExp (U2, P2), t2)) ->
          (Conv.conv ((U1, I.id), (U2, (T.coerceSub t2)))) &&
            (prgEqual (P1, (P2, t2)))
      | (PairBlock (B1, P1), (PairBlock (B2, P2), t2)) ->
          (blockEqual (B1, (I.blockSub (B2, (T.coerceSub t2))))) &&
            (prgEqual (P1, (P2, t2)))
      | (PairPrg (P1a, P1b), (PairPrg (P2a, P2b), t2)) ->
          (prgEqual (P1a, (P2a, t2))) && (prgEqual (P1b, (P2b, t2)))
      | (T.Unit, (T.Unit, t2)) -> true__
      | (Const lemma1, (Const lemma2, _)) -> lemma1 = lemma2
      | (Var x1, (Var x2, t2)) ->
          (match getFrontIndex (T.varSub (x2, t2)) with
           | NONE -> false__
           | SOME i -> x1 = i)
      | (Redex (P1, S1), (Redex (P2, S2), t2)) ->
          (prgEqual (P1, (P2, t2))) && (spineEqual (S1, (S2, t2)))
      | (Rec (D1, P1), (Rec (D2, P2), t2)) ->
          (decEqual (D1, (D2, t2))) && (prgEqual (P1, (P2, (T.dot1 t2))))
      | (Case (Cases (O1)), (Case (Cases (O2)), t2)) ->
          caseEqual (O1, (O2, t2))
      | (Let (D1, P1a, P1b), (Let (D2, P2a, P2b), t2)) ->
          (decEqual (D1, (D2, t2))) && (prgEqual (P1a, (P2a, t2)))
      | (PClo (P1, t1), (PClo (P2, t2a), t2b)) ->
          raise (Error "PClo should not exist!")
      | (EVar (Psi1, P1optRef, F1, _, _, _),
         (EVar (Psi2, P2optref, F2, _, _, _), t2)) ->
          raise (Error "No EVARs should exist!")
      | _ -> false__(* there are no PClo created in converter *)
      (*      | prgEqual ((T.Root (H1, S1)), (T.Root (H2, S2), t2)) =
                (case (H1, H2)
                   of (T.Const lemma1, T.Const lemma2) => ((lemma1=lemma2) andalso (spineEqual(S1, (S2,t2))))
                 |  (T.Var x1, T.Var x2) =>
                           (case getFrontIndex(T.varSub(x2,t2)) of
                              NONE => false
                            | SOME i => ((x1 = i) andalso (spineEqual(S1, (S2,t2)))))
                 |  _ => false)
*)
    let rec convertCases =
      function
      | (A)::C ->
          let ((Psi, t, P), C') = removeRedundancy (A, C) in
          (::) (Psi, t, (convert P)) convertCases C'
      | C -> C
    let rec removeRedundancy =
      function
      | (C, []) -> (C, [])
      | (C, (C')::rest) ->
          let (C'')::Cs = mergeIfNecessary (C, C') in
          let (C''', rest') = removeRedundancy (C'', rest) in
          (C''', (Cs @ rest'))
    let rec getFrontIndex =
      function
      | Idx k -> SOME k
      | Prg (P) -> getPrgIndex P
      | Exp (U) -> getExpIndex U
      | Block (B) -> getBlockIndex B
      | T.Undef -> NONE
    let rec getPrgIndex =
      function
      | Var k -> SOME k
      | Redex (P, T.Nil) -> getPrgIndex P
      | PClo (P, t) ->
          (match getPrgIndex P with
           | NONE -> NONE
           | SOME i -> getFrontIndex (T.varSub (i, t)))
      | _ -> NONE(* it is possible in the matchSub that we will get PClo under a sub (usually id) *)
    let rec getExpIndex =
      function
      | Root (BVar k, I.Nil) -> SOME k
      | Redex (U, I.Nil) -> getExpIndex U
      | EClo (U, t) ->
          (match getExpIndex U with
           | NONE -> NONE
           | SOME i -> getFrontIndex (T.revCoerceFront (I.bvarSub (i, t))))
      | Lam (Dec (_, U1), U2) as U ->
          (try SOME (Whnf.etaContract U) with | Whnf.Eta -> NONE)
      | _ -> NONE
    let rec getBlockIndex = function | Bidx k -> SOME k | _ -> NONE
    let rec cleanSub =
      function
      | Shift _ as S -> S
      | Dot (Ft1, s1) ->
          (match getFrontIndex Ft1 with
           | NONE -> T.Dot (Ft1, (cleanSub s1))
           | SOME index -> T.Dot ((T.Idx index), (cleanSub s1)))
    let rec IsSubRenamingOnly =
      function
      | Shift n -> true__
      | Dot (Ft1, s1) ->
          (match getFrontIndex Ft1 with | NONE -> false__ | SOME _ -> true__)
            && (IsSubRenamingOnly s1)
    let rec mergeSpines =
      function
      | (T.Nil, (T.Nil, t2)) -> T.Nil
      | (AppExp (E1, S1), (AppExp (E2, S2), t2)) ->
          if Conv.conv ((E1, I.id), (E2, (T.coerceSub t2)))
          then T.AppExp (E1, (mergeSpines (S1, (S2, t2))))
          else raise (Error "Spine not equal (AppExp)")
      | (AppBlock (B1, S1), (AppBlock (B2, S2), t2)) ->
          if blockEqual (B1, (I.blockSub (B2, (T.coerceSub t2))))
          then T.AppBlock (B1, (mergeSpines (S1, (S2, t2))))
          else raise (Error "Spine not equal (AppBlock)")
      | (AppPrg (P1, S1), (AppPrg (P2, S2), t2)) ->
          if prgEqual (P1, (P2, t2))
          then T.AppPrg (P1, (mergeSpines (S1, (S2, t2))))
          else raise (Error "Prg (in App) not equal")
      | (SClo (S, t1), (SClo (s, t2a), t2)) ->
          raise (Error "SClo should not exist!")
      | _ -> raise (Error "Spine are not equivalent")(* there are no SClo created in converter *)
    let rec mergePrgs =
      function
      | (Lam (D1, P1), (Lam (D2, P2), t2)) ->
          if (decEqual (D1, (D2, t2))) && (prgEqual (P1, (P2, (T.dot1 t2))))
          then T.Lam (D1, P1)
          else raise (Error "Lambda don't match")
      | (New (P1), (New (P2), t2)) ->
          if prgEqual (P1, (P2, t2))
          then T.New P1
          else raise (Error "New don't match")
      | (Choose (P1), (Choose (P2), t2)) ->
          if prgEqual (P1, (P2, t2))
          then T.Choose P1
          else raise (Error "Choose don't match")
      | (PairExp (U1, P1), (PairExp (U2, P2), t2)) ->
          let t2' = T.coerceSub t2 in
          if Conv.conv ((U1, I.id), (U2, t2'))
          then T.PairExp (U1, (mergePrgs (P1, (P2, t2))))
          else raise (Error "cannot merge PairExp")
      | (PairBlock (B1, P1), (PairBlock (B2, P2), t2)) ->
          let B2' = I.blockSub (B2, (T.coerceSub t2)) in
          if blockEqual (B1, B2')
          then T.PairBlock (B1, (mergePrgs (P1, (P2, t2))))
          else raise (Error "cannot merge PairBlock")
      | (PairPrg (P1a, P1b), (PairPrg (P2a, P2b), t2)) ->
          if prgEqual (P1a, (P2a, t2))
          then T.PairPrg (P1a, (mergePrgs (P1b, (P2b, t2))))
          else raise (Error "cannot merge PairPrg")
      | (T.Unit, (T.Unit, t2)) -> T.Unit
      | (Const lemma1, (Const lemma2, _)) ->
          if lemma1 = lemma2
          then T.Const lemma1
          else raise (Error "Constants do not match.")
      | (Var x1, (Var x2, t2)) ->
          (match getFrontIndex (T.varSub (x2, t2)) with
           | NONE -> raise (Error "Variables do not match.")
           | SOME i ->
               if x1 = i
               then T.Var x1
               else raise (Error "Variables do not match."))
      | (Redex (P1, S1), (Redex (P2, S2), t2)) ->
          let newS = mergeSpines (S1, (S2, t2)) in
          if prgEqual (P1, (P2, t2))
          then T.Redex (P1, newS)
          else raise (Error "Redex Prgs don't match")
      | (Rec (D1, P1), (Rec (D2, P2), t2)) ->
          if (decEqual (D1, (D2, t2))) && (prgEqual (P1, (P2, (T.dot1 t2))))
          then T.Rec (D1, P1)
          else raise (Error "Rec's don't match")
      | (Case (Cases (O1)), (Case (Cases ((C)::[])), t2)) ->
          T.Case (T.Cases (mergeCase (O1, (C, t2))))
      | (Case (O1), (Case (O2), t2)) -> raise (Error "Invariant Violated")
      | (PClo (P1, t1), (PClo (P2, t2a), t2b)) ->
          raise (Error "PClo should not exist!")
      | (Let (D1, P1a, P1b), (Let (D2, P2a, P2b), t2)) ->
          if (decEqual (D1, (D2, t2))) && (prgEqual (P1a, (P2a, t2)))
          then T.Let (D1, P1a, (mergePrgs (P1b, (P2b, (T.dot1 t2)))))
          else raise (Error "Let don't match")
      | (EVar (Psi1, P1optRef, F1, _, _, _),
         (EVar (Psi2, P2optref, F2, _, _, _), t2)) ->
          raise (Error "No EVARs should exist!")
      | _ ->
          raise
            (Error "Redundancy in cases could not automatically be removed.")
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
        function
        | (n, Shift _, p) -> NONE
        | (n, Dot (T.Undef, s'), p) -> lookup ((n + 1), s', p)
        | (n, Dot (Ft, s'), p) ->
            (match getFrontIndex Ft with
             | NONE -> lookup ((n + 1), s', p)
             | SOME k -> if k = p then SOME n else lookup ((n + 1), s', p)) in
      let rec invertSub'' =
        function
        | (0, si) -> si
        | (p, si) ->
            (match lookup (1, s, p) with
             | SOME k -> invertSub'' ((p - 1), (T.Dot ((T.Idx k), si)))
             | NONE -> invertSub'' ((p - 1), (T.Dot (T.Undef, si)))) in
      let rec invertSub' =
        function
        | (n, Shift p) -> invertSub'' (p, (T.Shift n))
        | (n, Dot (_, s')) -> invertSub' ((n + 1), s') in
      invertSub' (0, s)
    let rec printSub =
      function
      | Shift k -> print (((^) "Shift " Int.toString k) ^ "\n")
      | Dot (Idx k, s) ->
          (print (((^) "Idx " Int.toString k) ^ " (DOT) "); printSub s)
      | Dot (Prg (EVar _), s) -> (print "PRG_EVAR (DOT) "; printSub s)
      | Dot (Exp (EVar _), s) -> (print "EXP_EVAR (DOT) "; printSub s)
      | Dot (Prg (P), s) -> (print "PRG (DOT) "; printSub s)
      | Dot (Exp (E), s) -> (print "EXP (DOT) "; printSub s)
      | Dot (Block (B), s) -> (print "BLOCK (DOT) "; printSub s)
      | Dot (T.Undef, s) -> (print "UNDEF. (DOT) "; printSub s)
    let rec mergeCase =
      function
      | ([], C) -> raise (Error "Case incompatible, cannot merge")
      | (((Psi1, t1, P1)::O as L), (((Psi2, t2, P2), tAfter) as C)) ->
          let tAfterInv = T.invertSub tAfter in
          let t3 = T.comp (tAfterInv, t2) in
          let t = Opsem.createVarSub (Psi1, Psi2) in
          let t' = T.comp (t3, t) in
          let doMatch =
            try Opsem.matchSub (Psi1, t1, t'); true__
            with | NoMatch -> false__ in
          ((if doMatch
            then
              let newT = T.normalizeSub t in
              let stillMatch = IsSubRenamingOnly newT in
              (((if stillMatch
                 then
                   (Psi1, t1, (mergePrgs (P1, (P2, (cleanSub newT))))) :: O
                 else
                   ((if (length O) = 0
                     then (Psi2, t3, P2) :: L
                     else (::) (Psi1, t1, P1) mergeCase (O, C))
                   (* We tried all the cases, and we can now add it *)
                   (* Try other cases *))))
                (* Since the case matches, lets continue the merge on P1 and P2
           * Note that removing the redundancy of other case statements
           * is handled recursively ... see convertCases
           *)
                (* Note that tAfter and newT are both renaming substitutions *))
            else
              ((if (length O) = 0
                then (Psi2, t3, P2) :: L
                else (::) (Psi1, t1, P1) mergeCase (O, C))
              (* We tried all the cases, and we can now add it *)
              (* Try other cases *)))
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
            (* Psi1 |- t : Psi2 *)(* Psi1 |- t' : Psi1' *)
            (* If we can get this to match, then Psi1 |- P2[t] *))
    let rec mergeIfNecessary (((Psi1, s1, P1) as C), ((Psi2, s2, P2) as C'))
      =
      let t = Opsem.createVarSub (Psi1, Psi2) in
      let t' = T.comp (s2, t) in
      let doMatch =
        try Opsem.matchSub (Psi1, s1, t'); true__ with | NoMatch -> false__ in
      ((if not doMatch
        then [C; C']
        else
          (let newT = T.normalizeSub t in
           if IsSubRenamingOnly newT
           then
             ((try [(Psi1, s1, (mergePrgs (P1, (P2, (cleanSub newT)))))]
               with
               | Error s ->
                   raise
                     (Error
                        (("***WARNING*** -- redundant case automatically ANNIHILATED:  "
                            ^ s)
                           ^ "\n")))
             (* In this case, C' is redundant and cannot be fixed, so C' will never be called
               * [C,C']
               *)
             (* (print ("***WARNING*** -- redundant case automatically ANNIHILATED:  " ^ s ^ "\n") ; [C]) *))
           else [C; C']))
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
  end ;;
