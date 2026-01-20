
module type REDUNDANT  =
  sig exception Error of string  val convert : Tomega.__Prg -> Tomega.__Prg
  end;;




module Redundant(Redundant:sig module Opsem : OPSEM end) : REDUNDANT =
  struct
    exception Error of string 
    module T = Tomega
    module I = IntSyn
    let rec optionRefEqual r1 r2 func =
      if r1 = r2
      then true__
      else
        (match (r1, r2) with
         | ({ contents = NONE }, { contents = NONE }) -> true__
         | ({ contents = Some (__P1) }, { contents = Some (__P2) }) ->
             func (__P1, __P2)
         | _ -> false__)
    let rec convert =
      function
      | Lam (__D, __P) -> T.Lam (__D, (convert __P))
      | New (__P) -> T.New (convert __P)
      | Choose (__P) -> T.Choose (convert __P)
      | PairExp (__M, __P) -> T.PairExp (__M, (convert __P))
      | PairBlock (rho, __P) -> T.PairBlock (rho, (convert __P))
      | PairPrg (__P1, __P2) -> T.PairPrg ((convert __P1), (convert __P2))
      | T.Unit -> T.Unit
      | Var x -> T.Var x
      | Const x -> T.Const x
      | Redex (__P, __S) -> T.Redex ((convert __P), (convertSpine __S))
      | Rec (__D, __P) -> T.Rec (__D, (convert __P))
      | Case (Cases (__O)) -> T.Case (T.Cases (convertCases __O))
      | Let (__D, __P1, __P2) -> T.Let (__D, (convert __P1), (convert __P2))
    let rec convertSpine =
      function
      | T.Nil -> T.Nil
      | AppExp (__I, __S) -> T.AppExp (__I, (convertSpine __S))
      | AppBlock (__I, __S) -> T.AppBlock (__I, (convertSpine __S))
      | AppPrg (__P, __S) -> T.AppPrg ((convert __P), (convertSpine __S))
      | SClo (__S, t) -> raise (Error "SClo should not exist")
    let rec expEqual (__E1) (__E2) = Conv.conv ((__E1, I.id), (__E2, I.id))
    let rec IsubEqual sub1 sub2 = Conv.convSub (sub1, sub2)
    let rec blockEqual __0__ __1__ =
      match (__0__, __1__) with
      | (Bidx x, Bidx x') -> x = x'
      | (LVar (r, sub1, (cid, sub2)), LVar (r', sub1', (cid', sub2'))) ->
          (optionRefEqual (r, r', blockEqual)) &&
            ((IsubEqual (sub1, sub1')) &&
               ((cid = cid') && (IsubEqual (sub1', sub2'))))
      | _ -> false__(* Should not occur -- ap 2/18/03 *)
    let rec decEqual __2__ __3__ =
      match (__2__, __3__) with
      | (UDec (__D1), (UDec (__D2), t2)) ->
          Conv.convDec ((__D1, I.id), (__D2, (T.coerceSub t2)))
      | (PDec (_, __F1, _, _), (PDec (_, __F2, _, _), t2)) ->
          T.convFor ((__F1, T.id), (__F2, t2))
      | _ -> false__
    let rec caseEqual __4__ __5__ =
      match (__4__, __5__) with
      | ((Psi1, t1, __P1)::__O1, ((Psi2, t2, __P2)::__O2, tAfter)) ->
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
              stillMatch && (prgEqual (__P1, (__P2, (cleanSub newT))))
            else false__)
            (* Note:  (Psi1 |- t1: Psi0) *)(* Psi1 |- t: Psi2 *)
            (* Psi1 |- t' : Psi_0 *))
      | (nil, (nil, t2)) -> true__
      | _ -> false__(* Recall that we (Psi2, t2, P2)[tAfter] = (Psi2, (tAfterInv \circ t2), P2) *)
    let rec spineEqual __6__ __7__ =
      match (__6__, __7__) with
      | (T.Nil, (T.Nil, t2)) -> true__
      | (AppExp (__E1, __S1), (AppExp (__E2, __S2), t2)) ->
          (Conv.conv ((__E1, I.id), (__E2, (T.coerceSub t2)))) &&
            (spineEqual (__S1, (__S2, t2)))
      | (AppBlock (__B1, __S1), (AppBlock (__B2, __S2), t2)) ->
          (blockEqual (__B1, (I.blockSub (__B2, (T.coerceSub t2))))) &&
            (spineEqual (__S1, (__S2, t2)))
      | (AppPrg (__P1, __S1), (AppPrg (__P2, __S2), t2)) ->
          (prgEqual (__P1, (__P2, t2))) && (spineEqual (__S1, (__S2, t2)))
      | (SClo (__S, t1), (SClo (s, t2a), t2)) ->
          raise (Error "SClo should not exist!")
      | _ -> false__(* there are no SClo created in converter *)
    let rec prgEqual __8__ __9__ =
      match (__8__, __9__) with
      | (Lam (__D1, __P1), (Lam (__D2, __P2), t2)) ->
          (decEqual (__D1, (__D2, t2))) &&
            (prgEqual (__P1, (__P2, (T.dot1 t2))))
      | (New (__P1), (New (__P2), t2)) -> prgEqual (__P1, (__P2, t2))
      | (Choose (__P1), (Choose (__P2), t2)) -> prgEqual (__P1, (__P2, t2))
      | (PairExp (__U1, __P1), (PairExp (__U2, __P2), t2)) ->
          (Conv.conv ((__U1, I.id), (__U2, (T.coerceSub t2)))) &&
            (prgEqual (__P1, (__P2, t2)))
      | (PairBlock (__B1, __P1), (PairBlock (__B2, __P2), t2)) ->
          (blockEqual (__B1, (I.blockSub (__B2, (T.coerceSub t2))))) &&
            (prgEqual (__P1, (__P2, t2)))
      | (PairPrg (P1a, P1b), (PairPrg (P2a, P2b), t2)) ->
          (prgEqual (P1a, (P2a, t2))) && (prgEqual (P1b, (P2b, t2)))
      | (T.Unit, (T.Unit, t2)) -> true__
      | (Const lemma1, (Const lemma2, _)) -> lemma1 = lemma2
      | (Var x1, (Var x2, t2)) ->
          (match getFrontIndex (T.varSub (x2, t2)) with
           | NONE -> false__
           | Some i -> x1 = i)
      | (Redex (__P1, __S1), (Redex (__P2, __S2), t2)) ->
          (prgEqual (__P1, (__P2, t2))) && (spineEqual (__S1, (__S2, t2)))
      | (Rec (__D1, __P1), (Rec (__D2, __P2), t2)) ->
          (decEqual (__D1, (__D2, t2))) &&
            (prgEqual (__P1, (__P2, (T.dot1 t2))))
      | (Case (Cases (__O1)), (Case (Cases (__O2)), t2)) ->
          caseEqual (__O1, (__O2, t2))
      | (Let (__D1, P1a, P1b), (Let (__D2, P2a, P2b), t2)) ->
          (decEqual (__D1, (__D2, t2))) && (prgEqual (P1a, (P2a, t2)))
      | (PClo (__P1, t1), (PClo (__P2, t2a), t2b)) ->
          raise (Error "PClo should not exist!")
      | (EVar (Psi1, P1optRef, __F1, _, _, _),
         (EVar (Psi2, P2optref, __F2, _, _, _), t2)) ->
          raise (Error "No EVARs should exist!")
      | _ -> false__(* there are no PClo created in converter *)
      (*      | prgEqual ((T.Root (H1, S1)), (T.Root (H2, S2), t2)) =
                (case (H1, H2)
                   of (T.Const lemma1, T.Const lemma2) => ((lemma1=lemma2) andalso (spineEqual(S1, (S2,t2))))
                 |  (T.Var x1, T.Var x2) =>
                           (case getFrontIndex(T.varSub(x2,t2)) of
                              NONE => false
                            | Some i => ((x1 = i) andalso (spineEqual(S1, (S2,t2)))))
                 |  _ => false)
*)
    let rec convertCases =
      function
      | (__A)::__C ->
          let ((Psi, t, __P), __C') = removeRedundancy (__A, __C) in
          (::) (Psi, t, (convert __P)) convertCases __C'
      | __C -> __C
    let rec removeRedundancy __10__ __11__ =
      match (__10__, __11__) with
      | (__C, []) -> (__C, [])
      | (__C, (__C')::rest) ->
          let (C'')::__Cs = mergeIfNecessary (__C, __C') in
          let (C''', rest') = removeRedundancy (C'', rest) in
          (C''', (__Cs @ rest'))
    let rec getFrontIndex =
      function
      | Idx k -> Some k
      | Prg (__P) -> getPrgIndex __P
      | Exp (__U) -> getExpIndex __U
      | Block (__B) -> getBlockIndex __B
      | T.Undef -> NONE
    let rec getPrgIndex =
      function
      | Var k -> Some k
      | Redex (__P, T.Nil) -> getPrgIndex __P
      | PClo (__P, t) ->
          (match getPrgIndex __P with
           | NONE -> NONE
           | Some i -> getFrontIndex (T.varSub (i, t)))
      | _ -> NONE(* it is possible in the matchSub that we will get PClo under a sub (usually id) *)
    let rec getExpIndex =
      function
      | Root (BVar k, I.Nil) -> Some k
      | Redex (__U, I.Nil) -> getExpIndex __U
      | EClo (__U, t) ->
          (match getExpIndex __U with
           | NONE -> NONE
           | Some i -> getFrontIndex (T.revCoerceFront (I.bvarSub (i, t))))
      | Lam (Dec (_, __U1), __U2) as U ->
          (try Some (Whnf.etaContract __U) with | Whnf.Eta -> NONE)
      | _ -> NONE
    let rec getBlockIndex = function | Bidx k -> Some k | _ -> NONE
    let rec cleanSub =
      function
      | Shift _ as S -> __S
      | Dot (Ft1, s1) ->
          (match getFrontIndex Ft1 with
           | NONE -> T.Dot (Ft1, (cleanSub s1))
           | Some index -> T.Dot ((T.Idx index), (cleanSub s1)))
    let rec IsSubRenamingOnly =
      function
      | Shift n -> true__
      | Dot (Ft1, s1) ->
          (match getFrontIndex Ft1 with | NONE -> false__ | Some _ -> true__)
            && (IsSubRenamingOnly s1)
    let rec mergeSpines __12__ __13__ =
      match (__12__, __13__) with
      | (T.Nil, (T.Nil, t2)) -> T.Nil
      | (AppExp (__E1, __S1), (AppExp (__E2, __S2), t2)) ->
          if Conv.conv ((__E1, I.id), (__E2, (T.coerceSub t2)))
          then T.AppExp (__E1, (mergeSpines (__S1, (__S2, t2))))
          else raise (Error "Spine not equal (AppExp)")
      | (AppBlock (__B1, __S1), (AppBlock (__B2, __S2), t2)) ->
          if blockEqual (__B1, (I.blockSub (__B2, (T.coerceSub t2))))
          then T.AppBlock (__B1, (mergeSpines (__S1, (__S2, t2))))
          else raise (Error "Spine not equal (AppBlock)")
      | (AppPrg (__P1, __S1), (AppPrg (__P2, __S2), t2)) ->
          if prgEqual (__P1, (__P2, t2))
          then T.AppPrg (__P1, (mergeSpines (__S1, (__S2, t2))))
          else raise (Error "Prg (in App) not equal")
      | (SClo (__S, t1), (SClo (s, t2a), t2)) ->
          raise (Error "SClo should not exist!")
      | _ -> raise (Error "Spine are not equivalent")(* there are no SClo created in converter *)
    let rec mergePrgs __14__ __15__ =
      match (__14__, __15__) with
      | (Lam (__D1, __P1), (Lam (__D2, __P2), t2)) ->
          if
            (decEqual (__D1, (__D2, t2))) &&
              (prgEqual (__P1, (__P2, (T.dot1 t2))))
          then T.Lam (__D1, __P1)
          else raise (Error "Lambda don't match")
      | (New (__P1), (New (__P2), t2)) ->
          if prgEqual (__P1, (__P2, t2))
          then T.New __P1
          else raise (Error "New don't match")
      | (Choose (__P1), (Choose (__P2), t2)) ->
          if prgEqual (__P1, (__P2, t2))
          then T.Choose __P1
          else raise (Error "Choose don't match")
      | (PairExp (__U1, __P1), (PairExp (__U2, __P2), t2)) ->
          let t2' = T.coerceSub t2 in
          if Conv.conv ((__U1, I.id), (__U2, t2'))
          then T.PairExp (__U1, (mergePrgs (__P1, (__P2, t2))))
          else raise (Error "cannot merge PairExp")
      | (PairBlock (__B1, __P1), (PairBlock (__B2, __P2), t2)) ->
          let B2' = I.blockSub (__B2, (T.coerceSub t2)) in
          if blockEqual (__B1, B2')
          then T.PairBlock (__B1, (mergePrgs (__P1, (__P2, t2))))
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
           | Some i ->
               if x1 = i
               then T.Var x1
               else raise (Error "Variables do not match."))
      | (Redex (__P1, __S1), (Redex (__P2, __S2), t2)) ->
          let newS = mergeSpines (__S1, (__S2, t2)) in
          if prgEqual (__P1, (__P2, t2))
          then T.Redex (__P1, newS)
          else raise (Error "Redex Prgs don't match")
      | (Rec (__D1, __P1), (Rec (__D2, __P2), t2)) ->
          if
            (decEqual (__D1, (__D2, t2))) &&
              (prgEqual (__P1, (__P2, (T.dot1 t2))))
          then T.Rec (__D1, __P1)
          else raise (Error "Rec's don't match")
      | (Case (Cases (__O1)), (Case (Cases ((__C)::[])), t2)) ->
          T.Case (T.Cases (mergeCase (__O1, (__C, t2))))
      | (Case (__O1), (Case (__O2), t2)) ->
          raise (Error "Invariant Violated")
      | (PClo (__P1, t1), (PClo (__P2, t2a), t2b)) ->
          raise (Error "PClo should not exist!")
      | (Let (__D1, P1a, P1b), (Let (__D2, P2a, P2b), t2)) ->
          if (decEqual (__D1, (__D2, t2))) && (prgEqual (P1a, (P2a, t2)))
          then T.Let (__D1, P1a, (mergePrgs (P1b, (P2b, (T.dot1 t2)))))
          else raise (Error "Let don't match")
      | (EVar (Psi1, P1optRef, __F1, _, _, _),
         (EVar (Psi2, P2optref, __F2, _, _, _), t2)) ->
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
                            | Some i =>
                                (if (x1 = i) then
                                   T.Root (T.Var x1, mergeSpines((S1),(S2,t2)))
                                 else
                                   raise Error "Root does not match."))
                   |  _ => raise Error "Root does not match.")
*)
    let rec invertSub s =
      let rec lookup __16__ __17__ __18__ =
        match (__16__, __17__, __18__) with
        | (n, Shift _, p) -> NONE
        | (n, Dot (T.Undef, s'), p) -> lookup ((n + 1), s', p)
        | (n, Dot (Ft, s'), p) ->
            (match getFrontIndex Ft with
             | NONE -> lookup ((n + 1), s', p)
             | Some k -> if k = p then Some n else lookup ((n + 1), s', p)) in
      let rec invertSub'' __19__ __20__ =
        match (__19__, __20__) with
        | (0, si) -> si
        | (p, si) ->
            (match lookup (1, s, p) with
             | Some k -> invertSub'' ((p - 1), (T.Dot ((T.Idx k), si)))
             | NONE -> invertSub'' ((p - 1), (T.Dot (T.Undef, si)))) in
      let rec invertSub' __21__ __22__ =
        match (__21__, __22__) with
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
      | Dot (Prg (__P), s) -> (print "PRG (DOT) "; printSub s)
      | Dot (Exp (__E), s) -> (print "EXP (DOT) "; printSub s)
      | Dot (Block (__B), s) -> (print "BLOCK (DOT) "; printSub s)
      | Dot (T.Undef, s) -> (print "UNDEF. (DOT) "; printSub s)
    let rec mergeCase __23__ __24__ =
      match (__23__, __24__) with
      | ([], __C) -> raise (Error "Case incompatible, cannot merge")
      | (((Psi1, t1, __P1)::__O as L), (((Psi2, t2, __P2), tAfter) as C)) ->
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
                   (Psi1, t1, (mergePrgs (__P1, (__P2, (cleanSub newT))))) ::
                     __O
                 else
                   ((if (length __O) = 0
                     then (Psi2, t3, __P2) :: __L
                     else (::) (Psi1, t1, __P1) mergeCase (__O, __C))
                   (* We tried all the cases, and we can now add it *)
                   (* Try other cases *))))
                (* Since the case matches, lets continue the merge on P1 and P2
           * Note that removing the redundancy of other case statements
           * is handled recursively ... see convertCases
           *)
                (* Note that tAfter and newT are both renaming substitutions *))
            else
              ((if (length __O) = 0
                then (Psi2, t3, __P2) :: __L
                else (::) (Psi1, t1, __P1) mergeCase (__O, __C))
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
    let rec mergeIfNecessary ((Psi1, s1, __P1) as C) ((Psi2, s2, __P2) as C')
      =
      let t = Opsem.createVarSub (Psi1, Psi2) in
      let t' = T.comp (s2, t) in
      let doMatch =
        try Opsem.matchSub (Psi1, s1, t'); true__ with | NoMatch -> false__ in
      ((if not doMatch
        then [__C; __C']
        else
          (let newT = T.normalizeSub t in
           if IsSubRenamingOnly newT
           then
             ((try [(Psi1, s1, (mergePrgs (__P1, (__P2, (cleanSub newT)))))]
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
           else [__C; __C']))
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
