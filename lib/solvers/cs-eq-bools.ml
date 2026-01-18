
(* Booleans Equation Solver *)
(* Author: Roberto Virga *)
module CSEqBools(CSEqBools:sig
                             (*! structure IntSyn : INTSYN !*)
                             module Whnf : WHNF
                             (*! sharing Whnf.IntSyn = IntSyn !*)
                             module Unify : UNIFY
                           end) : CS =
  struct
    (*! sharing Unify.IntSyn = IntSyn !*)
    (*! structure CSManager : CS_MANAGER !*)
    (*! sharing CSManager.IntSyn = IntSyn !*)
    (*! structure CSManager = CSManager !*)
    (*! structure IntSyn = IntSyn !*)
    type nonrec 'a set = 'a list
    (* Set                        *)
    type __Sum =
      | Sum of (bool * __Mon set) 
    and __Mon =
      | Mon of (IntSyn.__Exp * IntSyn.__Sub) set 
    (* Mon ::= U1[s1] * ...       *)
    (* A monomial (U1[s1] * U2[s2] * ...) is said to be normal iff
       (a) each (Ui,si) is in whnf and not a foreign term corresponding
           to a sum;
       (b) the terms Ui[si] are pairwise distinct.
     A sum is normal iff all its monomials are normal, and moreover they
     are pairwise distinct.
  *)
    open IntSyn
    module FX = CSManager.Fixity
    module MS = ModeSyn
    exception MyIntsynRep of __Sum 
    let rec extractSum =
      function | MyIntsynRep sum -> sum | fe -> raise (UnexpectedFgnExp fe)
    let myID = (ref (-1) : csid ref)
    let boolID = (ref (-1) : cid ref)
    let rec bool () = Root ((Const (!boolID)), Nil)
    let trueID = (ref (-1) : cid ref)
    let falseID = (ref (-1) : cid ref)
    let rec trueExp () = Root ((Const (!trueID)), Nil)
    let rec falseExp () = Root ((Const (!falseID)), Nil)
    let rec solveBool =
      function
      | (G, S, 0) -> SOME (trueExp ())
      | (G, S, 1) -> SOME (falseExp ())
      | (G, S, k) -> NONE
    let notID = (ref (-1) : cid ref)
    let xorID = (ref (-1) : cid ref)
    let andID = (ref (-1) : cid ref)
    let orID = (ref (-1) : cid ref)
    let impliesID = (ref (-1) : cid ref)
    let iffID = (ref (-1) : cid ref)
    let rec notExp (U) = Root ((Const (!notID)), (App (U, Nil)))
    let rec xorExp (U, V) =
      Root ((Const (!xorID)), (App (U, (App (V, Nil)))))
    let rec andExp (U, V) =
      Root ((Const (!andID)), (App (U, (App (V, Nil)))))
    let rec orExp (U, V) = Root ((Const (!orID)), (App (U, (App (V, Nil)))))
    let rec impliesExp (U, V) =
      Root ((Const (!impliesID)), (App (U, (App (V, Nil)))))
    let rec iffExp (U, V) =
      Root ((Const (!iffID)), (App (U, (App (V, Nil)))))
    let rec member eq (x, L) = List.exists (function | y -> eq (x, y)) L
    let rec differenceSet eq (L1, L2) =
      let L1' = List.filter (function | x -> not (member eq (x, L2))) L1 in
      let L2' = List.filter (function | x -> not (member eq (x, L1))) L2 in
      L1' @ L2'
    let rec equalSet eq (L1, L2) =
      match differenceSet eq (L1, L2) with | nil -> true__ | _::_ -> false__
    let rec unionSet eq (L1, L2) =
      let L2' = List.filter (function | x -> not (member eq (x, L1))) L2 in
      L1 @ L2'
    let rec toExp =
      function
      | Sum (m, nil) ->
          let cid = if m then !trueID else !falseID in
          Root ((Const cid), Nil)
      | Sum (m, mon::[]) ->
          if m = false__
          then toExpMon mon
          else xorExp ((toExp (Sum (m, nil))), (toExpMon mon))
      | Sum (m, (mon::monL as monLL)) ->
          xorExp ((toExp (Sum (m, monL))), (toExpMon mon))
    let rec toExpMon =
      function
      | Mon ((Us)::[]) -> toExpEClo Us
      | Mon ((Us)::UsL) -> andExp ((toExpMon (Mon UsL)), (toExpEClo Us))
    let rec toExpEClo = function | (U, Shift 0) -> U | Us -> EClo Us
    let rec compatibleMon (Mon (UsL1), Mon (UsL2)) =
      equalSet (function | (Us1, Us2) -> sameExp (Us1, Us2)) (UsL1, UsL2)
    let rec sameExpW =
      function
      | (((Root (H1, S1), s1) as Us1), ((Root (H2, S2), s2) as Us2)) ->
          (match (H1, H2) with
           | (BVar k1, BVar k2) ->
               (k1 = k2) && (sameSpine ((S1, s1), (S2, s2)))
           | (FVar (n1, _, _), FVar (n2, _, _)) ->
               (n1 = n2) && (sameSpine ((S1, s1), (S2, s2)))
           | _ -> false__)
      | ((((EVar (r1, G1, V1, cnstrs1) as U1), s1) as Us1),
         (((EVar (r2, G2, V2, cnstrs2) as U2), s2) as Us2)) ->
          (r1 = r2) && (sameSub (s1, s2))
      | _ -> false__
    let rec sameExp (Us1, Us2) = sameExpW ((Whnf.whnf Us1), (Whnf.whnf Us2))
    let rec sameSpine =
      function
      | ((Nil, s1), (Nil, s2)) -> true__
      | ((SClo (S1, s1'), s1), Ss2) ->
          sameSpine ((S1, (comp (s1', s1))), Ss2)
      | (Ss1, (SClo (S2, s2'), s2)) ->
          sameSpine (Ss1, (S2, (comp (s2', s2))))
      | ((App (U1, S1), s1), (App (U2, S2), s2)) ->
          (sameExp ((U1, s1), (U2, s2))) && (sameSpine ((S1, s1), (S2, s2)))
      | _ -> false__
    let rec sameSub =
      function
      | (Shift _, Shift _) -> true__
      | (Dot (Idx k1, s1), Dot (Idx k2, s2)) ->
          (k1 = k2) && (sameSub (s1, s2))
      | ((Dot (Idx _, _) as s1), Shift k2) ->
          sameSub
            (s1, (Dot ((Idx (Int.(+) (k2, 1))), (Shift (Int.(+) (k2, 1))))))
      | (Shift k1, (Dot (Idx _, _) as s2)) ->
          sameSub
            ((Dot ((Idx (Int.(+) (k1, 1))), (Shift (Int.(+) (k1, 1))))), s2)
      | _ -> false__
    let rec xorSum (Sum (m1, monL1), Sum (m2, monL2)) =
      Sum ((not (m1 = m2)), (differenceSet compatibleMon (monL1, monL2)))
    let rec andSum =
      function
      | ((Sum (false__, nil) as sum1), sum2) -> sum1
      | (sum1, (Sum (false__, nil) as sum2)) -> sum2
      | ((Sum (true__, nil) as sum1), sum2) -> sum2
      | (sum1, (Sum (true__, nil) as sum2)) -> sum1
      | (Sum (m1, mon1::monL1), sum2) ->
          xorSum
            ((andSumMon (sum2, mon1)), (andSum ((Sum (m1, monL1)), sum2)))
    let rec andSumMon =
      function
      | (Sum (true__, nil), mon) -> Sum (false__, [mon])
      | ((Sum (false__, nil) as sum1), mon) -> sum1
      | (Sum (m1, (Mon (UsL1))::monL1), (Mon (UsL2) as mon2)) ->
          let UsL = unionSet sameExp (UsL1, UsL2) in
          xorSum
            ((Sum (false__, [Mon UsL])),
              (andSumMon ((Sum (m1, monL1)), mon2)))
    let rec notSum (Sum (m, monL)) = Sum ((not m), monL)
    let rec orSum (sum1, sum2) =
      xorSum (sum1, (xorSum (sum2, (andSum (sum1, sum2)))))
    let rec impliesSum (sum1, sum2) =
      notSum (xorSum (sum1, (andSum (sum1, sum2))))
    let rec iffSum (sum1, sum2) = notSum (xorSum (sum1, sum2))
    let rec fromExpW =
      function
      | (FgnExp (cs, fe), _) as Us ->
          if (!) ((=) cs) myID
          then normalizeSum (extractSum fe)
          else Sum (false__, [Mon [Us]])
      | Us -> Sum (false__, [Mon [Us]])
    let rec fromExp (Us) = fromExpW (Whnf.whnf Us)
    let rec normalizeSum =
      function
      | Sum (m, nil) as sum -> sum
      | Sum (m, mon::[]) -> xorSum ((Sum (m, nil)), (normalizeMon mon))
      | Sum (m, mon::monL) ->
          xorSum ((normalizeMon mon), (normalizeSum (Sum (m, monL))))
    let rec normalizeMon =
      function
      | Mon ((Us)::[]) -> fromExp Us
      | Mon ((Us)::UsL) -> andSum ((fromExp Us), (normalizeMon (Mon UsL)))
    let rec mapSum (f, Sum (m, monL)) =
      Sum (m, (List.map (function | mon -> mapMon (f, mon)) monL))
    let rec mapMon (f, Mon (UsL)) =
      Mon (List.map (function | Us -> Whnf.whnf ((f (EClo Us)), id)) UsL)
    let rec appSum (f, Sum (m, monL)) =
      List.app (function | mon -> appMon (f, mon)) monL
    let rec appMon (f, Mon (UsL)) =
      List.app (function | Us -> f (EClo Us)) UsL
    let rec findMon f (G, Sum (m, monL)) =
      let rec findMon' =
        function
        | (nil, monL2) -> NONE
        | (mon::monL1, monL2) ->
            (match f (G, mon, (Sum (m, (monL1 @ monL2)))) with
             | SOME _ as result -> result
             | NONE -> findMon' (monL1, (mon :: monL2))) in
      findMon' (monL, nil)
    let rec unifySum (G, sum1, sum2) =
      let rec invertMon =
        function
        | (G, Mon (((EVar (r, _, _, _) as LHS), s)::[]), sum) ->
            if Whnf.isPatSub s
            then
              let ss = Whnf.invert s in
              let RHS = toFgn sum in
              (if Unify.invertible (G, (RHS, id), ss, r)
               then SOME (G, LHS, RHS, ss)
               else NONE)
            else NONE
        | _ -> NONE in
      match xorSum (sum2, sum1) with
      | Sum (false__, nil) -> Succeed nil
      | Sum (true__, nil) -> Fail
      | sum ->
          (match findMon invertMon (G, sum) with
           | SOME assignment -> Succeed [Assign assignment]
           | NONE ->
               let U = toFgn sum in
               let cnstr = ref (Eqn (G, U, (falseExp ()))) in
               Succeed [Delay (U, cnstr)])
    let rec toFgn =
      function
      | Sum (m, nil) as sum -> toExp sum
      | Sum (m, monL) as sum -> FgnExp ((!myID), (MyIntsynRep sum))
    let rec toInternal arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (MyIntsynRep sum, ()) -> toExp (normalizeSum sum)
      | (fe, ()) -> raise (UnexpectedFgnExp fe)
    let rec map arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (MyIntsynRep sum, f) -> toFgn (normalizeSum (mapSum (f, sum)))
      | (fe, _) -> raise (UnexpectedFgnExp fe)
    let rec app arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (MyIntsynRep sum, f) -> appSum (f, sum)
      | (fe, _) -> raise (UnexpectedFgnExp fe)
    let rec equalTo arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (MyIntsynRep sum, U2) ->
          (match xorSum ((normalizeSum sum), (fromExp (U2, id))) with
           | Sum (m, nil) -> m = false__
           | _ -> false__)
      | (fe, _) -> raise (UnexpectedFgnExp fe)
    let rec unifyWith arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (MyIntsynRep sum, (G, U2)) ->
          unifySum (G, (normalizeSum sum), (fromExp (U2, id)))
      | (fe, _) -> raise (UnexpectedFgnExp fe)
    let rec installFgnExpOps () =
      let csid = !myID in
      let _ = FgnExpStd.ToInternal.install (csid, toInternal) in
      let _ = FgnExpStd.Map.install (csid, map) in
      let _ = FgnExpStd.App.install (csid, app) in
      let _ = FgnExpStd.UnifyWith.install (csid, unifyWith) in
      let _ = FgnExpStd.EqualTo.install (csid, equalTo) in ()
    let rec makeFgn (arity, opExp) (S) =
      let rec makeParams =
        function
        | 0 -> Nil
        | n -> App ((Root ((BVar n), Nil)), (makeParams (Int.(-) (n, 1)))) in
      let rec makeLam arg__0 arg__1 =
        match (arg__0, arg__1) with
        | (E, 0) -> E
        | (E, n) ->
            Lam ((Dec (NONE, (bool ()))), (makeLam E (Int.(-) (n, 1)))) in
      let rec expand =
        function
        | ((Nil, s), arity) -> ((makeParams arity), arity)
        | ((App (U, S), s), arity) ->
            let (S', arity') = expand ((S, s), (Int.(-) (arity, 1))) in
            ((App ((EClo (U, (comp (s, (Shift arity'))))), S')), arity')
        | ((SClo (S, s'), s), arity) -> expand ((S, (comp (s', s))), arity) in
      let (S', arity') = expand ((S, id), arity) in
      makeLam (toFgn (opExp S')) arity'
    let rec makeFgnUnary opSum =
      makeFgn (1, (function | App (U, Nil) -> opSum (fromExp (U, id))))
    let rec makeFgnBinary opSum =
      makeFgn
        (2,
          (function
           | App (U1, App (U2, Nil)) ->
               opSum ((fromExp (U1, id)), (fromExp (U2, id)))))
    let rec arrow (U, V) = Pi (((Dec (NONE, U)), No), V)
    let rec init (cs, installF) =
      myID := cs;
      (:=) boolID installF
        ((ConDec
            ("bool", NONE, 0, (Constraint ((!myID), solveBool)), (Uni Type),
              Kind)), NONE, [MS.Mnil]);
      (:=) trueID installF
        ((ConDec
            ("true", NONE, 0,
              (Foreign ((!myID), (function | _ -> toFgn (Sum (true__, nil))))),
              (bool ()), Type)), NONE, nil);
      (:=) falseID installF
        ((ConDec
            ("false", NONE, 0,
              (Foreign
                 ((!myID), (function | _ -> toFgn (Sum (false__, nil))))),
              (bool ()), Type)), NONE, nil);
      (:=) notID installF
        ((ConDec
            ("!", NONE, 0, (Foreign ((!myID), (makeFgnUnary notSum))),
              (arrow ((bool ()), (bool ()))), Type)),
          (SOME (FX.Prefix FX.maxPrec)), nil);
      (:=) xorID installF
        ((ConDec
            ("||", NONE, 0, (Foreign ((!myID), (makeFgnBinary xorSum))),
              (arrow ((bool ()), (arrow ((bool ()), (bool ()))))), Type)),
          (SOME (FX.Infix ((FX.dec FX.maxPrec), FX.Left))), nil);
      (:=) andID installF
        ((ConDec
            ("&", NONE, 0, (Foreign ((!myID), (makeFgnBinary andSum))),
              (arrow ((bool ()), (arrow ((bool ()), (bool ()))))), Type)),
          (SOME (FX.Infix ((FX.dec FX.maxPrec), FX.Left))), nil);
      (:=) orID installF
        ((ConDec
            ("|", NONE, 0, (Foreign ((!myID), (makeFgnBinary orSum))),
              (arrow ((bool ()), (arrow ((bool ()), (bool ()))))), Type)),
          (SOME (FX.Infix ((FX.dec FX.maxPrec), FX.Left))), nil);
      (:=) impliesID installF
        ((ConDec
            ("=>", NONE, 0, (Foreign ((!myID), (makeFgnBinary impliesSum))),
              (arrow ((bool ()), (arrow ((bool ()), (bool ()))))), Type)),
          (SOME (FX.Infix ((FX.dec (FX.dec FX.maxPrec)), FX.Left))), nil);
      (:=) iffID installF
        ((ConDec
            ("<=>", NONE, 0, (Foreign ((!myID), (makeFgnBinary iffSum))),
              (arrow ((bool ()), (arrow ((bool ()), (bool ()))))), Type)),
          (SOME (FX.Infix ((FX.dec (FX.dec FX.maxPrec)), FX.Left))), nil);
      installFgnExpOps ();
      ()
    (* CSManager.ModeSyn *)
    (* member eq (x, L) = true iff there there is a y in L s.t. eq(y, x) *)
    (* differenceSet eq L1 L2 = (L1 \ L2) U (L2 \ L1) *)
    (* equalSet eq (L1, L2) = true iff L1 is equal to L2 (both seen as sets) *)
    (* unionSet eq (L1, L2) = L1 U L2 *)
    (* toExp sum = U

       Invariant:
       If sum is normal
       G |- U : V and U is the Twelf syntax conversion of sum
    *)
    (* toExpMon mon = U

       Invariant:
       If mon is normal
       G |- U : V and U is the Twelf syntax conversion of mon
    *)
    (* toExpEClo (U,s) = U

       Invariant:
       G |- U : V and U is the Twelf syntax conversion of Us
    *)
    (* compatibleMon (mon1, mon2) = true only if mon1 = mon2 (as monomials) *)
    (* sameExpW ((U1,s1), (U2,s2)) = T

       Invariant:
       If   G |- s1 : G1    G1 |- U1 : V1    (U1,s1)  in whnf
       and  G |- s2 : G2    G2 |- U2 : V2    (U2,s2)  in whnf
       then T only if U1[s1] = U2[s2] (as expressions)
    *)
    (* sameExp ((U1,s1), (U2,s2)) = T

       Invariant:
       If   G |- s1 : G1    G1 |- U1 : V1
       and  G |- s2 : G2    G2 |- U2 : V2
       then T only if U1[s1] = U2[s2] (as expressions)
    *)
    (* sameSpine (S1, S2) = T

       Invariant:
       If   G |- S1 : V > W
       and  G |- S2 : V > W
       then T only if S1 = S2 (as spines)
    *)
    (* sameSub (s1, s2) = T

       Invariant:
       If   G |- s1 : G'
       and  G |- s2 : G'
       then T only if s1 = s2 (as substitutions)
    *)
    (* xorSum (sum1, sum2) = sum3

       Invariant:
       If   sum1 normal
       and  sum2 normal
       then sum3 normal
       and  sum3 = sum1 xor sum2
    *)
    (* andSum (sum1, sum2) = sum3

       Invariant:
       If   sum1 normal
       and  sum2 normal
       then sum3 normal
       and  sum3 = sum1 and sum2
    *)
    (* andSumMon (sum1, mon2) = sum3

       Invariant:
       If   sum1 normal
       and  mon2 normal
       then sum3 normal
       and  sum3 = sum1 and mon2
    *)
    (* notSum sum = sum'

       Invariant:
       If   sum  normal
       then sum' normal
       and  sum' = not sum
    *)
    (* orSum (sum1, sum2) = sum3

       Invariant:
       If   sum1 normal
       and  sum2 normal
       then sum3 normal
       and  sum3 = sum1 or sum2
    *)
    (* impliesSum (sum1, sum2) = sum3

       Invariant:
       If   sum1 normal
       and  sum2 normal
       then sum3 normal
       and  sum3 = sum1 implies sum2
    *)
    (* iffSum (sum1, sum2) = sum3

       Invariant:
       If   sum1 normal
       and  sum2 normal
       then sum3 normal
       and  sum3 = sum1 iff sum2
    *)
    (* fromExpW (U, s) = sum

       Invariant:
       If   G' |- s : G    G |- U : V    (U,s)  in whnf
       then sum is the internal representation of U[s] as sum of monomials
       and sum is normal
    *)
    (* normalizeSum sum = sum', where sum' normal and sum' = sum *)
    (* normalizeMon mon = mon', where mon' normal and mon' = mon *)
    (* mapSum (f, m + M1 + ...) = m + mapMon(f,M1) + ... *)
    (* mapMon (f, n * (U1,s1) + ...) = n * f(U1,s1) * ... *)
    (* appSum (f, m + M1 + ...) = ()     and appMon (f, Mi) for each i *)
    (* appMon (f, n * (U1, s1) + ... ) = () and f (Ui[si]) for each i *)
    (* findMon f (G, sum) =
         SOME(x) if f(M) = SOME(x) for some monomial M in sum
         NONE    if f(M) = NONE for all monomials M in sum
    *)
    (* unifySum (G, sum1, sum2) = result

       Invariant:
       If   G |- sum1 : number     sum1 normal
       and  G |- sum2 : number     sum2 normal
       then result is the outcome (of type FgnUnify) of solving the
       equation sum1 = sum2 by gaussian elimination.
    *)
    (* toFgn sum = U

       Invariant:
       If sum normal
       then U is a foreign expression representing sum.
    *)
    (* toInternal (fe) = U

       Invariant:
       if fe is (MyIntsynRep sum) and sum : normal
       then U is the Twelf syntax conversion of sum
    *)
    (* map (fe) f = U'

       Invariant:
       if fe is (MyIntsynRep sum)   sum : normal
       and
         f sum = f (m + mon1 + ... + monN) =
               = m + f (m1 * Us1 * ... * UsM) + ...
               = m + (m1 * (f Us1) * ... * f (UsM))
               = sum'           sum' : normal
       then
         U' is a foreign expression representing sum'
    *)
    (* app (fe) f = ()

       Invariant:
       if fe is (MyIntsynRep sum)     sum : normal
       and
          sum = m + mon1 + ... monN
          where moni = mi * Usi1 * ... UsiMi
       then f is applied to each Usij
         (since sum : normal, each Usij is in whnf)
    *)
    (* AK: redundant normalizeSum ? *)
    (* init (cs, installFunction) = ()
       Initialize the constraint solver.
       installFunction is used to add its signature symbols.
    *)
    let solver =
      {
        name = "equality/booleans";
        keywords = "booleans,equality";
        needs = ["Unify"];
        fgnConst = NONE;
        init;
        reset = (function | () -> ());
        mark = (function | () -> ());
        unwind = (function | () -> ())
      }
  end ;;
