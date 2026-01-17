
module type CS_EQ_FIELD  =
  sig
    include
      ((CS)(* Gaussian-Elimination Equation Solver *)
      (* Author: Roberto Virga *))
    module Field : FIELD
    type nonrec 'a mset =
      (('a)(* Foreign expressions *)(*! structure IntSyn : INTSYN !*))
        list
    type __Sum =
      | Sum of
      (((Field.number)(* Sum :                      *)
      (* MultiSet                   *)) * __Mon mset) 
    and __Mon =
      | Mon of
      (((Field.number)(* Monomials:                 *)
      (* Sum ::= m + M1 + ...       *)) * (IntSyn.__Exp *
      IntSyn.__Sub) mset) 
    val fromExp :
      IntSyn.eclo ->
        ((__Sum)(* Mon ::= n * U1[s1] * ...   *))
    val toExp : __Sum -> IntSyn.__Exp
    val normalize : __Sum -> __Sum
    val compatibleMon : (__Mon * __Mon) -> bool
    val number :
      unit ->
        ((IntSyn.__Exp)(* Internal expressions constructors *))
    val unaryMinus : IntSyn.__Exp -> IntSyn.__Exp
    val plus : (IntSyn.__Exp * IntSyn.__Exp) -> IntSyn.__Exp
    val minus : (IntSyn.__Exp * IntSyn.__Exp) -> IntSyn.__Exp
    val times : (IntSyn.__Exp * IntSyn.__Exp) -> IntSyn.__Exp
    val constant : Field.number -> IntSyn.__Exp
  end;;




module CSEqField(CSEqField:sig
                             module Field : FIELD
                             module Whnf : WHNF
                             module Unify :
                             ((UNIFY)(* Gaussian-Elimination Equation Solver *)
                             (* Author: Roberto Virga *)
                             (*! structure IntSyn : INTSYN !*)(*! sharing Whnf.IntSyn = IntSyn !*))
                           end) : CS_EQ_FIELD =
  struct
    module Field =
      ((Field)(*! sharing Unify.IntSyn = IntSyn !*)(*! structure CSManager : CS_MANAGER !*)
      (*! sharing CSManager.IntSyn = IntSyn !*)(*! structure CSManager = CSManager !*))
    type nonrec 'a mset =
      (('a)(*! structure IntSyn = IntSyn !*)) list
    type __Sum =
      | Sum of
      (((Field.number)(* Sum :                      *)
      (* MultiSet                   *)) * __Mon mset) 
    and __Mon =
      | Mon of
      (((Field.number)(* Monomials:                 *)
      (* Sum ::= m + M1 + ...       *)) * (IntSyn.__Exp *
      IntSyn.__Sub) mset) 
    open IntSyn
    open Field
    module FX = CSManager.Fixity
    module MS = ModeSyn
    exception MyIntsynRep of __Sum 
    let rec extractSum =
      function | MyIntsynRep sum -> sum | fe -> raise (UnexpectedFgnExp fe)
    let myID = (ref (-1) : csid ref)
    let numberID = (ref (-1) : cid ref)
    let rec number () = Root ((Const (!numberID)), Nil)
    let unaryMinusID = (ref (-1) : cid ref)
    let plusID = (ref (-1) : cid ref)
    let minusID = (ref (-1) : cid ref)
    let timesID = (ref (-1) : cid ref)
    let rec unaryMinusExp (U) =
      Root ((Const (!unaryMinusID)), (App (U, Nil)))
    let rec plusExp (U, V) =
      Root ((Const (!plusID)), (App (U, (App (V, Nil)))))
    let rec minusExp (U, V) =
      Root ((Const (!minusID)), (App (U, (App (V, Nil)))))
    let rec timesExp (U, V) =
      Root ((Const (!timesID)), (App (U, (App (V, Nil)))))
    let rec numberConDec d =
      ConDec ((toString d), NONE, 0, Normal, (number ()), Type)
    let rec numberExp d = Root ((FgnConst ((!myID), (numberConDec d))), Nil)
    let rec parseNumber string =
      match fromString string with
      | SOME d -> SOME (numberConDec d)
      | NONE -> NONE
    let rec solveNumber (G, S, k) = SOME (numberExp (fromInt k))
    let rec findMSet eq (x, L) =
      let findMSet' =
        function
        | (tried, nil) -> NONE
        | (tried, y::L) ->
            if eq (x, y)
            then SOME (y, (tried @ L))
            else findMSet' ((y :: tried), L) in
      findMSet' (nil, L)
    let rec equalMSet eq =
      let equalMSet' =
        function
        | (nil, nil) -> true__
        | (x::L1', L2) ->
            (match findMSet eq (x, L2) with
             | SOME (y, L2') -> equalMSet' (L1', L2')
             | NONE -> false__)
        | _ -> false__ in
      equalMSet'
    let rec toExp =
      function
      | Sum (m, nil) -> numberExp m
      | Sum (m, mon::[]) ->
          if m = zero
          then toExpMon mon
          else plusExp ((toExp (Sum (m, nil))), (toExpMon mon))
      | Sum (m, (mon::monL as monLL)) ->
          plusExp ((toExp (Sum (m, monL))), (toExpMon mon))
    let rec toExpMon =
      function
      | Mon (n, nil) -> numberExp n
      | Mon (n, (Us)::[]) ->
          if n = one
          then toExpEClo Us
          else timesExp ((toExpMon (Mon (n, nil))), (toExpEClo Us))
      | Mon (n, (Us)::UsL) ->
          timesExp ((toExpMon (Mon (n, UsL))), (toExpEClo Us))
    let rec toExpEClo = function | (U, Shift 0) -> U | Us -> EClo Us
    let rec compatibleMon (Mon (_, UsL1), Mon (_, UsL2)) =
      equalMSet (function | (Us1, Us2) -> sameExpW (Us1, Us2)) (UsL1, UsL2)
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
    let rec plusSum =
      function
      | (Sum (m1, nil), Sum (m2, monL2)) -> Sum ((m1 + m2), monL2)
      | (Sum (m1, monL1), Sum (m2, nil)) -> Sum ((m1 + m2), monL1)
      | (Sum (m1, mon1::monL1), Sum (m2, monL2)) ->
          plusSumMon ((plusSum ((Sum (m1, monL1)), (Sum (m2, monL2)))), mon1)
    let rec plusSumMon =
      function
      | (Sum (m, nil), mon) -> Sum (m, [mon])
      | (Sum (m, monL), (Mon (n, UsL) as mon)) ->
          (match findMSet compatibleMon (mon, monL) with
           | SOME (Mon (n', _), monL') ->
               let n'' = n + n' in
               if n'' = zero
               then Sum (m, monL')
               else Sum (m, ((Mon (n'', UsL)) :: monL'))
           | NONE -> Sum (m, (mon :: monL)))
    let rec timesSum =
      function
      | (Sum (m1, nil), Sum (m2, nil)) -> Sum ((m1 * m2), nil)
      | (Sum (m1, mon1::monL1), sum2) ->
          plusSum
            ((timesSumMon (sum2, mon1)),
              (timesSum ((Sum (m1, monL1)), sum2)))
      | (sum1, Sum (m2, mon2::monL2)) ->
          plusSum
            ((timesSumMon (sum1, mon2)),
              (timesSum (sum1, (Sum (m2, monL2)))))
    let rec timesSumMon =
      function
      | (Sum (m, nil), Mon (n, UsL)) ->
          let n' = m * n in
          if n' = zero then Sum (n', nil) else Sum (zero, [Mon (n', UsL)])
      | (Sum (m, (Mon (n', UsL'))::monL), (Mon (n, UsL) as mon)) ->
          let n'' = n * n' in
          let UsL'' = UsL @ UsL' in
          let Sum (m', monL') = timesSumMon ((Sum (m, monL)), mon) in
          Sum (m', ((Mon (n'', UsL'')) :: monL'))
    let rec unaryMinusSum sum = timesSum ((Sum ((~ one), nil)), sum)
    let rec minusSum (sum1, sum2) = plusSum (sum1, (unaryMinusSum sum2))
    let rec fromExpW =
      function
      | (FgnExp (cs, fe), _) as Us ->
          if (!) ((=) cs) myID
          then normalizeSum (extractSum fe)
          else Sum (zero, [Mon (one, [Us])])
      | (Root (FgnConst (cs, conDec), _), _) as Us ->
          if (!) ((=) cs) myID
          then
            (match fromString (conDecName conDec) with
             | SOME m -> Sum (m, nil))
          else Sum (zero, [Mon (one, [Us])])
      | (Root (Def d, _), _) as Us -> fromExpW (Whnf.expandDef Us)
      | Us -> Sum (zero, [Mon (one, [Us])])
    let rec fromExp (Us) = fromExpW (Whnf.whnf Us)
    let rec normalizeSum =
      function
      | Sum (m, nil) as sum -> sum
      | Sum (m, mon::[]) -> plusSum ((Sum (m, nil)), (normalizeMon mon))
      | Sum (m, mon::monL) ->
          plusSum ((normalizeMon mon), (normalizeSum (Sum (m, monL))))
    let rec normalizeMon =
      function
      | Mon (n, nil) as mon -> Sum (n, nil)
      | Mon (n, (Us)::[]) -> timesSum ((Sum (n, nil)), (fromExp Us))
      | Mon (n, (Us)::UsL) as mon ->
          timesSum ((fromExp Us), (normalizeMon (Mon (n, UsL))))
    let rec mapSum (f, Sum (m, monL)) =
      Sum (m, (List.map (function | mon -> mapMon (f, mon)) monL))
    let rec mapMon (f, Mon (n, UsL)) =
      Mon
        (n, (List.map (function | Us -> Whnf.whnf ((f (EClo Us)), id)) UsL))
    let rec appSum (f, Sum (m, monL)) =
      List.app (function | mon -> appMon (f, mon)) monL
    let rec appMon (f, Mon (n, UsL)) =
      List.app (function | Us -> f (EClo Us)) UsL
    let rec findMon f (G, Sum (m, monL)) =
      let findMon' =
        function
        | (nil, monL2) -> NONE
        | (mon::monL1, monL2) ->
            (match f (G, mon, (Sum (m, (monL1 @ monL2)))) with
             | SOME _ as result -> result
             | NONE -> findMon' (monL1, (mon :: monL2))) in
      findMon' (monL, nil)
    let rec unifySum (G, sum1, sum2) =
      let invertMon =
        function
        | (G, Mon (n, ((EVar (r, _, _, _) as LHS), s)::[]), sum) ->
            if Whnf.isPatSub s
            then
              let ss = Whnf.invert s in
              let RHS = toFgn (timesSum ((Sum ((~ (inverse n)), nil)), sum)) in
              (if Unify.invertible (G, (RHS, id), ss, r)
               then SOME (G, LHS, RHS, ss)
               else NONE)
            else NONE
        | _ -> NONE in
      match minusSum (sum2, sum1) with
      | Sum (m, nil) -> if m = zero then Succeed nil else Fail
      | sum ->
          (match findMon invertMon (G, sum) with
           | SOME assignment -> Succeed [Assign assignment]
           | NONE ->
               let U = toFgn sum in
               let cnstr = ref (Eqn (G, U, (numberExp zero))) in
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
          (match minusSum ((normalizeSum sum), (fromExp (U2, id))) with
           | Sum (m, nil) -> m = zero
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
      let makeParams =
        function
        | 0 -> Nil
        | n -> App ((Root ((BVar n), Nil)), (makeParams (Int.(-) (n, 1)))) in
      let makeLam arg__0 arg__1 =
        match (arg__0, arg__1) with
        | (E, 0) -> E
        | (E, n) ->
            Lam ((Dec (NONE, (number ()))), (makeLam E (Int.(-) (n, 1)))) in
      let expand =
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
      (:=) numberID installF
        ((ConDec
            (Field.name, NONE, 0, (Constraint ((!myID), solveNumber)),
              (Uni Type), Kind)), NONE, [MS.Mnil]);
      (:=) unaryMinusID installF
        ((ConDec
            ("~", NONE, 0, (Foreign ((!myID), (makeFgnUnary unaryMinusSum))),
              (arrow ((number ()), (number ()))), Type)),
          (SOME (FX.Prefix FX.maxPrec)), nil);
      (:=) plusID installF
        ((ConDec
            ("+", NONE, 0, (Foreign ((!myID), (makeFgnBinary plusSum))),
              (arrow ((number ()), (arrow ((number ()), (number ()))))),
              Type)),
          (SOME (FX.Infix ((FX.dec (FX.dec FX.maxPrec)), FX.Left))), nil);
      (:=) minusID installF
        ((ConDec
            ("-", NONE, 0, (Foreign ((!myID), (makeFgnBinary minusSum))),
              (arrow ((number ()), (arrow ((number ()), (number ()))))),
              Type)),
          (SOME (FX.Infix ((FX.dec (FX.dec FX.maxPrec)), FX.Left))), nil);
      (:=) timesID installF
        ((ConDec
            ("*", NONE, 0, (Foreign ((!myID), (makeFgnBinary timesSum))),
              (arrow ((number ()), (arrow ((number ()), (number ()))))),
              Type)), (SOME (FX.Infix ((FX.dec FX.maxPrec), FX.Left))), nil);
      installFgnExpOps ();
      ()
    let ((solver)(* Mon ::= n * U1[s1] * ...   *)(* A monomial (n * U1[s1] * U2[s2] * ...) is said to be normal iff
       (a) the coefficient n is different from zero;
       (b) each (Ui,si) is in whnf and not a foreign term corresponding
           to a sum.
     A sum is normal iff all its monomials are normal, and moreover they
     are pairwise distinct.
  *)
      (* CSManager.ModeSyn *)(* FgnExp representation for this domain *)
      (* constraint solver ID of this module *)(* constant ID of the type family constant "number" *)
      (* constant ID's of the object constants defined by this module *)
      (* ~ : number -> number           *)(* + : number -> number -> number *)
      (* - : number -> number -> number *)(* * : number -> number -> number *)
      (* parseNumber str = SOME(conDec) or NONE

       Invariant:
       If str parses to the number n
       then conDec is the (foreign) constant declaration of n
    *)
      (* solveNumber k = SOME(U)

       Invariant:
       U is the term obtained applying the foreign constant
       corresponding to the number k to an empty spine
    *)
      (* findMset eq (x, L) =
         SOME (y, L') if there exists y such that eq (x, y)
                         and L ~ (y :: L') (multiset equality)
         NONE if there is no y in L such that eq (x, y)
    *)
      (* equalMset eq (L, L') = true iff L ~ L' (multiset equality) *)
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
      (* plusSum (sum1, sum2) = sum3

       Invariant:
       If   sum1 normal
       and  sum2 normal
       then sum3 normal
       and  sum3 = sum1 + sum2
    *)
      (* plusSumMon (sum1, mon2) = sum3

       Invariant:
       If   sum1 normal
       and  mon2 normal
       then sum3 normal
       and  sum3 = sum1 + mon2
    *)
      (* timesSum (sum1, sum2) = sum3

       Invariant:
       If   sum1 normal
       and  sum2 normal
       then sum3 normal
       and  sum3 = sum1 * sum2
    *)
      (* timesSumMon (sum1, mon2) = sum3

       Invariant:
       If   sum1 normal
       and  mon2 normal
       then sum3 normal
       and  sum3 = sum1 * mon2
    *)
      (* unaryMinusSum sum = sum'

       Invariant:
       If   sum  normal
       then sum' normal
       and  sum' = ~1 * sum
    *)
      (* minusSum (sum1, sum2) = sum3

       Invariant:
       If   sum1 normal
       and  sum2 normal
       then sum3 normal
       and  sum3 = sum1 - sum2
    *)
      (* fromExpW (U, s) = sum

       Invariant:
       If   G' |- s : G    G |- U : V    (U,s)  in whnf
       then sum is the internal representation of U[s] as sum of monomials
       and sum is normal
    *)
      (* fromExp (U, s) = sum

       Invariant:
       If   G' |- s : G    G |- U : V
       then sum is the internal representation of U[s] as sum of monomials
       and sum is normal
    *)
      (* normalizeSum sum = sum', where sum' normal and sum' = sum *)
      (* normalizeMon mon = mon', where mon' normal and mon' = mon *)
      (* mapSum (f, m + M1 + ...) = m + mapMon(f,M1) + ... *)(* mapMon (f, n * (U1,s1) + ...) = n * f(U1,s1) * ... *)
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
      (* init (cs, installFunction) = ()
       Initialize the constraint solver.
       installFunction is used to add its signature symbols.
    *))
      =
      {
        name = (("equality/" ^ Field.name) ^ "s");
        keywords = "arithmetic,equality";
        needs = ["Unify"];
        fgnConst = (SOME { parse = parseNumber });
        init;
        reset = (function | () -> ());
        mark = (function | () -> ());
        unwind = (function | () -> ())
      }
    let fromExp = fromExp
    let toExp = toExp
    let normalize = normalizeSum
    let compatibleMon = compatibleMon
    let number = number
    let rec unaryMinus (U) = toFgn (unaryMinusSum (fromExp (U, id)))
    let rec plus (U, V) =
      toFgn (plusSum ((fromExp (U, id)), (fromExp (V, id))))
    let rec minus (U, V) =
      toFgn (minusSum ((fromExp (U, id)), (fromExp (V, id))))
    let rec times (U, V) =
      toFgn (timesSum ((fromExp (U, id)), (fromExp (V, id))))
    let constant = numberExp
  end ;;
