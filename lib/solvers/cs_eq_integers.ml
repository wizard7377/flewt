
module type CS_EQ_INTEGERS  =
  sig
    include CS
    module Integers : INTEGERS
    type nonrec 'a mset = 'a list
    type __Sum =
      | Sum of (Integers.int * __Mon mset) 
    and __Mon =
      | Mon of (Integers.int * (IntSyn.__Exp * IntSyn.__Sub) mset) 
    val fromExp : IntSyn.eclo -> __Sum
    val toExp : __Sum -> IntSyn.__Exp
    val normalize : __Sum -> __Sum
    val compatibleMon : __Mon -> __Mon -> bool
    val number : unit -> IntSyn.__Exp
    val unaryMinus : IntSyn.__Exp -> IntSyn.__Exp
    val plus : IntSyn.__Exp -> IntSyn.__Exp -> IntSyn.__Exp
    val minus : IntSyn.__Exp -> IntSyn.__Exp -> IntSyn.__Exp
    val times : IntSyn.__Exp -> IntSyn.__Exp -> IntSyn.__Exp
    val constant : Integers.int -> IntSyn.__Exp
  end;;




module CSEqIntegers(CSEqIntegers:sig
                                   module Integers : INTEGERS
                                   module Whnf : WHNF
                                   module Unify : UNIFY
                                 end) : CS_EQ_INTEGERS =
  struct
    module Integers = Integers
    type nonrec 'a mset = 'a list
    type __Sum =
      | Sum of (Integers.int * __Mon mset) 
    and __Mon =
      | Mon of (Integers.int * (IntSyn.__Exp * IntSyn.__Sub) mset) 
    open IntSyn
    open Integers
    module FX = CSManager.Fixity
    module MS = ModeSyn
    exception MyIntsynRep of __Sum 
    let rec extractSum =
      function | MyIntsynRep sum -> sum | fe -> raise (UnexpectedFgnExp fe)
    let zero = fromInt 0
    let one = fromInt 1
    let myID = (ref (-1) : csid ref)
    let numberID = (ref (-1) : cid ref)
    let rec number () = Root ((Const (!numberID)), Nil)
    let unaryMinusID = (ref (-1) : cid ref)
    let plusID = (ref (-1) : cid ref)
    let minusID = (ref (-1) : cid ref)
    let timesID = (ref (-1) : cid ref)
    let rec unaryMinusExp (__U) =
      Root ((Const (!unaryMinusID)), (App (__U, Nil)))
    let rec plusExp (__U) (__V) =
      Root ((Const (!plusID)), (App (__U, (App (__V, Nil)))))
    let rec minusExp (__U) (__V) =
      Root ((Const (!minusID)), (App (__U, (App (__V, Nil)))))
    let rec timesExp (__U) (__V) =
      Root ((Const (!timesID)), (App (__U, (App (__V, Nil)))))
    let rec numberConDec d =
      ConDec ((toString d), None, 0, Normal, (number ()), Type)
    let rec numberExp d = Root ((FgnConst ((!myID), (numberConDec d))), Nil)
    let rec parseNumber string =
      match fromString string with
      | Some d -> Some (numberConDec d)
      | None -> None
    let rec solveNumber (__G) (__S) k = Some (numberExp (fromInt k))
    let rec findMSet eq x (__L) =
      let rec findMSet' __0__ __1__ =
        match (__0__, __1__) with
        | (tried, nil) -> None
        | (tried, y::__L) ->
            if eq (x, y)
            then Some (y, (tried @ __L))
            else findMSet' ((y :: tried), __L) in
      findMSet' (nil, __L)
    let rec equalMSet eq =
      let rec equalMSet' __2__ __3__ =
        match (__2__, __3__) with
        | (nil, nil) -> true
        | (x::L1', __L2) ->
            (match findMSet eq (x, __L2) with
             | Some (y, L2') -> equalMSet' (L1', L2')
             | None -> false)
        | _ -> false in
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
      | Mon (n, (__Us)::[]) ->
          if n = one
          then toExpEClo __Us
          else timesExp ((toExpMon (Mon (n, nil))), (toExpEClo __Us))
      | Mon (n, (__Us)::UsL) ->
          timesExp ((toExpMon (Mon (n, UsL))), (toExpEClo __Us))
    let rec toExpEClo __4__ __5__ =
      match (__4__, __5__) with | (__U, Shift 0) -> __U | __Us -> EClo __Us
    let rec compatibleMon (Mon (_, UsL1)) (Mon (_, UsL2)) =
      equalMSet (fun (__Us1) -> fun (__Us2) -> sameExpW (__Us1, __Us2))
        (UsL1, UsL2)
    let rec sameExpW __6__ __7__ =
      match (__6__, __7__) with
      | (((Root (__H1, __S1), s1) as Us1), ((Root (__H2, __S2), s2) as Us2))
          ->
          (match (__H1, __H2) with
           | (BVar k1, BVar k2) ->
               (k1 = k2) && (sameSpine ((__S1, s1), (__S2, s2)))
           | (FVar (n1, _, _), FVar (n2, _, _)) ->
               (n1 = n2) && (sameSpine ((__S1, s1), (__S2, s2)))
           | _ -> false)
      | ((((EVar (r1, __G1, __V1, cnstrs1) as U1), s1) as Us1),
         (((EVar (r2, __G2, __V2, cnstrs2) as U2), s2) as Us2)) ->
          (r1 = r2) && (sameSub (s1, s2))
      | _ -> false
    let rec sameExp (__Us1) (__Us2) =
      sameExpW ((Whnf.whnf __Us1), (Whnf.whnf __Us2))
    let rec sameSpine __8__ __9__ =
      match (__8__, __9__) with
      | ((Nil, s1), (Nil, s2)) -> true
      | ((SClo (__S1, s1'), s1), __Ss2) ->
          sameSpine ((__S1, (comp (s1', s1))), __Ss2)
      | (__Ss1, (SClo (__S2, s2'), s2)) ->
          sameSpine (__Ss1, (__S2, (comp (s2', s2))))
      | ((App (__U1, __S1), s1), (App (__U2, __S2), s2)) ->
          (sameExp ((__U1, s1), (__U2, s2))) &&
            (sameSpine ((__S1, s1), (__S2, s2)))
      | _ -> false
    let rec sameSub __10__ __11__ =
      match (__10__, __11__) with
      | (Shift _, Shift _) -> true
      | (Dot (Idx k1, s1), Dot (Idx k2, s2)) ->
          (k1 = k2) && (sameSub (s1, s2))
      | ((Dot (Idx _, _) as s1), Shift k2) ->
          sameSub
            (s1, (Dot ((Idx (Int.(+) (k2, 1))), (Shift (Int.(+) (k2, 1))))))
      | (Shift k1, (Dot (Idx _, _) as s2)) ->
          sameSub
            ((Dot ((Idx (Int.(+) (k1, 1))), (Shift (Int.(+) (k1, 1))))), s2)
      | (_, _) -> false
    let rec plusSum __12__ __13__ =
      match (__12__, __13__) with
      | (Sum (m1, nil), Sum (m2, monL2)) -> Sum ((m1 + m2), monL2)
      | (Sum (m1, monL1), Sum (m2, nil)) -> Sum ((m1 + m2), monL1)
      | (Sum (m1, mon1::monL1), Sum (m2, monL2)) ->
          plusSumMon ((plusSum ((Sum (m1, monL1)), (Sum (m2, monL2)))), mon1)
    let rec plusSumMon __14__ __15__ =
      match (__14__, __15__) with
      | (Sum (m, nil), mon) -> Sum (m, [mon])
      | (Sum (m, monL), (Mon (n, UsL) as mon)) ->
          (match findMSet compatibleMon (mon, monL) with
           | Some (Mon (n', _), monL') ->
               let n'' = n + n' in
               if n'' = zero
               then Sum (m, monL')
               else Sum (m, ((Mon (n'', UsL)) :: monL'))
           | None -> Sum (m, (mon :: monL)))
    let rec timesSum __16__ __17__ =
      match (__16__, __17__) with
      | (Sum (m1, nil), Sum (m2, nil)) -> Sum ((m1 * m2), nil)
      | (Sum (m1, mon1::monL1), sum2) ->
          plusSum
            ((timesSumMon (sum2, mon1)),
              (timesSum ((Sum (m1, monL1)), sum2)))
      | (sum1, Sum (m2, mon2::monL2)) ->
          plusSum
            ((timesSumMon (sum1, mon2)),
              (timesSum (sum1, (Sum (m2, monL2)))))
    let rec timesSumMon __18__ __19__ =
      match (__18__, __19__) with
      | (Sum (m, nil), Mon (n, UsL)) ->
          let n' = m * n in
          if n' = zero then Sum (n', nil) else Sum (zero, [Mon (n', UsL)])
      | (Sum (m, (Mon (n', UsL'))::monL), (Mon (n, UsL) as mon)) ->
          let n'' = n * n' in
          let UsL'' = UsL @ UsL' in
          let Sum (m', monL') = timesSumMon ((Sum (m, monL)), mon) in
          Sum (m', ((Mon (n'', UsL'')) :: monL'))
    let rec unaryMinusSum sum = timesSum ((Sum ((~ one), nil)), sum)
    let rec minusSum sum1 sum2 = plusSum (sum1, (unaryMinusSum sum2))
    let rec fromExpW =
      function
      | (FgnExp (cs, fe), _) as Us ->
          if (!) ((=) cs) myID
          then normalizeSum (extractSum fe)
          else Sum (zero, [Mon (one, [__Us])])
      | (Root (FgnConst (cs, conDec), _), _) as Us ->
          if (!) ((=) cs) myID
          then
            (match fromString (conDecName conDec) with
             | Some m -> Sum (m, nil))
          else Sum (zero, [Mon (one, [__Us])])
      | __Us -> Sum (zero, [Mon (one, [__Us])])
    let rec fromExp (__Us) = fromExpW (Whnf.whnf __Us)
    let rec normalizeSum =
      function
      | Sum (m, nil) as sum -> sum
      | Sum (m, mon::[]) -> plusSum ((Sum (m, nil)), (normalizeMon mon))
      | Sum (m, mon::monL) ->
          plusSum ((normalizeMon mon), (normalizeSum (Sum (m, monL))))
    let rec normalizeMon =
      function
      | Mon (n, nil) as mon -> Sum (n, nil)
      | Mon (n, (__Us)::[]) -> timesSum ((Sum (n, nil)), (fromExp __Us))
      | Mon (n, (__Us)::UsL) as mon ->
          timesSum ((fromExp __Us), (normalizeMon (Mon (n, UsL))))
    let rec mapSum f (Sum (m, monL)) =
      Sum (m, (List.map (fun mon -> mapMon (f, mon)) monL))
    let rec mapMon f (Mon (n, UsL)) =
      Mon (n, (List.map (fun (__Us) -> Whnf.whnf ((f (EClo __Us)), id)) UsL))
    let rec appSum f (Sum (m, monL)) =
      List.app (fun mon -> appMon (f, mon)) monL
    let rec appMon f (Mon (n, UsL)) =
      List.app (fun (__Us) -> f (EClo __Us)) UsL
    let rec solvableSum (Sum (m, monL)) =
      let rec gcd_list =
        function
        | n1::nil -> n1
        | n1::n2::nil -> gcd (n1, n2)
        | n1::n2::l -> gcd ((gcd (n1, n2)), (gcd_list l)) in
      let coeffL = List.map (fun (Mon (n, _)) -> n) monL in
      let g = gcd_list coeffL in (rem (m, (gcd_list coeffL))) = zero
    let rec findMon f (__G) (Sum (m, monL)) =
      let rec findMon' __20__ __21__ =
        match (__20__, __21__) with
        | (nil, monL2) -> None
        | (mon::monL1, monL2) ->
            (match f (__G, mon, (Sum (m, (monL1 @ monL2)))) with
             | Some _ as result -> result
             | None -> findMon' (monL1, (mon :: monL2))) in
      findMon' (monL, nil)
    let rec divideSum (Sum (m, monL)) k =
      let exception Err  in
        let rec divide n =
          if (rem (n, k)) = zero then quot (n, k) else raise Err in
        let rec divideMon (Mon (n, UsL)) = Mon ((divide n), UsL) in
        try Some (Sum ((divide m), (List.map divideMon monL)))
        with | Err -> None
    let rec delaySum (__G) sum =
      let __U = toFgn sum in
      let cnstr = ref (Eqn (__G, __U, (numberExp zero))) in
      Delay (__U, cnstr)
    let rec solveSum __25__ __26__ =
      match (__25__, __26__) with
      | (__G,
         (Sum (m, (Mon (n, ((EVar (r, _, _, _) as X), s)::[]))::[]) as sum))
          ->
          if Whnf.isPatSub s
          then
            [Assign
               (__G, __X, (numberExp (~ (quot (m, n)))), (Whnf.invert s))]
          else [delaySum (__G, sum)]
      | (__G, sum) ->
          let rec invertMon __22__ __23__ __24__ =
            match (__22__, __23__, __24__) with
            | (__G, (Mon (n, (EVar (r, _, _, _), s)::[]) as mon), sum) ->
                if Whnf.isPatSub s
                then
                  let ss = Whnf.invert s in
                  let RHS = toFgn sum in
                  (if Unify.invertible (__G, (RHS, id), ss, r)
                   then Some (mon, ss, sum)
                   else None)
                else None
            | (__G, mon, sum) -> None in
          (match findMon invertMon (__G, sum) with
           | Some (Mon (n1, (__X1, s1)::[]), ss1, sum1) ->
               (match findMon invertMon (__G, sum1) with
                | Some (Mon (n2, (__X2, s2)::[]), ss2, sum2) ->
                    let s = Unify.intersection (s1, s2) in
                    let ss = Whnf.invert s in
                    let __G' = Whnf.strengthen (ss, __G) in
                    let g = gcd (n1, n2) in
                    let (x1, x2) = solve_gcd (n1, n2) in
                    let __K = newEVar (__G', (number ())) in
                    let __Z = newEVar (__G', (number ())) in
                    (::) ((::) (Assign
                                  (__G, __X1,
                                    (toFgn
                                       (plusSum
                                          ((Sum
                                              (zero,
                                                [Mon
                                                   ((quot (n2, g)),
                                                     [(__K, ss)])])),
                                            (timesSum
                                               ((Sum (x1, nil)),
                                                 (Sum
                                                    (zero,
                                                      [Mon (one, [(__Z, ss)])]))))))),
                                    ss1))
                            Assign
                            (__G, __X2,
                              (toFgn
                                 (plusSum
                                    ((Sum
                                        (zero,
                                          [Mon
                                             ((~ (quot (n1, g))),
                                               [(__K, ss)])])),
                                      (timesSum
                                         ((Sum (x2, nil)),
                                           (Sum
                                              (zero,
                                                [Mon (one, [(__Z, ss)])]))))))),
                              ss2))
                      solveSum
                      (__G,
                        (plusSum ((Sum (zero, [Mon (g, [(__Z, ss)])])), sum2)))
                | None ->
                    (match divideSum (sum1, n1) with
                     | Some sum1' ->
                         [Assign
                            (__G, __X1, (toFgn (unaryMinusSum sum1')), ss1)]
                     | None -> [delaySum (__G, sum)]))
           | None -> [delaySum (__G, sum)])
    let rec unifySum (__G) sum1 sum2 =
      let rec invertMon (__G) (Mon (n, ((EVar (r, _, _, _) as LHS), s)::[]))
        sum =
        if Whnf.isPatSub s
        then
          let ss = Whnf.invert s in
          let RHS = toFgn (timesSum ((Sum ((~ n), nil)), sum)) in
          (if Unify.invertible (__G, (RHS, id), ss, r)
           then Some (__G, LHS, RHS, ss)
           else None)
        else None in
      match minusSum (sum2, sum1) with
      | Sum (m, nil) -> if m = zero then Succeed nil else Fail
      | sum ->
          if solvableSum sum then Succeed (solveSum (__G, sum)) else Fail
    let rec toFgn =
      function
      | Sum (m, nil) as sum -> toExp sum
      | Sum (m, monL) as sum -> FgnExp ((!myID), (MyIntsynRep sum))
    let rec toInternal __27__ __28__ =
      match (__27__, __28__) with
      | (MyIntsynRep sum, ()) -> toExp (normalizeSum sum)
      | (fe, ()) -> raise (UnexpectedFgnExp fe)
    let rec map __29__ __30__ =
      match (__29__, __30__) with
      | (MyIntsynRep sum, f) -> toFgn (normalizeSum (mapSum (f, sum)))
      | (fe, _) -> raise (UnexpectedFgnExp fe)
    let rec app __31__ __32__ =
      match (__31__, __32__) with
      | (MyIntsynRep sum, f) -> appSum (f, sum)
      | (fe, _) -> raise (UnexpectedFgnExp fe)
    let rec equalTo __33__ __34__ =
      match (__33__, __34__) with
      | (MyIntsynRep sum, __U2) ->
          (match minusSum ((normalizeSum sum), (fromExp (__U2, id))) with
           | Sum (m, nil) -> m = zero
           | _ -> false)
      | (fe, _) -> raise (UnexpectedFgnExp fe)
    let rec unifyWith __35__ __36__ __37__ =
      match (__35__, __36__, __37__) with
      | (MyIntsynRep sum, __G, __U2) ->
          unifySum (__G, (normalizeSum sum), (fromExp (__U2, id)))
      | (fe, _) -> raise (UnexpectedFgnExp fe)
    let rec installFgnExpOps () =
      let csid = !myID in
      let _ = FgnExpStd.ToInternal.install (csid, toInternal) in
      let _ = FgnExpStd.Map.install (csid, map) in
      let _ = FgnExpStd.App.install (csid, app) in
      let _ = FgnExpStd.UnifyWith.install (csid, unifyWith) in
      let _ = FgnExpStd.EqualTo.install (csid, equalTo) in ()
    let rec makeFgn arity opExp (__S) =
      let rec makeParams =
        function
        | 0 -> Nil
        | n -> App ((Root ((BVar n), Nil)), (makeParams (Int.(-) (n, 1)))) in
      let rec makeLam __38__ __39__ =
        match (__38__, __39__) with
        | (__E, 0) -> __E
        | (__E, n) ->
            Lam ((Dec (None, (number ()))), (makeLam __E (Int.(-) (n, 1)))) in
      let rec expand __40__ __41__ =
        match (__40__, __41__) with
        | ((Nil, s), arity) -> ((makeParams arity), arity)
        | ((App (__U, __S), s), arity) ->
            let (__S', arity') = expand ((__S, s), (Int.(-) (arity, 1))) in
            ((App ((EClo (__U, (comp (s, (Shift arity'))))), __S')), arity')
        | ((SClo (__S, s'), s), arity) ->
            expand ((__S, (comp (s', s))), arity) in
      let (__S', arity') = expand ((__S, id), arity) in
      makeLam (toFgn (opExp __S')) arity'
    let rec makeFgnUnary opSum =
      makeFgn (1, (fun (App (__U, Nil)) -> opSum (fromExp (__U, id))))
    let rec makeFgnBinary opSum =
      makeFgn
        (2,
          (fun (App (__U1, App (__U2, Nil))) ->
             opSum ((fromExp (__U1, id)), (fromExp (__U2, id)))))
    let rec arrow (__U) (__V) = Pi (((Dec (None, __U)), No), __V)
    let rec init cs installF =
      myID := cs;
      (:=) numberID installF
        ((ConDec
            ("integer", None, 0, (Constraint ((!myID), solveNumber)),
              (Uni Type), Kind)), None, [MS.Mnil]);
      (:=) unaryMinusID installF
        ((ConDec
            ("~", None, 0, (Foreign ((!myID), (makeFgnUnary unaryMinusSum))),
              (arrow ((number ()), (number ()))), Type)),
          (Some (FX.Prefix FX.maxPrec)), nil);
      (:=) plusID installF
        ((ConDec
            ("+", None, 0, (Foreign ((!myID), (makeFgnBinary plusSum))),
              (arrow ((number ()), (arrow ((number ()), (number ()))))),
              Type)),
          (Some (FX.Infix ((FX.dec (FX.dec FX.maxPrec)), FX.Left))), nil);
      (:=) minusID installF
        ((ConDec
            ("-", None, 0, (Foreign ((!myID), (makeFgnBinary minusSum))),
              (arrow ((number ()), (arrow ((number ()), (number ()))))),
              Type)),
          (Some (FX.Infix ((FX.dec (FX.dec FX.maxPrec)), FX.Left))), nil);
      (:=) timesID installF
        ((ConDec
            ("*", None, 0, (Foreign ((!myID), (makeFgnBinary timesSum))),
              (arrow ((number ()), (arrow ((number ()), (number ()))))),
              Type)), (Some (FX.Infix ((FX.dec FX.maxPrec), FX.Left))), nil);
      installFgnExpOps ();
      ()
    let solver =
      {
        name = "equality/integers";
        keywords = "arithmetic,equality";
        needs = ["Unify"];
        fgnConst = (Some { parse = parseNumber });
        init;
        reset = (fun () -> ());
        mark = (fun () -> ());
        unwind = (fun () -> ())
      }
    let fromExp = fromExp
    let toExp = toExp
    let normalize = normalizeSum
    let compatibleMon = compatibleMon
    let number = number
    let rec unaryMinus (__U) = toFgn (unaryMinusSum (fromExp (__U, id)))
    let rec plus (__U) (__V) =
      toFgn (plusSum ((fromExp (__U, id)), (fromExp (__V, id))))
    let rec minus (__U) (__V) =
      toFgn (minusSum ((fromExp (__U, id)), (fromExp (__V, id))))
    let rec times (__U) (__V) =
      toFgn (timesSum ((fromExp (__U, id)), (fromExp (__V, id))))
    let constant = numberExp
  end ;;
