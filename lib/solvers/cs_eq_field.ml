
module type CS_EQ_FIELD  =
  sig
    include CS
    module Field : FIELD
    type nonrec 'a mset = 'a list
    type __Sum =
      | Sum of (Field.number * __Mon mset) 
    and __Mon =
      | Mon of (Field.number * (IntSyn.__Exp * IntSyn.__Sub) mset) 
    val fromExp : IntSyn.eclo -> __Sum
    val toExp : __Sum -> IntSyn.__Exp
    val normalize : __Sum -> __Sum
    val compatibleMon : __Mon -> __Mon -> bool
    val number : unit -> IntSyn.__Exp
    val unaryMinus : IntSyn.__Exp -> IntSyn.__Exp
    val plus : IntSyn.__Exp -> IntSyn.__Exp -> IntSyn.__Exp
    val minus : IntSyn.__Exp -> IntSyn.__Exp -> IntSyn.__Exp
    val times : IntSyn.__Exp -> IntSyn.__Exp -> IntSyn.__Exp
    val constant : Field.number -> IntSyn.__Exp
  end;;




module CSEqField(CSEqField:sig
                             module Field : FIELD
                             module Whnf : WHNF
                             module Unify : UNIFY
                           end) : CS_EQ_FIELD =
  struct
    module Field = Field
    type nonrec 'a mset = 'a list
    type __Sum =
      | Sum of (Field.number * __Mon mset) 
    and __Mon =
      | Mon of (Field.number * (IntSyn.__Exp * IntSyn.__Sub) mset) 
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
    let rec unaryMinusExp (__U) =
      Root ((Const (!unaryMinusID)), (App (__U, Nil)))
    let rec plusExp (__U) (__V) =
      Root ((Const (!plusID)), (App (__U, (App (__V, Nil)))))
    let rec minusExp (__U) (__V) =
      Root ((Const (!minusID)), (App (__U, (App (__V, Nil)))))
    let rec timesExp (__U) (__V) =
      Root ((Const (!timesID)), (App (__U, (App (__V, Nil)))))
    let rec numberConDec d =
      ConDec ((toString d), NONE, 0, Normal, (number ()), Type)
    let rec numberExp d = Root ((FgnConst ((!myID), (numberConDec d))), Nil)
    let rec parseNumber string =
      match fromString string with
      | Some d -> Some (numberConDec d)
      | NONE -> NONE
    let rec solveNumber (__G) (__S) k = Some (numberExp (fromInt k))
    let rec findMSet eq x (__L) =
      let rec findMSet' __0__ __1__ =
        match (__0__, __1__) with
        | (tried, nil) -> NONE
        | (tried, y::__L) ->
            if eq (x, y)
            then Some (y, (tried @ __L))
            else findMSet' ((y :: tried), __L) in
      findMSet' (nil, __L)
    let rec equalMSet eq =
      let rec equalMSet' __2__ __3__ =
        match (__2__, __3__) with
        | (nil, nil) -> true__
        | (x::L1', __L2) ->
            (match findMSet eq (x, __L2) with
             | Some (y, L2') -> equalMSet' (L1', L2')
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
           | _ -> false__)
      | ((((EVar (r1, __G1, __V1, cnstrs1) as U1), s1) as Us1),
         (((EVar (r2, __G2, __V2, cnstrs2) as U2), s2) as Us2)) ->
          (r1 = r2) && (sameSub (s1, s2))
      | _ -> false__
    let rec sameExp (__Us1) (__Us2) =
      sameExpW ((Whnf.whnf __Us1), (Whnf.whnf __Us2))
    let rec sameSpine __8__ __9__ =
      match (__8__, __9__) with
      | ((Nil, s1), (Nil, s2)) -> true__
      | ((SClo (__S1, s1'), s1), __Ss2) ->
          sameSpine ((__S1, (comp (s1', s1))), __Ss2)
      | (__Ss1, (SClo (__S2, s2'), s2)) ->
          sameSpine (__Ss1, (__S2, (comp (s2', s2))))
      | ((App (__U1, __S1), s1), (App (__U2, __S2), s2)) ->
          (sameExp ((__U1, s1), (__U2, s2))) &&
            (sameSpine ((__S1, s1), (__S2, s2)))
      | _ -> false__
    let rec sameSub __10__ __11__ =
      match (__10__, __11__) with
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
           | NONE -> Sum (m, (mon :: monL)))
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
      | (Root (Def d, _), _) as Us -> fromExpW (Whnf.expandDef __Us)
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
    let rec findMon f (__G) (Sum (m, monL)) =
      let rec findMon' __20__ __21__ =
        match (__20__, __21__) with
        | (nil, monL2) -> NONE
        | (mon::monL1, monL2) ->
            (match f (__G, mon, (Sum (m, (monL1 @ monL2)))) with
             | Some _ as result -> result
             | NONE -> findMon' (monL1, (mon :: monL2))) in
      findMon' (monL, nil)
    let rec unifySum (__G) sum1 sum2 =
      let rec invertMon __22__ __23__ __24__ =
        match (__22__, __23__, __24__) with
        | (__G, Mon (n, ((EVar (r, _, _, _) as LHS), s)::[]), sum) ->
            if Whnf.isPatSub s
            then
              let ss = Whnf.invert s in
              let RHS = toFgn (timesSum ((Sum ((~ (inverse n)), nil)), sum)) in
              (if Unify.invertible (__G, (RHS, id), ss, r)
               then Some (__G, LHS, RHS, ss)
               else NONE)
            else NONE
        | _ -> NONE in
      match minusSum (sum2, sum1) with
      | Sum (m, nil) -> if m = zero then Succeed nil else Fail
      | sum ->
          (match findMon invertMon (__G, sum) with
           | Some assignment -> Succeed [Assign assignment]
           | NONE ->
               let __U = toFgn sum in
               let cnstr = ref (Eqn (__G, __U, (numberExp zero))) in
               Succeed [Delay (__U, cnstr)])
    let rec toFgn =
      function
      | Sum (m, nil) as sum -> toExp sum
      | Sum (m, monL) as sum -> FgnExp ((!myID), (MyIntsynRep sum))
    let rec toInternal __25__ __26__ =
      match (__25__, __26__) with
      | (MyIntsynRep sum, ()) -> toExp (normalizeSum sum)
      | (fe, ()) -> raise (UnexpectedFgnExp fe)
    let rec map __27__ __28__ =
      match (__27__, __28__) with
      | (MyIntsynRep sum, f) -> toFgn (normalizeSum (mapSum (f, sum)))
      | (fe, _) -> raise (UnexpectedFgnExp fe)
    let rec app __29__ __30__ =
      match (__29__, __30__) with
      | (MyIntsynRep sum, f) -> appSum (f, sum)
      | (fe, _) -> raise (UnexpectedFgnExp fe)
    let rec equalTo __31__ __32__ =
      match (__31__, __32__) with
      | (MyIntsynRep sum, __U2) ->
          (match minusSum ((normalizeSum sum), (fromExp (__U2, id))) with
           | Sum (m, nil) -> m = zero
           | _ -> false__)
      | (fe, _) -> raise (UnexpectedFgnExp fe)
    let rec unifyWith __33__ __34__ __35__ =
      match (__33__, __34__, __35__) with
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
      let rec makeLam __36__ __37__ =
        match (__36__, __37__) with
        | (__E, 0) -> __E
        | (__E, n) ->
            Lam ((Dec (NONE, (number ()))), (makeLam __E (Int.(-) (n, 1)))) in
      let rec expand __38__ __39__ =
        match (__38__, __39__) with
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
    let rec arrow (__U) (__V) = Pi (((Dec (NONE, __U)), No), __V)
    let rec init cs installF =
      myID := cs;
      (:=) numberID installF
        ((ConDec
            (Field.name, NONE, 0, (Constraint ((!myID), solveNumber)),
              (Uni Type), Kind)), NONE, [MS.Mnil]);
      (:=) unaryMinusID installF
        ((ConDec
            ("~", NONE, 0, (Foreign ((!myID), (makeFgnUnary unaryMinusSum))),
              (arrow ((number ()), (number ()))), Type)),
          (Some (FX.Prefix FX.maxPrec)), nil);
      (:=) plusID installF
        ((ConDec
            ("+", NONE, 0, (Foreign ((!myID), (makeFgnBinary plusSum))),
              (arrow ((number ()), (arrow ((number ()), (number ()))))),
              Type)),
          (Some (FX.Infix ((FX.dec (FX.dec FX.maxPrec)), FX.Left))), nil);
      (:=) minusID installF
        ((ConDec
            ("-", NONE, 0, (Foreign ((!myID), (makeFgnBinary minusSum))),
              (arrow ((number ()), (arrow ((number ()), (number ()))))),
              Type)),
          (Some (FX.Infix ((FX.dec (FX.dec FX.maxPrec)), FX.Left))), nil);
      (:=) timesID installF
        ((ConDec
            ("*", NONE, 0, (Foreign ((!myID), (makeFgnBinary timesSum))),
              (arrow ((number ()), (arrow ((number ()), (number ()))))),
              Type)), (Some (FX.Infix ((FX.dec FX.maxPrec), FX.Left))), nil);
      installFgnExpOps ();
      ()
    let solver =
      {
        name = (("equality/" ^ Field.name) ^ "s");
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
