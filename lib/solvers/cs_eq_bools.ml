
module CSEqBools(CSEqBools:sig module Whnf : WHNF module Unify : UNIFY end) :
  CS =
  struct
    type nonrec 'a set = 'a list
    type __Sum =
      | Sum of (bool * __Mon set) 
    and __Mon =
      | Mon of (IntSyn.__Exp * IntSyn.__Sub) set 
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
    let rec solveBool __0__ __1__ __2__ =
      match (__0__, __1__, __2__) with
      | (__G, __S, 0) -> Some (trueExp ())
      | (__G, __S, 1) -> Some (falseExp ())
      | (__G, __S, k) -> None
    let notID = (ref (-1) : cid ref)
    let xorID = (ref (-1) : cid ref)
    let andID = (ref (-1) : cid ref)
    let orID = (ref (-1) : cid ref)
    let impliesID = (ref (-1) : cid ref)
    let iffID = (ref (-1) : cid ref)
    let rec notExp (__U) = Root ((Const (!notID)), (App (__U, Nil)))
    let rec xorExp (__U) (__V) =
      Root ((Const (!xorID)), (App (__U, (App (__V, Nil)))))
    let rec andExp (__U) (__V) =
      Root ((Const (!andID)), (App (__U, (App (__V, Nil)))))
    let rec orExp (__U) (__V) =
      Root ((Const (!orID)), (App (__U, (App (__V, Nil)))))
    let rec impliesExp (__U) (__V) =
      Root ((Const (!impliesID)), (App (__U, (App (__V, Nil)))))
    let rec iffExp (__U) (__V) =
      Root ((Const (!iffID)), (App (__U, (App (__V, Nil)))))
    let rec member eq x (__L) = List.exists (fun y -> eq (x, y)) __L
    let rec differenceSet eq (__L1) (__L2) =
      let L1' = List.filter (fun x -> not (member eq (x, __L2))) __L1 in
      let L2' = List.filter (fun x -> not (member eq (x, __L1))) __L2 in
      L1' @ L2'
    let rec equalSet eq (__L1) (__L2) =
      match differenceSet eq (__L1, __L2) with
      | nil -> true
      | _::_ -> false
    let rec unionSet eq (__L1) (__L2) =
      let L2' = List.filter (fun x -> not (member eq (x, __L1))) __L2 in
      __L1 @ L2'
    let rec toExp =
      function
      | Sum (m, nil) ->
          let cid = if m then !trueID else !falseID in
          Root ((Const cid), Nil)
      | Sum (m, mon::[]) ->
          if m = false
          then toExpMon mon
          else xorExp ((toExp (Sum (m, nil))), (toExpMon mon))
      | Sum (m, (mon::monL as monLL)) ->
          xorExp ((toExp (Sum (m, monL))), (toExpMon mon))
    let rec toExpMon =
      function
      | Mon ((__Us)::[]) -> toExpEClo __Us
      | Mon ((__Us)::UsL) -> andExp ((toExpMon (Mon UsL)), (toExpEClo __Us))
    let rec toExpEClo __3__ __4__ =
      match (__3__, __4__) with | (__U, Shift 0) -> __U | __Us -> EClo __Us
    let rec compatibleMon (Mon (UsL1)) (Mon (UsL2)) =
      equalSet (fun (__Us1) -> fun (__Us2) -> sameExp (__Us1, __Us2))
        (UsL1, UsL2)
    let rec sameExpW __5__ __6__ =
      match (__5__, __6__) with
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
    let rec sameSpine __7__ __8__ =
      match (__7__, __8__) with
      | ((Nil, s1), (Nil, s2)) -> true
      | ((SClo (__S1, s1'), s1), __Ss2) ->
          sameSpine ((__S1, (comp (s1', s1))), __Ss2)
      | (__Ss1, (SClo (__S2, s2'), s2)) ->
          sameSpine (__Ss1, (__S2, (comp (s2', s2))))
      | ((App (__U1, __S1), s1), (App (__U2, __S2), s2)) ->
          (sameExp ((__U1, s1), (__U2, s2))) &&
            (sameSpine ((__S1, s1), (__S2, s2)))
      | _ -> false
    let rec sameSub __9__ __10__ =
      match (__9__, __10__) with
      | (Shift _, Shift _) -> true
      | (Dot (Idx k1, s1), Dot (Idx k2, s2)) ->
          (k1 = k2) && (sameSub (s1, s2))
      | ((Dot (Idx _, _) as s1), Shift k2) ->
          sameSub
            (s1, (Dot ((Idx (Int.(+) (k2, 1))), (Shift (Int.(+) (k2, 1))))))
      | (Shift k1, (Dot (Idx _, _) as s2)) ->
          sameSub
            ((Dot ((Idx (Int.(+) (k1, 1))), (Shift (Int.(+) (k1, 1))))), s2)
      | _ -> false
    let rec xorSum (Sum (m1, monL1)) (Sum (m2, monL2)) =
      Sum ((not (m1 = m2)), (differenceSet compatibleMon (monL1, monL2)))
    let rec andSum __11__ __12__ =
      match (__11__, __12__) with
      | ((Sum (false, nil) as sum1), sum2) -> sum1
      | (sum1, (Sum (false, nil) as sum2)) -> sum2
      | ((Sum (true, nil) as sum1), sum2) -> sum2
      | (sum1, (Sum (true, nil) as sum2)) -> sum1
      | (Sum (m1, mon1::monL1), sum2) ->
          xorSum
            ((andSumMon (sum2, mon1)), (andSum ((Sum (m1, monL1)), sum2)))
    let rec andSumMon __13__ __14__ =
      match (__13__, __14__) with
      | (Sum (true, nil), mon) -> Sum (false, [mon])
      | ((Sum (false, nil) as sum1), mon) -> sum1
      | (Sum (m1, (Mon (UsL1))::monL1), (Mon (UsL2) as mon2)) ->
          let UsL = unionSet sameExp (UsL1, UsL2) in
          xorSum
            ((Sum (false, [Mon UsL])),
              (andSumMon ((Sum (m1, monL1)), mon2)))
    let rec notSum (Sum (m, monL)) = Sum ((not m), monL)
    let rec orSum sum1 sum2 =
      xorSum (sum1, (xorSum (sum2, (andSum (sum1, sum2)))))
    let rec impliesSum sum1 sum2 =
      notSum (xorSum (sum1, (andSum (sum1, sum2))))
    let rec iffSum sum1 sum2 = notSum (xorSum (sum1, sum2))
    let rec fromExpW =
      function
      | (FgnExp (cs, fe), _) as Us ->
          if (!) ((=) cs) myID
          then normalizeSum (extractSum fe)
          else Sum (false, [Mon [__Us]])
      | __Us -> Sum (false, [Mon [__Us]])
    let rec fromExp (__Us) = fromExpW (Whnf.whnf __Us)
    let rec normalizeSum =
      function
      | Sum (m, nil) as sum -> sum
      | Sum (m, mon::[]) -> xorSum ((Sum (m, nil)), (normalizeMon mon))
      | Sum (m, mon::monL) ->
          xorSum ((normalizeMon mon), (normalizeSum (Sum (m, monL))))
    let rec normalizeMon =
      function
      | Mon ((__Us)::[]) -> fromExp __Us
      | Mon ((__Us)::UsL) ->
          andSum ((fromExp __Us), (normalizeMon (Mon UsL)))
    let rec mapSum f (Sum (m, monL)) =
      Sum (m, (List.map (fun mon -> mapMon (f, mon)) monL))
    let rec mapMon f (Mon (UsL)) =
      Mon (List.map (fun (__Us) -> Whnf.whnf ((f (EClo __Us)), id)) UsL)
    let rec appSum f (Sum (m, monL)) =
      List.app (fun mon -> appMon (f, mon)) monL
    let rec appMon f (Mon (UsL)) = List.app (fun (__Us) -> f (EClo __Us)) UsL
    let rec findMon f (__G) (Sum (m, monL)) =
      let rec findMon' __15__ __16__ =
        match (__15__, __16__) with
        | (nil, monL2) -> None
        | (mon::monL1, monL2) ->
            (match f (__G, mon, (Sum (m, (monL1 @ monL2)))) with
             | Some _ as result -> result
             | None -> findMon' (monL1, (mon :: monL2))) in
      findMon' (monL, nil)
    let rec unifySum (__G) sum1 sum2 =
      let rec invertMon __17__ __18__ __19__ =
        match (__17__, __18__, __19__) with
        | (__G, Mon (((EVar (r, _, _, _) as LHS), s)::[]), sum) ->
            if Whnf.isPatSub s
            then
              let ss = Whnf.invert s in
              let RHS = toFgn sum in
              (if Unify.invertible (__G, (RHS, id), ss, r)
               then Some (__G, LHS, RHS, ss)
               else None)
            else None
        | _ -> None in
      match xorSum (sum2, sum1) with
      | Sum (false, nil) -> Succeed nil
      | Sum (true, nil) -> Fail
      | sum ->
          (match findMon invertMon (__G, sum) with
           | Some assignment -> Succeed [Assign assignment]
           | None ->
               let __U = toFgn sum in
               let cnstr = ref (Eqn (__G, __U, (falseExp ()))) in
               Succeed [Delay (__U, cnstr)])
    let rec toFgn =
      function
      | Sum (m, nil) as sum -> toExp sum
      | Sum (m, monL) as sum -> FgnExp ((!myID), (MyIntsynRep sum))
    let rec toInternal __20__ __21__ =
      match (__20__, __21__) with
      | (MyIntsynRep sum, ()) -> toExp (normalizeSum sum)
      | (fe, ()) -> raise (UnexpectedFgnExp fe)
    let rec map __22__ __23__ =
      match (__22__, __23__) with
      | (MyIntsynRep sum, f) -> toFgn (normalizeSum (mapSum (f, sum)))
      | (fe, _) -> raise (UnexpectedFgnExp fe)
    let rec app __24__ __25__ =
      match (__24__, __25__) with
      | (MyIntsynRep sum, f) -> appSum (f, sum)
      | (fe, _) -> raise (UnexpectedFgnExp fe)
    let rec equalTo __26__ __27__ =
      match (__26__, __27__) with
      | (MyIntsynRep sum, __U2) ->
          (((match xorSum ((normalizeSum sum), (fromExp (__U2, id))) with
             | Sum (m, nil) -> m = false
             | _ -> false))
          (* AK: redundant normalizeSum ? *))
      | (fe, _) -> raise (UnexpectedFgnExp fe)
    let rec unifyWith __28__ __29__ __30__ =
      match (__28__, __29__, __30__) with
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
      let rec makeLam __31__ __32__ =
        match (__31__, __32__) with
        | (__E, 0) -> __E
        | (__E, n) ->
            Lam ((Dec (None, (bool ()))), (makeLam __E (Int.(-) (n, 1)))) in
      let rec expand __33__ __34__ =
        match (__33__, __34__) with
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
      (:=) boolID installF
        ((ConDec
            ("bool", None, 0, (Constraint ((!myID), solveBool)), (Uni Type),
              Kind)), None, [MS.Mnil]);
      (:=) trueID installF
        ((ConDec
            ("true", None, 0,
              (Foreign ((!myID), (fun _ -> toFgn (Sum (true, nil))))),
              (bool ()), Type)), None, nil);
      (:=) falseID installF
        ((ConDec
            ("false", None, 0,
              (Foreign ((!myID), (fun _ -> toFgn (Sum (false, nil))))),
              (bool ()), Type)), None, nil);
      (:=) notID installF
        ((ConDec
            ("!", None, 0, (Foreign ((!myID), (makeFgnUnary notSum))),
              (arrow ((bool ()), (bool ()))), Type)),
          (Some (FX.Prefix FX.maxPrec)), nil);
      (:=) xorID installF
        ((ConDec
            ("||", None, 0, (Foreign ((!myID), (makeFgnBinary xorSum))),
              (arrow ((bool ()), (arrow ((bool ()), (bool ()))))), Type)),
          (Some (FX.Infix ((FX.dec FX.maxPrec), FX.Left))), nil);
      (:=) andID installF
        ((ConDec
            ("&", None, 0, (Foreign ((!myID), (makeFgnBinary andSum))),
              (arrow ((bool ()), (arrow ((bool ()), (bool ()))))), Type)),
          (Some (FX.Infix ((FX.dec FX.maxPrec), FX.Left))), nil);
      (:=) orID installF
        ((ConDec
            ("|", None, 0, (Foreign ((!myID), (makeFgnBinary orSum))),
              (arrow ((bool ()), (arrow ((bool ()), (bool ()))))), Type)),
          (Some (FX.Infix ((FX.dec FX.maxPrec), FX.Left))), nil);
      (:=) impliesID installF
        ((ConDec
            ("=>", None, 0, (Foreign ((!myID), (makeFgnBinary impliesSum))),
              (arrow ((bool ()), (arrow ((bool ()), (bool ()))))), Type)),
          (Some (FX.Infix ((FX.dec (FX.dec FX.maxPrec)), FX.Left))), nil);
      (:=) iffID installF
        ((ConDec
            ("<=>", None, 0, (Foreign ((!myID), (makeFgnBinary iffSum))),
              (arrow ((bool ()), (arrow ((bool ()), (bool ()))))), Type)),
          (Some (FX.Infix ((FX.dec (FX.dec FX.maxPrec)), FX.Left))), nil);
      installFgnExpOps ();
      ()
    let solver =
      {
        name = "equality/booleans";
        keywords = "booleans,equality";
        needs = ["Unify"];
        fgnConst = None;
        init;
        reset = (fun () -> ());
        mark = (fun () -> ());
        unwind = (fun () -> ())
      }
  end ;;
