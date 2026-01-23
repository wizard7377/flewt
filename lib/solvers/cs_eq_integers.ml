module type CS_EQ_INTEGERS  =
  sig
    include CS
    module Integers : INTEGERS
    type nonrec 'a mset = 'a list
    type sum_ =
      | Sum of (Integers.int * mon_ mset) 
    and mon_ =
      | Mon of (Integers.int * (IntSyn.exp_ * IntSyn.sub_) mset) 
    val fromExp : IntSyn.eclo -> sum_
    val toExp : sum_ -> IntSyn.exp_
    val normalize : sum_ -> sum_
    val compatibleMon : (mon_ * mon_) -> bool
    val number : unit -> IntSyn.exp_
    val unaryMinus : IntSyn.exp_ -> IntSyn.exp_
    val plus : (IntSyn.exp_ * IntSyn.exp_) -> IntSyn.exp_
    val minus : (IntSyn.exp_ * IntSyn.exp_) -> IntSyn.exp_
    val times : (IntSyn.exp_ * IntSyn.exp_) -> IntSyn.exp_
    val constant : Integers.int -> IntSyn.exp_
  end


module CSEqIntegers(CSEqIntegers:sig
                                   module Integers : INTEGERS
                                   module Whnf : WHNF
                                   module Unify : UNIFY
                                 end) : CS_EQ_INTEGERS =
  struct
    module Integers = Integers
    type nonrec 'a mset = 'a list
    type sum_ =
      | Sum of (Integers.int * mon_ mset) 
    and mon_ =
      | Mon of (Integers.int * (IntSyn.exp_ * IntSyn.sub_) mset) 
    open IntSyn
    open Integers
    module FX = CSManager.Fixity
    module MS = ModeSyn
    exception MyIntsynRep of sum_ 
    let rec extractSum =
      begin function
      | MyIntsynRep sum -> sum
      | fe -> raise (UnexpectedFgnExp fe) end
    let zero = fromInt 0
    let one = fromInt 1
    let myID = (ref (-1) : csid ref)
    let numberID = (ref (-1) : cid ref)
    let rec number () = Root ((Const !numberID), Nil)
    let unaryMinusID = (ref (-1) : cid ref)
    let plusID = (ref (-1) : cid ref)
    let minusID = (ref (-1) : cid ref)
    let timesID = (ref (-1) : cid ref)
    let rec unaryMinusExp (u_) =
      Root ((Const !unaryMinusID), (App (u_, Nil)))
    let rec plusExp (u_, v_) =
      Root ((Const !plusID), (App (u_, (App (v_, Nil)))))
    let rec minusExp (u_, v_) =
      Root ((Const !minusID), (App (u_, (App (v_, Nil)))))
    let rec timesExp (u_, v_) =
      Root ((Const !timesID), (App (u_, (App (v_, Nil)))))
    let rec numberConDec d =
      ConDec ((toString d), None, 0, Normal, (number ()), Type)
    let rec numberExp d = Root ((FgnConst (!myID, (numberConDec d))), Nil)
    let rec parseNumber string =
      begin match fromString string with
      | Some d -> Some (numberConDec d)
      | None -> None end
  let rec solveNumber (g_, s_, k) = Some (numberExp (fromInt k))
  let rec findMSet eq (x, l_) =
    let rec findMSet' =
      begin function
      | (tried, []) -> None
      | (tried, y::l_) -> if eq (x, y) then begin Some (y, (tried @ l_)) end
          else begin findMSet' ((y :: tried), l_) end end in
findMSet' ([], l_)
let rec equalMSet eq =
  let rec equalMSet' =
    begin function
    | ([], []) -> true
    | (x::L1', l2_) ->
        (begin match findMSet eq (x, l2_) with
         | Some (y, L2') -> equalMSet' (L1', L2')
         | None -> false end)
    | _ -> false end in
equalMSet'
let rec toExp =
  begin function
  | Sum (m, []) -> numberExp m
  | Sum (m, mon::[]) -> if m = zero then begin toExpMon mon end
      else begin plusExp ((toExp (Sum (m, []))), (toExpMon mon)) end
  | Sum (m, (mon::monL as monLL)) ->
      plusExp ((toExp (Sum (m, monL))), (toExpMon mon)) end
let rec toExpMon =
  begin function
  | Mon (n, []) -> numberExp n
  | Mon (n, (us_)::[]) -> if n = one then begin toExpEClo us_ end
      else begin timesExp ((toExpMon (Mon (n, []))), (toExpEClo us_)) end
  | Mon (n, (us_)::UsL) ->
      timesExp ((toExpMon (Mon (n, UsL))), (toExpEClo us_)) end
let rec toExpEClo =
  begin function | (u_, Shift 0) -> u_ | us_ -> EClo us_ end
let rec compatibleMon (Mon (_, UsL1), Mon (_, UsL2)) =
  equalMSet (begin function | (us1_, us2_) -> sameExpW (us1_, us2_) end)
  (UsL1, UsL2)
let rec sameExpW =
  begin function
  | (((Root (h1_, s1_), s1) as us1_), ((Root (h2_, s2_), s2) as us2_)) ->
      (begin match (h1_, h2_) with
       | (BVar k1, BVar k2) ->
           (k1 = k2) && (sameSpine ((s1_, s1), (s2_, s2)))
       | (FVar (n1, _, _), FVar (n2, _, _)) ->
           (n1 = n2) && (sameSpine ((s1_, s1), (s2_, s2)))
       | _ -> false end)
  | ((((EVar (r1, g1_, v1_, cnstrs1) as u1_), s1) as us1_),
     (((EVar (r2, g2_, v2_, cnstrs2) as u2_), s2) as us2_)) ->
      (r1 = r2) && (sameSub (s1, s2))
  | _ -> false end
let rec sameExp (us1_, us2_) = sameExpW ((Whnf.whnf us1_), (Whnf.whnf us2_))
let rec sameSpine =
  begin function
  | ((Nil, s1), (Nil, s2)) -> true
  | ((SClo (s1_, s1'), s1), ss2_) ->
      sameSpine ((s1_, (comp (s1', s1))), ss2_)
  | (ss1_, (SClo (s2_, s2'), s2)) ->
      sameSpine (ss1_, (s2_, (comp (s2', s2))))
  | ((App (u1_, s1_), s1), (App (u2_, s2_), s2)) ->
      (sameExp ((u1_, s1), (u2_, s2))) && (sameSpine ((s1_, s1), (s2_, s2)))
  | _ -> false end
let rec sameSub =
  begin function
  | (Shift _, Shift _) -> true
  | (Dot (Idx k1, s1), Dot (Idx k2, s2)) -> (k1 = k2) && (sameSub (s1, s2))
  | ((Dot (Idx _, _) as s1), Shift k2) ->
      sameSub
        (s1, (Dot ((Idx (Int.(+) (k2, 1))), (Shift (Int.(+) (k2, 1))))))
  | (Shift k1, (Dot (Idx _, _) as s2)) ->
      sameSub
        ((Dot ((Idx (Int.(+) (k1, 1))), (Shift (Int.(+) (k1, 1))))), s2)
  | (_, _) -> false end
let rec plusSum =
  begin function
  | (Sum (m1, []), Sum (m2, monL2)) -> Sum ((m1 + m2), monL2)
  | (Sum (m1, monL1), Sum (m2, [])) -> Sum ((m1 + m2), monL1)
  | (Sum (m1, mon1::monL1), Sum (m2, monL2)) ->
      plusSumMon ((plusSum ((Sum (m1, monL1)), (Sum (m2, monL2)))), mon1) end
let rec plusSumMon =
  begin function
  | (Sum (m, []), mon) -> Sum (m, [mon])
  | (Sum (m, monL), (Mon (n, UsL) as mon)) ->
      (begin match findMSet compatibleMon (mon, monL) with
       | Some (Mon (n', _), monL') ->
           let n'' = n + n' in if n'' = zero then begin Sum (m, monL') end
             else begin Sum (m, ((Mon (n'', UsL)) :: monL')) end
  | None -> Sum (m, (mon :: monL)) end) end
let rec timesSum =
  begin function
  | (Sum (m1, []), Sum (m2, [])) -> Sum ((m1 * m2), [])
  | (Sum (m1, mon1::monL1), sum2) ->
      plusSum
        ((timesSumMon (sum2, mon1)), (timesSum ((Sum (m1, monL1)), sum2)))
  | (sum1, Sum (m2, mon2::monL2)) ->
      plusSum
        ((timesSumMon (sum1, mon2)), (timesSum (sum1, (Sum (m2, monL2))))) end
let rec timesSumMon =
  begin function
  | (Sum (m, []), Mon (n, UsL)) ->
      let n' = m * n in if n' = zero then begin Sum (n', []) end
        else begin Sum (zero, [Mon (n', UsL)]) end
  | (Sum (m, (Mon (n', UsL'))::monL), (Mon (n, UsL) as mon)) ->
      let n'' = n * n' in
      let UsL'' = UsL @ UsL' in
      let Sum (m', monL') = timesSumMon ((Sum (m, monL)), mon) in
      Sum (m', ((Mon (n'', UsL'')) :: monL')) end
let rec unaryMinusSum sum = timesSum ((Sum ((- one), [])), sum)
let rec minusSum (sum1, sum2) = plusSum (sum1, (unaryMinusSum sum2))
let rec fromExpW =
  begin function
  | (FgnExp (cs, fe), _) as us_ ->
      if (!) ((=) cs) myID then begin normalizeSum (extractSum fe) end
      else begin Sum (zero, [Mon (one, [us_])]) end
  | (Root (FgnConst (cs, conDec), _), _) as us_ ->
      if (!) ((=) cs) myID
      then
        begin (begin match fromString (conDecName conDec) with
               | Some m -> Sum (m, []) end) end
  else begin Sum (zero, [Mon (one, [us_])]) end
| us_ -> Sum (zero, [Mon (one, [us_])]) end
let rec fromExp (us_) = fromExpW (Whnf.whnf us_)
let rec normalizeSum =
  begin function
  | Sum (m, []) as sum -> sum
  | Sum (m, mon::[]) -> plusSum ((Sum (m, [])), (normalizeMon mon))
  | Sum (m, mon::monL) ->
      plusSum ((normalizeMon mon), (normalizeSum (Sum (m, monL)))) end
let rec normalizeMon =
  begin function
  | Mon (n, []) as mon -> Sum (n, [])
  | Mon (n, (us_)::[]) -> timesSum ((Sum (n, [])), (fromExp us_))
  | Mon (n, (us_)::UsL) as mon ->
      timesSum ((fromExp us_), (normalizeMon (Mon (n, UsL)))) end
let rec mapSum (f, Sum (m, monL)) =
  Sum (m, (List.map (begin function | mon -> mapMon (f, mon) end) monL))
let rec mapMon (f, Mon (n, UsL)) =
  Mon
    (n,
      (List.map (begin function | us_ -> Whnf.whnf ((f (EClo us_)), id) end)
      UsL))
let rec appSum (f, Sum (m, monL)) =
  List.app (begin function | mon -> appMon (f, mon) end) monL
let rec appMon (f, Mon (n, UsL)) =
  List.app (begin function | us_ -> f (EClo us_) end) UsL
let rec solvableSum (Sum (m, monL)) =
  let rec gcd_list =
    begin function
    | n1::[] -> n1
    | n1::n2::[] -> gcd (n1, n2)
    | n1::n2::l -> gcd ((gcd (n1, n2)), (gcd_list l)) end in
let coeffL = List.map (begin function | Mon (n, _) -> n end) monL in
let g = gcd_list coeffL in (rem (m, (gcd_list coeffL))) = zero
let rec findMon f (g_, Sum (m, monL)) =
  let rec findMon' =
    begin function
    | ([], monL2) -> None
    | (mon::monL1, monL2) ->
        (begin match f (g_, mon, (Sum (m, (monL1 @ monL2)))) with
         | Some _ as result -> result
         | None -> findMon' (monL1, (mon :: monL2)) end) end in
findMon' (monL, [])
let rec divideSum (Sum (m, monL), k) =
  let exception Err  in
    let rec divide n = if (rem (n, k)) = zero then begin quot (n, k) end
      else begin raise Err end in
let rec divideMon (Mon (n, UsL)) = Mon ((divide n), UsL) in
begin try Some (Sum ((divide m), (List.map divideMon monL)))
with | Err -> None end
let rec delaySum (g_, sum) =
  let u_ = toFgn sum in
  let cnstr = ref (Eqn (g_, u_, (numberExp zero))) in Delay (u_, cnstr)
let rec solveSum =
  begin function
  | (g_, (Sum (m, (Mon (n, ((EVar (r, _, _, _) as x_), s)::[]))::[]) as sum))
      ->
      if Whnf.isPatSub s
      then
        begin [Assign
                 (g_, x_, (numberExp (- (quot (m, n)))), (Whnf.invert s))] end
      else begin [delaySum (g_, sum)] end
  | (g_, sum) ->
      let rec invertMon =
        begin function
        | (g_, (Mon (n, (EVar (r, _, _, _), s)::[]) as mon), sum) ->
            if Whnf.isPatSub s
            then
              begin let ss = Whnf.invert s in
                    let RHS = toFgn sum in
                    (if Unify.invertible (g_, (RHS, id), ss, r)
                     then begin Some (mon, ss, sum) end else begin None end) end
        else begin None end
  | (g_, mon, sum) -> None end in
(begin match findMon invertMon (g_, sum) with
| Some (Mon (n1, (x1_, s1)::[]), ss1, sum1) ->
   (begin match findMon invertMon (g_, sum1) with
    | Some (Mon (n2, (x2_, s2)::[]), ss2, sum2) ->
        let s = Unify.intersection (s1, s2) in
        let ss = Whnf.invert s in
        let g'_ = Whnf.strengthen (ss, g_) in
        let g = gcd (n1, n2) in
        let (x1, x2) = solve_gcd (n1, n2) in
        let k_ = newEVar (g'_, (number ())) in
        let z_ = newEVar (g'_, (number ())) in
        (::) ((::) (Assign
                      (g_, x1_,
                        (toFgn
                           (plusSum
                              ((Sum
                                  (zero, [Mon ((quot (n2, g)), [(k_, ss)])])),
                                (timesSum
                                   ((Sum (x1, [])),
                                     (Sum (zero, [Mon (one, [(z_, ss)])]))))))),
                        ss1))
                Assign
                (g_, x2_,
                  (toFgn
                     (plusSum
                        ((Sum (zero, [Mon ((- (quot (n1, g))), [(k_, ss)])])),
                          (timesSum
                             ((Sum (x2, [])),
                               (Sum (zero, [Mon (one, [(z_, ss)])]))))))),
                  ss2))
          solveSum
          (g_, (plusSum ((Sum (zero, [Mon (g, [(z_, ss)])])), sum2)))
    | None ->
        (begin match divideSum (sum1, n1) with
         | Some sum1' ->
             [Assign (g_, x1_, (toFgn (unaryMinusSum sum1')), ss1)]
         | None -> [delaySum (g_, sum)] end) end)
| None -> [delaySum (g_, sum)] end) end
let rec unifySum (g_, sum1, sum2) =
  let rec invertMon (g_, Mon (n, ((EVar (r, _, _, _) as LHS), s)::[]), sum) =
    if Whnf.isPatSub s
    then
      begin let ss = Whnf.invert s in
            let RHS = toFgn (timesSum ((Sum ((- n), [])), sum)) in
            (if Unify.invertible (g_, (RHS, id), ss, r)
             then begin Some (g_, LHS, RHS, ss) end else begin None end) end
  else begin None end in
begin match minusSum (sum2, sum1) with
| Sum (m, []) -> if m = zero then begin Succeed [] end else begin Fail end
| sum -> if solvableSum sum then begin Succeed (solveSum (g_, sum)) end
    else begin Fail end end
let rec toFgn =
  begin function
  | Sum (m, []) as sum -> toExp sum
  | Sum (m, monL) as sum -> FgnExp (!myID, (MyIntsynRep sum)) end
let rec toInternal arg__0 arg__1 =
  begin match (arg__0, arg__1) with
  | (MyIntsynRep sum, ()) -> toExp (normalizeSum sum)
  | (fe, ()) -> raise (UnexpectedFgnExp fe) end
let rec map arg__2 arg__3 =
  begin match (arg__2, arg__3) with
  | (MyIntsynRep sum, f) -> toFgn (normalizeSum (mapSum (f, sum)))
  | (fe, _) -> raise (UnexpectedFgnExp fe) end
let rec app arg__4 arg__5 =
  begin match (arg__4, arg__5) with
  | (MyIntsynRep sum, f) -> appSum (f, sum)
  | (fe, _) -> raise (UnexpectedFgnExp fe) end
let rec equalTo arg__6 arg__7 =
  begin match (arg__6, arg__7) with
  | (MyIntsynRep sum, u2_) ->
      (begin match minusSum ((normalizeSum sum), (fromExp (u2_, id))) with
       | Sum (m, []) -> m = zero
       | _ -> false end)
  | (fe, _) -> raise (UnexpectedFgnExp fe) end
let rec unifyWith arg__8 arg__9 =
  begin match (arg__8, arg__9) with
  | (MyIntsynRep sum, (g_, u2_)) ->
      unifySum (g_, (normalizeSum sum), (fromExp (u2_, id)))
  | (fe, _) -> raise (UnexpectedFgnExp fe) end
let rec installFgnExpOps () =
  let csid = !myID in
  let _ = FgnExpStd.ToInternal.install (csid, toInternal) in
  let _ = FgnExpStd.Map.install (csid, map) in
  let _ = FgnExpStd.App.install (csid, app) in
  let _ = FgnExpStd.UnifyWith.install (csid, unifyWith) in
  let _ = FgnExpStd.EqualTo.install (csid, equalTo) in ()
let rec makeFgn (arity, opExp) (s_) =
  let rec makeParams =
    begin function
    | 0 -> Nil
    | n -> App ((Root ((BVar n), Nil)), (makeParams (Int.(-) (n, 1)))) end in
let rec makeLam arg__10 arg__11 =
  begin match (arg__10, arg__11) with
  | (e_, 0) -> e_
  | (e_, n) -> Lam ((Dec (None, (number ()))), (makeLam e_ (Int.(-) (n, 1)))) end in
let rec expand =
  begin function
  | ((Nil, s), arity) -> ((makeParams arity), arity)
  | ((App (u_, s_), s), arity) ->
      let (s'_, arity') = expand ((s_, s), (Int.(-) (arity, 1))) in
      ((App ((EClo (u_, (comp (s, (Shift arity'))))), s'_)), arity')
  | ((SClo (s_, s'), s), arity) -> expand ((s_, (comp (s', s))), arity) end in
let (s'_, arity') = expand ((s_, id), arity) in
makeLam (toFgn (opExp s'_)) arity'
let rec makeFgnUnary opSum =
  makeFgn
    (1, (begin function | App (u_, Nil) -> opSum (fromExp (u_, id)) end))
let rec makeFgnBinary opSum =
  makeFgn
    (2,
      (begin function
       | App (u1_, App (u2_, Nil)) ->
           opSum ((fromExp (u1_, id)), (fromExp (u2_, id))) end))
let rec arrow (u_, v_) = Pi (((Dec (None, u_)), No), v_)
let rec init (cs, installF) =
  begin myID := cs;
  (:=) numberID installF
    ((ConDec
        ("integer", None, 0, (Constraint (!myID, solveNumber)), (Uni Type),
          Kind)), None, [MS.Mnil]);
  (:=) unaryMinusID installF
    ((ConDec
        ("~", None, 0, (Foreign (!myID, (makeFgnUnary unaryMinusSum))),
          (arrow ((number ()), (number ()))), Type)),
      (Some (FX.Prefix FX.maxPrec)), []);
  (:=) plusID installF
    ((ConDec
        ("+", None, 0, (Foreign (!myID, (makeFgnBinary plusSum))),
          (arrow ((number ()), (arrow ((number ()), (number ()))))), Type)),
      (Some (FX.Infix ((FX.dec (FX.dec FX.maxPrec)), FX.Left))), []);
  (:=) minusID installF
    ((ConDec
        ("-", None, 0, (Foreign (!myID, (makeFgnBinary minusSum))),
          (arrow ((number ()), (arrow ((number ()), (number ()))))), Type)),
      (Some (FX.Infix ((FX.dec (FX.dec FX.maxPrec)), FX.Left))), []);
  (:=) timesID installF
    ((ConDec
        ("*", None, 0, (Foreign (!myID, (makeFgnBinary timesSum))),
          (arrow ((number ()), (arrow ((number ()), (number ()))))), Type)),
      (Some (FX.Infix ((FX.dec FX.maxPrec), FX.Left))), []);
  installFgnExpOps ();
  () end
let solver =
  {
    name = "equality/integers";
    keywords = "arithmetic,equality";
    needs = ["Unify"];
    fgnConst = (Some { parse = parseNumber });
    init;
    reset = (begin function | () -> () end);
  mark = (begin function | () -> () end);
  unwind = (begin function | () -> () end)
}
let fromExp = fromExp
let toExp = toExp
let normalize = normalizeSum
let compatibleMon = compatibleMon
let number = number
let rec unaryMinus (u_) = toFgn (unaryMinusSum (fromExp (u_, id)))
let rec plus (u_, v_) =
  toFgn (plusSum ((fromExp (u_, id)), (fromExp (v_, id))))
let rec minus (u_, v_) =
  toFgn (minusSum ((fromExp (u_, id)), (fromExp (v_, id))))
let rec times (u_, v_) =
  toFgn (timesSum ((fromExp (u_, id)), (fromExp (v_, id))))
let constant = numberExp end
