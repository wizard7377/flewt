module CSEqBools(CSEqBools:sig module Whnf : WHNF module Unify : UNIFY end) :
  CS =
  struct
    type nonrec 'a set = 'a list
    type sum_ =
      | Sum of (bool * mon_ set) 
    and mon_ =
      | Mon of (IntSyn.exp_ * IntSyn.sub_) set 
    open IntSyn
    module FX = CSManager.Fixity
    module MS = ModeSyn
    exception MyIntsynRep of sum_ 
    let rec extractSum =
      begin function
      | MyIntsynRep sum -> sum
      | fe -> raise (UnexpectedFgnExp fe) end
    let myID = (ref (-1) : csid ref)
    let boolID = (ref (-1) : cid ref)
    let rec bool () = Root ((Const !boolID), Nil)
    let trueID = (ref (-1) : cid ref)
    let falseID = (ref (-1) : cid ref)
    let rec trueExp () = Root ((Const !trueID), Nil)
    let rec falseExp () = Root ((Const !falseID), Nil)
    let rec solveBool =
      begin function
      | (g_, s_, 0) -> Some (trueExp ())
      | (g_, s_, 1) -> Some (falseExp ())
      | (g_, s_, k) -> None end
  let notID = (ref (-1) : cid ref)
  let xorID = (ref (-1) : cid ref)
  let andID = (ref (-1) : cid ref)
  let orID = (ref (-1) : cid ref)
  let impliesID = (ref (-1) : cid ref)
  let iffID = (ref (-1) : cid ref)
  let rec notExp (u_) = Root ((Const !notID), (App (u_, Nil)))
  let rec xorExp (u_, v_) =
    Root ((Const !xorID), (App (u_, (App (v_, Nil)))))
  let rec andExp (u_, v_) =
    Root ((Const !andID), (App (u_, (App (v_, Nil)))))
  let rec orExp (u_, v_) = Root ((Const !orID), (App (u_, (App (v_, Nil)))))
  let rec impliesExp (u_, v_) =
    Root ((Const !impliesID), (App (u_, (App (v_, Nil)))))
  let rec iffExp (u_, v_) =
    Root ((Const !iffID), (App (u_, (App (v_, Nil)))))
  let rec member eq (x, l_) =
    List.exists (begin function | y -> eq (x, y) end) l_
let rec differenceSet eq (l1_, l2_) =
  let L1' = List.filter (begin function | x -> not (member eq (x, l2_)) end)
    l1_ in
let L2' = List.filter (begin function | x -> not (member eq (x, l1_)) end)
  l2_ in
L1' @ L2'
let rec equalSet eq (l1_, l2_) =
  begin match differenceSet eq (l1_, l2_) with | [] -> true | _::_ -> false end
let rec unionSet eq (l1_, l2_) =
  let L2' = List.filter (begin function | x -> not (member eq (x, l1_)) end)
    l2_ in
l1_ @ L2'
let rec toExp =
  begin function
  | Sum (m, []) ->
      let cid = if m then begin !trueID end else begin !falseID end in
Root ((Const cid), Nil)
  | Sum (m, mon::[]) -> if m = false then begin toExpMon mon end
      else begin xorExp ((toExp (Sum (m, []))), (toExpMon mon)) end
| Sum (m, (mon::monL as monLL)) ->
    xorExp ((toExp (Sum (m, monL))), (toExpMon mon)) end
let rec toExpMon =
  begin function
  | Mon ((us_)::[]) -> toExpEClo us_
  | Mon ((us_)::UsL) -> andExp ((toExpMon (Mon UsL)), (toExpEClo us_)) end
let rec toExpEClo =
  begin function | (u_, Shift 0) -> u_ | us_ -> EClo us_ end
let rec compatibleMon (Mon (UsL1), Mon (UsL2)) =
  equalSet (begin function | (us1_, us2_) -> sameExp (us1_, us2_) end)
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
  | _ -> false end
let rec xorSum (Sum (m1, monL1), Sum (m2, monL2)) =
  Sum ((not (m1 = m2)), (differenceSet compatibleMon (monL1, monL2)))
let rec andSum =
  begin function
  | ((Sum (false, []) as sum1), sum2) -> sum1
  | (sum1, (Sum (false, []) as sum2)) -> sum2
  | ((Sum (true, []) as sum1), sum2) -> sum2
  | (sum1, (Sum (true, []) as sum2)) -> sum1
  | (Sum (m1, mon1::monL1), sum2) ->
      xorSum ((andSumMon (sum2, mon1)), (andSum ((Sum (m1, monL1)), sum2))) end
let rec andSumMon =
  begin function
  | (Sum (true, []), mon) -> Sum (false, [mon])
  | ((Sum (false, []) as sum1), mon) -> sum1
  | (Sum (m1, (Mon (UsL1))::monL1), (Mon (UsL2) as mon2)) ->
      let UsL = unionSet sameExp (UsL1, UsL2) in
      xorSum
        ((Sum (false, [Mon UsL])), (andSumMon ((Sum (m1, monL1)), mon2))) end
let rec notSum (Sum (m, monL)) = Sum ((not m), monL)
let rec orSum (sum1, sum2) =
  xorSum (sum1, (xorSum (sum2, (andSum (sum1, sum2)))))
let rec impliesSum (sum1, sum2) =
  notSum (xorSum (sum1, (andSum (sum1, sum2))))
let rec iffSum (sum1, sum2) = notSum (xorSum (sum1, sum2))
let rec fromExpW =
  begin function
  | (FgnExp (cs, fe), _) as us_ ->
      if (!) ((=) cs) myID then begin normalizeSum (extractSum fe) end
      else begin Sum (false, [Mon [us_]]) end
  | us_ -> Sum (false, [Mon [us_]]) end
let rec fromExp (us_) = fromExpW (Whnf.whnf us_)
let rec normalizeSum =
  begin function
  | Sum (m, []) as sum -> sum
  | Sum (m, mon::[]) -> xorSum ((Sum (m, [])), (normalizeMon mon))
  | Sum (m, mon::monL) ->
      xorSum ((normalizeMon mon), (normalizeSum (Sum (m, monL)))) end
let rec normalizeMon =
  begin function
  | Mon ((us_)::[]) -> fromExp us_
  | Mon ((us_)::UsL) -> andSum ((fromExp us_), (normalizeMon (Mon UsL))) end
let rec mapSum (f, Sum (m, monL)) =
  Sum (m, (List.map (begin function | mon -> mapMon (f, mon) end) monL))
let rec mapMon (f, Mon (UsL)) =
  Mon (List.map (begin function | us_ -> Whnf.whnf ((f (EClo us_)), id) end)
    UsL)
let rec appSum (f, Sum (m, monL)) =
  List.app (begin function | mon -> appMon (f, mon) end) monL
let rec appMon (f, Mon (UsL)) =
  List.app (begin function | us_ -> f (EClo us_) end) UsL
let rec findMon f (g_, Sum (m, monL)) =
  let rec findMon' =
    begin function
    | ([], monL2) -> None
    | (mon::monL1, monL2) ->
        (begin match f (g_, mon, (Sum (m, (monL1 @ monL2)))) with
         | Some _ as result -> result
         | None -> findMon' (monL1, (mon :: monL2)) end) end in
findMon' (monL, [])
let rec unifySum (g_, sum1, sum2) =
  let rec invertMon =
    begin function
    | (g_, Mon (((EVar (r, _, _, _) as LHS), s)::[]), sum) ->
        if Whnf.isPatSub s
        then
          begin let ss = Whnf.invert s in
                let RHS = toFgn sum in
                (if Unify.invertible (g_, (RHS, id), ss, r)
                 then begin Some (g_, LHS, RHS, ss) end else begin None end) end
    else begin None end
  | _ -> None end in
begin match xorSum (sum2, sum1) with
| Sum (false, []) -> Succeed []
| Sum (true, []) -> Fail
| sum ->
  (begin match findMon invertMon (g_, sum) with
   | Some assignment -> Succeed [Assign assignment]
   | None ->
       let u_ = toFgn sum in
       let cnstr = ref (Eqn (g_, u_, (falseExp ()))) in
       Succeed [Delay (u_, cnstr)] end) end
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
      (((begin match xorSum ((normalizeSum sum), (fromExp (u2_, id))) with
         | Sum (m, []) -> m = false
         | _ -> false end))
  (* AK: redundant normalizeSum ? *))
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
  | (e_, n) -> Lam ((Dec (None, (bool ()))), (makeLam e_ (Int.(-) (n, 1)))) end in
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
  (:=) boolID installF
    ((ConDec
        ("bool", None, 0, (Constraint (!myID, solveBool)), (Uni Type), Kind)),
      None, [MS.Mnil]);
  (:=) trueID installF
    ((ConDec
        ("true", None, 0,
          (Foreign
             (!myID, (begin function | _ -> toFgn (Sum (true, [])) end))),
        (bool ()), Type)),
    None, []);
  (:=) falseID installF
    ((ConDec
        ("false", None, 0,
          (Foreign
             (!myID, (begin function | _ -> toFgn (Sum (false, [])) end))),
        (bool ()), Type)),
    None, []);
  (:=) notID installF
    ((ConDec
        ("!", None, 0, (Foreign (!myID, (makeFgnUnary notSum))),
          (arrow ((bool ()), (bool ()))), Type)),
      (Some (FX.Prefix FX.maxPrec)), []);
  (:=) xorID installF
    ((ConDec
        ("||", None, 0, (Foreign (!myID, (makeFgnBinary xorSum))),
          (arrow ((bool ()), (arrow ((bool ()), (bool ()))))), Type)),
      (Some (FX.Infix ((FX.dec FX.maxPrec), FX.Left))), []);
  (:=) andID installF
    ((ConDec
        ("&", None, 0, (Foreign (!myID, (makeFgnBinary andSum))),
          (arrow ((bool ()), (arrow ((bool ()), (bool ()))))), Type)),
      (Some (FX.Infix ((FX.dec FX.maxPrec), FX.Left))), []);
  (:=) orID installF
    ((ConDec
        ("|", None, 0, (Foreign (!myID, (makeFgnBinary orSum))),
          (arrow ((bool ()), (arrow ((bool ()), (bool ()))))), Type)),
      (Some (FX.Infix ((FX.dec FX.maxPrec), FX.Left))), []);
  (:=) impliesID installF
    ((ConDec
        ("=>", None, 0, (Foreign (!myID, (makeFgnBinary impliesSum))),
          (arrow ((bool ()), (arrow ((bool ()), (bool ()))))), Type)),
      (Some (FX.Infix ((FX.dec (FX.dec FX.maxPrec)), FX.Left))), []);
  (:=) iffID installF
    ((ConDec
        ("<=>", None, 0, (Foreign (!myID, (makeFgnBinary iffSum))),
          (arrow ((bool ()), (arrow ((bool ()), (bool ()))))), Type)),
      (Some (FX.Infix ((FX.dec (FX.dec FX.maxPrec)), FX.Left))), []);
  installFgnExpOps (); () end
let solver =
  {
    name = "equality/booleans";
    keywords = "booleans,equality";
    needs = ["Unify"];
    fgnConst = None;
    init;
    reset = (begin function | () -> () end);
  mark = (begin function | () -> () end);
  unwind = (begin function | () -> () end) } end
