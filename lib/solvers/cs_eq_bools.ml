
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
    (* Mon ::= __U1[s1] * ...       *)
    (* A monomial (__U1[s1] * __U2[s2] * ...) is said to be normal iff
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
      | (__g, S, 0) -> Some (trueExp ())
      | (__g, S, 1) -> Some (falseExp ())
      | (__g, S, k) -> None
    let notID = (ref (-1) : cid ref)
    let xorID = (ref (-1) : cid ref)
    let andID = (ref (-1) : cid ref)
    let orID = (ref (-1) : cid ref)
    let impliesID = (ref (-1) : cid ref)
    let iffID = (ref (-1) : cid ref)
    let rec notExp (__u) = Root ((Const (!notID)), (App (__u, Nil)))
    let rec xorExp (__u, __v) =
      Root ((Const (!xorID)), (App (__u, (App (__v, Nil)))))
    let rec andExp (__u, __v) =
      Root ((Const (!andID)), (App (__u, (App (__v, Nil)))))
    let rec orExp (__u, __v) = Root ((Const (!orID)), (App (__u, (App (__v, Nil)))))
    let rec impliesExp (__u, __v) =
      Root ((Const (!impliesID)), (App (__u, (App (__v, Nil)))))
    let rec iffExp (__u, __v) =
      Root ((Const (!iffID)), (App (__u, (App (__v, Nil)))))
    let rec member eq (x, __l) = List.exists (function | y -> eq (x, y)) __l
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
      | Mon ((__Us)::[]) -> toExpEClo __Us
      | Mon ((__Us)::UsL) -> andExp ((toExpMon (Mon UsL)), (toExpEClo __Us))
    let rec toExpEClo = function | (__u, Shift 0) -> __u | __Us -> EClo __Us
    let rec compatibleMon (Mon (UsL1), Mon (UsL2)) =
      equalSet (function | (us1, us2) -> sameExp (us1, us2)) (UsL1, UsL2)
    let rec sameExpW =
      function
      | (((Root (H1, S1), s1) as us1), ((Root (H2, S2), s2) as us2)) ->
          (match (H1, H2) with
           | (BVar k1, BVar k2) ->
               (k1 = k2) && (sameSpine ((S1, s1), (S2, s2)))
           | (FVar (n1, _, _), FVar (n2, _, _)) ->
               (n1 = n2) && (sameSpine ((S1, s1), (S2, s2)))
           | _ -> false__)
      | ((((EVar (r1, G1, V1, cnstrs1) as __U1), s1) as us1),
         (((EVar (r2, G2, V2, cnstrs2) as __U2), s2) as us2)) ->
          (r1 = r2) && (sameSub (s1, s2))
      | _ -> false__
    let rec sameExp (us1, us2) = sameExpW ((Whnf.whnf us1), (Whnf.whnf us2))
    let rec sameSpine =
      function
      | ((Nil, s1), (Nil, s2)) -> true__
      | ((SClo (S1, s1'), s1), Ss2) ->
          sameSpine ((S1, (comp (s1', s1))), Ss2)
      | (Ss1, (SClo (S2, s2'), s2)) ->
          sameSpine (Ss1, (S2, (comp (s2', s2))))
      | ((App (__U1, S1), s1), (App (__U2, S2), s2)) ->
          (sameExp ((__U1, s1), (__U2, s2))) && (sameSpine ((S1, s1), (S2, s2)))
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
      | (FgnExp (cs, fe), _) as __Us ->
          if (!) ((=) cs) myID
          then normalizeSum (extractSum fe)
          else Sum (false__, [Mon [__Us]])
      | __Us -> Sum (false__, [Mon [__Us]])
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
      | Mon ((__Us)::UsL) -> andSum ((fromExp __Us), (normalizeMon (Mon UsL)))
    let rec mapSum (f, Sum (m, monL)) =
      Sum (m, (List.map (function | mon -> mapMon (f, mon)) monL))
    let rec mapMon (f, Mon (UsL)) =
      Mon (List.map (function | __Us -> Whnf.whnf ((f (EClo __Us)), id)) UsL)
    let rec appSum (f, Sum (m, monL)) =
      List.app (function | mon -> appMon (f, mon)) monL
    let rec appMon (f, Mon (UsL)) =
      List.app (function | __Us -> f (EClo __Us)) UsL
    let rec findMon f (__g, Sum (m, monL)) =
      let rec findMon' =
        function
        | (nil, monL2) -> None
        | (mon::monL1, monL2) ->
            (match f (__g, mon, (Sum (m, (monL1 @ monL2)))) with
             | Some _ as result -> result
             | None -> findMon' (monL1, (mon :: monL2))) in
      findMon' (monL, nil)
    let rec unifySum (__g, sum1, sum2) =
      let rec invertMon =
        function
        | (__g, Mon (((EVar (r, _, _, _) as LHS), s)::[]), sum) ->
            if Whnf.isPatSub s
            then
              let ss = Whnf.invert s in
              let RHS = toFgn sum in
              (if Unify.invertible (__g, (RHS, id), ss, r)
               then Some (__g, LHS, RHS, ss)
               else None)
            else None
        | _ -> None in
      match xorSum (sum2, sum1) with
      | Sum (false__, nil) -> Succeed nil
      | Sum (true__, nil) -> Fail
      | sum ->
          (match findMon invertMon (__g, sum) with
           | Some assignment -> Succeed [Assign assignment]
           | None ->
               let __u = toFgn sum in
               let cnstr = ref (Eqn (__g, __u, (falseExp ()))) in
               Succeed [Delay (__u, cnstr)])
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
      | (MyIntsynRep sum, __U2) ->
          (match xorSum ((normalizeSum sum), (fromExp (__U2, id))) with
           | Sum (m, nil) -> m = false__
           | _ -> false__)
      | (fe, _) -> raise (UnexpectedFgnExp fe)
    let rec unifyWith arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (MyIntsynRep sum, (__g, __U2)) ->
          unifySum (__g, (normalizeSum sum), (fromExp (__U2, id)))
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
            Lam ((Dec (None, (bool ()))), (makeLam E (Int.(-) (n, 1)))) in
      let rec expand =
        function
        | ((Nil, s), arity) -> ((makeParams arity), arity)
        | ((App (__u, S), s), arity) ->
            let (S', arity') = expand ((S, s), (Int.(-) (arity, 1))) in
            ((App ((EClo (__u, (comp (s, (Shift arity'))))), S')), arity')
        | ((SClo (S, s'), s), arity) -> expand ((S, (comp (s', s))), arity) in
      let (S', arity') = expand ((S, id), arity) in
      makeLam (toFgn (opExp S')) arity'
    let rec makeFgnUnary opSum =
      makeFgn (1, (function | App (__u, Nil) -> opSum (fromExp (__u, id))))
    let rec makeFgnBinary opSum =
      makeFgn
        (2,
          (function
           | App (__U1, App (__U2, Nil)) ->
               opSum ((fromExp (__U1, id)), (fromExp (__U2, id)))))
    let rec arrow (__u, __v) = Pi (((Dec (None, __u)), No), __v)
    let rec init (cs, installF) =
      myID := cs;
      (:=) boolID installF
        ((ConDec
            ("bool", None, 0, (Constraint ((!myID), solveBool)), (Uni Type),
              Kind)), None, [MS.Mnil]);
      (:=) trueID installF
        ((ConDec
            ("true", None, 0,
              (Foreign ((!myID), (function | _ -> toFgn (Sum (true__, nil))))),
              (bool ()), Type)), None, nil);
      (:=) falseID installF
        ((ConDec
            ("false", None, 0,
              (Foreign
                 ((!myID), (function | _ -> toFgn (Sum (false__, nil))))),
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
    (* CSManager.ModeSyn *)
    (* member eq (x, __l) = true iff there there is a y in __l s.t. eq(y, x) *)
    (* differenceSet eq L1 L2 = (L1 \ L2) __u (L2 \ L1) *)
    (* equalSet eq (L1, L2) = true iff L1 is equal to L2 (both seen as sets) *)
    (* unionSet eq (L1, L2) = L1 __u L2 *)
    (* toExp sum = __u

       Invariant:
       If sum is normal
       __g |- __u : __v and __u is the Twelf syntax conversion of sum
    *)
    (* toExpMon mon = __u

       Invariant:
       If mon is normal
       __g |- __u : __v and __u is the Twelf syntax conversion of mon
    *)
    (* toExpEClo (__u,s) = __u

       Invariant:
       __g |- __u : __v and __u is the Twelf syntax conversion of __Us
    *)
    (* compatibleMon (mon1, mon2) = true only if mon1 = mon2 (as monomials) *)
    (* sameExpW ((__U1,s1), (__U2,s2)) = T

       Invariant:
       If   __g |- s1 : G1    G1 |- __U1 : V1    (__U1,s1)  in whnf
       and  __g |- s2 : G2    G2 |- __U2 : V2    (__U2,s2)  in whnf
       then T only if __U1[s1] = __U2[s2] (as expressions)
    *)
    (* sameExp ((__U1,s1), (__U2,s2)) = T

       Invariant:
       If   __g |- s1 : G1    G1 |- __U1 : V1
       and  __g |- s2 : G2    G2 |- __U2 : V2
       then T only if __U1[s1] = __U2[s2] (as expressions)
    *)
    (* sameSpine (S1, S2) = T

       Invariant:
       If   __g |- S1 : __v > W
       and  __g |- S2 : __v > W
       then T only if S1 = S2 (as spines)
    *)
    (* sameSub (s1, s2) = T

       Invariant:
       If   __g |- s1 : __g'
       and  __g |- s2 : __g'
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
    (* fromExpW (__u, s) = sum

       Invariant:
       If   __g' |- s : __g    __g |- __u : __v    (__u,s)  in whnf
       then sum is the internal representation of __u[s] as sum of monomials
       and sum is normal
    *)
    (* normalizeSum sum = sum', where sum' normal and sum' = sum *)
    (* normalizeMon mon = mon', where mon' normal and mon' = mon *)
    (* mapSum (f, m + M1 + ...) = m + mapMon(f,M1) + ... *)
    (* mapMon (f, n * (__U1,s1) + ...) = n * f(__U1,s1) * ... *)
    (* appSum (f, m + M1 + ...) = ()     and appMon (f, Mi) for each i *)
    (* appMon (f, n * (__U1, s1) + ... ) = () and f (Ui[si]) for each i *)
    (* findMon f (__g, sum) =
         Some(x) if f(M) = Some(x) for some monomial M in sum
         None    if f(M) = None for all monomials M in sum
    *)
    (* unifySum (__g, sum1, sum2) = result

       Invariant:
       If   __g |- sum1 : number     sum1 normal
       and  __g |- sum2 : number     sum2 normal
       then result is the outcome (of type FgnUnify) of solving the
       equation sum1 = sum2 by gaussian elimination.
    *)
    (* toFgn sum = __u

       Invariant:
       If sum normal
       then __u is a foreign expression representing sum.
    *)
    (* toInternal (fe) = __u

       Invariant:
       if fe is (MyIntsynRep sum) and sum : normal
       then __u is the Twelf syntax conversion of sum
    *)
    (* map (fe) f = __u'

       Invariant:
       if fe is (MyIntsynRep sum)   sum : normal
       and
         f sum = f (m + mon1 + ... + monN) =
               = m + f (m1 * us1 * ... * UsM) + ...
               = m + (m1 * (f us1) * ... * f (UsM))
               = sum'           sum' : normal
       then
         __u' is a foreign expression representing sum'
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
        fgnConst = None;
        init;
        reset = (function | () -> ());
        mark = (function | () -> ());
        unwind = (function | () -> ())
      }
  end ;;
