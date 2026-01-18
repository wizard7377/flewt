
(* Gaussian-Elimination Equation Solver *)
(* Author: Roberto Virga *)
module type CS_EQ_FIELD  =
  sig
    include CS
    module Field : FIELD
    (*! structure IntSyn : INTSYN !*)
    (* Foreign expressions *)
    type nonrec 'a mset = 'a list
    (* MultiSet                   *)
    type __Sum =
      | Sum of (Field.number * __Mon mset) 
    and __Mon =
      | Mon of (Field.number * (IntSyn.__Exp * IntSyn.__Sub) mset) 
    (* Mon ::= n * __U1[s1] * ...   *)
    val fromExp : IntSyn.eclo -> __Sum
    val toExp : __Sum -> IntSyn.__Exp
    val normalize : __Sum -> __Sum
    val compatibleMon : (__Mon * __Mon) -> bool
    (* Internal expressions constructors *)
    val number : unit -> IntSyn.__Exp
    val unaryMinus : IntSyn.__Exp -> IntSyn.__Exp
    val plus : (IntSyn.__Exp * IntSyn.__Exp) -> IntSyn.__Exp
    val minus : (IntSyn.__Exp * IntSyn.__Exp) -> IntSyn.__Exp
    val times : (IntSyn.__Exp * IntSyn.__Exp) -> IntSyn.__Exp
    val constant : Field.number -> IntSyn.__Exp
  end;;




(* Gaussian-Elimination Equation Solver *)
(* Author: Roberto Virga *)
module CSEqField(CSEqField:sig
                             module Field : FIELD
                             module Whnf : WHNF
                             (*! structure IntSyn : INTSYN !*)
                             (*! sharing Whnf.IntSyn = IntSyn !*)
                             module Unify : UNIFY
                           end) : CS_EQ_FIELD =
  struct
    (*! sharing Unify.IntSyn = IntSyn !*)
    (*! structure CSManager : CS_MANAGER !*)
    (*! sharing CSManager.IntSyn = IntSyn !*)
    (*! structure CSManager = CSManager !*)
    module Field = Field
    (*! structure IntSyn = IntSyn !*)
    type nonrec 'a mset = 'a list
    (* MultiSet                   *)
    type __Sum =
      | Sum of (Field.number * __Mon mset) 
    and __Mon =
      | Mon of (Field.number * (IntSyn.__Exp * IntSyn.__Sub) mset) 
    (* Mon ::= n * __U1[s1] * ...   *)
    (* A monomial (n * __U1[s1] * __U2[s2] * ...) is said to be normal iff
       (a) the coefficient n is different from zero;
       (b) each (Ui,si) is in whnf and not a foreign term corresponding
           to a sum.
     A sum is normal iff all its monomials are normal, and moreover they
     are pairwise distinct.
  *)
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
    let rec unaryMinusExp (__u) =
      Root ((Const (!unaryMinusID)), (App (__u, Nil)))
    let rec plusExp (__u, __v) =
      Root ((Const (!plusID)), (App (__u, (App (__v, Nil)))))
    let rec minusExp (__u, __v) =
      Root ((Const (!minusID)), (App (__u, (App (__v, Nil)))))
    let rec timesExp (__u, __v) =
      Root ((Const (!timesID)), (App (__u, (App (__v, Nil)))))
    let rec numberConDec d =
      ConDec ((toString d), None, 0, Normal, (number ()), Type)
    let rec numberExp d = Root ((FgnConst ((!myID), (numberConDec d))), Nil)
    let rec parseNumber string =
      match fromString string with
      | Some d -> Some (numberConDec d)
      | None -> None
    let rec solveNumber (__g, S, k) = Some (numberExp (fromInt k))
    let rec findMSet eq (x, __l) =
      let rec findMSet' =
        function
        | (tried, nil) -> None
        | (tried, y::__l) ->
            if eq (x, y)
            then Some (y, (tried @ __l))
            else findMSet' ((y :: tried), __l) in
      findMSet' (nil, __l)
    let rec equalMSet eq =
      let rec equalMSet' =
        function
        | (nil, nil) -> true__
        | (x::L1', L2) ->
            (match findMSet eq (x, L2) with
             | Some (y, L2') -> equalMSet' (L1', L2')
             | None -> false__)
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
    let rec toExpEClo = function | (__u, Shift 0) -> __u | __Us -> EClo __Us
    let rec compatibleMon (Mon (_, UsL1), Mon (_, UsL2)) =
      equalMSet (function | (us1, us2) -> sameExpW (us1, us2)) (UsL1, UsL2)
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
           | Some (Mon (n', _), monL') ->
               let n'' = n + n' in
               if n'' = zero
               then Sum (m, monL')
               else Sum (m, ((Mon (n'', UsL)) :: monL'))
           | None -> Sum (m, (mon :: monL)))
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
    let rec unaryMinusSum sum = timesSum ((Sum ((~- one), nil)), sum)
    let rec minusSum (sum1, sum2) = plusSum (sum1, (unaryMinusSum sum2))
    let rec fromExpW =
      function
      | (FgnExp (cs, fe), _) as __Us ->
          if (!) ((=) cs) myID
          then normalizeSum (extractSum fe)
          else Sum (zero, [Mon (one, [__Us])])
      | (Root (FgnConst (cs, conDec), _), _) as __Us ->
          if (!) ((=) cs) myID
          then
            (match fromString (conDecName conDec) with
             | Some m -> Sum (m, nil))
          else Sum (zero, [Mon (one, [__Us])])
      | (Root (Def d, _), _) as __Us -> fromExpW (Whnf.expandDef __Us)
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
    let rec mapSum (f, Sum (m, monL)) =
      Sum (m, (List.map (function | mon -> mapMon (f, mon)) monL))
    let rec mapMon (f, Mon (n, UsL)) =
      Mon
        (n, (List.map (function | __Us -> Whnf.whnf ((f (EClo __Us)), id)) UsL))
    let rec appSum (f, Sum (m, monL)) =
      List.app (function | mon -> appMon (f, mon)) monL
    let rec appMon (f, Mon (n, UsL)) =
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
        | (__g, Mon (n, ((EVar (r, _, _, _) as LHS), s)::[]), sum) ->
            if Whnf.isPatSub s
            then
              let ss = Whnf.invert s in
              let RHS = toFgn (timesSum ((Sum ((~- (inverse n)), nil)), sum)) in
              (if Unify.invertible (__g, (RHS, id), ss, r)
               then Some (__g, LHS, RHS, ss)
               else None)
            else None
        | _ -> None in
      match minusSum (sum2, sum1) with
      | Sum (m, nil) -> if m = zero then Succeed nil else Fail
      | sum ->
          (match findMon invertMon (__g, sum) with
           | Some assignment -> Succeed [Assign assignment]
           | None ->
               let __u = toFgn sum in
               let cnstr = ref (Eqn (__g, __u, (numberExp zero))) in
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
          (match minusSum ((normalizeSum sum), (fromExp (__U2, id))) with
           | Sum (m, nil) -> m = zero
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
            Lam ((Dec (None, (number ()))), (makeLam E (Int.(-) (n, 1)))) in
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
      (:=) numberID installF
        ((ConDec
            (Field.name, None, 0, (Constraint ((!myID), solveNumber)),
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
    (* CSManager.ModeSyn *)
    (* FgnExp representation for this domain *)
    (* constraint solver ID of this module *)
    (* constant ID of the type family constant "number" *)
    (* constant ID's of the object constants defined by this module *)
    (* ~ : number -> number           *)
    (* + : number -> number -> number *)
    (* - : number -> number -> number *)
    (* * : number -> number -> number *)
    (* parseNumber str = Some(conDec) or None

       Invariant:
       If str parses to the number n
       then conDec is the (foreign) constant declaration of n
    *)
    (* solveNumber k = Some(__u)

       Invariant:
       __u is the term obtained applying the foreign constant
       corresponding to the number k to an empty spine
    *)
    (* findMset eq (x, __l) =
         Some (y, __l') if there exists y such that eq (x, y)
                         and __l ~- (y :: __l') (multiset equality)
         None if there is no y in __l such that eq (x, y)
    *)
    (* equalMset eq (__l, __l') = true iff __l ~ __l' (multiset equality) *)
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
       and  sum' = ~-1 * sum
    *)
    (* minusSum (sum1, sum2) = sum3

       Invariant:
       If   sum1 normal
       and  sum2 normal
       then sum3 normal
       and  sum3 = sum1 - sum2
    *)
    (* fromExpW (__u, s) = sum

       Invariant:
       If   __g' |- s : __g    __g |- __u : __v    (__u,s)  in whnf
       then sum is the internal representation of __u[s] as sum of monomials
       and sum is normal
    *)
    (* fromExp (__u, s) = sum

       Invariant:
       If   __g' |- s : __g    __g |- __u : __v
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
    (* init (cs, installFunction) = ()
       Initialize the constraint solver.
       installFunction is used to add its signature symbols.
    *)
    let solver =
      {
        name = (("equality/" ^ Field.name) ^ "s");
        keywords = "arithmetic,equality";
        needs = ["Unify"];
        fgnConst = (Some { parse = parseNumber });
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
    let rec unaryMinus (__u) = toFgn (unaryMinusSum (fromExp (__u, id)))
    let rec plus (__u, __v) =
      toFgn (plusSum ((fromExp (__u, id)), (fromExp (__v, id))))
    let rec minus (__u, __v) =
      toFgn (minusSum ((fromExp (__u, id)), (fromExp (__v, id))))
    let rec times (__u, __v) =
      toFgn (timesSum ((fromExp (__u, id)), (fromExp (__v, id))))
    let constant = numberExp
  end ;;
