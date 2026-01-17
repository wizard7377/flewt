
module CSEqStrings(CSEqStrings:sig
                                 module Whnf : WHNF
                                 module Unify :
                                 ((UNIFY)(* String Equation Solver *)
                                 (* Author: Roberto Virga *)
                                 (*! structure IntSyn : INTSYN !*)
                                 (*! sharing Whnf.IntSyn = IntSyn !*))
                               end) : CS =
  struct
    open IntSyn
    module FX = CSManager.Fixity
    module MS = ModeSyn
    let myID = (ref (-1) : IntSyn.csid ref)
    let stringID = (ref (-1) : IntSyn.cid ref)
    let rec string () = Root ((Const (!stringID)), Nil)
    let concatID = (ref (-1) : IntSyn.cid ref)
    let rec concatExp (U, V) =
      Root ((Const (!concatID)), (App (U, (App (V, Nil)))))
    let rec toString s = ("\"" ^ s) ^ "\""
    let rec stringConDec str =
      ConDec ((toString str), NONE, 0, Normal, (string ()), Type)
    let rec stringExp str =
      Root ((FgnConst ((!myID), (stringConDec str))), Nil)
    let rec fromString string =
      let len = String.size string in
      if
        ((String.sub (string, 0)) = '"') &&
          ((String.sub (string, (len - 1))) = '"')
      then SOME (String.substring (string, 1, (len - 2)))
      else NONE
    let rec parseString string =
      match fromString string with
      | SOME str -> SOME (stringConDec str)
      | NONE -> NONE
    let rec solveString (G, S, k) = SOME (stringExp (Int.toString k))
    type __Concat =
      | Concat of __Atom list 
    and __Atom =
      | String of string 
      | Exp of IntSyn.eclo 
    exception MyIntsynRep of __Concat 
    let rec extractConcat =
      function
      | MyIntsynRep concat -> concat
      | fe -> raise (UnexpectedFgnExp fe)
    let rec toExp =
      function
      | Concat nil -> stringExp ""
      | Concat ((String str)::[]) -> stringExp str
      | Concat ((Exp (U, Shift 0))::[]) -> U
      | Concat ((Exp (Us))::[]) -> EClo Us
      | Concat ((A)::AL) ->
          concatExp ((toExp (Concat [A])), (toExp (Concat AL)))
    let rec catConcat =
      function
      | (Concat nil, concat2) -> concat2
      | (concat1, Concat nil) -> concat1
      | (Concat (AL1), Concat (AL2)) ->
          (match ((List.rev AL1), AL2) with
           | ((String str1)::revAL1', (String str2)::AL2') ->
               Concat ((List.rev revAL1') @ ((String (str1 ^ str2)) :: AL2'))
           | (_, _) -> Concat (AL1 @ AL2))
    let rec fromExpW =
      function
      | (FgnExp (cs, fe), _) as Us ->
          if (!) ((=) cs) myID
          then normalize (extractConcat fe)
          else Concat [Exp Us]
      | (Root (FgnConst (cs, conDec), _), _) as Us ->
          if (!) ((=) cs) myID
          then
            (match fromString (conDecName conDec) with
             | SOME str ->
                 if str = "" then Concat nil else Concat [String str])
          else Concat [Exp Us]
      | Us -> Concat [Exp Us]
    let rec fromExp (Us) = fromExpW (Whnf.whnf Us)
    let rec normalize =
      function
      | Concat nil as concat -> concat
      | Concat ((String str)::[]) as concat -> concat
      | Concat ((Exp (Us))::[]) -> fromExp Us
      | Concat ((A)::AL) ->
          catConcat ((normalize (Concat [A])), (normalize (Concat AL)))
    let rec mapConcat (f, Concat (AL)) =
      let mapConcat' =
        function
        | nil -> nil
        | (Exp (Us))::AL -> (::) (Exp ((f (EClo Us)), id)) mapConcat' AL
        | (String str)::AL -> (::) (String str) mapConcat' AL in
      Concat (mapConcat' AL)
    let rec appConcat (f, Concat (AL)) =
      let appAtom = function | Exp (Us) -> f (EClo Us) | String _ -> () in
      List.app appAtom AL
    type __Split =
      | Split of (string * string) 
    type __Decomp =
      | Decomp of (string * string list) 
    let rec index (str1, str2) =
      let max = (String.size str2) - (String.size str1) in
      let index' i =
        if i <= max
        then
          (if String.isPrefix str1 (String.extract (str2, i, NONE))
           then (::) i index' (i + 1)
           else index' (i + 1))
        else nil in
      index' 0
    let rec split (str1, str2) =
      let len = String.size str1 in
      let split' i =
        Split
          ((String.extract (str2, 0, (SOME i))),
            (String.extract (str2, (i + len), NONE))) in
      List.map split' (index (str1, str2))
    let rec sameConcat (Concat (AL1), Concat (AL2)) =
      let sameConcat' =
        function
        | (nil, nil) -> true__
        | ((String str1)::AL1, (String str2)::AL2) ->
            (str1 = str2) && (sameConcat' (AL1, AL2))
        | ((Exp (Us1))::AL1, (Exp (Us2))::AL2) ->
            (sameExp (Us1, Us2)) && (sameConcat' (AL1, AL2))
        | _ -> false__ in
      sameConcat' (AL1, AL2)
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
    type __StringUnify =
      | MultAssign of (__Dec __Ctx * __Exp * __Exp * __Sub) list 
      | MultDelay of (__Exp list * __Cnstr ref) 
      | Failure 
    let rec toFgnUnify =
      function
      | MultAssign (L) ->
          IntSyn.Succeed (List.map (function | GXUss -> Assign GXUss) L)
      | MultDelay (UL, cnstr) ->
          IntSyn.Succeed (List.map (function | U -> Delay (U, cnstr)) UL)
      | Failure -> Fail
    let rec unifyRigid (G, Concat (AL1), Concat (AL2)) =
      let unifyRigid' =
        function
        | (nil, nil) -> MultAssign nil
        | ((String str1)::AL1, (String str2)::AL2) ->
            if str1 = str2 then unifyRigid' (AL1, AL2) else Failure
        | ((Exp ((EVar (r, _, _, _) as U1), s))::AL1, (Exp
           ((Root (FVar _, _) as U2), _))::AL2) ->
            let ss = Whnf.invert s in
            if Unify.invertible (G, (U2, id), ss, r)
            then
              (match unifyRigid' (AL1, AL2) with
               | MultAssign l -> MultAssign ((G, U1, U2, ss) :: l)
               | Failure -> Failure)
            else Failure
        | ((Exp ((Root (FVar _, _) as U1), _))::AL1, (Exp
           ((EVar (r, _, _, _) as U2), s))::AL2) ->
            let ss = Whnf.invert s in
            if Unify.invertible (G, (U1, id), ss, r)
            then
              (match unifyRigid' (AL1, AL2) with
               | MultAssign l -> MultAssign ((G, U2, U1, ss) :: l)
               | Failure -> Failure)
            else Failure
        | ((Exp ((Root (FVar _, _), _) as Us1))::AL1, (Exp
           ((Root (FVar _, _), _) as Us2))::AL2) ->
            if sameExpW (Us1, Us2) then unifyRigid' (AL1, AL2) else Failure
        | ((Exp ((EVar (_, _, _, _), _) as Us1))::AL1, (Exp
           ((EVar (_, _, _, _), _) as Us2))::AL2) ->
            if sameExpW (Us1, Us2) then unifyRigid' (AL1, AL2) else Failure
        | _ -> Failure in
      unifyRigid' (AL1, AL2)
    let rec unifyString =
      function
      | (G, Concat ((String prefix)::AL), str, cnstr) ->
          if String.isPrefix prefix str
          then
            let suffix = String.extract (str, (String.size prefix), NONE) in
            unifyString (G, (Concat AL), suffix, cnstr)
          else Failure
      | (G, Concat (AL), str, cnstr) ->
          let unifyString' =
            function
            | (AL, nil) -> (Failure, nil)
            | (nil, (Decomp (parse, parsedL))::[]) ->
                ((MultAssign nil), (parse :: parsedL))
            | (nil, candidates) -> ((MultDelay (nil, cnstr)), nil)
            | ((Exp (Us1))::(Exp (Us2))::AL, _) ->
                ((MultDelay ([EClo Us1; EClo Us2], cnstr)), nil)
            | ((Exp ((EVar (r, _, _, _) as U), s))::AL, candidates) ->
                if Whnf.isPatSub s
                then
                  let assign arg__0 arg__1 =
                    match (arg__0, arg__1) with
                    | (r, nil) -> NONE
                    | (r,
                       (_, EVar (r', _, _, _), Root
                        (FgnConst (cs, conDec), Nil), _)::L) ->
                        if r = r'
                        then fromString (conDecName conDec)
                        else assign r L
                    | (r, _::L) -> assign r L in
                  (match unifyString' (AL, candidates) with
                   | (MultAssign (L), parsed::parsedL) ->
                       (match assign r L with
                        | NONE ->
                            let ss = Whnf.invert s in
                            let W = stringExp parsed in
                            ((MultAssign ((G, U, W, ss) :: L)), parsedL)
                        | SOME parsed' ->
                            if parsed = parsed'
                            then ((MultAssign L), parsedL)
                            else (Failure, nil))
                   | (MultDelay (UL, cnstr), _) ->
                       ((MultDelay (((EClo (U, s)) :: UL), cnstr)), nil)
                   | (Failure, _) -> (Failure, nil))
                else ((MultDelay ([EClo (U, s)], cnstr)), nil)
            | ((Exp (Us))::AL, _) -> ((MultDelay ([EClo Us], cnstr)), nil)
            | ((String str)::[], candidates) ->
                let successors (Decomp (parse, parsedL)) =
                  List.mapPartial
                    (function
                     | Split (prefix, "") -> SOME (Decomp (prefix, parsedL))
                     | Split (prefix, suffix) -> NONE) (split (str, parse)) in
                let candidates' =
                  List.foldr (@) nil (List.map successors candidates) in
                unifyString' (nil, candidates')
            | ((String str)::AL, candidates) ->
                let successors (Decomp (parse, parsedL)) =
                  List.map
                    (function
                     | Split (prefix, suffix) ->
                         Decomp (suffix, (prefix :: parsedL)))
                    (split (str, parse)) in
                let candidates' =
                  List.foldr (@) nil (List.map successors candidates) in
                unifyString' (AL, candidates') in
          (match unifyString' (AL, [Decomp (str, nil)]) with
           | (result, nil) -> result
           | (result, ""::[]) -> result
           | (result, parsedL) -> Failure)
    let rec unifyConcat
      (G, (Concat (AL1) as concat1), (Concat (AL2) as concat2)) =
      let U1 = toFgn concat1 in
      let U2 = toFgn concat2 in
      let cnstr = ref (Eqn (G, U1, U2)) in
      match (AL1, AL2) with
      | (nil, nil) -> MultAssign nil
      | (nil, _) -> Failure
      | (_, nil) -> Failure
      | ((String str1)::[], (String str2)::[]) ->
          if str1 = str2 then MultAssign nil else Failure
      | ((Exp ((EVar (r, _, _, _) as U), s))::[], _) ->
          if Whnf.isPatSub s
          then
            let ss = Whnf.invert s in
            (if Unify.invertible (G, (U2, id), ss, r)
             then MultAssign [(G, U, U2, ss)]
             else MultDelay ([U1; U2], cnstr))
          else MultDelay ([U1; U2], cnstr)
      | (_, (Exp ((EVar (r, _, _, _) as U), s))::[]) ->
          if Whnf.isPatSub s
          then
            let ss = Whnf.invert s in
            (if Unify.invertible (G, (U1, id), ss, r)
             then MultAssign [(G, U, U1, ss)]
             else MultDelay ([U1; U2], cnstr))
          else MultDelay ([U1; U2], cnstr)
      | ((String str)::[], _) -> unifyString (G, concat2, str, cnstr)
      | (_, (String str)::[]) -> unifyString (G, concat1, str, cnstr)
      | _ ->
          (match unifyRigid (G, concat1, concat2) with
           | MultAssign _ as result -> result
           | Failure ->
               if sameConcat (concat1, concat2)
               then MultAssign nil
               else MultDelay ([U1; U2], cnstr))
    let rec toFgn =
      function
      | Concat ((String str)::[]) as concat -> stringExp str
      | Concat ((Exp (U, id))::[]) as concat -> U
      | concat -> FgnExp ((!myID), (MyIntsynRep concat))
    let rec toInternal arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (MyIntsynRep concat, ()) -> toExp (normalize concat)
      | (fe, ()) -> raise (UnexpectedFgnExp fe)
    let rec map arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (MyIntsynRep concat, f) -> toFgn (normalize (mapConcat (f, concat)))
      | (fe, _) -> raise (UnexpectedFgnExp fe)
    let rec app arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (MyIntsynRep concat, f) -> appConcat (f, concat)
      | (fe, _) -> raise (UnexpectedFgnExp fe)
    let rec equalTo arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (MyIntsynRep concat, U2) ->
          sameConcat ((normalize concat), (fromExp (U2, id)))
      | (fe, _) -> raise (UnexpectedFgnExp fe)
    let rec unifyWith arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (MyIntsynRep concat, (G, U2)) ->
          toFgnUnify
            (unifyConcat (G, (normalize concat), (fromExp (U2, id))))
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
        | n -> App ((Root ((BVar n), Nil)), (makeParams (n - 1))) in
      let makeLam arg__0 arg__1 =
        match (arg__0, arg__1) with
        | (E, 0) -> E
        | (E, n) -> Lam ((Dec (NONE, (string ()))), (makeLam E (n - 1))) in
      let expand =
        function
        | ((Nil, s), arity) -> ((makeParams arity), arity)
        | ((App (U, S), s), arity) ->
            let (S', arity') = expand ((S, s), (arity - 1)) in
            ((App ((EClo (U, (comp (s, (Shift arity'))))), S')), arity')
        | ((SClo (S, s'), s), arity) -> expand ((S, (comp (s, s'))), arity) in
      let (S', arity') = expand ((S, id), arity) in
      makeLam (toFgn (opExp S')) arity'
    let rec makeFgnBinary opConcat =
      makeFgn
        (2,
          (function
           | App (U1, App (U2, Nil)) ->
               opConcat ((fromExp (U1, id)), (fromExp (U2, id)))))
    let rec arrow (U, V) = Pi (((Dec (NONE, U)), No), V)
    let rec init (cs, installF) =
      myID := cs;
      (:=) stringID installF
        ((ConDec
            ("string", NONE, 0, (Constraint ((!myID), solveString)),
              (Uni Type), Kind)), NONE, [MS.Mnil]);
      (:=) concatID installF
        ((ConDec
            ("++", NONE, 0, (Foreign ((!myID), (makeFgnBinary catConcat))),
              (arrow ((string ()), (arrow ((string ()), (string ()))))),
              Type)), (SOME (FX.Infix (FX.maxPrec, FX.Right))), nil);
      installFgnExpOps ();
      ()
    let ((solver)(*! sharing Unify.IntSyn = IntSyn !*)
      (*! structure CSManager : CS_MANAGER !*)(*! sharing CSManager.IntSyn = IntSyn !*)
      (*! structure CSManager = CSManager !*)(* CSManager.ModeSyn *)
      (* fromString string =
         SOME(str)  if string parses to the string str
         NONE       otherwise
    *)
      (* parseString string = SOME(conDec) or NONE

       Invariant:
       If str parses to the string str
       then conDec is the (foreign) constant declaration of str
    *)
      (* solveString str = SOME(U)

       Invariant:
       U is the term obtained applying the foreign constant
       corresponding to the string str to an empty spine
    *)
      (* Concatenation:             *)(* Concat::= A1 ++ A2 ++ ...  *)
      (* Atoms:                     *)(* Atom ::= "str"             *)
      (*        | (U,s)             *)(* Internal syntax representation of this module *)
      (* A concatenation is said to be normal if
         (a) it does not contain empty string atoms
         (b) it does not contain two consecutive string atoms
    *)
      (* ... and Exp atoms are in whnf?  - ak *)(* toExp concat = U

       Invariant:
       If concat is normal
       G |- U : V and U is the Twelf syntax conversion of concat
    *)
      (* catConcat (concat1, concat2) = concat3

       Invariant:
       If   concat1 normal
       and  concat2 normal
       then concat3 normal
       and  concat3 = concat1 ++ concat2
    *)
      (* fromExpW (U, s) = concat

       Invariant:
       If   G' |- s : G    G |- U : V    (U,s)  in whnf
       then concat is the representation of U[s] as concatenation of atoms
       and  concat is normal
    *)
      (* fromExp (U, s) = concat

       Invariant:
       If   G' |- s : G    G |- U : V
       then concat is the representation of U[s] as concatenation of atoms
       and  concat is normal
    *)
      (* normalize concat = concat', where concat' normal and concat' = concat *)
      (* mapSum (f, A1 + ...) = f(A1) ++ ... *)(* appConcat (f, A1 + ... ) = ()  and f(Ui) for Ai = Exp Ui *)
      (* Split:                                         *)
      (* Split ::= str1 ++ str2                         *)
      (* Decomposition:                                 *)
      (* Decomp ::= toParse | [parsed1, ..., parsedn]   *)
      (* index (str1, str2) = [idx1, ..., idxn]
       where the idxk are all the positions in str2 where str1 appear.
    *)
      (* split (str1, str2) = [Split(l1,r1), ..., Split(ln,rn)]
       where, for each k, str2 = lk ++ str1 ++ rk.
    *)
      (* sameConcat (concat1, concat2) =
         true only if concat1 = concat2 (as concatenations)
    *)
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
      (* Unification Result:
       StringUnify ::= {G1 |- X1 := U1[s1], ..., Gn |- Xn := Un[sn]}
                     | {delay U1 on cnstr1, ..., delay Un on cnstrn}
                     | Failure
    *)
      (* toFgnUnify stringUnify = result
       where result is obtained translating stringUnify.
    *)
      (* unifyRigid (G, concat1, concat2) = stringUnify

       Invariant:
       If   G |- concat1 : string    concat1 normal
       and  G |- concat2 : string    concat2 normal
       then if there is an instantiation I :
               s.t. G |- concat1 <I> == concat2 <I>
            then stringUnify = MultAssign I
            else stringUnify = Failure
    *)
      (* FIX: the next two cases are wrong -kw *)(* unifyString (G, concat, str, cnstr) = stringUnify

       Invariant:
       If   G |- concat : string    concat1 normal
       then if there is an instantiation I :
               s.t. G |- concat <I> == str
            then stringUnify = MultAssign I
            else if there cannot be any possible such instantiation
            then stringUnify = Failure
            else stringUnify = MultDelay [U1, ..., Un] cnstr
                   where U1, ..., Un are expression to be delayed on cnstr
    *)
      (* unifyConcat (G, concat1, concat2) = stringUnify

       Invariant:
       If   G |- concat1 : string    concat1 normal
       and  G |- concat2 : string    concat2 normal
       then if there is an instantiation I :
               s.t. G |- concat1 <I> == concat2 <I>
            then stringUnify = MultAssign I
            else if there cannot be any possible such instantiation
            then stringUnify = Failure
            else stringUnify = MultDelay [U1, ..., Un] cnstr
                   where U1, ..., Un are expression to be delayed on cnstr
    *)
      (* FIX: the next two cases are wrong -kw *)(* toFgn sum = U

       Invariant:
       If sum normal
       then U is a foreign expression representing sum.
    *)
      (* toInternal (fe) = U

       Invariant:
       if fe is (MyIntsynRep concat) and concat : normal
       then U is the Twelf syntax conversion of concat
    *)
      (* map (fe) f = U'

       Invariant:
       if fe is (MyIntsynRep concat)   concat : normal
       and
         f concat = f (A1 ++ ... ++ AN )
                  = f (A1) ++ ... ++ f (AN)
                  = concat'           concat' : normal
       then
         U' is a foreign expression representing concat'
    *)
      (* app (fe) f = ()

       Invariant:
       if fe is (MyIntsynRep concat)     concat : normal
       and
          concat = A1 ++ ... ++ AN
          where some Ai are (Exp Usi)
       then f is applied to each Usi
       (since concat : normal, each Usij is in whnf)
    *)
      (* init (cs, installFunction) = ()
       Initialize the constraint solver.
       installFunction is used to add its signature symbols.
    *))
      =
      ({
         name = "equality/strings";
         keywords = "strings,equality";
         needs = ["Unify"];
         fgnConst = (SOME { parse = parseString });
         init;
         reset = (function | () -> ());
         mark = (function | () -> ());
         unwind = (function | () -> ())
       } : CSManager.solver)
  end ;;
