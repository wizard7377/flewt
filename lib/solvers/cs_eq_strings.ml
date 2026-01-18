
(* String Equation Solver *)
(* Author: Roberto Virga *)
module CSEqStrings(CSEqStrings:sig
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
    open IntSyn
    module FX = CSManager.Fixity
    module MS = ModeSyn
    let myID = (ref (-1) : IntSyn.csid ref)
    let stringID = (ref (-1) : IntSyn.cid ref)
    let rec string () = Root ((Const (!stringID)), Nil)
    let concatID = (ref (-1) : IntSyn.cid ref)
    let rec concatExp (__u, __v) =
      Root ((Const (!concatID)), (App (__u, (App (__v, Nil)))))
    let rec toString s = ("\"" ^ s) ^ "\""
    let rec stringConDec str =
      ConDec ((toString str), None, 0, Normal, (string ()), Type)
    let rec stringExp str =
      Root ((FgnConst ((!myID), (stringConDec str))), Nil)
    let rec fromString string =
      let len = String.size string in
      if
        ((String.sub (string, 0)) = '"') &&
          ((String.sub (string, (len - 1))) = '"')
      then Some (String.substring (string, 1, (len - 2)))
      else None
    let rec parseString string =
      match fromString string with
      | Some str -> Some (stringConDec str)
      | None -> None
    let rec solveString (__g, S, k) = Some (stringExp (Int.toString k))
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
      | Concat ((Exp (__u, Shift 0))::[]) -> __u
      | Concat ((Exp (__Us))::[]) -> EClo __Us
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
      | (FgnExp (cs, fe), _) as __Us ->
          if (!) ((=) cs) myID
          then normalize (extractConcat fe)
          else Concat [Exp __Us]
      | (Root (FgnConst (cs, conDec), _), _) as __Us ->
          if (!) ((=) cs) myID
          then
            (match fromString (conDecName conDec) with
             | Some str ->
                 if str = "" then Concat nil else Concat [String str])
          else Concat [Exp __Us]
      | __Us -> Concat [Exp __Us]
    let rec fromExp (__Us) = fromExpW (Whnf.whnf __Us)
    let rec normalize =
      function
      | Concat nil as concat -> concat
      | Concat ((String str)::[]) as concat -> concat
      | Concat ((Exp (__Us))::[]) -> fromExp __Us
      | Concat ((A)::AL) ->
          catConcat ((normalize (Concat [A])), (normalize (Concat AL)))
    let rec mapConcat (f, Concat (AL)) =
      let rec mapConcat' =
        function
        | nil -> nil
        | (Exp (__Us))::AL -> (::) (Exp ((f (EClo __Us)), id)) mapConcat' AL
        | (String str)::AL -> (::) (String str) mapConcat' AL in
      Concat (mapConcat' AL)
    let rec appConcat (f, Concat (AL)) =
      let rec appAtom = function | Exp (__Us) -> f (EClo __Us) | String _ -> () in
      List.app appAtom AL
    type __Split =
      | Split of (string * string) 
    type __Decomp =
      | Decomp of (string * string list) 
    let rec index (str1, str2) =
      let max = (String.size str2) - (String.size str1) in
      let rec index' i =
        if i <= max
        then
          (if String.isPrefix str1 (String.extract (str2, i, None))
           then (::) i index' (i + 1)
           else index' (i + 1))
        else nil in
      index' 0
    let rec split (str1, str2) =
      let len = String.size str1 in
      let rec split' i =
        Split
          ((String.extract (str2, 0, (Some i))),
            (String.extract (str2, (i + len), None))) in
      List.map split' (index (str1, str2))
    let rec sameConcat (Concat (AL1), Concat (AL2)) =
      let rec sameConcat' =
        function
        | (nil, nil) -> true__
        | ((String str1)::AL1, (String str2)::AL2) ->
            (str1 = str2) && (sameConcat' (AL1, AL2))
        | ((Exp (us1))::AL1, (Exp (us2))::AL2) ->
            (sameExp (us1, us2)) && (sameConcat' (AL1, AL2))
        | _ -> false__ in
      sameConcat' (AL1, AL2)
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
    type __StringUnify =
      | MultAssign of (__Dec __Ctx * __Exp * __Exp * __Sub) list 
      | MultDelay of (__Exp list * __Cnstr ref) 
      | Failure 
    let rec toFgnUnify =
      function
      | MultAssign (__l) ->
          IntSyn.Succeed (List.map (function | GXUss -> Assign GXUss) __l)
      | MultDelay (UL, cnstr) ->
          IntSyn.Succeed (List.map (function | __u -> Delay (__u, cnstr)) UL)
      | Failure -> Fail
    let rec unifyRigid (__g, Concat (AL1), Concat (AL2)) =
      let rec unifyRigid' =
        function
        | (nil, nil) -> MultAssign nil
        | ((String str1)::AL1, (String str2)::AL2) ->
            if str1 = str2 then unifyRigid' (AL1, AL2) else Failure
        | ((Exp ((EVar (r, _, _, _) as __U1), s))::AL1, (Exp
           ((Root (FVar _, _) as __U2), _))::AL2) ->
            let ss = Whnf.invert s in
            if Unify.invertible (__g, (__U2, id), ss, r)
            then
              (match unifyRigid' (AL1, AL2) with
               | MultAssign l -> MultAssign ((__g, __U1, __U2, ss) :: l)
               | Failure -> Failure)
            else Failure
        | ((Exp ((Root (FVar _, _) as __U1), _))::AL1, (Exp
           ((EVar (r, _, _, _) as __U2), s))::AL2) ->
            let ss = Whnf.invert s in
            if Unify.invertible (__g, (__U1, id), ss, r)
            then
              (match unifyRigid' (AL1, AL2) with
               | MultAssign l -> MultAssign ((__g, __U2, __U1, ss) :: l)
               | Failure -> Failure)
            else Failure
        | ((Exp ((Root (FVar _, _), _) as us1))::AL1, (Exp
           ((Root (FVar _, _), _) as us2))::AL2) ->
            if sameExpW (us1, us2) then unifyRigid' (AL1, AL2) else Failure
        | ((Exp ((EVar (_, _, _, _), _) as us1))::AL1, (Exp
           ((EVar (_, _, _, _), _) as us2))::AL2) ->
            if sameExpW (us1, us2) then unifyRigid' (AL1, AL2) else Failure
        | _ -> Failure in
      unifyRigid' (AL1, AL2)
    let rec unifyString =
      function
      | (__g, Concat ((String prefix)::AL), str, cnstr) ->
          if String.isPrefix prefix str
          then
            let suffix = String.extract (str, (String.size prefix), None) in
            unifyString (__g, (Concat AL), suffix, cnstr)
          else Failure
      | (__g, Concat (AL), str, cnstr) ->
          let rec unifyString' =
            function
            | (AL, nil) -> (Failure, nil)
            | (nil, (Decomp (parse, parsedL))::[]) ->
                ((MultAssign nil), (parse :: parsedL))
            | (nil, candidates) -> ((MultDelay (nil, cnstr)), nil)
            | ((Exp (us1))::(Exp (us2))::AL, _) ->
                ((MultDelay ([EClo us1; EClo us2], cnstr)), nil)
            | ((Exp ((EVar (r, _, _, _) as __u), s))::AL, candidates) ->
                if Whnf.isPatSub s
                then
                  let rec assign arg__0 arg__1 =
                    match (arg__0, arg__1) with
                    | (r, nil) -> None
                    | (r,
                       (_, EVar (r', _, _, _), Root
                        (FgnConst (cs, conDec), Nil), _)::__l) ->
                        if r = r'
                        then fromString (conDecName conDec)
                        else assign r __l
                    | (r, _::__l) -> assign r __l in
                  (match unifyString' (AL, candidates) with
                   | (MultAssign (__l), parsed::parsedL) ->
                       (match assign r __l with
                        | None ->
                            let ss = Whnf.invert s in
                            let W = stringExp parsed in
                            ((MultAssign ((__g, __u, W, ss) :: __l)), parsedL)
                        | Some parsed' ->
                            if parsed = parsed'
                            then ((MultAssign __l), parsedL)
                            else (Failure, nil))
                   | (MultDelay (UL, cnstr), _) ->
                       ((MultDelay (((EClo (__u, s)) :: UL), cnstr)), nil)
                   | (Failure, _) -> (Failure, nil))
                else ((MultDelay ([EClo (__u, s)], cnstr)), nil)
            | ((Exp (__Us))::AL, _) -> ((MultDelay ([EClo __Us], cnstr)), nil)
            | ((String str)::[], candidates) ->
                let rec successors (Decomp (parse, parsedL)) =
                  List.mapPartial
                    (function
                     | Split (prefix, "") -> Some (Decomp (prefix, parsedL))
                     | Split (prefix, suffix) -> None) (split (str, parse)) in
                let candidates' =
                  List.foldr (@) nil (List.map successors candidates) in
                unifyString' (nil, candidates')
            | ((String str)::AL, candidates) ->
                let rec successors (Decomp (parse, parsedL)) =
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
      (__g, (Concat (AL1) as concat1), (Concat (AL2) as concat2)) =
      let __U1 = toFgn concat1 in
      let __U2 = toFgn concat2 in
      let cnstr = ref (Eqn (__g, __U1, __U2)) in
      match (AL1, AL2) with
      | (nil, nil) -> MultAssign nil
      | (nil, _) -> Failure
      | (_, nil) -> Failure
      | ((String str1)::[], (String str2)::[]) ->
          if str1 = str2 then MultAssign nil else Failure
      | ((Exp ((EVar (r, _, _, _) as __u), s))::[], _) ->
          if Whnf.isPatSub s
          then
            let ss = Whnf.invert s in
            (if Unify.invertible (__g, (__U2, id), ss, r)
             then MultAssign [(__g, __u, __U2, ss)]
             else MultDelay ([__U1; __U2], cnstr))
          else MultDelay ([__U1; __U2], cnstr)
      | (_, (Exp ((EVar (r, _, _, _) as __u), s))::[]) ->
          if Whnf.isPatSub s
          then
            let ss = Whnf.invert s in
            (if Unify.invertible (__g, (__U1, id), ss, r)
             then MultAssign [(__g, __u, __U1, ss)]
             else MultDelay ([__U1; __U2], cnstr))
          else MultDelay ([__U1; __U2], cnstr)
      | ((String str)::[], _) -> unifyString (__g, concat2, str, cnstr)
      | (_, (String str)::[]) -> unifyString (__g, concat1, str, cnstr)
      | _ ->
          (match unifyRigid (__g, concat1, concat2) with
           | MultAssign _ as result -> result
           | Failure ->
               if sameConcat (concat1, concat2)
               then MultAssign nil
               else MultDelay ([__U1; __U2], cnstr))
    let rec toFgn =
      function
      | Concat ((String str)::[]) as concat -> stringExp str
      | Concat ((Exp (__u, id))::[]) as concat -> __u
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
      | (MyIntsynRep concat, __U2) ->
          sameConcat ((normalize concat), (fromExp (__U2, id)))
      | (fe, _) -> raise (UnexpectedFgnExp fe)
    let rec unifyWith arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (MyIntsynRep concat, (__g, __U2)) ->
          toFgnUnify
            (unifyConcat (__g, (normalize concat), (fromExp (__U2, id))))
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
        | n -> App ((Root ((BVar n), Nil)), (makeParams (n - 1))) in
      let rec makeLam arg__0 arg__1 =
        match (arg__0, arg__1) with
        | (E, 0) -> E
        | (E, n) -> Lam ((Dec (None, (string ()))), (makeLam E (n - 1))) in
      let rec expand =
        function
        | ((Nil, s), arity) -> ((makeParams arity), arity)
        | ((App (__u, S), s), arity) ->
            let (S', arity') = expand ((S, s), (arity - 1)) in
            ((App ((EClo (__u, (comp (s, (Shift arity'))))), S')), arity')
        | ((SClo (S, s'), s), arity) -> expand ((S, (comp (s, s'))), arity) in
      let (S', arity') = expand ((S, id), arity) in
      makeLam (toFgn (opExp S')) arity'
    let rec makeFgnBinary opConcat =
      makeFgn
        (2,
          (function
           | App (__U1, App (__U2, Nil)) ->
               opConcat ((fromExp (__U1, id)), (fromExp (__U2, id)))))
    let rec arrow (__u, __v) = Pi (((Dec (None, __u)), No), __v)
    let rec init (cs, installF) =
      myID := cs;
      (:=) stringID installF
        ((ConDec
            ("string", None, 0, (Constraint ((!myID), solveString)),
              (Uni Type), Kind)), None, [MS.Mnil]);
      (:=) concatID installF
        ((ConDec
            ("++", None, 0, (Foreign ((!myID), (makeFgnBinary catConcat))),
              (arrow ((string ()), (arrow ((string ()), (string ()))))),
              Type)), (Some (FX.Infix (FX.maxPrec, FX.Right))), nil);
      installFgnExpOps ();
      ()
    (* CSManager.ModeSyn *)
    (* fromString string =
         Some(str)  if string parses to the string str
         None       otherwise
    *)
    (* parseString string = Some(conDec) or None

       Invariant:
       If str parses to the string str
       then conDec is the (foreign) constant declaration of str
    *)
    (* solveString str = Some(__u)

       Invariant:
       __u is the term obtained applying the foreign constant
       corresponding to the string str to an empty spine
    *)
    (* Concatenation:             *)
    (* Concat::= A1 ++ A2 ++ ...  *)
    (* Atoms:                     *)
    (* Atom ::= "str"             *)
    (*        | (__u,s)             *)
    (* Internal syntax representation of this module *)
    (* A concatenation is said to be normal if
         (a) it does not contain empty string atoms
         (b) it does not contain two consecutive string atoms
    *)
    (* ... and Exp atoms are in whnf?  - ak *)
    (* toExp concat = __u

       Invariant:
       If concat is normal
       __g |- __u : __v and __u is the Twelf syntax conversion of concat
    *)
    (* catConcat (concat1, concat2) = concat3

       Invariant:
       If   concat1 normal
       and  concat2 normal
       then concat3 normal
       and  concat3 = concat1 ++ concat2
    *)
    (* fromExpW (__u, s) = concat

       Invariant:
       If   __g' |- s : __g    __g |- __u : __v    (__u,s)  in whnf
       then concat is the representation of __u[s] as concatenation of atoms
       and  concat is normal
    *)
    (* fromExp (__u, s) = concat

       Invariant:
       If   __g' |- s : __g    __g |- __u : __v
       then concat is the representation of __u[s] as concatenation of atoms
       and  concat is normal
    *)
    (* normalize concat = concat', where concat' normal and concat' = concat *)
    (* mapSum (f, A1 + ...) = f(A1) ++ ... *)
    (* appConcat (f, A1 + ... ) = ()  and f(Ui) for Ai = Exp Ui *)
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
    (* Unification Result:
       StringUnify ::= {G1 |- X1 := __U1[s1], ..., Gn |- Xn := Un[sn]}
                     | {delay __U1 on cnstr1, ..., delay Un on cnstrn}
                     | Failure
    *)
    (* toFgnUnify stringUnify = result
       where result is obtained translating stringUnify.
    *)
    (* unifyRigid (__g, concat1, concat2) = stringUnify

       Invariant:
       If   __g |- concat1 : string    concat1 normal
       and  __g |- concat2 : string    concat2 normal
       then if there is an instantiation I :
               s.t. __g |- concat1 <I> == concat2 <I>
            then stringUnify = MultAssign I
            else stringUnify = Failure
    *)
    (* FIX: the next two cases are wrong -kw *)
    (* unifyString (__g, concat, str, cnstr) = stringUnify

       Invariant:
       If   __g |- concat : string    concat1 normal
       then if there is an instantiation I :
               s.t. __g |- concat <I> == str
            then stringUnify = MultAssign I
            else if there cannot be any possible such instantiation
            then stringUnify = Failure
            else stringUnify = MultDelay [__U1, ..., Un] cnstr
                   where __U1, ..., Un are expression to be delayed on cnstr
    *)
    (* unifyConcat (__g, concat1, concat2) = stringUnify

       Invariant:
       If   __g |- concat1 : string    concat1 normal
       and  __g |- concat2 : string    concat2 normal
       then if there is an instantiation I :
               s.t. __g |- concat1 <I> == concat2 <I>
            then stringUnify = MultAssign I
            else if there cannot be any possible such instantiation
            then stringUnify = Failure
            else stringUnify = MultDelay [__U1, ..., Un] cnstr
                   where __U1, ..., Un are expression to be delayed on cnstr
    *)
    (* FIX: the next two cases are wrong -kw *)
    (* toFgn sum = __u

       Invariant:
       If sum normal
       then __u is a foreign expression representing sum.
    *)
    (* toInternal (fe) = __u

       Invariant:
       if fe is (MyIntsynRep concat) and concat : normal
       then __u is the Twelf syntax conversion of concat
    *)
    (* map (fe) f = __u'

       Invariant:
       if fe is (MyIntsynRep concat)   concat : normal
       and
         f concat = f (A1 ++ ... ++ AN )
                  = f (A1) ++ ... ++ f (AN)
                  = concat'           concat' : normal
       then
         __u' is a foreign expression representing concat'
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
    *)
    let solver =
      ({
         name = "equality/strings";
         keywords = "strings,equality";
         needs = ["Unify"];
         fgnConst = (Some { parse = parseString });
         init;
         reset = (function | () -> ());
         mark = (function | () -> ());
         unwind = (function | () -> ())
       } : CSManager.solver)
  end ;;
