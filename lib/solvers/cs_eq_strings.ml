
module CSEqStrings(CSEqStrings:sig module Whnf : WHNF module Unify : UNIFY
                               end) : CS =
  struct
    open IntSyn
    module FX = CSManager.Fixity
    module MS = ModeSyn
    let myID = (ref (-1) : IntSyn.csid ref)
    let stringID = (ref (-1) : IntSyn.cid ref)
    let rec string () = Root ((Const (!stringID)), Nil)
    let concatID = (ref (-1) : IntSyn.cid ref)
    let rec concatExp (__U) (__V) =
      Root ((Const (!concatID)), (App (__U, (App (__V, Nil)))))
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
    let rec solveString (__G) (__S) k = Some (stringExp (Int.toString k))
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
      | Concat ((Exp (__U, Shift 0))::[]) -> __U
      | Concat ((Exp (__Us))::[]) -> EClo __Us
      | Concat ((__A)::AL) ->
          concatExp ((toExp (Concat [__A])), (toExp (Concat AL)))
    let rec catConcat __0__ __1__ =
      match (__0__, __1__) with
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
          else Concat [Exp __Us]
      | (Root (FgnConst (cs, conDec), _), _) as Us ->
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
      | Concat ((__A)::AL) ->
          catConcat ((normalize (Concat [__A])), (normalize (Concat AL)))
    let rec mapConcat f (Concat (AL)) =
      let rec mapConcat' =
        function
        | nil -> nil
        | (Exp (__Us))::AL -> (::) (Exp ((f (EClo __Us)), id)) mapConcat' AL
        | (String str)::AL -> (::) (String str) mapConcat' AL in
      Concat (mapConcat' AL)
    let rec appConcat f (Concat (AL)) =
      let rec appAtom =
        function | Exp (__Us) -> f (EClo __Us) | String _ -> () in
      List.app appAtom AL
    type __Split =
      | Split of (string * string) 
    type __Decomp =
      | Decomp of (string * string list) 
    let rec index str1 str2 =
      let max = (String.size str2) - (String.size str1) in
      let rec index' i =
        if i <= max
        then
          (if String.isPrefix str1 (String.extract (str2, i, None))
           then (::) i index' (i + 1)
           else index' (i + 1))
        else nil in
      index' 0
    let rec split str1 str2 =
      let len = String.size str1 in
      let rec split' i =
        Split
          ((String.extract (str2, 0, (Some i))),
            (String.extract (str2, (i + len), None))) in
      List.map split' (index (str1, str2))
    let rec sameConcat (Concat (AL1)) (Concat (AL2)) =
      let rec sameConcat' __2__ __3__ =
        match (__2__, __3__) with
        | (nil, nil) -> true
        | ((String str1)::AL1, (String str2)::AL2) ->
            (str1 = str2) && (sameConcat' (AL1, AL2))
        | ((Exp (__Us1))::AL1, (Exp (__Us2))::AL2) ->
            (sameExp (__Us1, __Us2)) && (sameConcat' (AL1, AL2))
        | _ -> false in
      sameConcat' (AL1, AL2)
    let rec sameExpW __4__ __5__ =
      match (__4__, __5__) with
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
    let rec sameSpine __6__ __7__ =
      match (__6__, __7__) with
      | ((Nil, s1), (Nil, s2)) -> true
      | ((SClo (__S1, s1'), s1), __Ss2) ->
          sameSpine ((__S1, (comp (s1', s1))), __Ss2)
      | (__Ss1, (SClo (__S2, s2'), s2)) ->
          sameSpine (__Ss1, (__S2, (comp (s2', s2))))
      | ((App (__U1, __S1), s1), (App (__U2, __S2), s2)) ->
          (sameExp ((__U1, s1), (__U2, s2))) &&
            (sameSpine ((__S1, s1), (__S2, s2)))
      | _ -> false
    let rec sameSub __8__ __9__ =
      match (__8__, __9__) with
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
    type __StringUnify =
      | MultAssign of (__Dec __Ctx * __Exp * __Exp * __Sub) list 
      | MultDelay of (__Exp list * __Cnstr ref) 
      | Failure 
    let rec toFgnUnify =
      function
      | MultAssign (__L) ->
          IntSyn.Succeed (List.map (fun (GXUss) -> Assign GXUss) __L)
      | MultDelay (UL, cnstr) ->
          IntSyn.Succeed (List.map (fun (__U) -> Delay (__U, cnstr)) UL)
      | Failure -> Fail
    let rec unifyRigid (__G) (Concat (AL1)) (Concat (AL2)) =
      let rec unifyRigid' __10__ __11__ =
        match (__10__, __11__) with
        | (nil, nil) -> MultAssign nil
        | ((String str1)::AL1, (String str2)::AL2) ->
            if str1 = str2 then unifyRigid' (AL1, AL2) else Failure
        | ((Exp ((EVar (r, _, _, _) as U1), s))::AL1, (Exp
           ((Root (FVar _, _) as U2), _))::AL2) ->
            let ss = Whnf.invert s in
            if Unify.invertible (__G, (__U2, id), ss, r)
            then
              (match unifyRigid' (AL1, AL2) with
               | MultAssign l -> MultAssign ((__G, __U1, __U2, ss) :: l)
               | Failure -> Failure)
            else Failure
        | ((Exp ((Root (FVar _, _) as U1), _))::AL1, (Exp
           ((EVar (r, _, _, _) as U2), s))::AL2) ->
            let ss = Whnf.invert s in
            if Unify.invertible (__G, (__U1, id), ss, r)
            then
              (match unifyRigid' (AL1, AL2) with
               | MultAssign l -> MultAssign ((__G, __U2, __U1, ss) :: l)
               | Failure -> Failure)
            else Failure
        | ((Exp ((Root (FVar _, _), _) as Us1))::AL1, (Exp
           ((Root (FVar _, _), _) as Us2))::AL2) ->
            if sameExpW (__Us1, __Us2)
            then unifyRigid' (AL1, AL2)
            else Failure
        | ((Exp ((EVar (_, _, _, _), _) as Us1))::AL1, (Exp
           ((EVar (_, _, _, _), _) as Us2))::AL2) ->
            if sameExpW (__Us1, __Us2)
            then unifyRigid' (AL1, AL2)
            else Failure
        | _ -> Failure(* FIX: the next two cases are wrong -kw *) in
      unifyRigid' (AL1, AL2)
    let rec unifyString __16__ __17__ __18__ __19__ =
      match (__16__, __17__, __18__, __19__) with
      | (__G, Concat ((String prefix)::AL), str, cnstr) ->
          if String.isPrefix prefix str
          then
            let suffix = String.extract (str, (String.size prefix), None) in
            unifyString (__G, (Concat AL), suffix, cnstr)
          else Failure
      | (__G, Concat (AL), str, cnstr) ->
          let rec unifyString' __14__ __15__ =
            match (__14__, __15__) with
            | (AL, nil) -> (Failure, nil)
            | (nil, (Decomp (parse, parsedL))::[]) ->
                ((MultAssign nil), (parse :: parsedL))
            | (nil, candidates) -> ((MultDelay (nil, cnstr)), nil)
            | ((Exp (__Us1))::(Exp (__Us2))::AL, _) ->
                ((MultDelay ([EClo __Us1; EClo __Us2], cnstr)), nil)
            | ((Exp ((EVar (r, _, _, _) as U), s))::AL, candidates) ->
                if Whnf.isPatSub s
                then
                  let rec assign __12__ __13__ =
                    match (__12__, __13__) with
                    | (r, nil) -> None
                    | (r,
                       (_, EVar (r', _, _, _), Root
                        (FgnConst (cs, conDec), Nil), _)::__L) ->
                        if r = r'
                        then fromString (conDecName conDec)
                        else assign r __L
                    | (r, _::__L) -> assign r __L in
                  (match unifyString' (AL, candidates) with
                   | (MultAssign (__L), parsed::parsedL) ->
                       (match assign r __L with
                        | None ->
                            let ss = Whnf.invert s in
                            let __W = stringExp parsed in
                            ((MultAssign ((__G, __U, __W, ss) :: __L)),
                              parsedL)
                        | Some parsed' ->
                            if parsed = parsed'
                            then ((MultAssign __L), parsedL)
                            else (Failure, nil))
                   | (MultDelay (UL, cnstr), _) ->
                       ((MultDelay (((EClo (__U, s)) :: UL), cnstr)), nil)
                   | (Failure, _) -> (Failure, nil))
                else ((MultDelay ([EClo (__U, s)], cnstr)), nil)
            | ((Exp (__Us))::AL, _) ->
                ((MultDelay ([EClo __Us], cnstr)), nil)
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
                    (fun (Split (prefix, suffix)) ->
                       Decomp (suffix, (prefix :: parsedL)))
                    (split (str, parse)) in
                let candidates' =
                  List.foldr (@) nil (List.map successors candidates) in
                unifyString' (AL, candidates') in
          (match unifyString' (AL, [Decomp (str, nil)]) with
           | (result, nil) -> result
           | (result, ""::[]) -> result
           | (result, parsedL) -> Failure)
    let rec unifyConcat (__G) (Concat (AL1) as concat1)
      (Concat (AL2) as concat2) =
      let __U1 = toFgn concat1 in
      let __U2 = toFgn concat2 in
      let cnstr = ref (Eqn (__G, __U1, __U2)) in
      ((match (AL1, AL2) with
        | (nil, nil) -> MultAssign nil
        | (nil, _) -> Failure
        | (_, nil) -> Failure
        | ((String str1)::[], (String str2)::[]) ->
            if str1 = str2 then MultAssign nil else Failure
        | ((Exp ((EVar (r, _, _, _) as U), s))::[], _) ->
            if Whnf.isPatSub s
            then
              let ss = Whnf.invert s in
              (if Unify.invertible (__G, (__U2, id), ss, r)
               then MultAssign [(__G, __U, __U2, ss)]
               else MultDelay ([__U1; __U2], cnstr))
            else MultDelay ([__U1; __U2], cnstr)
        | (_, (Exp ((EVar (r, _, _, _) as U), s))::[]) ->
            if Whnf.isPatSub s
            then
              let ss = Whnf.invert s in
              (if Unify.invertible (__G, (__U1, id), ss, r)
               then MultAssign [(__G, __U, __U1, ss)]
               else MultDelay ([__U1; __U2], cnstr))
            else MultDelay ([__U1; __U2], cnstr)
        | ((String str)::[], _) -> unifyString (__G, concat2, str, cnstr)
        | (_, (String str)::[]) -> unifyString (__G, concat1, str, cnstr)
        | _ ->
            (match unifyRigid (__G, concat1, concat2) with
             | MultAssign _ as result -> result
             | Failure ->
                 if sameConcat (concat1, concat2)
                 then MultAssign nil
                 else MultDelay ([__U1; __U2], cnstr)))
        (* FIX: the next two cases are wrong -kw *))
    let rec toFgn =
      function
      | Concat ((String str)::[]) as concat -> stringExp str
      | Concat ((Exp (__U, id))::[]) as concat -> __U
      | concat -> FgnExp ((!myID), (MyIntsynRep concat))
    let rec toInternal __20__ __21__ =
      match (__20__, __21__) with
      | (MyIntsynRep concat, ()) -> toExp (normalize concat)
      | (fe, ()) -> raise (UnexpectedFgnExp fe)
    let rec map __22__ __23__ =
      match (__22__, __23__) with
      | (MyIntsynRep concat, f) -> toFgn (normalize (mapConcat (f, concat)))
      | (fe, _) -> raise (UnexpectedFgnExp fe)
    let rec app __24__ __25__ =
      match (__24__, __25__) with
      | (MyIntsynRep concat, f) -> appConcat (f, concat)
      | (fe, _) -> raise (UnexpectedFgnExp fe)
    let rec equalTo __26__ __27__ =
      match (__26__, __27__) with
      | (MyIntsynRep concat, __U2) ->
          sameConcat ((normalize concat), (fromExp (__U2, id)))
      | (fe, _) -> raise (UnexpectedFgnExp fe)
    let rec unifyWith __28__ __29__ __30__ =
      match (__28__, __29__, __30__) with
      | (MyIntsynRep concat, __G, __U2) ->
          toFgnUnify
            (unifyConcat (__G, (normalize concat), (fromExp (__U2, id))))
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
        | n -> App ((Root ((BVar n), Nil)), (makeParams (n - 1))) in
      let rec makeLam __31__ __32__ =
        match (__31__, __32__) with
        | (__E, 0) -> __E
        | (__E, n) -> Lam ((Dec (None, (string ()))), (makeLam __E (n - 1))) in
      let rec expand __33__ __34__ =
        match (__33__, __34__) with
        | ((Nil, s), arity) -> ((makeParams arity), arity)
        | ((App (__U, __S), s), arity) ->
            let (__S', arity') = expand ((__S, s), (arity - 1)) in
            ((App ((EClo (__U, (comp (s, (Shift arity'))))), __S')), arity')
        | ((SClo (__S, s'), s), arity) ->
            expand ((__S, (comp (s, s'))), arity) in
      let (__S', arity') = expand ((__S, id), arity) in
      makeLam (toFgn (opExp __S')) arity'
    let rec makeFgnBinary opConcat =
      makeFgn
        (2,
          (fun (App (__U1, App (__U2, Nil))) ->
             opConcat ((fromExp (__U1, id)), (fromExp (__U2, id)))))
    let rec arrow (__U) (__V) = Pi (((Dec (None, __U)), No), __V)
    let rec init cs installF =
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
    let solver =
      ({
         name = "equality/strings";
         keywords = "strings,equality";
         needs = ["Unify"];
         fgnConst = (Some { parse = parseString });
         init;
         reset = (fun () -> ());
         mark = (fun () -> ());
         unwind = (fun () -> ())
       } : CSManager.solver)
  end ;;
