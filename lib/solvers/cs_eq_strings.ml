module CSEqStrings(CSEqStrings:sig module Whnf : WHNF module Unify : UNIFY
                               end) : CS =
  struct
    open IntSyn
    module FX = CSManager.Fixity
    module MS = ModeSyn
    let myID = (ref (-1) : IntSyn.csid ref)
    let stringID = (ref (-1) : IntSyn.cid ref)
    let rec string () = Root ((Const !stringID), Nil)
    let concatID = (ref (-1) : IntSyn.cid ref)
    let rec concatExp (u_, v_) =
      Root ((Const !concatID), (App (u_, (App (v_, Nil)))))
    let rec toString s = ("\"" ^ s) ^ "\""
    let rec stringConDec str =
      ConDec ((toString str), None, 0, Normal, (string ()), Type)
    let rec stringExp str =
      Root ((FgnConst (!myID, (stringConDec str))), Nil)
    let rec fromString string =
      let len = String.size string in
      if
        ((String.sub (string, 0)) = '"') &&
          ((String.sub (string, (len - 1))) = '"')
      then begin Some (String.substring (string, 1, (len - 2))) end
        else begin None end
  let rec parseString string =
    begin match fromString string with
    | Some str -> Some (stringConDec str)
    | None -> None end
let rec solveString (g_, s_, k) = Some (stringExp (Int.toString k))
type concat_ =
  | Concat of atom_ list 
and atom_ =
  | String of string 
  | Exp of IntSyn.eclo 
exception MyIntsynRep of concat_ 
let rec extractConcat =
  begin function
  | MyIntsynRep concat -> concat
  | fe -> raise (UnexpectedFgnExp fe) end
let rec toExp =
  begin function
  | Concat [] -> stringExp ""
  | Concat ((String str)::[]) -> stringExp str
  | Concat ((Exp (u_, Shift 0))::[]) -> u_
  | Concat ((Exp (us_))::[]) -> EClo us_
  | Concat ((a_)::AL) ->
      concatExp ((toExp (Concat [a_])), (toExp (Concat AL))) end
let rec catConcat =
  begin function
  | (Concat [], concat2) -> concat2
  | (concat1, Concat []) -> concat1
  | (Concat (AL1), Concat (AL2)) ->
      (begin match ((List.rev AL1), AL2) with
       | ((String str1)::revAL1', (String str2)::AL2') ->
           Concat ((List.rev revAL1') @ ((String (str1 ^ str2)) :: AL2'))
       | (_, _) -> Concat (AL1 @ AL2) end) end
let rec fromExpW =
  begin function
  | (FgnExp (cs, fe), _) as us_ ->
      if (!) ((=) cs) myID then begin normalize (extractConcat fe) end
      else begin Concat [Exp us_] end
  | (Root (FgnConst (cs, conDec), _), _) as us_ ->
      if (!) ((=) cs) myID
      then
        begin (begin match fromString (conDecName conDec) with
               | Some str -> if str = "" then begin Concat [] end
                   else begin Concat [String str] end end) end
else begin Concat [Exp us_] end
| us_ -> Concat [Exp us_] end
let rec fromExp (us_) = fromExpW (Whnf.whnf us_)
let rec normalize =
  begin function
  | Concat [] as concat -> concat
  | Concat ((String str)::[]) as concat -> concat
  | Concat ((Exp (us_))::[]) -> fromExp us_
  | Concat ((a_)::AL) ->
      catConcat ((normalize (Concat [a_])), (normalize (Concat AL))) end
let rec mapConcat (f, Concat (AL)) =
  let rec mapConcat' =
    begin function
    | [] -> []
    | (Exp (us_))::AL -> (::) (Exp ((f (EClo us_)), id)) mapConcat' AL
    | (String str)::AL -> (::) (String str) mapConcat' AL end in
Concat (mapConcat' AL)
let rec appConcat (f, Concat (AL)) =
  let rec appAtom =
    begin function | Exp (us_) -> f (EClo us_) | String _ -> () end in
List.app appAtom AL
type split_ =
  | Split of (string * string) 
type decomp_ =
  | Decomp of (string * string list) 
let rec index (str1, str2) =
  let max = (String.size str2) - (String.size str1) in
  let rec index' i =
    if i <= max
    then
      begin (if String.isPrefix str1 (String.extract (str2, i, None))
             then begin (::) i index' (i + 1) end
      else begin index' (i + 1) end) end
    else begin [] end in
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
    begin function
    | ([], []) -> true
    | ((String str1)::AL1, (String str2)::AL2) ->
        (str1 = str2) && (sameConcat' (AL1, AL2))
    | ((Exp (us1_))::AL1, (Exp (us2_))::AL2) ->
        (sameExp (us1_, us2_)) && (sameConcat' (AL1, AL2))
    | _ -> false end in
sameConcat' (AL1, AL2)
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
type stringUnify_ =
  | MultAssign of (dec_ ctx_ * exp_ * exp_ * sub_) list 
  | MultDelay of (exp_ list * cnstr_ ref) 
  | Failure 
let rec toFgnUnify =
  begin function
  | MultAssign (l_) ->
      IntSyn.Succeed (List.map (begin function | GXUss -> Assign GXUss end)
        l_)
  | MultDelay (UL, cnstr) ->
      IntSyn.Succeed (List.map (begin function | u_ -> Delay (u_, cnstr) end)
        UL)
  | Failure -> Fail end
let rec unifyRigid (g_, Concat (AL1), Concat (AL2)) =
  let rec unifyRigid' =
    begin function
    | ([], []) -> MultAssign []
    | ((String str1)::AL1, (String str2)::AL2) ->
        if str1 = str2 then begin unifyRigid' (AL1, AL2) end
        else begin Failure end
    | ((Exp ((EVar (r, _, _, _) as u1_), s))::AL1, (Exp
       ((Root (FVar _, _) as u2_), _))::AL2) ->
        let ss = Whnf.invert s in
        if Unify.invertible (g_, (u2_, id), ss, r)
        then
          begin (begin match unifyRigid' (AL1, AL2) with
                 | MultAssign l -> MultAssign ((g_, u1_, u2_, ss) :: l)
                 | Failure -> Failure end) end
        else begin Failure end
| ((Exp ((Root (FVar _, _) as u1_), _))::AL1, (Exp
   ((EVar (r, _, _, _) as u2_), s))::AL2) ->
    let ss = Whnf.invert s in
    if Unify.invertible (g_, (u1_, id), ss, r)
    then
      begin (begin match unifyRigid' (AL1, AL2) with
             | MultAssign l -> MultAssign ((g_, u2_, u1_, ss) :: l)
             | Failure -> Failure end) end
    else begin Failure end
| ((Exp ((Root (FVar _, _), _) as us1_))::AL1, (Exp
   ((Root (FVar _, _), _) as us2_))::AL2) ->
    if sameExpW (us1_, us2_) then begin unifyRigid' (AL1, AL2) end
    else begin Failure end
| ((Exp ((EVar (_, _, _, _), _) as us1_))::AL1, (Exp
   ((EVar (_, _, _, _), _) as us2_))::AL2) ->
    if sameExpW (us1_, us2_) then begin unifyRigid' (AL1, AL2) end
    else begin Failure end
| _ -> Failure end(* FIX: the next two cases are wrong -kw *) in
unifyRigid' (AL1, AL2)
let rec unifyString =
  begin function
  | (g_, Concat ((String prefix)::AL), str, cnstr) ->
      if String.isPrefix prefix str
      then
        begin let suffix = String.extract (str, (String.size prefix), None) in
              unifyString (g_, (Concat AL), suffix, cnstr) end
      else begin Failure end
  | (g_, Concat (AL), str, cnstr) ->
      let rec unifyString' =
        begin function
        | (AL, []) -> (Failure, [])
        | ([], (Decomp (parse, parsedL))::[]) ->
            ((MultAssign []), (parse :: parsedL))
        | ([], candidates) -> ((MultDelay ([], cnstr)), [])
        | ((Exp (us1_))::(Exp (us2_))::AL, _) ->
            ((MultDelay ([EClo us1_; EClo us2_], cnstr)), [])
        | ((Exp ((EVar (r, _, _, _) as u_), s))::AL, candidates) ->
            if Whnf.isPatSub s
            then
              begin let rec assign arg__0 arg__1 =
                      begin match (arg__0, arg__1) with
                      | (r, []) -> None
                      | (r,
                         (_, EVar (r', _, _, _), Root
                          (FgnConst (cs, conDec), Nil), _)::l_) ->
                          if r = r'
                          then begin fromString (conDecName conDec) end
                          else begin assign r l_ end
                      | (r, _::l_) -> assign r l_ end in
          (begin match unifyString' (AL, candidates) with
           | (MultAssign (l_), parsed::parsedL) ->
               (begin match assign r l_ with
                | None ->
                    let ss = Whnf.invert s in
                    let w_ = stringExp parsed in
                    ((MultAssign ((g_, u_, w_, ss) :: l_)), parsedL)
                | Some parsed' ->
                    if parsed = parsed'
                    then begin ((MultAssign l_), parsedL) end
                    else begin (Failure, []) end end)
        | (MultDelay (UL, cnstr), _) ->
            ((MultDelay (((EClo (u_, s)) :: UL), cnstr)), [])
        | (Failure, _) -> (Failure, []) end) end
else begin ((MultDelay ([EClo (u_, s)], cnstr)), []) end
| ((Exp (us_))::AL, _) -> ((MultDelay ([EClo us_], cnstr)), [])
| ((String str)::[], candidates) ->
    let rec successors (Decomp (parse, parsedL)) =
      List.mapPartial
        (begin function
         | Split (prefix, "") -> Some (Decomp (prefix, parsedL))
         | Split (prefix, suffix) -> None end)
      (split (str, parse)) in
  let candidates' = List.foldr (@) [] (List.map successors candidates) in
  unifyString' ([], candidates')
| ((String str)::AL, candidates) ->
    let rec successors (Decomp (parse, parsedL)) =
      List.map
        (begin function
         | Split (prefix, suffix) -> Decomp (suffix, (prefix :: parsedL)) end)
      (split (str, parse)) in
  let candidates' = List.foldr (@) [] (List.map successors candidates) in
  unifyString' (AL, candidates') end in
(begin match unifyString' (AL, [Decomp (str, [])]) with
| (result, []) -> result
| (result, ""::[]) -> result
| (result, parsedL) -> Failure end) end
let rec unifyConcat
  (g_, (Concat (AL1) as concat1), (Concat (AL2) as concat2)) =
  let u1_ = toFgn concat1 in
  let u2_ = toFgn concat2 in
  let cnstr = ref (Eqn (g_, u1_, u2_)) in
  ((begin match (AL1, AL2) with
    | ([], []) -> MultAssign []
    | ([], _) -> Failure
    | (_, []) -> Failure
    | ((String str1)::[], (String str2)::[]) ->
        if str1 = str2 then begin MultAssign [] end else begin Failure end
    | ((Exp ((EVar (r, _, _, _) as u_), s))::[], _) ->
        if Whnf.isPatSub s
        then
          begin let ss = Whnf.invert s in
                (if Unify.invertible (g_, (u2_, id), ss, r)
                 then begin MultAssign [(g_, u_, u2_, ss)] end
                  else begin MultDelay ([u1_; u2_], cnstr) end) end
    else begin MultDelay ([u1_; u2_], cnstr) end
| (_, (Exp ((EVar (r, _, _, _) as u_), s))::[]) ->
    if Whnf.isPatSub s
    then
      begin let ss = Whnf.invert s in
            (if Unify.invertible (g_, (u1_, id), ss, r)
             then begin MultAssign [(g_, u_, u1_, ss)] end
              else begin MultDelay ([u1_; u2_], cnstr) end) end
else begin MultDelay ([u1_; u2_], cnstr) end
| ((String str)::[], _) -> unifyString (g_, concat2, str, cnstr)
| (_, (String str)::[]) -> unifyString (g_, concat1, str, cnstr)
| _ ->
    (begin match unifyRigid (g_, concat1, concat2) with
     | MultAssign _ as result -> result
     | Failure ->
         if sameConcat (concat1, concat2) then begin MultAssign [] end
         else begin MultDelay ([u1_; u2_], cnstr) end end) end)
(* FIX: the next two cases are wrong -kw *))
let rec toFgn =
  begin function
  | Concat ((String str)::[]) as concat -> stringExp str
  | Concat ((Exp (u_, id))::[]) as concat -> u_
  | concat -> FgnExp (!myID, (MyIntsynRep concat)) end
let rec toInternal arg__2 arg__3 =
  begin match (arg__2, arg__3) with
  | (MyIntsynRep concat, ()) -> toExp (normalize concat)
  | (fe, ()) -> raise (UnexpectedFgnExp fe) end
let rec map arg__4 arg__5 =
  begin match (arg__4, arg__5) with
  | (MyIntsynRep concat, f) -> toFgn (normalize (mapConcat (f, concat)))
  | (fe, _) -> raise (UnexpectedFgnExp fe) end
let rec app arg__6 arg__7 =
  begin match (arg__6, arg__7) with
  | (MyIntsynRep concat, f) -> appConcat (f, concat)
  | (fe, _) -> raise (UnexpectedFgnExp fe) end
let rec equalTo arg__8 arg__9 =
  begin match (arg__8, arg__9) with
  | (MyIntsynRep concat, u2_) ->
      sameConcat ((normalize concat), (fromExp (u2_, id)))
  | (fe, _) -> raise (UnexpectedFgnExp fe) end
let rec unifyWith arg__10 arg__11 =
  begin match (arg__10, arg__11) with
  | (MyIntsynRep concat, (g_, u2_)) ->
      toFgnUnify (unifyConcat (g_, (normalize concat), (fromExp (u2_, id))))
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
    | n -> App ((Root ((BVar n), Nil)), (makeParams (n - 1))) end in
let rec makeLam arg__12 arg__13 =
  begin match (arg__12, arg__13) with
  | (e_, 0) -> e_
  | (e_, n) -> Lam ((Dec (None, (string ()))), (makeLam e_ (n - 1))) end in
let rec expand =
  begin function
  | ((Nil, s), arity) -> ((makeParams arity), arity)
  | ((App (u_, s_), s), arity) ->
      let (s'_, arity') = expand ((s_, s), (arity - 1)) in
      ((App ((EClo (u_, (comp (s, (Shift arity'))))), s'_)), arity')
  | ((SClo (s_, s'), s), arity) -> expand ((s_, (comp (s, s'))), arity) end in
let (s'_, arity') = expand ((s_, id), arity) in
makeLam (toFgn (opExp s'_)) arity'
let rec makeFgnBinary opConcat =
  makeFgn
    (2,
      (begin function
       | App (u1_, App (u2_, Nil)) ->
           opConcat ((fromExp (u1_, id)), (fromExp (u2_, id))) end))
let rec arrow (u_, v_) = Pi (((Dec (None, u_)), No), v_)
let rec init (cs, installF) =
  begin myID := cs;
  (:=) stringID installF
    ((ConDec
        ("string", None, 0, (Constraint (!myID, solveString)), (Uni Type),
          Kind)), None, [MS.Mnil]);
  (:=) concatID installF
    ((ConDec
        ("++", None, 0, (Foreign (!myID, (makeFgnBinary catConcat))),
          (arrow ((string ()), (arrow ((string ()), (string ()))))), Type)),
      (Some (FX.Infix (FX.maxPrec, FX.Right))), []);
  installFgnExpOps ();
  () end
let solver =
  ({
     name = "equality/strings";
     keywords = "strings,equality";
     needs = ["Unify"];
     fgnConst = (Some { parse = parseString });
     init;
     reset = (begin function | () -> () end);
   mark = (begin function | () -> () end);
  unwind = (begin function | () -> () end) } : CSManager.solver) end
