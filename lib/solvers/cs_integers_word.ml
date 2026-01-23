module CSIntWord(CSIntWord:sig
                             module Whnf : WHNF
                             module Unify : UNIFY
                             val wordSize : int
                           end) : CS =
  struct
    open IntSyn
    module W = LargeWord
    module FX = CSManager.Fixity
    module MS = ModeSyn
    exception MyFgnCnstrRepPlus of (dctx * exp_ * exp_ * exp_ * exp_) 
    exception MyFgnCnstrRepTimes of (dctx * exp_ * exp_ * exp_ * exp_) 
    exception MyFgnCnstrRepQuot of (dctx * exp_ * exp_ * exp_ * exp_) 
    let wordSize' = Int.min (wordSize, W.wordSize)
    let zero = W.fromInt 0
    let max = W.(>>) ((W.notb zero), (Word.fromInt (W.wordSize - wordSize')))
    let rec numCheck d = W.(<=) (d, max)
    let rec plusCheck (d1, d2) =
      let d3 = W.(+) (d1, d2) in
      (W.(>=) (d3, d1)) && ((W.(>=) (d3, d2)) && (W.(<=) (d3, max)))
    let rec timesCheck (d1, d2) =
      if (d1 = zero) || (d2 = zero) then begin true end
      else begin (let d3 = W.div ((W.div (max, d1)), d2) in W.(>) (d3, zero)) end
  let rec quotCheck (d1, d2) = W.(>) (d2, zero)
  let myID = (ref (-1) : csid ref)
  let wordID = (ref (-1) : cid ref)
  let rec word () = Root ((Const !wordID), Nil)
  let plusID = (ref (-1) : cid ref)
  let timesID = (ref (-1) : cid ref)
  let quotID = (ref (-1) : cid ref)
  let rec plusExp (u_, v_, w_) =
    Root ((Const !plusID), (App (u_, (App (v_, (App (w_, Nil)))))))
  let rec timesExp (u_, v_, w_) =
    Root ((Const !timesID), (App (u_, (App (v_, (App (w_, Nil)))))))
  let rec quotExp (u_, v_, w_) =
    Root ((Const !quotID), (App (u_, (App (v_, (App (w_, Nil)))))))
  let provePlusID = (ref (-1) : cid ref)
  let proveTimesID = (ref (-1) : cid ref)
  let proveQuotID = (ref (-1) : cid ref)
  let proofPlusID = (ref (-1) : cid ref)
  let proofTimesID = (ref (-1) : cid ref)
  let proofQuotID = (ref (-1) : cid ref)
  let rec provePlusExp (u_, v_, w_, p_) =
    Root
      ((Const !provePlusID),
        (App (u_, (App (v_, (App (w_, (App (p_, Nil)))))))))
  let rec proofPlusExp (u_, v_, w_, p_) =
    Root
      ((Const !proofPlusID),
        (App (u_, (App (v_, (App (w_, (App (p_, Nil)))))))))
  let rec proofTimesExp (u_, v_, w_, p_) =
    Root
      ((Const !proofTimesID),
        (App (u_, (App (v_, (App (w_, (App (p_, Nil)))))))))
  let rec proveTimesExp (u_, v_, w_, p_) =
    Root
      ((Const !proveTimesID),
        (App (u_, (App (v_, (App (w_, (App (p_, Nil)))))))))
  let rec proveQuotExp (u_, v_, w_, p_) =
    Root
      ((Const !proveQuotID),
        (App (u_, (App (v_, (App (w_, (App (p_, Nil)))))))))
  let rec proofQuotExp (u_, v_, w_, p_) =
    Root
      ((Const !proofQuotID),
        (App (u_, (App (v_, (App (w_, (App (p_, Nil)))))))))
  let rec numberConDec d =
    ConDec ((W.fmt StringCvt.DEC d), None, 0, Normal, (word ()), Type)
  let rec numberExp d = Root ((FgnConst (!myID, (numberConDec d))), Nil)
  let rec scanNumber str =
    let rec check =
      begin function
      | _::_ as chars -> List.all Char.isDigit chars
      | [] -> false end in
  if check (String.explode str)
  then
    begin begin match StringCvt.scanString (W.scan StringCvt.DEC) str with
          | Some d -> (if numCheck d then begin Some d end
              else begin None end)
  | None -> None end end else begin None end
let rec parseNumber string =
  begin match scanNumber string with
  | Some d -> Some (numberConDec d)
  | None -> None end
let rec plusPfConDec (d1, d2) =
  let d3 = W.(+) (d1, d2) in
  ConDec
    (((^) ((W.fmt StringCvt.DEC d1) ^ "+") W.fmt StringCvt.DEC d2), None, 0,
      Normal, (plusExp ((numberExp d1), (numberExp d2), (numberExp d3))),
      Type)
let rec plusPfExp ds = Root ((FgnConst (!myID, (plusPfConDec ds))), Nil)
let rec timesPfConDec (d1, d2) =
  let d3 = W.( * ) (d1, d2) in
  ConDec
    (((^) ((W.fmt StringCvt.DEC d1) ^ "*") W.fmt StringCvt.DEC d2), None, 0,
      Normal, (timesExp ((numberExp d1), (numberExp d2), (numberExp d3))),
      Type)
let rec timesPfExp ds = Root ((FgnConst (!myID, (timesPfConDec ds))), Nil)
let rec quotPfConDec (d1, d2) =
  let d3 = W.div (d1, d2) in
  ConDec
    (((^) ((W.fmt StringCvt.DEC d1) ^ "/") W.fmt StringCvt.DEC d2), None, 0,
      Normal, (quotExp ((numberExp d1), (numberExp d2), (numberExp d3))),
      Type)
let rec quotPfExp ds = Root ((FgnConst (!myID, (quotPfConDec ds))), Nil)
let rec scanBinopPf oper string =
  let args = String.tokens (begin function | c -> c = oper end) string in
begin match args with
| arg1::arg2::[] ->
    (begin match ((StringCvt.scanString (W.scan StringCvt.DEC) arg1),
                   (StringCvt.scanString (W.scan StringCvt.DEC) arg2))
           with
     | (Some d1, Some d2) -> Some (d1, d2)
     | _ -> None end)
  | _ -> None end
let rec parseBinopPf oper string =
  begin match (oper, (scanBinopPf oper string)) with
  | ('+', Some ds) -> Some (plusPfConDec ds)
  | ('*', Some ds) -> Some (timesPfConDec ds)
  | ('/', Some ds) -> Some (quotPfConDec ds)
  | _ -> None end
let parsePlusPf = parseBinopPf '+'
let parseTimesPf = parseBinopPf '*'
let parseQuotPf = parseBinopPf '/'
let rec parseAll string =
  begin match parseNumber string with
  | Some conDec -> Some conDec
  | None ->
      (begin match parsePlusPf string with
       | Some conDec -> Some conDec
       | None ->
           (begin match parseTimesPf string with
            | Some conDec -> Some conDec
            | None -> parseQuotPf string end) end) end
type fixTerm_ =
  | Num of W.word 
  | PlusPf of (W.word * W.word) 
  | TimesPf of (W.word * W.word) 
  | QuotPf of (W.word * W.word) 
  | Expr of (exp_ * sub_) 
let rec fromExpW =
  begin function
  | (Root (FgnConst (cs, conDec), _), _) as us_ ->
      if (!) ((=) cs) myID
      then
        begin let string = conDecName conDec in
              (begin match scanNumber string with
               | Some d -> Num d
               | None ->
                   (begin match scanBinopPf '/' string with
                    | Some ds -> QuotPf ds
                    | None ->
                        (begin match scanBinopPf '+' string with
                         | Some ds -> PlusPf ds
                         | None ->
                             (begin match scanBinopPf '*' string with
                              | Some ds -> TimesPf ds
                              | None -> Expr us_ end) end) end) end) end
else begin Expr us_ end
| (Root (Def d, _), _) as us_ -> fromExpW (Whnf.expandDef us_)
| us_ -> Expr us_ end
let rec fromExp (us_) = fromExpW (Whnf.whnf us_)
let rec toExp =
  begin function
  | Num d -> numberExp d
  | PlusPf ds -> plusPfExp ds
  | TimesPf ds -> timesPfExp ds
  | QuotPf ds -> quotPfExp ds
  | Expr (us_) -> EClo us_ end
let rec solveNumber (g_, s_, k) = Some (numberExp (W.fromInt k))
let rec fst =
  begin function
  | (App (u1_, _), s) -> (u1_, s)
  | (SClo (s_, s'), s) -> fst (s_, (comp (s', s))) end
let rec snd =
  begin function
  | (App (_, s_), s) -> fst (s_, s)
  | (SClo (s_, s'), s) -> snd (s_, (comp (s', s))) end
let rec trd =
  begin function
  | (App (_, s_), s) -> snd (s_, s)
  | (SClo (s_, s'), s) -> trd (s_, (comp (s', s))) end
let rec fth =
  begin function
  | (App (_, s_), s) -> trd (s_, s)
  | (SClo (s_, s'), s) -> fth (s_, (comp (s', s))) end
let rec toInternalPlus (g_, u1_, u2_, u3_) () =
  [(g_, (plusExp (u1_, u2_, u3_)))]
let rec awakePlus (g_, proof, u1_, u2_, u3_) () =
  begin match solvePlus (g_, (App (u1_, (App (u2_, (App (u3_, Nil)))))), 0)
        with
  | Some proof' -> Unify.unifiable (g_, (proof, id), (proof', id))
  | None -> false end
let rec makeCnstrPlus (g_, proof, u1_, u2_, u3_) =
  FgnCnstr (!myID, (MyFgnCnstrRepPlus (g_, proof, u1_, u2_, u3_)))
let rec solvePlus =
  begin function
  | (g_, s_, 0) ->
      let us1_ = fst (s_, id) in
      let us2_ = snd (s_, id) in
      let us3_ = trd (s_, id) in
      (begin match ((fromExp us1_), (fromExp us2_), (fromExp us3_)) with
       | (Num d1, Num d2, Num d3) ->
           if ((=) d3 W.(+) (d1, d2)) && (plusCheck (d1, d2))
           then begin Some (plusPfExp (d1, d2)) end else begin None end
        | (Expr (us1_), Num d2, Num d3) ->
            if
              (W.(>=) (d3, d2)) &&
                (Unify.unifiable
                   (g_, us1_, ((numberExp (W.(-) (d3, d2))), id)))
            then begin Some (plusPfExp ((W.(-) (d3, d2)), d2)) end
            else begin None end
      | (Num d1, Expr (us2_), Num d3) ->
          if
            (W.(>=) (d3, d1)) &&
              (Unify.unifiable (g_, us2_, ((numberExp (W.(-) (d3, d1))), id)))
          then begin Some (plusPfExp (d1, (W.(-) (d3, d1)))) end
          else begin None end
  | (Num d1, Num d2, Expr (us3_)) ->
      if
        (plusCheck (d1, d2)) &&
          (Unify.unifiable (g_, us3_, ((numberExp (W.(+) (d1, d2))), id)))
      then begin Some (plusPfExp (d1, d2)) end else begin None end
| _ ->
    let proof =
      newEVar (g_, (plusExp ((EClo us1_), (EClo us2_), (EClo us3_)))) in
    let cnstr =
      makeCnstrPlus (g_, proof, (EClo us1_), (EClo us2_), (EClo us3_)) in
    let _ =
      List.app (begin function | us_ -> Unify.delay (us_, (ref cnstr)) end)
      [us1_; us2_; us3_] in
    Some proof end)
| (g_, s_, n) -> None end
let rec toInternalTimes (g_, u1_, u2_, u3_) () =
  [(g_, (timesExp (u1_, u2_, u3_)))]
let rec awakeTimes (g_, proof, u1_, u2_, u3_) () =
  begin match solveTimes (g_, (App (u1_, (App (u2_, (App (u3_, Nil)))))), 0)
        with
  | Some proof' -> Unify.unifiable (g_, (proof, id), (proof', id))
  | None -> false end
let rec makeCnstrTimes (g_, proof, u1_, u2_, u3_) =
  FgnCnstr (!myID, (MyFgnCnstrRepTimes (g_, proof, u1_, u2_, u3_)))
let rec solveTimes =
  begin function
  | (g_, s_, 0) ->
      let us1_ = fst (s_, id) in
      let us2_ = snd (s_, id) in
      let us3_ = trd (s_, id) in
      (begin match ((fromExp us1_), (fromExp us2_), (fromExp us3_)) with
       | (Num d1, Num d2, Num d3) ->
           if ((=) d3 W.( * ) (d1, d2)) && (timesCheck (d1, d2))
           then begin Some (timesPfExp (d1, d2)) end else begin None end
        | (Expr (us1_), Num d2, Num d3) ->
            if
              (d3 = zero) &&
                (Unify.unifiable (g_, us1_, ((numberExp zero), id)))
            then begin Some (timesPfExp (zero, d2)) end
            else begin
              if
                (W.(>) (d2, zero)) &&
                  ((W.(>) (d3, zero)) &&
                     (((W.mod_ (d3, d2)) = zero) &&
                        (Unify.unifiable
                           (g_, us1_, ((numberExp (W.div (d3, d2))), id)))))
              then begin Some (timesPfExp ((W.div (d3, d2)), d2)) end
              else begin None end end
  | (Num d1, Expr (us2_), Num d3) ->
      if (d3 = zero) && (Unify.unifiable (g_, us2_, ((numberExp zero), id)))
      then begin Some (timesPfExp (d1, zero)) end
      else begin
        if
          (W.(>) (d1, zero)) &&
            ((W.(>) (d3, zero)) &&
               (((W.mod_ (d3, d1)) = zero) &&
                  (Unify.unifiable
                     (g_, us2_, ((numberExp (W.div (d3, d1))), id)))))
        then begin Some (timesPfExp (d1, (W.div (d3, d1)))) end
        else begin None end end
| (Num d1, Num d2, Expr (us3_)) ->
    if
      (timesCheck (d1, d2)) &&
        (Unify.unifiable (g_, us3_, ((numberExp (W.( * ) (d1, d2))), id)))
    then begin Some (timesPfExp (d1, d2)) end else begin None end
| _ ->
    let proof =
      newEVar (g_, (timesExp ((EClo us1_), (EClo us2_), (EClo us3_)))) in
    let cnstr =
      makeCnstrTimes (g_, proof, (EClo us1_), (EClo us2_), (EClo us3_)) in
    let _ =
      List.app (begin function | us_ -> Unify.delay (us_, (ref cnstr)) end)
      [us1_; us2_; us3_] in
    Some proof end)
| (g_, s_, n) -> None end
let rec toInternalQuot (g_, u1_, u2_, u3_) () =
  [(g_, (quotExp (u1_, u2_, u3_)))]
let rec awakeQuot (g_, proof, u1_, u2_, u3_) () =
  begin match solveQuot (g_, (App (u1_, (App (u2_, (App (u3_, Nil)))))), 0)
        with
  | Some proof' -> Unify.unifiable (g_, (proof, id), (proof', id))
  | None -> false end
let rec makeCnstrQuot (g_, proof, u1_, u2_, u3_) =
  FgnCnstr (!myID, (MyFgnCnstrRepQuot (g_, proof, u1_, u2_, u3_)))
let rec solveQuot =
  begin function
  | (g_, s_, 0) ->
      let us1_ = fst (s_, id) in
      let us2_ = snd (s_, id) in
      let us3_ = trd (s_, id) in
      (begin match ((fromExp us1_), (fromExp us2_), (fromExp us3_)) with
       | (Num d1, Num d2, Num d3) ->
           if (quotCheck (d1, d2)) && ((=) d3 W.div (d1, d2))
           then begin Some (quotPfExp (d1, d2)) end else begin None end
        | (Num d1, Num d2, Expr (us3_)) ->
            if
              (quotCheck (d1, d2)) &&
                (Unify.unifiable
                   (g_, us3_, ((numberExp (W.div (d1, d2))), id)))
            then begin Some (quotPfExp (d1, d2)) end else begin None end
      | _ ->
          let proof =
            newEVar (g_, (quotExp ((EClo us1_), (EClo us2_), (EClo us3_)))) in
          let cnstr =
            makeCnstrQuot (g_, proof, (EClo us1_), (EClo us2_), (EClo us3_)) in
          let _ =
            List.app
              (begin function | us_ -> Unify.delay (us_, (ref cnstr)) end)
            [us1_; us2_; us3_] in
          Some proof end)
| (g_, s_, n) -> None end
let rec solveProvePlus (g_, s_, k) =
  let us1_ = fst (s_, id) in
  let us2_ = snd (s_, id) in
  let us3_ = trd (s_, id) in
  let us4_ = fth (s_, id) in
  begin match solvePlus
                (g_,
                  (App
                     ((EClo us1_),
                       (App ((EClo us2_), (App ((EClo us3_), Nil)))))), k)
        with
  | Some (u_) ->
      if Unify.unifiable (g_, us4_, (u_, id))
      then
        begin Some
                (proofPlusExp
                   ((EClo us1_), (EClo us2_), (EClo us3_), (EClo us4_))) end
      else begin None end
    | None -> None end
let rec solveProveTimes (g_, s_, k) =
  let us1_ = fst (s_, id) in
  let us2_ = snd (s_, id) in
  let us3_ = trd (s_, id) in
  let us4_ = fth (s_, id) in
  begin match solveTimes
                (g_,
                  (App
                     ((EClo us1_),
                       (App ((EClo us2_), (App ((EClo us3_), Nil)))))), k)
        with
  | Some (u_) ->
      if Unify.unifiable (g_, us4_, (u_, id))
      then
        begin Some
                (proofTimesExp
                   ((EClo us1_), (EClo us2_), (EClo us3_), (EClo us4_))) end
      else begin None end
    | None -> None end
let rec solveProveQuot (g_, s_, k) =
  let us1_ = fst (s_, id) in
  let us2_ = snd (s_, id) in
  let us3_ = trd (s_, id) in
  let us4_ = fth (s_, id) in
  begin match solveQuot
                (g_,
                  (App
                     ((EClo us1_),
                       (App ((EClo us2_), (App ((EClo us3_), Nil)))))), k)
        with
  | Some (u_) ->
      if Unify.unifiable (g_, us4_, (u_, id))
      then
        begin Some
                (proofQuotExp
                   ((EClo us1_), (EClo us2_), (EClo us3_), (EClo us4_))) end
      else begin None end
    | None -> None end
let rec arrow (u_, v_) = Pi (((Dec (None, u_)), No), v_)
let rec pi (name, u_, v_) = Pi (((Dec ((Some name), u_)), Maybe), v_)
let rec bvar n = Root ((BVar n), Nil)
let rec installFgnCnstrOps () =
  let csid = !myID in
  let _ =
    FgnCnstrStd.ToInternal.install
      (csid,
        (begin function
         | MyFgnCnstrRepPlus (g_, _, u1_, u2_, u3_) ->
             toInternalPlus (g_, u1_, u2_, u3_)
         | MyFgnCnstrRepTimes (g_, _, u1_, u2_, u3_) ->
             toInternalTimes (g_, u1_, u2_, u3_)
         | MyFgnCnstrRepQuot (g_, _, u1_, u2_, u3_) ->
             toInternalQuot (g_, u1_, u2_, u3_)
         | fc -> raise (UnexpectedFgnCnstr fc) end)) in
  let _ =
    FgnCnstrStd.Awake.install
      (csid,
        (begin function
         | MyFgnCnstrRepPlus (g_, proof, u1_, u2_, u3_) ->
             awakePlus (g_, proof, u1_, u2_, u3_)
         | MyFgnCnstrRepTimes (g_, proof, u1_, u2_, u3_) ->
             awakeTimes (g_, proof, u1_, u2_, u3_)
         | MyFgnCnstrRepQuot (g_, proof, u1_, u2_, u3_) ->
             awakeQuot (g_, proof, u1_, u2_, u3_)
         | fc -> raise (UnexpectedFgnCnstr fc) end)) in
  let _ =
    FgnCnstrStd.Simplify.install
      (csid,
        (begin function
         | MyFgnCnstrRepPlus _ -> (begin function | () -> false end)
        | MyFgnCnstrRepTimes _ -> (begin function | () -> false end)
      | MyFgnCnstrRepQuot _ -> (begin function | () -> false end)
    | fc -> raise (UnexpectedFgnCnstr fc) end)) in
()
let rec init (cs, installF) =
  begin myID := cs;
  (:=) wordID installF
    ((ConDec
        (((^) "word" Int.toString wordSize'), None, 0,
          (Constraint (!myID, solveNumber)), (Uni Type), Kind)),
      (None : FX.fixity option), [MS.Mnil]);
  (:=) plusID installF
    ((ConDec
        ("+", None, 0, (Constraint (!myID, solvePlus)),
          (arrow
             ((word ()),
               (arrow ((word ()), (arrow ((word ()), (Uni Type))))))), Kind)),
      None,
      [MS.Mapp
         ((MS.Marg (MS.Plus, (Some "X"))),
           (MS.Mapp
              ((MS.Marg (MS.Plus, (Some "Y"))),
                (MS.Mapp ((MS.Marg (MS.Minus, (Some "Z"))), MS.Mnil)))));
      MS.Mapp
        ((MS.Marg (MS.Plus, (Some "X"))),
          (MS.Mapp
             ((MS.Marg (MS.Minus, (Some "Y"))),
               (MS.Mapp ((MS.Marg (MS.Plus, (Some "Z"))), MS.Mnil)))));
      MS.Mapp
        ((MS.Marg (MS.Minus, (Some "X"))),
          (MS.Mapp
             ((MS.Marg (MS.Plus, (Some "Y"))),
               (MS.Mapp ((MS.Marg (MS.Plus, (Some "Z"))), MS.Mnil)))))]);
  (:=) timesID installF
    ((ConDec
        ("*", None, 0, (Constraint (!myID, solveTimes)),
          (arrow
             ((word ()),
               (arrow ((word ()), (arrow ((word ()), (Uni Type))))))), Kind)),
      None,
      [MS.Mapp
         ((MS.Marg (MS.Plus, (Some "X"))),
           (MS.Mapp
              ((MS.Marg (MS.Plus, (Some "Y"))),
                (MS.Mapp ((MS.Marg (MS.Minus, (Some "Z"))), MS.Mnil)))));
      MS.Mapp
        ((MS.Marg (MS.Plus, (Some "X"))),
          (MS.Mapp
             ((MS.Marg (MS.Minus, (Some "Y"))),
               (MS.Mapp ((MS.Marg (MS.Plus, (Some "Z"))), MS.Mnil)))));
      MS.Mapp
        ((MS.Marg (MS.Minus, (Some "X"))),
          (MS.Mapp
             ((MS.Marg (MS.Plus, (Some "Y"))),
               (MS.Mapp ((MS.Marg (MS.Plus, (Some "Z"))), MS.Mnil)))))]);
  (:=) quotID installF
    ((ConDec
        ("/", None, 0, (Constraint (!myID, solveQuot)),
          (arrow
             ((word ()),
               (arrow ((word ()), (arrow ((word ()), (Uni Type))))))), Kind)),
      None,
      [MS.Mapp
         ((MS.Marg (MS.Plus, (Some "X"))),
           (MS.Mapp
              ((MS.Marg (MS.Plus, (Some "Y"))),
                (MS.Mapp ((MS.Marg (MS.Minus, (Some "Z"))), MS.Mnil)))));
      MS.Mapp
        ((MS.Marg (MS.Plus, (Some "X"))),
          (MS.Mapp
             ((MS.Marg (MS.Minus, (Some "Y"))),
               (MS.Mapp ((MS.Marg (MS.Plus, (Some "Z"))), MS.Mnil)))))]);
  (:=) provePlusID installF
    ((ConDec
        ("prove+", None, 0, (Constraint (!myID, solveProvePlus)),
          (pi
             ("X", (word ()),
               (pi
                  ("Y", (word ()),
                    (pi
                       ("Z", (word ()),
                         (pi
                            ("P", (plusExp ((bvar 3), (bvar 2), (bvar 1))),
                              (Uni Type))))))))), Kind)), None,
      [MS.Mapp
         ((MS.Marg (MS.Star, (Some "X"))),
           (MS.Mapp
              ((MS.Marg (MS.Star, (Some "Y"))),
                (MS.Mapp
                   ((MS.Marg (MS.Star, (Some "Z"))),
                     (MS.Mapp ((MS.Marg (MS.Star, (Some "P"))), MS.Mnil)))))))]);
  (:=) proofPlusID installF
    ((ConDec
        ("proof+", None, 0, Normal,
          (pi
             ("X", (word ()),
               (pi
                  ("Y", (word ()),
                    (pi
                       ("Z", (word ()),
                         (pi
                            ("P", (plusExp ((bvar 3), (bvar 2), (bvar 1))),
                              (provePlusExp
                                 ((bvar 4), (bvar 3), (bvar 2), (bvar 1))))))))))),
          Type)), None, []);
  (:=) proveTimesID installF
    ((ConDec
        ("prove*", None, 0, (Constraint (!myID, solveProveTimes)),
          (pi
             ("X", (word ()),
               (pi
                  ("Y", (word ()),
                    (pi
                       ("Z", (word ()),
                         (pi
                            ("P", (timesExp ((bvar 3), (bvar 2), (bvar 1))),
                              (Uni Type))))))))), Kind)), None,
      [MS.Mapp
         ((MS.Marg (MS.Star, (Some "X"))),
           (MS.Mapp
              ((MS.Marg (MS.Star, (Some "Y"))),
                (MS.Mapp
                   ((MS.Marg (MS.Star, (Some "Z"))),
                     (MS.Mapp ((MS.Marg (MS.Star, (Some "P"))), MS.Mnil)))))))]);
  (:=) proofTimesID installF
    ((ConDec
        ("proof*", None, 0, Normal,
          (pi
             ("X", (word ()),
               (pi
                  ("Y", (word ()),
                    (pi
                       ("Z", (word ()),
                         (pi
                            ("P", (timesExp ((bvar 3), (bvar 2), (bvar 1))),
                              (proveTimesExp
                                 ((bvar 4), (bvar 3), (bvar 2), (bvar 1))))))))))),
          Type)), None, []);
  (:=) proveQuotID installF
    ((ConDec
        ("prove/", None, 0, (Constraint (!myID, solveProveQuot)),
          (pi
             ("X", (word ()),
               (pi
                  ("Y", (word ()),
                    (pi
                       ("Z", (word ()),
                         (pi
                            ("P", (quotExp ((bvar 3), (bvar 2), (bvar 1))),
                              (Uni Type))))))))), Kind)), None,
      [MS.Mapp
         ((MS.Marg (MS.Star, (Some "X"))),
           (MS.Mapp
              ((MS.Marg (MS.Star, (Some "Y"))),
                (MS.Mapp
                   ((MS.Marg (MS.Star, (Some "Z"))),
                     (MS.Mapp ((MS.Marg (MS.Star, (Some "P"))), MS.Mnil)))))))]);
  (:=) proofQuotID installF
    ((ConDec
        ("proof/", None, 0, Normal,
          (pi
             ("X", (word ()),
               (pi
                  ("Y", (word ()),
                    (pi
                       ("Z", (word ()),
                         (pi
                            ("P", (quotExp ((bvar 3), (bvar 2), (bvar 1))),
                              (proveQuotExp
                                 ((bvar 4), (bvar 3), (bvar 2), (bvar 1))))))))))),
          Type)), None, []);
  installFgnCnstrOps ();
  () end
let solver =
  {
    name = ((^) "word" Int.toString wordSize');
    keywords = "numbers,equality";
    needs = ["Unify"];
    fgnConst = (Some { parse = parseAll });
    init;
    reset = (begin function | () -> () end);
  mark = (begin function | () -> () end);
  unwind = (begin function | () -> () end) } end
