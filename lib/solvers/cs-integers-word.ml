
module CSIntWord(CSIntWord:sig
                             module Whnf : WHNF
                             module Unify : UNIFY
                             val wordSize :
                               ((int)(*! sharing CSManager.IntSyn = IntSyn !*)
                                 (*! structure CSManager : CS_MANAGER !*)
                                 (*! sharing Unify.IntSyn = IntSyn !*)
                                 (*! sharing Whnf.IntSyn = IntSyn !*)
                                 (*! structure IntSyn : INTSYN !*)
                                 (* Author: Roberto Virga *)
                                 (* Solver for machine integers *))
                           end) : CS =
  struct
    open IntSyn
    module W = LargeWord
    module FX = CSManager.Fixity
    module MS = ModeSyn
    exception MyFgnCnstrRepPlus of (dctx * __Exp * __Exp * __Exp * __Exp) 
    exception MyFgnCnstrRepTimes of (dctx * __Exp * __Exp * __Exp * __Exp) 
    exception MyFgnCnstrRepQuot of (dctx * __Exp * __Exp * __Exp * __Exp) 
    let wordSize' = Int.min (wordSize, W.wordSize)
    let zero = W.fromInt 0
    let max = W.(>>) ((W.notb zero), (Word.fromInt (W.wordSize - wordSize')))
    let rec numCheck d = W.(<=) (d, max)
    let rec plusCheck (d1, d2) =
      let d3 = W.(+) (d1, d2) in
      (W.(>=) (d3, d1)) && ((W.(>=) (d3, d2)) && (W.(<=) (d3, max)))
    let rec timesCheck (d1, d2) =
      if (d1 = zero) || (d2 = zero)
      then true__
      else (let d3 = W.div ((W.div (max, d1)), d2) in W.(>) (d3, zero))
    let rec quotCheck (d1, d2) = W.(>) (d2, zero)
    let myID = (ref (-1) : csid ref)
    let wordID = (ref (-1) : cid ref)
    let rec word () = Root ((Const (!wordID)), Nil)
    let plusID = (ref (-1) : cid ref)
    let timesID = (ref (-1) : cid ref)
    let quotID = (ref (-1) : cid ref)
    let rec plusExp (U, V, W) =
      Root ((Const (!plusID)), (App (U, (App (V, (App (W, Nil)))))))
    let rec timesExp (U, V, W) =
      Root ((Const (!timesID)), (App (U, (App (V, (App (W, Nil)))))))
    let rec quotExp (U, V, W) =
      Root ((Const (!quotID)), (App (U, (App (V, (App (W, Nil)))))))
    let provePlusID = (ref (-1) : cid ref)
    let proveTimesID = (ref (-1) : cid ref)
    let proveQuotID = (ref (-1) : cid ref)
    let proofPlusID = (ref (-1) : cid ref)
    let proofTimesID = (ref (-1) : cid ref)
    let proofQuotID = (ref (-1) : cid ref)
    let rec provePlusExp (U, V, W, P) =
      Root
        ((Const (!provePlusID)),
          (App (U, (App (V, (App (W, (App (P, Nil)))))))))
    let rec proofPlusExp (U, V, W, P) =
      Root
        ((Const (!proofPlusID)),
          (App (U, (App (V, (App (W, (App (P, Nil)))))))))
    let rec proofTimesExp (U, V, W, P) =
      Root
        ((Const (!proofTimesID)),
          (App (U, (App (V, (App (W, (App (P, Nil)))))))))
    let rec proveTimesExp (U, V, W, P) =
      Root
        ((Const (!proveTimesID)),
          (App (U, (App (V, (App (W, (App (P, Nil)))))))))
    let rec proveQuotExp (U, V, W, P) =
      Root
        ((Const (!proveQuotID)),
          (App (U, (App (V, (App (W, (App (P, Nil)))))))))
    let rec proofQuotExp (U, V, W, P) =
      Root
        ((Const (!proofQuotID)),
          (App (U, (App (V, (App (W, (App (P, Nil)))))))))
    let rec numberConDec d =
      ConDec ((W.fmt StringCvt.DEC d), NONE, 0, Normal, (word ()), Type)
    let rec numberExp d = Root ((FgnConst ((!myID), (numberConDec d))), Nil)
    let rec scanNumber str =
      let check =
        function
        | _::_ as chars -> List.all Char.isDigit chars
        | nil -> false__ in
      if check (String.explode str)
      then
        match StringCvt.scanString (W.scan StringCvt.DEC) str with
        | SOME d -> (if numCheck d then SOME d else NONE)
        | NONE -> NONE
      else NONE
    let rec parseNumber string =
      match scanNumber string with
      | SOME d -> SOME (numberConDec d)
      | NONE -> NONE
    let rec plusPfConDec (d1, d2) =
      let d3 = W.(+) (d1, d2) in
      ConDec
        (((^) ((W.fmt StringCvt.DEC d1) ^ "+") W.fmt StringCvt.DEC d2), NONE,
          0, Normal,
          (plusExp ((numberExp d1), (numberExp d2), (numberExp d3))), Type)
    let rec plusPfExp ds =
      Root ((FgnConst ((!myID), (plusPfConDec ds))), Nil)
    let rec timesPfConDec (d1, d2) =
      let d3 = W.( * ) (d1, d2) in
      ConDec
        (((^) ((W.fmt StringCvt.DEC d1) ^ "*") W.fmt StringCvt.DEC d2), NONE,
          0, Normal,
          (timesExp ((numberExp d1), (numberExp d2), (numberExp d3))), Type)
    let rec timesPfExp ds =
      Root ((FgnConst ((!myID), (timesPfConDec ds))), Nil)
    let rec quotPfConDec (d1, d2) =
      let d3 = W.div (d1, d2) in
      ConDec
        (((^) ((W.fmt StringCvt.DEC d1) ^ "/") W.fmt StringCvt.DEC d2), NONE,
          0, Normal,
          (quotExp ((numberExp d1), (numberExp d2), (numberExp d3))), Type)
    let rec quotPfExp ds =
      Root ((FgnConst ((!myID), (quotPfConDec ds))), Nil)
    let rec scanBinopPf oper string =
      let args = String.tokens (function | c -> c = oper) string in
      match args with
      | arg1::arg2::[] ->
          (match ((StringCvt.scanString (W.scan StringCvt.DEC) arg1),
                   (StringCvt.scanString (W.scan StringCvt.DEC) arg2))
           with
           | (SOME d1, SOME d2) -> SOME (d1, d2)
           | _ -> NONE)
      | _ -> NONE
    let rec parseBinopPf oper string =
      match (oper, (scanBinopPf oper string)) with
      | ('+', SOME ds) -> SOME (plusPfConDec ds)
      | ('*', SOME ds) -> SOME (timesPfConDec ds)
      | ('/', SOME ds) -> SOME (quotPfConDec ds)
      | _ -> NONE
    let parsePlusPf = parseBinopPf '+'
    let parseTimesPf = parseBinopPf '*'
    let parseQuotPf = parseBinopPf '/'
    let rec parseAll string =
      match parseNumber string with
      | SOME conDec -> SOME conDec
      | NONE ->
          (match parsePlusPf string with
           | SOME conDec -> SOME conDec
           | NONE ->
               (match parseTimesPf string with
                | SOME conDec -> SOME conDec
                | NONE -> parseQuotPf string))
    type __FixTerm =
      | Num of W.word 
      | PlusPf of (W.word * W.word) 
      | TimesPf of (W.word * W.word) 
      | QuotPf of (W.word * W.word) 
      | Expr of (__Exp * __Sub) 
    let rec fromExpW =
      function
      | (Root (FgnConst (cs, conDec), _), _) as Us ->
          if (!) ((=) cs) myID
          then
            let string = conDecName conDec in
            (match scanNumber string with
             | SOME d -> Num d
             | NONE ->
                 (match scanBinopPf '/' string with
                  | SOME ds -> QuotPf ds
                  | NONE ->
                      (match scanBinopPf '+' string with
                       | SOME ds -> PlusPf ds
                       | NONE ->
                           (match scanBinopPf '*' string with
                            | SOME ds -> TimesPf ds
                            | NONE -> Expr Us))))
          else Expr Us
      | (Root (Def d, _), _) as Us -> fromExpW (Whnf.expandDef Us)
      | Us -> Expr Us
    let rec fromExp (Us) = fromExpW (Whnf.whnf Us)
    let rec toExp =
      function
      | Num d -> numberExp d
      | PlusPf ds -> plusPfExp ds
      | TimesPf ds -> timesPfExp ds
      | QuotPf ds -> quotPfExp ds
      | Expr (Us) -> EClo Us
    let rec solveNumber (g, S, k) = SOME (numberExp (W.fromInt k))
    let rec fst =
      function
      | (App (u1, _), s) -> (u1, s)
      | (SClo (S, s'), s) -> fst (S, (comp (s', s)))
    let rec snd =
      function
      | (App (_, S), s) -> fst (S, s)
      | (SClo (S, s'), s) -> snd (S, (comp (s', s)))
    let rec trd =
      function
      | (App (_, S), s) -> snd (S, s)
      | (SClo (S, s'), s) -> trd (S, (comp (s', s)))
    let rec fth =
      function
      | (App (_, S), s) -> trd (S, s)
      | (SClo (S, s'), s) -> fth (S, (comp (s', s)))
    let rec toInternalPlus (g, u1, u2, u3) () = [(g, (plusExp (u1, u2, u3)))]
    let rec awakePlus (g, proof, u1, u2, u3) () =
      match solvePlus (g, (App (u1, (App (u2, (App (u3, Nil)))))), 0) with
      | SOME proof' -> Unify.unifiable (g, (proof, id), (proof', id))
      | NONE -> false__
    let rec makeCnstrPlus (g, proof, u1, u2, u3) =
      FgnCnstr ((!myID), (MyFgnCnstrRepPlus (g, proof, u1, u2, u3)))
    let rec solvePlus =
      function
      | (g, S, 0) ->
          let us1 = fst (S, id) in
          let us2 = snd (S, id) in
          let us3 = trd (S, id) in
          (match ((fromExp us1), (fromExp us2), (fromExp us3)) with
           | (Num d1, Num d2, Num d3) ->
               if ((=) d3 W.(+) (d1, d2)) && (plusCheck (d1, d2))
               then SOME (plusPfExp (d1, d2))
               else NONE
           | (Expr (us1), Num d2, Num d3) ->
               if
                 (W.(>=) (d3, d2)) &&
                   (Unify.unifiable
                      (g, us1, ((numberExp (W.(-) (d3, d2))), id)))
               then SOME (plusPfExp ((W.(-) (d3, d2)), d2))
               else NONE
           | (Num d1, Expr (us2), Num d3) ->
               if
                 (W.(>=) (d3, d1)) &&
                   (Unify.unifiable
                      (g, us2, ((numberExp (W.(-) (d3, d1))), id)))
               then SOME (plusPfExp (d1, (W.(-) (d3, d1))))
               else NONE
           | (Num d1, Num d2, Expr (us3)) ->
               if
                 (plusCheck (d1, d2)) &&
                   (Unify.unifiable
                      (g, us3, ((numberExp (W.(+) (d1, d2))), id)))
               then SOME (plusPfExp (d1, d2))
               else NONE
           | _ ->
               let proof =
                 newEVar (g, (plusExp ((EClo us1), (EClo us2), (EClo us3)))) in
               let cnstr =
                 makeCnstrPlus (g, proof, (EClo us1), (EClo us2), (EClo us3)) in
               let _ =
                 List.app (function | Us -> Unify.delay (Us, (ref cnstr)))
                   [us1; us2; us3] in
               SOME proof)
      | (g, S, n) -> NONE
    let rec toInternalTimes (g, u1, u2, u3) () =
      [(g, (timesExp (u1, u2, u3)))]
    let rec awakeTimes (g, proof, u1, u2, u3) () =
      match solveTimes (g, (App (u1, (App (u2, (App (u3, Nil)))))), 0) with
      | SOME proof' -> Unify.unifiable (g, (proof, id), (proof', id))
      | NONE -> false__
    let rec makeCnstrTimes (g, proof, u1, u2, u3) =
      FgnCnstr ((!myID), (MyFgnCnstrRepTimes (g, proof, u1, u2, u3)))
    let rec solveTimes =
      function
      | (g, S, 0) ->
          let us1 = fst (S, id) in
          let us2 = snd (S, id) in
          let us3 = trd (S, id) in
          (match ((fromExp us1), (fromExp us2), (fromExp us3)) with
           | (Num d1, Num d2, Num d3) ->
               if ((=) d3 W.( * ) (d1, d2)) && (timesCheck (d1, d2))
               then SOME (timesPfExp (d1, d2))
               else NONE
           | (Expr (us1), Num d2, Num d3) ->
               if
                 (d3 = zero) &&
                   (Unify.unifiable (g, us1, ((numberExp zero), id)))
               then SOME (timesPfExp (zero, d2))
               else
                 if
                   (W.(>) (d2, zero)) &&
                     ((W.(>) (d3, zero)) &&
                        (((W.mod__ (d3, d2)) = zero) &&
                           (Unify.unifiable
                              (g, us1, ((numberExp (W.div (d3, d2))), id)))))
                 then SOME (timesPfExp ((W.div (d3, d2)), d2))
                 else NONE
           | (Num d1, Expr (us2), Num d3) ->
               if
                 (d3 = zero) &&
                   (Unify.unifiable (g, us2, ((numberExp zero), id)))
               then SOME (timesPfExp (d1, zero))
               else
                 if
                   (W.(>) (d1, zero)) &&
                     ((W.(>) (d3, zero)) &&
                        (((W.mod__ (d3, d1)) = zero) &&
                           (Unify.unifiable
                              (g, us2, ((numberExp (W.div (d3, d1))), id)))))
                 then SOME (timesPfExp (d1, (W.div (d3, d1))))
                 else NONE
           | (Num d1, Num d2, Expr (us3)) ->
               if
                 (timesCheck (d1, d2)) &&
                   (Unify.unifiable
                      (g, us3, ((numberExp (W.( * ) (d1, d2))), id)))
               then SOME (timesPfExp (d1, d2))
               else NONE
           | _ ->
               let proof =
                 newEVar (g, (timesExp ((EClo us1), (EClo us2), (EClo us3)))) in
               let cnstr =
                 makeCnstrTimes
                   (g, proof, (EClo us1), (EClo us2), (EClo us3)) in
               let _ =
                 List.app (function | Us -> Unify.delay (Us, (ref cnstr)))
                   [us1; us2; us3] in
               SOME proof)
      | (g, S, n) -> NONE
    let rec toInternalQuot (g, u1, u2, u3) () = [(g, (quotExp (u1, u2, u3)))]
    let rec awakeQuot (g, proof, u1, u2, u3) () =
      match solveQuot (g, (App (u1, (App (u2, (App (u3, Nil)))))), 0) with
      | SOME proof' -> Unify.unifiable (g, (proof, id), (proof', id))
      | NONE -> false__
    let rec makeCnstrQuot (g, proof, u1, u2, u3) =
      FgnCnstr ((!myID), (MyFgnCnstrRepQuot (g, proof, u1, u2, u3)))
    let rec solveQuot =
      function
      | (g, S, 0) ->
          let us1 = fst (S, id) in
          let us2 = snd (S, id) in
          let us3 = trd (S, id) in
          (match ((fromExp us1), (fromExp us2), (fromExp us3)) with
           | (Num d1, Num d2, Num d3) ->
               if (quotCheck (d1, d2)) && ((=) d3 W.div (d1, d2))
               then SOME (quotPfExp (d1, d2))
               else NONE
           | (Num d1, Num d2, Expr (us3)) ->
               if
                 (quotCheck (d1, d2)) &&
                   (Unify.unifiable
                      (g, us3, ((numberExp (W.div (d1, d2))), id)))
               then SOME (quotPfExp (d1, d2))
               else NONE
           | _ ->
               let proof =
                 newEVar (g, (quotExp ((EClo us1), (EClo us2), (EClo us3)))) in
               let cnstr =
                 makeCnstrQuot (g, proof, (EClo us1), (EClo us2), (EClo us3)) in
               let _ =
                 List.app (function | Us -> Unify.delay (Us, (ref cnstr)))
                   [us1; us2; us3] in
               SOME proof)
      | (g, S, n) -> NONE
    let rec solveProvePlus (g, S, k) =
      let us1 = fst (S, id) in
      let us2 = snd (S, id) in
      let us3 = trd (S, id) in
      let us4 = fth (S, id) in
      match solvePlus
              (g,
                (App
                   ((EClo us1), (App ((EClo us2), (App ((EClo us3), Nil)))))),
                k)
      with
      | SOME (U) ->
          if Unify.unifiable (g, us4, (U, id))
          then
            SOME
              (proofPlusExp ((EClo us1), (EClo us2), (EClo us3), (EClo us4)))
          else NONE
      | NONE -> NONE
    let rec solveProveTimes (g, S, k) =
      let us1 = fst (S, id) in
      let us2 = snd (S, id) in
      let us3 = trd (S, id) in
      let us4 = fth (S, id) in
      match solveTimes
              (g,
                (App
                   ((EClo us1), (App ((EClo us2), (App ((EClo us3), Nil)))))),
                k)
      with
      | SOME (U) ->
          if Unify.unifiable (g, us4, (U, id))
          then
            SOME
              (proofTimesExp ((EClo us1), (EClo us2), (EClo us3), (EClo us4)))
          else NONE
      | NONE -> NONE
    let rec solveProveQuot (g, S, k) =
      let us1 = fst (S, id) in
      let us2 = snd (S, id) in
      let us3 = trd (S, id) in
      let us4 = fth (S, id) in
      match solveQuot
              (g,
                (App
                   ((EClo us1), (App ((EClo us2), (App ((EClo us3), Nil)))))),
                k)
      with
      | SOME (U) ->
          if Unify.unifiable (g, us4, (U, id))
          then
            SOME
              (proofQuotExp ((EClo us1), (EClo us2), (EClo us3), (EClo us4)))
          else NONE
      | NONE -> NONE
    let rec arrow (U, V) = Pi (((Dec (NONE, U)), No), V)
    let rec pi (name, U, V) = Pi (((Dec ((SOME name), U)), Maybe), V)
    let rec bvar n = Root ((BVar n), Nil)
    let rec installFgnCnstrOps () =
      let csid = !myID in
      let _ =
        FgnCnstrStd.ToInternal.install
          (csid,
            (function
             | MyFgnCnstrRepPlus (g, _, u1, u2, u3) ->
                 toInternalPlus (g, u1, u2, u3)
             | MyFgnCnstrRepTimes (g, _, u1, u2, u3) ->
                 toInternalTimes (g, u1, u2, u3)
             | MyFgnCnstrRepQuot (g, _, u1, u2, u3) ->
                 toInternalQuot (g, u1, u2, u3)
             | fc -> raise (UnexpectedFgnCnstr fc))) in
      let _ =
        FgnCnstrStd.Awake.install
          (csid,
            (function
             | MyFgnCnstrRepPlus (g, proof, u1, u2, u3) ->
                 awakePlus (g, proof, u1, u2, u3)
             | MyFgnCnstrRepTimes (g, proof, u1, u2, u3) ->
                 awakeTimes (g, proof, u1, u2, u3)
             | MyFgnCnstrRepQuot (g, proof, u1, u2, u3) ->
                 awakeQuot (g, proof, u1, u2, u3)
             | fc -> raise (UnexpectedFgnCnstr fc))) in
      let _ =
        FgnCnstrStd.Simplify.install
          (csid,
            (function
             | MyFgnCnstrRepPlus _ -> (function | () -> false__)
             | MyFgnCnstrRepTimes _ -> (function | () -> false__)
             | MyFgnCnstrRepQuot _ -> (function | () -> false__)
             | fc -> raise (UnexpectedFgnCnstr fc))) in
      ()
    let rec init (cs, installF) =
      myID := cs;
      (:=) wordID installF
        ((ConDec
            (((^) "word" Int.toString wordSize'), NONE, 0,
              (Constraint ((!myID), solveNumber)), (Uni Type), Kind)),
          (NONE : FX.fixity option), [MS.Mnil]);
      (:=) plusID installF
        ((ConDec
            ("+", NONE, 0, (Constraint ((!myID), solvePlus)),
              (arrow
                 ((word ()),
                   (arrow ((word ()), (arrow ((word ()), (Uni Type))))))),
              Kind)), NONE,
          [MS.Mapp
             ((MS.Marg (MS.Plus, (SOME "X"))),
               (MS.Mapp
                  ((MS.Marg (MS.Plus, (SOME "Y"))),
                    (MS.Mapp ((MS.Marg (MS.Minus, (SOME "Z"))), MS.Mnil)))));
          MS.Mapp
            ((MS.Marg (MS.Plus, (SOME "X"))),
              (MS.Mapp
                 ((MS.Marg (MS.Minus, (SOME "Y"))),
                   (MS.Mapp ((MS.Marg (MS.Plus, (SOME "Z"))), MS.Mnil)))));
          MS.Mapp
            ((MS.Marg (MS.Minus, (SOME "X"))),
              (MS.Mapp
                 ((MS.Marg (MS.Plus, (SOME "Y"))),
                   (MS.Mapp ((MS.Marg (MS.Plus, (SOME "Z"))), MS.Mnil)))))]);
      (:=) timesID installF
        ((ConDec
            ("*", NONE, 0, (Constraint ((!myID), solveTimes)),
              (arrow
                 ((word ()),
                   (arrow ((word ()), (arrow ((word ()), (Uni Type))))))),
              Kind)), NONE,
          [MS.Mapp
             ((MS.Marg (MS.Plus, (SOME "X"))),
               (MS.Mapp
                  ((MS.Marg (MS.Plus, (SOME "Y"))),
                    (MS.Mapp ((MS.Marg (MS.Minus, (SOME "Z"))), MS.Mnil)))));
          MS.Mapp
            ((MS.Marg (MS.Plus, (SOME "X"))),
              (MS.Mapp
                 ((MS.Marg (MS.Minus, (SOME "Y"))),
                   (MS.Mapp ((MS.Marg (MS.Plus, (SOME "Z"))), MS.Mnil)))));
          MS.Mapp
            ((MS.Marg (MS.Minus, (SOME "X"))),
              (MS.Mapp
                 ((MS.Marg (MS.Plus, (SOME "Y"))),
                   (MS.Mapp ((MS.Marg (MS.Plus, (SOME "Z"))), MS.Mnil)))))]);
      (:=) quotID installF
        ((ConDec
            ("/", NONE, 0, (Constraint ((!myID), solveQuot)),
              (arrow
                 ((word ()),
                   (arrow ((word ()), (arrow ((word ()), (Uni Type))))))),
              Kind)), NONE,
          [MS.Mapp
             ((MS.Marg (MS.Plus, (SOME "X"))),
               (MS.Mapp
                  ((MS.Marg (MS.Plus, (SOME "Y"))),
                    (MS.Mapp ((MS.Marg (MS.Minus, (SOME "Z"))), MS.Mnil)))));
          MS.Mapp
            ((MS.Marg (MS.Plus, (SOME "X"))),
              (MS.Mapp
                 ((MS.Marg (MS.Minus, (SOME "Y"))),
                   (MS.Mapp ((MS.Marg (MS.Plus, (SOME "Z"))), MS.Mnil)))))]);
      (:=) provePlusID installF
        ((ConDec
            ("prove+", NONE, 0, (Constraint ((!myID), solveProvePlus)),
              (pi
                 ("X", (word ()),
                   (pi
                      ("Y", (word ()),
                        (pi
                           ("Z", (word ()),
                             (pi
                                ("P",
                                  (plusExp ((bvar 3), (bvar 2), (bvar 1))),
                                  (Uni Type))))))))), Kind)), NONE,
          [MS.Mapp
             ((MS.Marg (MS.Star, (SOME "X"))),
               (MS.Mapp
                  ((MS.Marg (MS.Star, (SOME "Y"))),
                    (MS.Mapp
                       ((MS.Marg (MS.Star, (SOME "Z"))),
                         (MS.Mapp ((MS.Marg (MS.Star, (SOME "P"))), MS.Mnil)))))))]);
      (:=) proofPlusID installF
        ((ConDec
            ("proof+", NONE, 0, Normal,
              (pi
                 ("X", (word ()),
                   (pi
                      ("Y", (word ()),
                        (pi
                           ("Z", (word ()),
                             (pi
                                ("P",
                                  (plusExp ((bvar 3), (bvar 2), (bvar 1))),
                                  (provePlusExp
                                     ((bvar 4), (bvar 3), (bvar 2), (bvar 1))))))))))),
              Type)), NONE, nil);
      (:=) proveTimesID installF
        ((ConDec
            ("prove*", NONE, 0, (Constraint ((!myID), solveProveTimes)),
              (pi
                 ("X", (word ()),
                   (pi
                      ("Y", (word ()),
                        (pi
                           ("Z", (word ()),
                             (pi
                                ("P",
                                  (timesExp ((bvar 3), (bvar 2), (bvar 1))),
                                  (Uni Type))))))))), Kind)), NONE,
          [MS.Mapp
             ((MS.Marg (MS.Star, (SOME "X"))),
               (MS.Mapp
                  ((MS.Marg (MS.Star, (SOME "Y"))),
                    (MS.Mapp
                       ((MS.Marg (MS.Star, (SOME "Z"))),
                         (MS.Mapp ((MS.Marg (MS.Star, (SOME "P"))), MS.Mnil)))))))]);
      (:=) proofTimesID installF
        ((ConDec
            ("proof*", NONE, 0, Normal,
              (pi
                 ("X", (word ()),
                   (pi
                      ("Y", (word ()),
                        (pi
                           ("Z", (word ()),
                             (pi
                                ("P",
                                  (timesExp ((bvar 3), (bvar 2), (bvar 1))),
                                  (proveTimesExp
                                     ((bvar 4), (bvar 3), (bvar 2), (bvar 1))))))))))),
              Type)), NONE, nil);
      (:=) proveQuotID installF
        ((ConDec
            ("prove/", NONE, 0, (Constraint ((!myID), solveProveQuot)),
              (pi
                 ("X", (word ()),
                   (pi
                      ("Y", (word ()),
                        (pi
                           ("Z", (word ()),
                             (pi
                                ("P",
                                  (quotExp ((bvar 3), (bvar 2), (bvar 1))),
                                  (Uni Type))))))))), Kind)), NONE,
          [MS.Mapp
             ((MS.Marg (MS.Star, (SOME "X"))),
               (MS.Mapp
                  ((MS.Marg (MS.Star, (SOME "Y"))),
                    (MS.Mapp
                       ((MS.Marg (MS.Star, (SOME "Z"))),
                         (MS.Mapp ((MS.Marg (MS.Star, (SOME "P"))), MS.Mnil)))))))]);
      (:=) proofQuotID installF
        ((ConDec
            ("proof/", NONE, 0, Normal,
              (pi
                 ("X", (word ()),
                   (pi
                      ("Y", (word ()),
                        (pi
                           ("Z", (word ()),
                             (pi
                                ("P",
                                  (quotExp ((bvar 3), (bvar 2), (bvar 1))),
                                  (proveQuotExp
                                     ((bvar 4), (bvar 3), (bvar 2), (bvar 1))))))))))),
              Type)), NONE, nil);
      installFgnCnstrOps ();
      ()
    let ((solver)(*! structure CSManager = CSManager !*)
      (* CSManager.ModeSyn *)(* FgnCnstr Representation: (g, proof, u1, u2, u3) *)
      (* numCheck (d) = true iff d <= max *)(* plusCheck (d1, d2) = true iff d1 + d2 <= max *)
      (* timesCheck (d1, d2) = true iff d1 * d2 <= max *)
      (* quotCheck (d1, d2) = true iff  d2 != zero *)
      (* constraint solver ID of this module *)(* constant ID of the type family constant "wordXX" *)
      (* constant ID's of the operators defined by this module *)
      (* + : wordXX -> wordXX -> wordXX -> type *)(* * : wordXX -> wordXX -> wordXX -> type *)
      (* / : wordXX -> wordXX -> wordXX -> type *)(* constant ID's of the proof object generators and their proof objects *)
      (* (these are used as workaround for the lack of sigma types in Twelf)  *)
      (* prove+ : {U}{V}{W} + U V W -> type *)(* prove* : {U}{V}{W} * U V W -> type *)
      (* prove/ : {U}{V}{W} / U V W -> type *)(* proof* : {U}{V}{W}{P} prove+ U V W P *)
      (* proof* : {U}{V}{W}{P} prove* U V W P *)(* proof/ : {U}{V}{W}{P} prove/ U V W P *)
      (* scanNumber (str) = numOpt

       Invariant:
         numOpt = SOME(n) if str is the decimal representation of the number n
                = NONE otherwise
    *)
      (* parseNumber str = SOME(conDec) or NONE

       Invariant:
       If str parses to the number n
       then conDec is the (foreign) constant declaration of n
    *)
      (* parseBinopPf operator string = SOME(conDec) or NONE

       Invariant:
       If string parses to the proof object of n1<operator>n2
       then conDec is the (foreign) constant declaration of n1<operator>n2
    *)
      (* Term                       *)(* Term ::= n                 *)
      (*        | n1+n2             *)(*        | n1*n2             *)
      (*        | n1/n2             *)(*        | <Expr>            *)
      (* fromExpW (U, s) = t

       Invariant:
       If   g' |- s : g    g |- U : V    (U,s)  in whnf
       then t is the internal representation of U[s] as term
    *)
      (* fromExp (U, s) = t

       Invariant:
       If   g' |- s : g    g |- U : V
       then t is the internal representation of U[s] as term
    *)
      (* toExp t = U

       Invariant:
       g |- U : V and U is the Twelf syntax conversion of t
    *)
      (* fst (S, s) = u1, the first argument in S[s] *)
      (* snd (S, s) = u2, the second argument in S[s] *)
      (* trd (S, s) = u1, the third argument in S[s] *)
      (* fth (S, s) = u1, the fourth argument in S[s] *)
      (* constraint constructor *)(* solvePlus (g, S, n) tries to find the n-th solution to
          g |- '+' @ S : type
    *)
      (* solveTimes (g, S, n) tries to find the n-th solution to
         g |- '*' @ S : type
    *)
      (* constraint constructor *)(* solveQuot (g, S, n) tries to find the n-th solution to
         g |- '/' @ S : type
    *)
      (* solveProvePlus (g, S, n) tries to find the n-th solution to
         g |- prove+ @ S : type
    *)
      (* solveProveTimes (g, S, n) tries to find the n-th solution to
         g |- prove* @ S : type
    *)
      (* solveProveQuot (g, S, n) tries to find the n-th solution to
         g |- prove/ @ S : type
    *)
      (* init (cs, installFunction) = ()
       Initialize the constraint solver.
       installFunction is used to add its signature symbols.
    *))
      =
      {
        name = ((^) "word" Int.toString wordSize');
        keywords = "numbers,equality";
        needs = ["Unify"];
        fgnConst = (SOME { parse = parseAll });
        init;
        reset = (function | () -> ());
        mark = (function | () -> ());
        unwind = (function | () -> ())
      }
  end ;;
