
(* Solver for machine integers *)
(* Author: Roberto Virga *)
module CSIntWord(CSIntWord:sig
                             (*! structure IntSyn : INTSYN !*)
                             module Whnf : WHNF
                             module Unify : UNIFY
                             (*! sharing Whnf.IntSyn = IntSyn !*)
                             (*! sharing Unify.IntSyn = IntSyn !*)
                             (*! structure CSManager : CS_MANAGER !*)
                             (*! sharing CSManager.IntSyn = IntSyn !*)
                             val wordSize : int
                           end) : CS =
  struct
    (*! structure CSManager = CSManager !*)
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
    let rec plusExp (__u, __v, W) =
      Root ((Const (!plusID)), (App (__u, (App (__v, (App (W, Nil)))))))
    let rec timesExp (__u, __v, W) =
      Root ((Const (!timesID)), (App (__u, (App (__v, (App (W, Nil)))))))
    let rec quotExp (__u, __v, W) =
      Root ((Const (!quotID)), (App (__u, (App (__v, (App (W, Nil)))))))
    let provePlusID = (ref (-1) : cid ref)
    let proveTimesID = (ref (-1) : cid ref)
    let proveQuotID = (ref (-1) : cid ref)
    let proofPlusID = (ref (-1) : cid ref)
    let proofTimesID = (ref (-1) : cid ref)
    let proofQuotID = (ref (-1) : cid ref)
    let rec provePlusExp (__u, __v, W, P) =
      Root
        ((Const (!provePlusID)),
          (App (__u, (App (__v, (App (W, (App (P, Nil)))))))))
    let rec proofPlusExp (__u, __v, W, P) =
      Root
        ((Const (!proofPlusID)),
          (App (__u, (App (__v, (App (W, (App (P, Nil)))))))))
    let rec proofTimesExp (__u, __v, W, P) =
      Root
        ((Const (!proofTimesID)),
          (App (__u, (App (__v, (App (W, (App (P, Nil)))))))))
    let rec proveTimesExp (__u, __v, W, P) =
      Root
        ((Const (!proveTimesID)),
          (App (__u, (App (__v, (App (W, (App (P, Nil)))))))))
    let rec proveQuotExp (__u, __v, W, P) =
      Root
        ((Const (!proveQuotID)),
          (App (__u, (App (__v, (App (W, (App (P, Nil)))))))))
    let rec proofQuotExp (__u, __v, W, P) =
      Root
        ((Const (!proofQuotID)),
          (App (__u, (App (__v, (App (W, (App (P, Nil)))))))))
    let rec numberConDec d =
      ConDec ((W.fmt StringCvt.DEC d), None, 0, Normal, (word ()), Type)
    let rec numberExp d = Root ((FgnConst ((!myID), (numberConDec d))), Nil)
    let rec scanNumber str =
      let rec check =
        function
        | _::_ as chars -> List.all Char.isDigit chars
        | nil -> false__ in
      if check (String.explode str)
      then
        match StringCvt.scanString (W.scan StringCvt.DEC) str with
        | Some d -> (if numCheck d then Some d else None)
        | None -> None
      else None
    let rec parseNumber string =
      match scanNumber string with
      | Some d -> Some (numberConDec d)
      | None -> None
    let rec plusPfConDec (d1, d2) =
      let d3 = W.(+) (d1, d2) in
      ConDec
        (((^) ((W.fmt StringCvt.DEC d1) ^ "+") W.fmt StringCvt.DEC d2), None,
          0, Normal,
          (plusExp ((numberExp d1), (numberExp d2), (numberExp d3))), Type)
    let rec plusPfExp ds =
      Root ((FgnConst ((!myID), (plusPfConDec ds))), Nil)
    let rec timesPfConDec (d1, d2) =
      let d3 = W.( * ) (d1, d2) in
      ConDec
        (((^) ((W.fmt StringCvt.DEC d1) ^ "*") W.fmt StringCvt.DEC d2), None,
          0, Normal,
          (timesExp ((numberExp d1), (numberExp d2), (numberExp d3))), Type)
    let rec timesPfExp ds =
      Root ((FgnConst ((!myID), (timesPfConDec ds))), Nil)
    let rec quotPfConDec (d1, d2) =
      let d3 = W.div (d1, d2) in
      ConDec
        (((^) ((W.fmt StringCvt.DEC d1) ^ "/") W.fmt StringCvt.DEC d2), None,
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
           | (Some d1, Some d2) -> Some (d1, d2)
           | _ -> None)
      | _ -> None
    let rec parseBinopPf oper string =
      match (oper, (scanBinopPf oper string)) with
      | ('+', Some ds) -> Some (plusPfConDec ds)
      | ('*', Some ds) -> Some (timesPfConDec ds)
      | ('/', Some ds) -> Some (quotPfConDec ds)
      | _ -> None
    let parsePlusPf = parseBinopPf '+'
    let parseTimesPf = parseBinopPf '*'
    let parseQuotPf = parseBinopPf '/'
    let rec parseAll string =
      match parseNumber string with
      | Some conDec -> Some conDec
      | None ->
          (match parsePlusPf string with
           | Some conDec -> Some conDec
           | None ->
               (match parseTimesPf string with
                | Some conDec -> Some conDec
                | None -> parseQuotPf string))
    type __FixTerm =
      | Num of W.word 
      | PlusPf of (W.word * W.word) 
      | TimesPf of (W.word * W.word) 
      | QuotPf of (W.word * W.word) 
      | Expr of (__Exp * __Sub) 
    let rec fromExpW =
      function
      | (Root (FgnConst (cs, conDec), _), _) as __Us ->
          if (!) ((=) cs) myID
          then
            let string = conDecName conDec in
            (match scanNumber string with
             | Some d -> Num d
             | None ->
                 (match scanBinopPf '/' string with
                  | Some ds -> QuotPf ds
                  | None ->
                      (match scanBinopPf '+' string with
                       | Some ds -> PlusPf ds
                       | None ->
                           (match scanBinopPf '*' string with
                            | Some ds -> TimesPf ds
                            | None -> Expr __Us))))
          else Expr __Us
      | (Root (Def d, _), _) as __Us -> fromExpW (Whnf.expandDef __Us)
      | __Us -> Expr __Us
    let rec fromExp (__Us) = fromExpW (Whnf.whnf __Us)
    let rec toExp =
      function
      | Num d -> numberExp d
      | PlusPf ds -> plusPfExp ds
      | TimesPf ds -> timesPfExp ds
      | QuotPf ds -> quotPfExp ds
      | Expr (__Us) -> EClo __Us
    let rec solveNumber (__g, S, k) = Some (numberExp (W.fromInt k))
    let rec fst =
      function
      | (App (__U1, _), s) -> (__U1, s)
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
    let rec toInternalPlus (__g, __U1, __U2, __U3) () = [(__g, (plusExp (__U1, __U2, __U3)))]
    let rec awakePlus (__g, proof, __U1, __U2, __U3) () =
      match solvePlus (__g, (App (__U1, (App (__U2, (App (__U3, Nil)))))), 0) with
      | Some proof' -> Unify.unifiable (__g, (proof, id), (proof', id))
      | None -> false__
    let rec makeCnstrPlus (__g, proof, __U1, __U2, __U3) =
      FgnCnstr ((!myID), (MyFgnCnstrRepPlus (__g, proof, __U1, __U2, __U3)))
    let rec solvePlus =
      function
      | (__g, S, 0) ->
          let us1 = fst (S, id) in
          let us2 = snd (S, id) in
          let us3 = trd (S, id) in
          (match ((fromExp us1), (fromExp us2), (fromExp us3)) with
           | (Num d1, Num d2, Num d3) ->
               if ((=) d3 W.(+) (d1, d2)) && (plusCheck (d1, d2))
               then Some (plusPfExp (d1, d2))
               else None
           | (Expr (us1), Num d2, Num d3) ->
               if
                 (W.(>=) (d3, d2)) &&
                   (Unify.unifiable
                      (__g, us1, ((numberExp (W.(-) (d3, d2))), id)))
               then Some (plusPfExp ((W.(-) (d3, d2)), d2))
               else None
           | (Num d1, Expr (us2), Num d3) ->
               if
                 (W.(>=) (d3, d1)) &&
                   (Unify.unifiable
                      (__g, us2, ((numberExp (W.(-) (d3, d1))), id)))
               then Some (plusPfExp (d1, (W.(-) (d3, d1))))
               else None
           | (Num d1, Num d2, Expr (us3)) ->
               if
                 (plusCheck (d1, d2)) &&
                   (Unify.unifiable
                      (__g, us3, ((numberExp (W.(+) (d1, d2))), id)))
               then Some (plusPfExp (d1, d2))
               else None
           | _ ->
               let proof =
                 newEVar (__g, (plusExp ((EClo us1), (EClo us2), (EClo us3)))) in
               let cnstr =
                 makeCnstrPlus (__g, proof, (EClo us1), (EClo us2), (EClo us3)) in
               let _ =
                 List.app (function | __Us -> Unify.delay (__Us, (ref cnstr)))
                   [us1; us2; us3] in
               Some proof)
      | (__g, S, n) -> None
    let rec toInternalTimes (__g, __U1, __U2, __U3) () =
      [(__g, (timesExp (__U1, __U2, __U3)))]
    let rec awakeTimes (__g, proof, __U1, __U2, __U3) () =
      match solveTimes (__g, (App (__U1, (App (__U2, (App (__U3, Nil)))))), 0) with
      | Some proof' -> Unify.unifiable (__g, (proof, id), (proof', id))
      | None -> false__
    let rec makeCnstrTimes (__g, proof, __U1, __U2, __U3) =
      FgnCnstr ((!myID), (MyFgnCnstrRepTimes (__g, proof, __U1, __U2, __U3)))
    let rec solveTimes =
      function
      | (__g, S, 0) ->
          let us1 = fst (S, id) in
          let us2 = snd (S, id) in
          let us3 = trd (S, id) in
          (match ((fromExp us1), (fromExp us2), (fromExp us3)) with
           | (Num d1, Num d2, Num d3) ->
               if ((=) d3 W.( * ) (d1, d2)) && (timesCheck (d1, d2))
               then Some (timesPfExp (d1, d2))
               else None
           | (Expr (us1), Num d2, Num d3) ->
               if
                 (d3 = zero) &&
                   (Unify.unifiable (__g, us1, ((numberExp zero), id)))
               then Some (timesPfExp (zero, d2))
               else
                 if
                   (W.(>) (d2, zero)) &&
                     ((W.(>) (d3, zero)) &&
                        (((W.mod__ (d3, d2)) = zero) &&
                           (Unify.unifiable
                              (__g, us1, ((numberExp (W.div (d3, d2))), id)))))
                 then Some (timesPfExp ((W.div (d3, d2)), d2))
                 else None
           | (Num d1, Expr (us2), Num d3) ->
               if
                 (d3 = zero) &&
                   (Unify.unifiable (__g, us2, ((numberExp zero), id)))
               then Some (timesPfExp (d1, zero))
               else
                 if
                   (W.(>) (d1, zero)) &&
                     ((W.(>) (d3, zero)) &&
                        (((W.mod__ (d3, d1)) = zero) &&
                           (Unify.unifiable
                              (__g, us2, ((numberExp (W.div (d3, d1))), id)))))
                 then Some (timesPfExp (d1, (W.div (d3, d1))))
                 else None
           | (Num d1, Num d2, Expr (us3)) ->
               if
                 (timesCheck (d1, d2)) &&
                   (Unify.unifiable
                      (__g, us3, ((numberExp (W.( * ) (d1, d2))), id)))
               then Some (timesPfExp (d1, d2))
               else None
           | _ ->
               let proof =
                 newEVar (__g, (timesExp ((EClo us1), (EClo us2), (EClo us3)))) in
               let cnstr =
                 makeCnstrTimes
                   (__g, proof, (EClo us1), (EClo us2), (EClo us3)) in
               let _ =
                 List.app (function | __Us -> Unify.delay (__Us, (ref cnstr)))
                   [us1; us2; us3] in
               Some proof)
      | (__g, S, n) -> None
    let rec toInternalQuot (__g, __U1, __U2, __U3) () = [(__g, (quotExp (__U1, __U2, __U3)))]
    let rec awakeQuot (__g, proof, __U1, __U2, __U3) () =
      match solveQuot (__g, (App (__U1, (App (__U2, (App (__U3, Nil)))))), 0) with
      | Some proof' -> Unify.unifiable (__g, (proof, id), (proof', id))
      | None -> false__
    let rec makeCnstrQuot (__g, proof, __U1, __U2, __U3) =
      FgnCnstr ((!myID), (MyFgnCnstrRepQuot (__g, proof, __U1, __U2, __U3)))
    let rec solveQuot =
      function
      | (__g, S, 0) ->
          let us1 = fst (S, id) in
          let us2 = snd (S, id) in
          let us3 = trd (S, id) in
          (match ((fromExp us1), (fromExp us2), (fromExp us3)) with
           | (Num d1, Num d2, Num d3) ->
               if (quotCheck (d1, d2)) && ((=) d3 W.div (d1, d2))
               then Some (quotPfExp (d1, d2))
               else None
           | (Num d1, Num d2, Expr (us3)) ->
               if
                 (quotCheck (d1, d2)) &&
                   (Unify.unifiable
                      (__g, us3, ((numberExp (W.div (d1, d2))), id)))
               then Some (quotPfExp (d1, d2))
               else None
           | _ ->
               let proof =
                 newEVar (__g, (quotExp ((EClo us1), (EClo us2), (EClo us3)))) in
               let cnstr =
                 makeCnstrQuot (__g, proof, (EClo us1), (EClo us2), (EClo us3)) in
               let _ =
                 List.app (function | __Us -> Unify.delay (__Us, (ref cnstr)))
                   [us1; us2; us3] in
               Some proof)
      | (__g, S, n) -> None
    let rec solveProvePlus (__g, S, k) =
      let us1 = fst (S, id) in
      let us2 = snd (S, id) in
      let us3 = trd (S, id) in
      let us4 = fth (S, id) in
      match solvePlus
              (__g,
                (App
                   ((EClo us1), (App ((EClo us2), (App ((EClo us3), Nil)))))),
                k)
      with
      | Some (__u) ->
          if Unify.unifiable (__g, us4, (__u, id))
          then
            Some
              (proofPlusExp ((EClo us1), (EClo us2), (EClo us3), (EClo us4)))
          else None
      | None -> None
    let rec solveProveTimes (__g, S, k) =
      let us1 = fst (S, id) in
      let us2 = snd (S, id) in
      let us3 = trd (S, id) in
      let us4 = fth (S, id) in
      match solveTimes
              (__g,
                (App
                   ((EClo us1), (App ((EClo us2), (App ((EClo us3), Nil)))))),
                k)
      with
      | Some (__u) ->
          if Unify.unifiable (__g, us4, (__u, id))
          then
            Some
              (proofTimesExp ((EClo us1), (EClo us2), (EClo us3), (EClo us4)))
          else None
      | None -> None
    let rec solveProveQuot (__g, S, k) =
      let us1 = fst (S, id) in
      let us2 = snd (S, id) in
      let us3 = trd (S, id) in
      let us4 = fth (S, id) in
      match solveQuot
              (__g,
                (App
                   ((EClo us1), (App ((EClo us2), (App ((EClo us3), Nil)))))),
                k)
      with
      | Some (__u) ->
          if Unify.unifiable (__g, us4, (__u, id))
          then
            Some
              (proofQuotExp ((EClo us1), (EClo us2), (EClo us3), (EClo us4)))
          else None
      | None -> None
    let rec arrow (__u, __v) = Pi (((Dec (None, __u)), No), __v)
    let rec pi (name, __u, __v) = Pi (((Dec ((Some name), __u)), Maybe), __v)
    let rec bvar n = Root ((BVar n), Nil)
    let rec installFgnCnstrOps () =
      let csid = !myID in
      let _ =
        FgnCnstrStd.ToInternal.install
          (csid,
            (function
             | MyFgnCnstrRepPlus (__g, _, __U1, __U2, __U3) ->
                 toInternalPlus (__g, __U1, __U2, __U3)
             | MyFgnCnstrRepTimes (__g, _, __U1, __U2, __U3) ->
                 toInternalTimes (__g, __U1, __U2, __U3)
             | MyFgnCnstrRepQuot (__g, _, __U1, __U2, __U3) ->
                 toInternalQuot (__g, __U1, __U2, __U3)
             | fc -> raise (UnexpectedFgnCnstr fc))) in
      let _ =
        FgnCnstrStd.Awake.install
          (csid,
            (function
             | MyFgnCnstrRepPlus (__g, proof, __U1, __U2, __U3) ->
                 awakePlus (__g, proof, __U1, __U2, __U3)
             | MyFgnCnstrRepTimes (__g, proof, __U1, __U2, __U3) ->
                 awakeTimes (__g, proof, __U1, __U2, __U3)
             | MyFgnCnstrRepQuot (__g, proof, __U1, __U2, __U3) ->
                 awakeQuot (__g, proof, __U1, __U2, __U3)
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
            (((^) "word" Int.toString wordSize'), None, 0,
              (Constraint ((!myID), solveNumber)), (Uni Type), Kind)),
          (None : FX.fixity option), [MS.Mnil]);
      (:=) plusID installF
        ((ConDec
            ("+", None, 0, (Constraint ((!myID), solvePlus)),
              (arrow
                 ((word ()),
                   (arrow ((word ()), (arrow ((word ()), (Uni Type))))))),
              Kind)), None,
          [MS.Mapp
             ((MS.Marg (MS.Plus, (Some "x"))),
               (MS.Mapp
                  ((MS.Marg (MS.Plus, (Some "y"))),
                    (MS.Mapp ((MS.Marg (MS.Minus, (Some "Z"))), MS.Mnil)))));
          MS.Mapp
            ((MS.Marg (MS.Plus, (Some "x"))),
              (MS.Mapp
                 ((MS.Marg (MS.Minus, (Some "y"))),
                   (MS.Mapp ((MS.Marg (MS.Plus, (Some "Z"))), MS.Mnil)))));
          MS.Mapp
            ((MS.Marg (MS.Minus, (Some "x"))),
              (MS.Mapp
                 ((MS.Marg (MS.Plus, (Some "y"))),
                   (MS.Mapp ((MS.Marg (MS.Plus, (Some "Z"))), MS.Mnil)))))]);
      (:=) timesID installF
        ((ConDec
            ("*", None, 0, (Constraint ((!myID), solveTimes)),
              (arrow
                 ((word ()),
                   (arrow ((word ()), (arrow ((word ()), (Uni Type))))))),
              Kind)), None,
          [MS.Mapp
             ((MS.Marg (MS.Plus, (Some "x"))),
               (MS.Mapp
                  ((MS.Marg (MS.Plus, (Some "y"))),
                    (MS.Mapp ((MS.Marg (MS.Minus, (Some "Z"))), MS.Mnil)))));
          MS.Mapp
            ((MS.Marg (MS.Plus, (Some "x"))),
              (MS.Mapp
                 ((MS.Marg (MS.Minus, (Some "y"))),
                   (MS.Mapp ((MS.Marg (MS.Plus, (Some "Z"))), MS.Mnil)))));
          MS.Mapp
            ((MS.Marg (MS.Minus, (Some "x"))),
              (MS.Mapp
                 ((MS.Marg (MS.Plus, (Some "y"))),
                   (MS.Mapp ((MS.Marg (MS.Plus, (Some "Z"))), MS.Mnil)))))]);
      (:=) quotID installF
        ((ConDec
            ("/", None, 0, (Constraint ((!myID), solveQuot)),
              (arrow
                 ((word ()),
                   (arrow ((word ()), (arrow ((word ()), (Uni Type))))))),
              Kind)), None,
          [MS.Mapp
             ((MS.Marg (MS.Plus, (Some "x"))),
               (MS.Mapp
                  ((MS.Marg (MS.Plus, (Some "y"))),
                    (MS.Mapp ((MS.Marg (MS.Minus, (Some "Z"))), MS.Mnil)))));
          MS.Mapp
            ((MS.Marg (MS.Plus, (Some "x"))),
              (MS.Mapp
                 ((MS.Marg (MS.Minus, (Some "y"))),
                   (MS.Mapp ((MS.Marg (MS.Plus, (Some "Z"))), MS.Mnil)))))]);
      (:=) provePlusID installF
        ((ConDec
            ("prove+", None, 0, (Constraint ((!myID), solveProvePlus)),
              (pi
                 ("x", (word ()),
                   (pi
                      ("y", (word ()),
                        (pi
                           ("Z", (word ()),
                             (pi
                                ("P",
                                  (plusExp ((bvar 3), (bvar 2), (bvar 1))),
                                  (Uni Type))))))))), Kind)), None,
          [MS.Mapp
             ((MS.Marg (MS.Star, (Some "x"))),
               (MS.Mapp
                  ((MS.Marg (MS.Star, (Some "y"))),
                    (MS.Mapp
                       ((MS.Marg (MS.Star, (Some "Z"))),
                         (MS.Mapp ((MS.Marg (MS.Star, (Some "P"))), MS.Mnil)))))))]);
      (:=) proofPlusID installF
        ((ConDec
            ("proof+", None, 0, Normal,
              (pi
                 ("x", (word ()),
                   (pi
                      ("y", (word ()),
                        (pi
                           ("Z", (word ()),
                             (pi
                                ("P",
                                  (plusExp ((bvar 3), (bvar 2), (bvar 1))),
                                  (provePlusExp
                                     ((bvar 4), (bvar 3), (bvar 2), (bvar 1))))))))))),
              Type)), None, nil);
      (:=) proveTimesID installF
        ((ConDec
            ("prove*", None, 0, (Constraint ((!myID), solveProveTimes)),
              (pi
                 ("x", (word ()),
                   (pi
                      ("y", (word ()),
                        (pi
                           ("Z", (word ()),
                             (pi
                                ("P",
                                  (timesExp ((bvar 3), (bvar 2), (bvar 1))),
                                  (Uni Type))))))))), Kind)), None,
          [MS.Mapp
             ((MS.Marg (MS.Star, (Some "x"))),
               (MS.Mapp
                  ((MS.Marg (MS.Star, (Some "y"))),
                    (MS.Mapp
                       ((MS.Marg (MS.Star, (Some "Z"))),
                         (MS.Mapp ((MS.Marg (MS.Star, (Some "P"))), MS.Mnil)))))))]);
      (:=) proofTimesID installF
        ((ConDec
            ("proof*", None, 0, Normal,
              (pi
                 ("x", (word ()),
                   (pi
                      ("y", (word ()),
                        (pi
                           ("Z", (word ()),
                             (pi
                                ("P",
                                  (timesExp ((bvar 3), (bvar 2), (bvar 1))),
                                  (proveTimesExp
                                     ((bvar 4), (bvar 3), (bvar 2), (bvar 1))))))))))),
              Type)), None, nil);
      (:=) proveQuotID installF
        ((ConDec
            ("prove/", None, 0, (Constraint ((!myID), solveProveQuot)),
              (pi
                 ("x", (word ()),
                   (pi
                      ("y", (word ()),
                        (pi
                           ("Z", (word ()),
                             (pi
                                ("P",
                                  (quotExp ((bvar 3), (bvar 2), (bvar 1))),
                                  (Uni Type))))))))), Kind)), None,
          [MS.Mapp
             ((MS.Marg (MS.Star, (Some "x"))),
               (MS.Mapp
                  ((MS.Marg (MS.Star, (Some "y"))),
                    (MS.Mapp
                       ((MS.Marg (MS.Star, (Some "Z"))),
                         (MS.Mapp ((MS.Marg (MS.Star, (Some "P"))), MS.Mnil)))))))]);
      (:=) proofQuotID installF
        ((ConDec
            ("proof/", None, 0, Normal,
              (pi
                 ("x", (word ()),
                   (pi
                      ("y", (word ()),
                        (pi
                           ("Z", (word ()),
                             (pi
                                ("P",
                                  (quotExp ((bvar 3), (bvar 2), (bvar 1))),
                                  (proveQuotExp
                                     ((bvar 4), (bvar 3), (bvar 2), (bvar 1))))))))))),
              Type)), None, nil);
      installFgnCnstrOps ();
      ()
    (* CSManager.ModeSyn *)
    (* FgnCnstr Representation: (__g, proof, __U1, __U2, __U3) *)
    (* numCheck (d) = true iff d <= max *)
    (* plusCheck (d1, d2) = true iff d1 + d2 <= max *)
    (* timesCheck (d1, d2) = true iff d1 * d2 <= max *)
    (* quotCheck (d1, d2) = true iff  d2 != zero *)
    (* constraint solver ID of this module *)
    (* constant ID of the type family constant "wordXX" *)
    (* constant ID's of the operators defined by this module *)
    (* + : wordXX -> wordXX -> wordXX -> type *)
    (* * : wordXX -> wordXX -> wordXX -> type *)
    (* / : wordXX -> wordXX -> wordXX -> type *)
    (* constant ID's of the proof object generators and their proof objects *)
    (* (these are used as workaround for the lack of sigma types in Twelf)  *)
    (* prove+ : {__u}{__v}{W} + __u __v W -> type *)
    (* prove* : {__u}{__v}{W} * __u __v W -> type *)
    (* prove/ : {__u}{__v}{W} / __u __v W -> type *)
    (* proof* : {__u}{__v}{W}{P} prove+ __u __v W P *)
    (* proof* : {__u}{__v}{W}{P} prove* __u __v W P *)
    (* proof/ : {__u}{__v}{W}{P} prove/ __u __v W P *)
    (* scanNumber (str) = numOpt

       Invariant:
         numOpt = Some(n) if str is the decimal representation of the number n
                = None otherwise
    *)
    (* parseNumber str = Some(conDec) or None

       Invariant:
       If str parses to the number n
       then conDec is the (foreign) constant declaration of n
    *)
    (* parseBinopPf operator string = Some(conDec) or None

       Invariant:
       If string parses to the proof object of n1<operator>n2
       then conDec is the (foreign) constant declaration of n1<operator>n2
    *)
    (* Term                       *)
    (* Term ::= n                 *)
    (*        | n1+n2             *)
    (*        | n1*n2             *)
    (*        | n1/n2             *)
    (*        | <Expr>            *)
    (* fromExpW (__u, s) = t

       Invariant:
       If   __g' |- s : __g    __g |- __u : __v    (__u,s)  in whnf
       then t is the internal representation of __u[s] as term
    *)
    (* fromExp (__u, s) = t

       Invariant:
       If   __g' |- s : __g    __g |- __u : __v
       then t is the internal representation of __u[s] as term
    *)
    (* toExp t = __u

       Invariant:
       __g |- __u : __v and __u is the Twelf syntax conversion of t
    *)
    (* fst (S, s) = __U1, the first argument in S[s] *)
    (* snd (S, s) = __U2, the second argument in S[s] *)
    (* trd (S, s) = __U1, the third argument in S[s] *)
    (* fth (S, s) = __U1, the fourth argument in S[s] *)
    (* constraint constructor *)
    (* solvePlus (__g, S, n) tries to find the n-th solution to
          __g |- '+' @ S : type
    *)
    (* solveTimes (__g, S, n) tries to find the n-th solution to
         __g |- '*' @ S : type
    *)
    (* constraint constructor *)
    (* solveQuot (__g, S, n) tries to find the n-th solution to
         __g |- '/' @ S : type
    *)
    (* solveProvePlus (__g, S, n) tries to find the n-th solution to
         __g |- prove+ @ S : type
    *)
    (* solveProveTimes (__g, S, n) tries to find the n-th solution to
         __g |- prove* @ S : type
    *)
    (* solveProveQuot (__g, S, n) tries to find the n-th solution to
         __g |- prove/ @ S : type
    *)
    (* init (cs, installFunction) = ()
       Initialize the constraint solver.
       installFunction is used to add its signature symbols.
    *)
    let solver =
      {
        name = ((^) "word" Int.toString wordSize');
        keywords = "numbers,equality";
        needs = ["Unify"];
        fgnConst = (Some { parse = parseAll });
        init;
        reset = (function | () -> ());
        mark = (function | () -> ());
        unwind = (function | () -> ())
      }
  end ;;
