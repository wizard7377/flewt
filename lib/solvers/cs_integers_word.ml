
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
    exception MyFgnCnstrRepPlus of (dctx * __Exp * __Exp * __Exp * __Exp) 
    exception MyFgnCnstrRepTimes of (dctx * __Exp * __Exp * __Exp * __Exp) 
    exception MyFgnCnstrRepQuot of (dctx * __Exp * __Exp * __Exp * __Exp) 
    let wordSize' = Int.min (wordSize, W.wordSize)
    let zero = W.fromInt 0
    let max = W.(>>) ((W.notb zero), (Word.fromInt (W.wordSize - wordSize')))
    let rec numCheck d = W.(<=) (d, max)
    let rec plusCheck d1 d2 =
      let d3 = W.(+) (d1, d2) in
      (W.(>=) (d3, d1)) && ((W.(>=) (d3, d2)) && (W.(<=) (d3, max)))
    let rec timesCheck d1 d2 =
      if (d1 = zero) || (d2 = zero)
      then true__
      else (let d3 = W.div ((W.div (max, d1)), d2) in W.(>) (d3, zero))
    let rec quotCheck d1 d2 = W.(>) (d2, zero)
    let myID = (ref (-1) : csid ref)
    let wordID = (ref (-1) : cid ref)
    let rec word () = Root ((Const (!wordID)), Nil)
    let plusID = (ref (-1) : cid ref)
    let timesID = (ref (-1) : cid ref)
    let quotID = (ref (-1) : cid ref)
    let rec plusExp (__U) (__V) (__W) =
      Root ((Const (!plusID)), (App (__U, (App (__V, (App (__W, Nil)))))))
    let rec timesExp (__U) (__V) (__W) =
      Root ((Const (!timesID)), (App (__U, (App (__V, (App (__W, Nil)))))))
    let rec quotExp (__U) (__V) (__W) =
      Root ((Const (!quotID)), (App (__U, (App (__V, (App (__W, Nil)))))))
    let provePlusID = (ref (-1) : cid ref)
    let proveTimesID = (ref (-1) : cid ref)
    let proveQuotID = (ref (-1) : cid ref)
    let proofPlusID = (ref (-1) : cid ref)
    let proofTimesID = (ref (-1) : cid ref)
    let proofQuotID = (ref (-1) : cid ref)
    let rec provePlusExp (__U) (__V) (__W) (__P) =
      Root
        ((Const (!provePlusID)),
          (App (__U, (App (__V, (App (__W, (App (__P, Nil)))))))))
    let rec proofPlusExp (__U) (__V) (__W) (__P) =
      Root
        ((Const (!proofPlusID)),
          (App (__U, (App (__V, (App (__W, (App (__P, Nil)))))))))
    let rec proofTimesExp (__U) (__V) (__W) (__P) =
      Root
        ((Const (!proofTimesID)),
          (App (__U, (App (__V, (App (__W, (App (__P, Nil)))))))))
    let rec proveTimesExp (__U) (__V) (__W) (__P) =
      Root
        ((Const (!proveTimesID)),
          (App (__U, (App (__V, (App (__W, (App (__P, Nil)))))))))
    let rec proveQuotExp (__U) (__V) (__W) (__P) =
      Root
        ((Const (!proveQuotID)),
          (App (__U, (App (__V, (App (__W, (App (__P, Nil)))))))))
    let rec proofQuotExp (__U) (__V) (__W) (__P) =
      Root
        ((Const (!proofQuotID)),
          (App (__U, (App (__V, (App (__W, (App (__P, Nil)))))))))
    let rec numberConDec d =
      ConDec ((W.fmt StringCvt.DEC d), NONE, 0, Normal, (word ()), Type)
    let rec numberExp d = Root ((FgnConst ((!myID), (numberConDec d))), Nil)
    let rec scanNumber str =
      let rec check =
        function
        | _::_ as chars -> List.all Char.isDigit chars
        | nil -> false__ in
      if check (String.explode str)
      then
        match StringCvt.scanString (W.scan StringCvt.DEC) str with
        | Some d -> (if numCheck d then Some d else NONE)
        | NONE -> NONE
      else NONE
    let rec parseNumber string =
      match scanNumber string with
      | Some d -> Some (numberConDec d)
      | NONE -> NONE
    let rec plusPfConDec d1 d2 =
      let d3 = W.(+) (d1, d2) in
      ConDec
        (((^) ((W.fmt StringCvt.DEC d1) ^ "+") W.fmt StringCvt.DEC d2), NONE,
          0, Normal,
          (plusExp ((numberExp d1), (numberExp d2), (numberExp d3))), Type)
    let rec plusPfExp ds =
      Root ((FgnConst ((!myID), (plusPfConDec ds))), Nil)
    let rec timesPfConDec d1 d2 =
      let d3 = W.( * ) (d1, d2) in
      ConDec
        (((^) ((W.fmt StringCvt.DEC d1) ^ "*") W.fmt StringCvt.DEC d2), NONE,
          0, Normal,
          (timesExp ((numberExp d1), (numberExp d2), (numberExp d3))), Type)
    let rec timesPfExp ds =
      Root ((FgnConst ((!myID), (timesPfConDec ds))), Nil)
    let rec quotPfConDec d1 d2 =
      let d3 = W.div (d1, d2) in
      ConDec
        (((^) ((W.fmt StringCvt.DEC d1) ^ "/") W.fmt StringCvt.DEC d2), NONE,
          0, Normal,
          (quotExp ((numberExp d1), (numberExp d2), (numberExp d3))), Type)
    let rec quotPfExp ds =
      Root ((FgnConst ((!myID), (quotPfConDec ds))), Nil)
    let rec scanBinopPf oper string =
      let args = String.tokens (fun c -> c = oper) string in
      match args with
      | arg1::arg2::[] ->
          (match ((StringCvt.scanString (W.scan StringCvt.DEC) arg1),
                   (StringCvt.scanString (W.scan StringCvt.DEC) arg2))
           with
           | (Some d1, Some d2) -> Some (d1, d2)
           | _ -> NONE)
      | _ -> NONE
    let rec parseBinopPf oper string =
      match (oper, (scanBinopPf oper string)) with
      | ('+', Some ds) -> Some (plusPfConDec ds)
      | ('*', Some ds) -> Some (timesPfConDec ds)
      | ('/', Some ds) -> Some (quotPfConDec ds)
      | _ -> NONE
    let parsePlusPf = parseBinopPf '+'
    let parseTimesPf = parseBinopPf '*'
    let parseQuotPf = parseBinopPf '/'
    let rec parseAll string =
      match parseNumber string with
      | Some conDec -> Some conDec
      | NONE ->
          (match parsePlusPf string with
           | Some conDec -> Some conDec
           | NONE ->
               (match parseTimesPf string with
                | Some conDec -> Some conDec
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
             | Some d -> Num d
             | NONE ->
                 (match scanBinopPf '/' string with
                  | Some ds -> QuotPf ds
                  | NONE ->
                      (match scanBinopPf '+' string with
                       | Some ds -> PlusPf ds
                       | NONE ->
                           (match scanBinopPf '*' string with
                            | Some ds -> TimesPf ds
                            | NONE -> Expr __Us))))
          else Expr __Us
      | (Root (Def d, _), _) as Us -> fromExpW (Whnf.expandDef __Us)
      | __Us -> Expr __Us
    let rec fromExp (__Us) = fromExpW (Whnf.whnf __Us)
    let rec toExp =
      function
      | Num d -> numberExp d
      | PlusPf ds -> plusPfExp ds
      | TimesPf ds -> timesPfExp ds
      | QuotPf ds -> quotPfExp ds
      | Expr (__Us) -> EClo __Us
    let rec solveNumber (__G) (__S) k = Some (numberExp (W.fromInt k))
    let rec fst __0__ __1__ =
      match (__0__, __1__) with
      | (App (__U1, _), s) -> (__U1, s)
      | (SClo (__S, s'), s) -> fst (__S, (comp (s', s)))
    let rec snd __2__ __3__ =
      match (__2__, __3__) with
      | (App (_, __S), s) -> fst (__S, s)
      | (SClo (__S, s'), s) -> snd (__S, (comp (s', s)))
    let rec trd __4__ __5__ =
      match (__4__, __5__) with
      | (App (_, __S), s) -> snd (__S, s)
      | (SClo (__S, s'), s) -> trd (__S, (comp (s', s)))
    let rec fth __6__ __7__ =
      match (__6__, __7__) with
      | (App (_, __S), s) -> trd (__S, s)
      | (SClo (__S, s'), s) -> fth (__S, (comp (s', s)))
    let rec toInternalPlus (__G) (__U1) (__U2) (__U3) () =
      [(__G, (plusExp (__U1, __U2, __U3)))]
    let rec awakePlus (__G) proof (__U1) (__U2) (__U3) () =
      match solvePlus (__G, (App (__U1, (App (__U2, (App (__U3, Nil)))))), 0)
      with
      | Some proof' -> Unify.unifiable (__G, (proof, id), (proof', id))
      | NONE -> false__
    let rec makeCnstrPlus (__G) proof (__U1) (__U2) (__U3) =
      FgnCnstr ((!myID), (MyFgnCnstrRepPlus (__G, proof, __U1, __U2, __U3)))
    let rec solvePlus __8__ __9__ __10__ =
      match (__8__, __9__, __10__) with
      | (__G, __S, 0) ->
          let __Us1 = fst (__S, id) in
          let __Us2 = snd (__S, id) in
          let __Us3 = trd (__S, id) in
          (match ((fromExp __Us1), (fromExp __Us2), (fromExp __Us3)) with
           | (Num d1, Num d2, Num d3) ->
               if ((=) d3 W.(+) (d1, d2)) && (plusCheck (d1, d2))
               then Some (plusPfExp (d1, d2))
               else NONE
           | (Expr (__Us1), Num d2, Num d3) ->
               if
                 (W.(>=) (d3, d2)) &&
                   (Unify.unifiable
                      (__G, __Us1, ((numberExp (W.(-) (d3, d2))), id)))
               then Some (plusPfExp ((W.(-) (d3, d2)), d2))
               else NONE
           | (Num d1, Expr (__Us2), Num d3) ->
               if
                 (W.(>=) (d3, d1)) &&
                   (Unify.unifiable
                      (__G, __Us2, ((numberExp (W.(-) (d3, d1))), id)))
               then Some (plusPfExp (d1, (W.(-) (d3, d1))))
               else NONE
           | (Num d1, Num d2, Expr (__Us3)) ->
               if
                 (plusCheck (d1, d2)) &&
                   (Unify.unifiable
                      (__G, __Us3, ((numberExp (W.(+) (d1, d2))), id)))
               then Some (plusPfExp (d1, d2))
               else NONE
           | _ ->
               let proof =
                 newEVar
                   (__G,
                     (plusExp ((EClo __Us1), (EClo __Us2), (EClo __Us3)))) in
               let cnstr =
                 makeCnstrPlus
                   (__G, proof, (EClo __Us1), (EClo __Us2), (EClo __Us3)) in
               let _ =
                 List.app (fun (__Us) -> Unify.delay (__Us, (ref cnstr)))
                   [__Us1; __Us2; __Us3] in
               Some proof)
      | (__G, __S, n) -> NONE
    let rec toInternalTimes (__G) (__U1) (__U2) (__U3) () =
      [(__G, (timesExp (__U1, __U2, __U3)))]
    let rec awakeTimes (__G) proof (__U1) (__U2) (__U3) () =
      match solveTimes
              (__G, (App (__U1, (App (__U2, (App (__U3, Nil)))))), 0)
      with
      | Some proof' -> Unify.unifiable (__G, (proof, id), (proof', id))
      | NONE -> false__
    let rec makeCnstrTimes (__G) proof (__U1) (__U2) (__U3) =
      FgnCnstr ((!myID), (MyFgnCnstrRepTimes (__G, proof, __U1, __U2, __U3)))
    let rec solveTimes __11__ __12__ __13__ =
      match (__11__, __12__, __13__) with
      | (__G, __S, 0) ->
          let __Us1 = fst (__S, id) in
          let __Us2 = snd (__S, id) in
          let __Us3 = trd (__S, id) in
          (match ((fromExp __Us1), (fromExp __Us2), (fromExp __Us3)) with
           | (Num d1, Num d2, Num d3) ->
               if ((=) d3 W.( * ) (d1, d2)) && (timesCheck (d1, d2))
               then Some (timesPfExp (d1, d2))
               else NONE
           | (Expr (__Us1), Num d2, Num d3) ->
               if
                 (d3 = zero) &&
                   (Unify.unifiable (__G, __Us1, ((numberExp zero), id)))
               then Some (timesPfExp (zero, d2))
               else
                 if
                   (W.(>) (d2, zero)) &&
                     ((W.(>) (d3, zero)) &&
                        (((W.mod__ (d3, d2)) = zero) &&
                           (Unify.unifiable
                              (__G, __Us1,
                                ((numberExp (W.div (d3, d2))), id)))))
                 then Some (timesPfExp ((W.div (d3, d2)), d2))
                 else NONE
           | (Num d1, Expr (__Us2), Num d3) ->
               if
                 (d3 = zero) &&
                   (Unify.unifiable (__G, __Us2, ((numberExp zero), id)))
               then Some (timesPfExp (d1, zero))
               else
                 if
                   (W.(>) (d1, zero)) &&
                     ((W.(>) (d3, zero)) &&
                        (((W.mod__ (d3, d1)) = zero) &&
                           (Unify.unifiable
                              (__G, __Us2,
                                ((numberExp (W.div (d3, d1))), id)))))
                 then Some (timesPfExp (d1, (W.div (d3, d1))))
                 else NONE
           | (Num d1, Num d2, Expr (__Us3)) ->
               if
                 (timesCheck (d1, d2)) &&
                   (Unify.unifiable
                      (__G, __Us3, ((numberExp (W.( * ) (d1, d2))), id)))
               then Some (timesPfExp (d1, d2))
               else NONE
           | _ ->
               let proof =
                 newEVar
                   (__G,
                     (timesExp ((EClo __Us1), (EClo __Us2), (EClo __Us3)))) in
               let cnstr =
                 makeCnstrTimes
                   (__G, proof, (EClo __Us1), (EClo __Us2), (EClo __Us3)) in
               let _ =
                 List.app (fun (__Us) -> Unify.delay (__Us, (ref cnstr)))
                   [__Us1; __Us2; __Us3] in
               Some proof)
      | (__G, __S, n) -> NONE
    let rec toInternalQuot (__G) (__U1) (__U2) (__U3) () =
      [(__G, (quotExp (__U1, __U2, __U3)))]
    let rec awakeQuot (__G) proof (__U1) (__U2) (__U3) () =
      match solveQuot (__G, (App (__U1, (App (__U2, (App (__U3, Nil)))))), 0)
      with
      | Some proof' -> Unify.unifiable (__G, (proof, id), (proof', id))
      | NONE -> false__
    let rec makeCnstrQuot (__G) proof (__U1) (__U2) (__U3) =
      FgnCnstr ((!myID), (MyFgnCnstrRepQuot (__G, proof, __U1, __U2, __U3)))
    let rec solveQuot __14__ __15__ __16__ =
      match (__14__, __15__, __16__) with
      | (__G, __S, 0) ->
          let __Us1 = fst (__S, id) in
          let __Us2 = snd (__S, id) in
          let __Us3 = trd (__S, id) in
          (match ((fromExp __Us1), (fromExp __Us2), (fromExp __Us3)) with
           | (Num d1, Num d2, Num d3) ->
               if (quotCheck (d1, d2)) && ((=) d3 W.div (d1, d2))
               then Some (quotPfExp (d1, d2))
               else NONE
           | (Num d1, Num d2, Expr (__Us3)) ->
               if
                 (quotCheck (d1, d2)) &&
                   (Unify.unifiable
                      (__G, __Us3, ((numberExp (W.div (d1, d2))), id)))
               then Some (quotPfExp (d1, d2))
               else NONE
           | _ ->
               let proof =
                 newEVar
                   (__G,
                     (quotExp ((EClo __Us1), (EClo __Us2), (EClo __Us3)))) in
               let cnstr =
                 makeCnstrQuot
                   (__G, proof, (EClo __Us1), (EClo __Us2), (EClo __Us3)) in
               let _ =
                 List.app (fun (__Us) -> Unify.delay (__Us, (ref cnstr)))
                   [__Us1; __Us2; __Us3] in
               Some proof)
      | (__G, __S, n) -> NONE
    let rec solveProvePlus (__G) (__S) k =
      let __Us1 = fst (__S, id) in
      let __Us2 = snd (__S, id) in
      let __Us3 = trd (__S, id) in
      let __Us4 = fth (__S, id) in
      match solvePlus
              (__G,
                (App
                   ((EClo __Us1),
                     (App ((EClo __Us2), (App ((EClo __Us3), Nil)))))), k)
      with
      | Some (__U) ->
          if Unify.unifiable (__G, __Us4, (__U, id))
          then
            Some
              (proofPlusExp
                 ((EClo __Us1), (EClo __Us2), (EClo __Us3), (EClo __Us4)))
          else NONE
      | NONE -> NONE
    let rec solveProveTimes (__G) (__S) k =
      let __Us1 = fst (__S, id) in
      let __Us2 = snd (__S, id) in
      let __Us3 = trd (__S, id) in
      let __Us4 = fth (__S, id) in
      match solveTimes
              (__G,
                (App
                   ((EClo __Us1),
                     (App ((EClo __Us2), (App ((EClo __Us3), Nil)))))), k)
      with
      | Some (__U) ->
          if Unify.unifiable (__G, __Us4, (__U, id))
          then
            Some
              (proofTimesExp
                 ((EClo __Us1), (EClo __Us2), (EClo __Us3), (EClo __Us4)))
          else NONE
      | NONE -> NONE
    let rec solveProveQuot (__G) (__S) k =
      let __Us1 = fst (__S, id) in
      let __Us2 = snd (__S, id) in
      let __Us3 = trd (__S, id) in
      let __Us4 = fth (__S, id) in
      match solveQuot
              (__G,
                (App
                   ((EClo __Us1),
                     (App ((EClo __Us2), (App ((EClo __Us3), Nil)))))), k)
      with
      | Some (__U) ->
          if Unify.unifiable (__G, __Us4, (__U, id))
          then
            Some
              (proofQuotExp
                 ((EClo __Us1), (EClo __Us2), (EClo __Us3), (EClo __Us4)))
          else NONE
      | NONE -> NONE
    let rec arrow (__U) (__V) = Pi (((Dec (NONE, __U)), No), __V)
    let rec pi name (__U) (__V) = Pi (((Dec ((Some name), __U)), Maybe), __V)
    let rec bvar n = Root ((BVar n), Nil)
    let rec installFgnCnstrOps () =
      let csid = !myID in
      let _ =
        FgnCnstrStd.ToInternal.install
          (csid,
            (function
             | MyFgnCnstrRepPlus (__G, _, __U1, __U2, __U3) ->
                 toInternalPlus (__G, __U1, __U2, __U3)
             | MyFgnCnstrRepTimes (__G, _, __U1, __U2, __U3) ->
                 toInternalTimes (__G, __U1, __U2, __U3)
             | MyFgnCnstrRepQuot (__G, _, __U1, __U2, __U3) ->
                 toInternalQuot (__G, __U1, __U2, __U3)
             | fc -> raise (UnexpectedFgnCnstr fc))) in
      let _ =
        FgnCnstrStd.Awake.install
          (csid,
            (function
             | MyFgnCnstrRepPlus (__G, proof, __U1, __U2, __U3) ->
                 awakePlus (__G, proof, __U1, __U2, __U3)
             | MyFgnCnstrRepTimes (__G, proof, __U1, __U2, __U3) ->
                 awakeTimes (__G, proof, __U1, __U2, __U3)
             | MyFgnCnstrRepQuot (__G, proof, __U1, __U2, __U3) ->
                 awakeQuot (__G, proof, __U1, __U2, __U3)
             | fc -> raise (UnexpectedFgnCnstr fc))) in
      let _ =
        FgnCnstrStd.Simplify.install
          (csid,
            (function
             | MyFgnCnstrRepPlus _ -> (fun () -> false__)
             | MyFgnCnstrRepTimes _ -> (fun () -> false__)
             | MyFgnCnstrRepQuot _ -> (fun () -> false__)
             | fc -> raise (UnexpectedFgnCnstr fc))) in
      ()
    let rec init cs installF =
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
            ("*", NONE, 0, (Constraint ((!myID), solveTimes)),
              (arrow
                 ((word ()),
                   (arrow ((word ()), (arrow ((word ()), (Uni Type))))))),
              Kind)), NONE,
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
            ("/", NONE, 0, (Constraint ((!myID), solveQuot)),
              (arrow
                 ((word ()),
                   (arrow ((word ()), (arrow ((word ()), (Uni Type))))))),
              Kind)), NONE,
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
             ((MS.Marg (MS.Star, (Some "X"))),
               (MS.Mapp
                  ((MS.Marg (MS.Star, (Some "Y"))),
                    (MS.Mapp
                       ((MS.Marg (MS.Star, (Some "Z"))),
                         (MS.Mapp ((MS.Marg (MS.Star, (Some "P"))), MS.Mnil)))))))]);
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
             ((MS.Marg (MS.Star, (Some "X"))),
               (MS.Mapp
                  ((MS.Marg (MS.Star, (Some "Y"))),
                    (MS.Mapp
                       ((MS.Marg (MS.Star, (Some "Z"))),
                         (MS.Mapp ((MS.Marg (MS.Star, (Some "P"))), MS.Mnil)))))))]);
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
             ((MS.Marg (MS.Star, (Some "X"))),
               (MS.Mapp
                  ((MS.Marg (MS.Star, (Some "Y"))),
                    (MS.Mapp
                       ((MS.Marg (MS.Star, (Some "Z"))),
                         (MS.Mapp ((MS.Marg (MS.Star, (Some "P"))), MS.Mnil)))))))]);
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
    let solver =
      {
        name = ((^) "word" Int.toString wordSize');
        keywords = "numbers,equality";
        needs = ["Unify"];
        fgnConst = (Some { parse = parseAll });
        init;
        reset = (fun () -> ());
        mark = (fun () -> ());
        unwind = (fun () -> ())
      }
  end ;;
