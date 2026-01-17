
module type FUNTYPECHECK  =
  sig
    module StateSyn :
    ((STATESYN)(* Type checking for functional proof term calculus *)
    (* Author: Carsten Schuermann *)(*! structure FunSyn : FUNSYN !*))
    exception Error of string 
    val isFor : (IntSyn.dctx * FunSyn.__For) -> unit
    val check : (FunSyn.__Pro * FunSyn.__For) -> unit
    val checkSub : (FunSyn.lfctx * IntSyn.__Sub * FunSyn.lfctx) -> unit
    val isState : StateSyn.__State -> unit
  end;;




module FunTypeCheck(FunTypeCheck:sig
                                   module StateSyn' : STATESYN
                                   module Abstract : ABSTRACT
                                   module TypeCheck : TYPECHECK
                                   module Conv : CONV
                                   module Whnf : WHNF
                                   module Print : PRINT
                                   module Subordinate : SUBORDINATE
                                   module Weaken : WEAKEN
                                   module FunPrint :
                                   ((FUNPRINT)(* Type checking for functional proof term calculus *)
                                   (* Author: Carsten Schuermann *)
                                   (*! structure FunSyn' : FUNSYN !*)
                                   (*! sharing StateSyn'.FunSyn = FunSyn' !*)
                                   (*! sharing Abstract.IntSyn = FunSyn'.IntSyn !*)
                                   (*! sharing TypeCheck.IntSyn = FunSyn'.IntSyn !*)
                                   (*! sharing Conv.IntSyn = FunSyn'.IntSyn !*)
                                   (*! sharing Whnf.IntSyn = FunSyn'.IntSyn !*)
                                   (*! sharing Print.IntSyn = FunSyn'.IntSyn !*)
                                   (*! sharing Subordinate.IntSyn = FunSyn'.IntSyn !*)
                                   (*! sharing Weaken.IntSyn = FunSyn'.IntSyn   !*))
                                 end) : FUNTYPECHECK =
  struct
    module StateSyn =
      ((StateSyn')(*! sharing FunPrint.FunSyn = FunSyn' !*)
      (*! structure FunSyn = FunSyn' !*))
    exception Error of string 
    module I = IntSyn
    module F = FunSyn
    module S = StateSyn
    let rec conv (Gs, Gs') =
      let exception Conv  in
        let conv =
          function
          | ((I.Null, s), (I.Null, s')) -> (s, s')
          | ((Decl (g, Dec (_, V)), s), (Decl (g', Dec (_, V')), s')) ->
              let (s1, s1') = conv ((g, s), (g', s')) in
              let (s2, s2') as ps = ((I.dot1 s1), (I.dot1 s1')) in
              if Conv.conv ((V, s1), (V', s1')) then ps else raise Conv
          | _ -> raise Conv in
        try conv (Gs, Gs'); true__ with | Conv -> false__
    let rec extend =
      function | (g, nil) -> g | (g, (D)::L) -> extend ((I.Decl (g, D)), L)
    let rec validBlock (Psi, k, (l, g)) =
      let skipBlock =
        function
        | (I.Null, k) -> k
        | (Decl (g', _), k) -> skipBlock (g', (k - 1)) in
      let validBlock' =
        function
        | (Decl (Psi, Block (CtxBlock (l', g'))), 0) ->
            if (l' = l) && (conv ((g, I.id), (g', I.id)))
            then ()
            else raise (Error "Typecheck Error: Not a valid block")
        | (Decl (Psi, Prim _), 0) ->
            raise (Error "Typecheck Error: Not a valid block")
        | (I.Null, k) -> raise (Error "Typecheck Error: Not a valid block")
        | (Decl (Psi, Block (CtxBlock (l', g'))), k) ->
            validBlock' (Psi, (skipBlock (g', k)))
        | (Decl (Psi, Prim (D)), k) -> validBlock' (Psi, (k - 1)) in
      validBlock' (Psi, k)
    let rec raiseSub (g, Psi') =
      let n = I.ctxLength g in
      let m = I.ctxLength Psi' in
      let args =
        function
        | (0, a, S) -> S
        | (n', a, S) ->
            let Dec (_, V) = I.ctxDec (g, n') in
            if Subordinate.belowEq ((I.targetFam V), a)
            then
              args ((n' - 1), a, (I.App ((I.Root ((I.BVar n'), I.Nil)), S)))
            else args ((n' - 1), a, S) in
      let term m' =
        let Dec (_, V) = I.ctxDec (Psi', m') in
        I.Exp
          (I.Root ((I.BVar (n + m')), (args (n, (I.targetFam V), I.Nil)))) in
      let raiseSub'' =
        function
        | (0, s) -> s
        | (m', s) -> raiseSub'' ((m' - 1), (I.Dot ((term m'), s))) in
      let raiseSub' =
        function
        | (0, s) -> raiseSub'' (m, s)
        | (n', s) -> raiseSub' ((n' - 1), (I.Dot ((I.Idx n'), s))) in
      raiseSub' (n, (I.Shift (n + m)))
    let rec raiseType (CtxBlock (l, g), Psi') =
      let raiseType'' =
        function
        | (I.Null, Vn, a) -> Vn
        | (Decl (g', (Dec (_, V') as D)), Vn, a) ->
            if Subordinate.belowEq ((I.targetFam V'), a)
            then raiseType'' (g', (Abstract.piDepend ((D, I.Maybe), Vn)), a)
            else raiseType'' (g', (Weaken.strengthenExp (Vn, I.shift)), a) in
      let raiseType' =
        function
        | (Psi1, nil) -> nil
        | (Psi1, (Prim (Dec (x, V) as D))::Psi1') ->
            let s = raiseSub (g, Psi1) in
            let Vn = Whnf.normalize (V, s) in
            let a = I.targetFam Vn in
            let D' = I.Dec (x, (raiseType'' (g, Vn, a))) in
            (F.Prim D') :: (raiseType' ((I.Decl (Psi1, D)), Psi1')) in
      raiseType' (I.Null, Psi')
    let rec raiseM =
      function
      | (B, nil) -> nil
      | (B, (MDec (xx, F))::L) ->
          (::) (F.MDec (xx, (F.All ((F.Block B), F)))) raiseM (B, L)
    let rec psub =
      function
      | (k, I.Null, s) -> s
      | (k, Decl (g, _), s) -> psub ((k - 1), g, (I.Dot ((I.Idx k), s)))
    let rec deltaSub =
      function
      | (I.Null, s) -> I.Null
      | (Decl (Delta, DD), s) ->
          I.Decl ((deltaSub (Delta, s)), (F.mdecSub (DD, s)))
    let rec shift (Delta) = deltaSub (Delta, I.shift)
    let rec shifts =
      function
      | (I.Null, Delta) -> Delta
      | (Decl (g, _), Delta) -> shifts (g, (shift Delta))
    let rec shiftBlock (CtxBlock (_, g), Delta) = shifts (g, Delta)
    let rec shiftSub =
      function
      | (I.Null, s) -> s
      | (Decl (g, _), s) -> shiftSub (g, (I.comp (I.shift, s)))
    let rec shiftSubBlock (CtxBlock (_, g), s) = shiftSub (g, s)
    let rec check =
      function
      | (Psi, Delta, F.Unit, (F.True, _)) -> ()
      | (Psi, Delta, Rec (DD, P), F) ->
          check (Psi, (I.Decl (Delta, DD)), P, F)
      | (Psi, Delta, Lam ((Prim (Dec (_, V)) as LD), P),
         (All (Prim (Dec (_, V')), F'), s')) ->
          if Conv.conv ((V, I.id), (V', s'))
          then
            check ((I.Decl (Psi, LD)), (shift Delta), P, (F', (I.dot1 s')))
          else raise (Error "Typecheck Error: Primitive Abstraction")
      | (Psi, Delta, Lam ((Block (CtxBlock (l, g) as B) as LD), P),
         (All (Block (CtxBlock (l', g')), F'), s')) ->
          if (l = l') && (conv ((g, I.id), (g', s')))
          then
            check
              ((I.Decl (Psi, LD)), (shiftBlock (B, Delta)), P,
                (F', (F.dot1n (g, s'))))
          else raise (Error "Typecheck Error: Block Abstraction")
      | (Psi, Delta, Inx (M, P), (Ex (Dec (_, V'), F'), s')) ->
          (TypeCheck.typeCheck ((F.makectx Psi), (M, (I.EClo (V', s'))));
           check (Psi, Delta, P, (F', (I.Dot ((I.Exp M), s')))))
      | (Psi, Delta, Case (Opts (O)), (F', s')) ->
          checkOpts (Psi, Delta, O, (F', s'))
      | (Psi, Delta, Pair (P1, P2), (And (F1', F2'), s')) ->
          (check (Psi, Delta, P1, (F1', s'));
           check (Psi, Delta, P2, (F2', s')))
      | (Psi, Delta, Let (Ds, P), (F', s')) ->
          let (Psi', Delta', s'') = assume (Psi, Delta, Ds) in
          check
            ((extend (Psi, Psi')), (extend (Delta, Delta')), P,
              (F', (I.comp (s', s''))))
      | _ -> raise (Error "Typecheck Error: Term not well-typed")
    let rec infer (Delta, kk) = ((I.ctxLookup (Delta, kk)), I.id)
    let rec assume =
      function
      | (Psi, Delta, F.Empty) -> (nil, nil, I.id)
      | (Psi, Delta, Split (kk, Ds)) ->
          (match infer (Delta, kk) with
           | (MDec (name, Ex (D, F)), s) ->
               let LD = F.Prim (I.decSub (D, s)) in
               let DD = F.MDec (name, (F.forSub (F, (I.dot1 s)))) in
               let (Psi', Delta', s') =
                 assume
                   ((I.Decl (Psi, LD)), (I.Decl ((shift Delta), DD)), Ds) in
               ((LD :: Psi'), ((F.mdecSub (DD, s')) :: Delta'),
                 (I.comp (I.shift, s')))
           | _ -> raise (Error "Typecheck Error: Declaration"))
      | (Psi, Delta, New (B, Ds)) ->
          let _ =
            TypeCheck.typeCheck
              ((F.makectx (I.Decl (Psi, (F.Block B)))),
                ((I.Uni I.Type), (I.Uni I.Kind))) in
          let (Psi', Delta', s') =
            assume ((I.Decl (Psi, (F.Block B))), (shiftBlock (B, Delta)), Ds) in
          ((raiseType (B, Psi')), (raiseM (B, Delta')), s')
      | (Psi, Delta, App ((kk, U), Ds)) ->
          (match infer (Delta, kk) with
           | (MDec (name, All (Prim (Dec (_, V)), F)), s) ->
               let _ =
                 try
                   TypeCheck.typeCheck
                     ((F.makectx Psi), (U, (I.EClo (V, s))))
                 with
                 | Error msg ->
                     raise
                       (Error
                          ((^) (((^) (((^) (msg ^ " ") Print.expToString
                                         ((F.makectx Psi), U))
                                        ^ " has type ")
                                   Print.expToString
                                   ((F.makectx Psi),
                                     (TypeCheck.infer' ((F.makectx Psi), U))))
                                  ^ " expected ")
                             Print.expToString
                             ((F.makectx Psi), (I.EClo (V, s))))) in
               let DD = F.MDec (name, (F.forSub (F, (I.Dot ((I.Exp U), s))))) in
               let (Psi', Delta', s') =
                 assume (Psi, (I.Decl (Delta, DD)), Ds) in
               (Psi', ((F.mdecSub (DD, s')) :: Delta'), s')
           | (MDec (name, F), s) ->
               raise
                 (Error
                    ("Typecheck Error: Declaration App" ^
                       (FunPrint.forToString (I.Null, F) ["x"]))))
      | (Psi, Delta, PApp ((kk, k), Ds)) ->
          (match infer (Delta, kk) with
           | (MDec (name, All (Block (CtxBlock (l, g)), F)), s) ->
               let _ = validBlock (Psi, k, (l, g)) in
               let DD = F.MDec (name, (F.forSub (F, (psub (k, g, s))))) in
               let (Psi', Delta', s') =
                 assume (Psi, (I.Decl (Delta, DD)), Ds) in
               (Psi', ((F.mdecSub (DD, s')) :: Delta'), s')
           | _ -> raise (Error "Typecheck Error: Declaration PApp"))
      | (Psi, Delta, Left (kk, Ds)) ->
          (match infer (Delta, kk) with
           | (MDec (name, And (F1, F2)), s) ->
               let DD = F.MDec (name, (F.forSub (F1, s))) in
               let (Psi', Delta', s') =
                 assume (Psi, (I.Decl (Delta, DD)), Ds) in
               (Psi', ((F.mdecSub (DD, s')) :: Delta'), s')
           | _ -> raise (Error "Typecheck Error: Declaration Left"))
      | (Psi, Delta, Right (kk, Ds)) ->
          (match infer (Delta, kk) with
           | (MDec (name, And (F1, F2)), s) ->
               let DD = F.MDec (name, (F.forSub (F2, s))) in
               let (Psi', Delta', s') =
                 assume (Psi, (I.Decl (Delta, DD)), Ds) in
               (Psi', ((F.mdecSub (DD, s')) :: Delta'), s')
           | _ -> raise (Error "Typecheck Error: Declaration Left"))
      | (Psi, Delta, Lemma (cc, Ds)) ->
          let LemmaDec (names, _, F) = F.lemmaLookup cc in
          let name = foldr (^) "" names in
          let DD = F.MDec ((SOME name), F) in
          let (Psi', Delta', s') = assume (Psi, (I.Decl (Delta, DD)), Ds) in
          (Psi', ((F.mdecSub (DD, s')) :: Delta'), s')
    let rec checkSub =
      function
      | (I.Null, Shift 0, I.Null) -> ()
      | (Decl (Psi, Prim (D)), Shift k, I.Null) ->
          if k > 0
          then checkSub (Psi, (I.Shift (k - 1)), I.Null)
          else raise (Error "Substitution not well-typed")
      | (Decl (Psi, Block (CtxBlock (_, g))), Shift k, I.Null) ->
          let g = I.ctxLength g in
          if k >= g
          then checkSub (Psi, (I.Shift (k - g)), I.Null)
          else raise (Error "Substitution not well-typed")
      | (Psi', Shift k, Psi) ->
          checkSub (Psi', (I.Dot ((I.Idx (k + 1)), (I.Shift (k + 1)))), Psi)
      | (Psi', Dot (Idx k, s'), Decl (Psi, Prim (Dec (_, V2)))) ->
          let g' = F.makectx Psi' in
          let Dec (_, V1) = I.ctxDec (g', k) in
          if Conv.conv ((V1, I.id), (V2, s'))
          then checkSub (Psi', s', Psi)
          else
            raise
              (Error
                 ((^) (((^) "Substitution not well-typed \n  found: "
                          Print.expToString (g', V1))
                         ^ "\n  expected: ")
                    Print.expToString (g', (I.EClo (V2, s')))))
      | (Psi', Dot (Exp (U), s'), Decl (Psi, Prim (Dec (_, V2)))) ->
          let g' = F.makectx Psi' in
          let _ = TypeCheck.typeCheck (g', (U, (I.EClo (V2, s')))) in
          checkSub (Psi', s', Psi)
      | (Psi', (Dot (Idx k, _) as s), Decl (Psi, Block (CtxBlock (l1, g))))
          ->
          let (Block (CtxBlock (l2, g')), w) = F.lfctxLFDec (Psi', k) in
          let checkSub' =
            function
            | ((I.Null, w1), s1, I.Null, _) -> s1
            | ((Decl (g', Dec (_, V')), w1), Dot (Idx k', s1), Decl
               (g, Dec (_, V)), m) ->
                if k' = m
                then
                  (if Conv.conv ((V', w1), (V, s1))
                   then
                     checkSub' ((g', (I.comp (w1, I.shift))), s1, g, (m + 1))
                   else
                     raise (Error "ContextBlock assignment not well-typed"))
                else raise (Error "ContextBlock assignment out of order") in
          checkSub (Psi', (checkSub' ((g', w), s, g, k)), Psi)
    let rec checkOpts =
      function
      | (Psi, Delta, nil, _) -> ()
      | (Psi, Delta, (Psi', t, P)::O, (F', s')) ->
          (checkSub (Psi', t, Psi);
           check (Psi', (deltaSub (Delta, t)), P, (F', (I.comp (s', t))));
           checkOpts (Psi, Delta, O, (F', s')))
    let rec checkRec (P, T) = check (I.Null, I.Null, P, (T, I.id))
    let rec isFor =
      function
      | (g, All (Prim (D), F)) ->
          (try TypeCheck.checkDec (g, (D, I.id)); isFor ((I.Decl (g, D)), F)
           with | Error msg -> raise (Error msg))
      | (g, All (Block (CtxBlock (_, G1)), F)) ->
          isForBlock (g, (F.ctxToList G1), F)
      | (g, Ex (D, F)) ->
          (try TypeCheck.checkDec (g, (D, I.id)); isFor ((I.Decl (g, D)), F)
           with | Error msg -> raise (Error msg))
      | (g, F.True) -> ()
      | (g, And (F1, F2)) -> (isFor (g, F1); isFor (g, F2))
    let rec isForBlock =
      function
      | (g, nil, F) -> isFor (g, F)
      | (g, (D)::G1, F) -> isForBlock ((I.Decl (g, D)), G1, F)
    let rec checkTags' =
      function
      | (V, Ex _) -> ()
      | (Pi (_, V), All (_, F)) -> checkTags' (V, F)
      | _ -> raise Domain
    let rec checkTags =
      function
      | (I.Null, I.Null) -> ()
      | (Decl (g, Dec (_, V)), Decl (B, T)) ->
          (checkTags (g, B); (match T with | Lemma _ -> () | _ -> ()))
    let rec isState (State (n, (g, B), (IH, OH), d, O, H, F)) =
      TypeCheck.typeCheckCtx g;
      checkTags (g, B);
      if not (Abstract.closedCtx g)
      then raise (Error "State context not closed!")
      else ();
      map (function | (n', F') -> isFor (g, F')) H;
      isFor (g, F)
    let ((isFor)(* conv ((g, s), (g', s')) = B

       Invariant:
       B iff g [s]  == g' [s']
       Might migrate in to conv module  --cs
    *)
      (* extend (g, L) = g'

       Invariant:
       If   g : 'a ctx
       and  L : 'a list
       then g' = g, L : 'a ctx
    *)
      (* validBlock (Psi, k, (l : g)) = ()

       Invariant:
       If   |- Psi ctx
       and  |- k is a debruijn index (for LF context)
       and  |- l label
       and  |- g LFctx
       then validBlock terminates with ()
       iff  Psi = Psi1, l': (x1:A1 .. xn:An), Psi2
       and  l = l'
       and  Psi(k) = x1
       and  g == x1:A1 .. xn:An
    *)
      (* raiseSub (l:g, Psi') = s'

       Invariant:
       If   |- Psi ctx
       and  Psi |- l:g ctx
       and  Psi, l:g |- Psi' ctx
       then Psi, {g} Psi', l:g|- s' : Psi, l:g, Psi'
    *)
      (* raiseType (l:g, L) = L'

       Invariant:
       L contains no parameter block declarations
       Each x:A in L is mapped xto  x:{g}A in L'
       L' preserves the order of L
    *)
      (* no case of F.Block by invariant *)(* raiseM (B, L) = L'

       Invariant
       Each xx in F in L is mapped to xx in PI B. F in L'
       L' preserves the order of L
    *)
      (* psub (k, Phi, s) = s'

       Invariant:
       If   |- Phi ctx
       and  |- Psi ctx
       and  Psi = Psi1, l': (x1:A1 .. xn:An), Psi2
       and  Psi (k) = x1
       and  | Phi | = n
       and  s = k-i ... k. id   for i <=n
       then s' = k-n . ... k . id
    *)
      (* check (Psi, Delta, P, (F, s)) = ()

       Invariant:
       If   Psi'' |- F formula
       and  Psi |- s : Psi''
       and  Psi |- Delta mctx
        returns () if there exists a F',
              s.t. Psi, Delta |- P  : F'
              and  Psi |- F' = F[s] formula
       otherwise Error is raised
    *)
      (* assume (Psi, Delta, Ds) = (Psi', Delta', s')

       Invariant:
       If   |- Psi context
       and  Psi |- Delta assumptions
       and  Psi, Delta |- Decs declarations
       then |- Psi, Psi' context
       and  Psi, Psi' |- Delta, Delta' assumptions
       and  Psi, Psi' |- s' = ^|Psi'| : Psi
    *)
      (* check B valid context block       <-------------- omission *)
      (* checkSub (Psi1, s, Psi2) = ()

       Invariant:
       The function terminates
       iff  Psi1 |- s : Psi2
    *)
      (* check that l1 = l2     <----------------------- omission *)
      (* checkSub' ((g', w), s, g, m) = ()
          *)
      (* checkOpts (Psi, Delta, (O, s) *)(* [Psi' strict in  t] <------------------------- omission*)
      (* isState (S) = ()

       Invariant:

       Side effect:
       If it doesn't hold that |- S state, then exception Error is raised

       Remark: Function is only partially implemented
    *)
      (* ;          TextIO.print ("Checked: " ^ (FunPrint.Formatter.makestring_fmt (FunPrint.formatForBare (g, F'))) ^ "\n") *)
      (* n' is not checked for consistency   --cs *)) =
      isFor
    let check = checkRec
    let checkSub = checkSub
    let isState = isState
  end ;;
