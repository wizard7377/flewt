
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
          | ((Decl (G, Dec (_, V)), s), (Decl (G', Dec (_, V')), s')) ->
              let (s1, s1') = conv ((G, s), (G', s')) in
              let (s2, s2') as ps = ((I.dot1 s1), (I.dot1 s1')) in
              if Conv.conv ((V, s1), (V', s1')) then ps else raise Conv
          | _ -> raise Conv in
        try conv (Gs, Gs'); true__ with | Conv -> false__
    let rec extend =
      function | (G, nil) -> G | (G, (D)::L) -> extend ((I.Decl (G, D)), L)
    let rec validBlock (Psi, k, (l, G)) =
      let skipBlock =
        function
        | (I.Null, k) -> k
        | (Decl (G', _), k) -> skipBlock (G', (k - 1)) in
      let validBlock' =
        function
        | (Decl (Psi, Block (CtxBlock (l', G'))), 0) ->
            if (l' = l) && (conv ((G, I.id), (G', I.id)))
            then ()
            else raise (Error "Typecheck Error: Not a valid block")
        | (Decl (Psi, Prim _), 0) ->
            raise (Error "Typecheck Error: Not a valid block")
        | (I.Null, k) -> raise (Error "Typecheck Error: Not a valid block")
        | (Decl (Psi, Block (CtxBlock (l', G'))), k) ->
            validBlock' (Psi, (skipBlock (G', k)))
        | (Decl (Psi, Prim (D)), k) -> validBlock' (Psi, (k - 1)) in
      validBlock' (Psi, k)
    let rec raiseSub (G, Psi') =
      let n = I.ctxLength G in
      let m = I.ctxLength Psi' in
      let args =
        function
        | (0, a, S) -> S
        | (n', a, S) ->
            let Dec (_, V) = I.ctxDec (G, n') in
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
    let rec raiseType (CtxBlock (l, G), Psi') =
      let raiseType'' =
        function
        | (I.Null, Vn, a) -> Vn
        | (Decl (G', (Dec (_, V') as D)), Vn, a) ->
            if Subordinate.belowEq ((I.targetFam V'), a)
            then raiseType'' (G', (Abstract.piDepend ((D, I.Maybe), Vn)), a)
            else raiseType'' (G', (Weaken.strengthenExp (Vn, I.shift)), a) in
      let raiseType' =
        function
        | (Psi1, nil) -> nil
        | (Psi1, (Prim (Dec (x, V) as D))::Psi1') ->
            let s = raiseSub (G, Psi1) in
            let Vn = Whnf.normalize (V, s) in
            let a = I.targetFam Vn in
            let D' = I.Dec (x, (raiseType'' (G, Vn, a))) in
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
      | (k, Decl (G, _), s) -> psub ((k - 1), G, (I.Dot ((I.Idx k), s)))
    let rec deltaSub =
      function
      | (I.Null, s) -> I.Null
      | (Decl (Delta, DD), s) ->
          I.Decl ((deltaSub (Delta, s)), (F.mdecSub (DD, s)))
    let rec shift (Delta) = deltaSub (Delta, I.shift)
    let rec shifts =
      function
      | (I.Null, Delta) -> Delta
      | (Decl (G, _), Delta) -> shifts (G, (shift Delta))
    let rec shiftBlock (CtxBlock (_, G), Delta) = shifts (G, Delta)
    let rec shiftSub =
      function
      | (I.Null, s) -> s
      | (Decl (G, _), s) -> shiftSub (G, (I.comp (I.shift, s)))
    let rec shiftSubBlock (CtxBlock (_, G), s) = shiftSub (G, s)
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
      | (Psi, Delta, Lam ((Block (CtxBlock (l, G) as B) as LD), P),
         (All (Block (CtxBlock (l', G')), F'), s')) ->
          if (l = l') && (conv ((G, I.id), (G', s')))
          then
            check
              ((I.Decl (Psi, LD)), (shiftBlock (B, Delta)), P,
                (F', (F.dot1n (G, s'))))
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
           | (MDec (name, All (Block (CtxBlock (l, G)), F)), s) ->
               let _ = validBlock (Psi, k, (l, G)) in
               let DD = F.MDec (name, (F.forSub (F, (psub (k, G, s))))) in
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
      | (Decl (Psi, Block (CtxBlock (_, G))), Shift k, I.Null) ->
          let g = I.ctxLength G in
          if k >= g
          then checkSub (Psi, (I.Shift (k - g)), I.Null)
          else raise (Error "Substitution not well-typed")
      | (Psi', Shift k, Psi) ->
          checkSub (Psi', (I.Dot ((I.Idx (k + 1)), (I.Shift (k + 1)))), Psi)
      | (Psi', Dot (Idx k, s'), Decl (Psi, Prim (Dec (_, V2)))) ->
          let G' = F.makectx Psi' in
          let Dec (_, V1) = I.ctxDec (G', k) in
          if Conv.conv ((V1, I.id), (V2, s'))
          then checkSub (Psi', s', Psi)
          else
            raise
              (Error
                 ((^) (((^) "Substitution not well-typed \n  found: "
                          Print.expToString (G', V1))
                         ^ "\n  expected: ")
                    Print.expToString (G', (I.EClo (V2, s')))))
      | (Psi', Dot (Exp (U), s'), Decl (Psi, Prim (Dec (_, V2)))) ->
          let G' = F.makectx Psi' in
          let _ = TypeCheck.typeCheck (G', (U, (I.EClo (V2, s')))) in
          checkSub (Psi', s', Psi)
      | (Psi', (Dot (Idx k, _) as s), Decl (Psi, Block (CtxBlock (l1, G))))
          ->
          let (Block (CtxBlock (l2, G')), w) = F.lfctxLFDec (Psi', k) in
          let checkSub' =
            function
            | ((I.Null, w1), s1, I.Null, _) -> s1
            | ((Decl (G', Dec (_, V')), w1), Dot (Idx k', s1), Decl
               (G, Dec (_, V)), m) ->
                if k' = m
                then
                  (if Conv.conv ((V', w1), (V, s1))
                   then
                     checkSub' ((G', (I.comp (w1, I.shift))), s1, G, (m + 1))
                   else
                     raise (Error "ContextBlock assignment not well-typed"))
                else raise (Error "ContextBlock assignment out of order") in
          checkSub (Psi', (checkSub' ((G', w), s, G, k)), Psi)
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
      | (G, All (Prim (D), F)) ->
          (try TypeCheck.checkDec (G, (D, I.id)); isFor ((I.Decl (G, D)), F)
           with | Error msg -> raise (Error msg))
      | (G, All (Block (CtxBlock (_, G1)), F)) ->
          isForBlock (G, (F.ctxToList G1), F)
      | (G, Ex (D, F)) ->
          (try TypeCheck.checkDec (G, (D, I.id)); isFor ((I.Decl (G, D)), F)
           with | Error msg -> raise (Error msg))
      | (G, F.True) -> ()
      | (G, And (F1, F2)) -> (isFor (G, F1); isFor (G, F2))
    let rec isForBlock =
      function
      | (G, nil, F) -> isFor (G, F)
      | (G, (D)::G1, F) -> isForBlock ((I.Decl (G, D)), G1, F)
    let rec checkTags' =
      function
      | (V, Ex _) -> ()
      | (Pi (_, V), All (_, F)) -> checkTags' (V, F)
      | _ -> raise Domain
    let rec checkTags =
      function
      | (I.Null, I.Null) -> ()
      | (Decl (G, Dec (_, V)), Decl (B, T)) ->
          (checkTags (G, B); (match T with | Lemma _ -> () | _ -> ()))
    let rec isState (State (n, (G, B), (IH, OH), d, O, H, F)) =
      TypeCheck.typeCheckCtx G;
      checkTags (G, B);
      if not (Abstract.closedCtx G)
      then raise (Error "State context not closed!")
      else ();
      map (function | (n', F') -> isFor (G, F')) H;
      isFor (G, F)
    let ((isFor)(* conv ((G, s), (G', s')) = B

       Invariant:
       B iff G [s]  == G' [s']
       Might migrate in to conv module  --cs
    *)
      (* extend (G, L) = G'

       Invariant:
       If   G : 'a ctx
       and  L : 'a list
       then G' = G, L : 'a ctx
    *)
      (* validBlock (Psi, k, (l : G)) = ()

       Invariant:
       If   |- Psi ctx
       and  |- k is a debruijn index (for LF context)
       and  |- l label
       and  |- G LFctx
       then validBlock terminates with ()
       iff  Psi = Psi1, l': (x1:A1 .. xn:An), Psi2
       and  l = l'
       and  Psi(k) = x1
       and  G == x1:A1 .. xn:An
    *)
      (* raiseSub (l:G, Psi') = s'

       Invariant:
       If   |- Psi ctx
       and  Psi |- l:G ctx
       and  Psi, l:G |- Psi' ctx
       then Psi, {G} Psi', l:G|- s' : Psi, l:G, Psi'
    *)
      (* raiseType (l:G, L) = L'

       Invariant:
       L contains no parameter block declarations
       Each x:A in L is mapped xto  x:{G}A in L'
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
      (* checkSub' ((G', w), s, G, m) = ()
          *)
      (* checkOpts (Psi, Delta, (O, s) *)(* [Psi' strict in  t] <------------------------- omission*)
      (* isState (S) = ()

       Invariant:

       Side effect:
       If it doesn't hold that |- S state, then exception Error is raised

       Remark: Function is only partially implemented
    *)
      (* ;          TextIO.print ("Checked: " ^ (FunPrint.Formatter.makestring_fmt (FunPrint.formatForBare (G, F'))) ^ "\n") *)
      (* n' is not checked for consistency   --cs *)) =
      isFor
    let check = checkRec
    let checkSub = checkSub
    let isState = isState
  end ;;
