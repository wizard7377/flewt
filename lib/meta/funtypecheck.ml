
(* Type checking for functional proof term calculus *)
(* Author: Carsten Schuermann *)
module type FUNTYPECHECK  =
  sig
    (*! structure FunSyn : FUNSYN !*)
    module StateSyn : STATESYN
    exception Error of string 
    val isFor : (IntSyn.dctx * FunSyn.__For) -> unit
    val check : (FunSyn.__Pro * FunSyn.__For) -> unit
    val checkSub : (FunSyn.lfctx * IntSyn.__Sub * FunSyn.lfctx) -> unit
    val isState : StateSyn.__State -> unit
  end;;




(* Type checking for functional proof term calculus *)
(* Author: Carsten Schuermann *)
module FunTypeCheck(FunTypeCheck:sig
                                   (*! structure FunSyn' : FUNSYN !*)
                                   module StateSyn' : STATESYN
                                   module Abstract : ABSTRACT
                                   module TypeCheck : TYPECHECK
                                   module Conv : CONV
                                   module Whnf : WHNF
                                   module Print : PRINT
                                   module Subordinate : SUBORDINATE
                                   module Weaken : WEAKEN
                                   (*! sharing StateSyn'.FunSyn = FunSyn' !*)
                                   (*! sharing Abstract.IntSyn = FunSyn'.IntSyn !*)
                                   (*! sharing TypeCheck.IntSyn = FunSyn'.IntSyn !*)
                                   (*! sharing Conv.IntSyn = FunSyn'.IntSyn !*)
                                   (*! sharing Whnf.IntSyn = FunSyn'.IntSyn !*)
                                   (*! sharing Print.IntSyn = FunSyn'.IntSyn !*)
                                   (*! sharing Subordinate.IntSyn = FunSyn'.IntSyn !*)
                                   (*! sharing Weaken.IntSyn = FunSyn'.IntSyn   !*)
                                   module FunPrint : FUNPRINT
                                 end) : FUNTYPECHECK =
  struct
    (*! sharing FunPrint.FunSyn = FunSyn' !*)
    (*! structure FunSyn = FunSyn' !*)
    module StateSyn = StateSyn'
    exception Error of string 
    module I = IntSyn
    module F = FunSyn
    module S = StateSyn
    let rec conv (__Gs, __Gs') =
      let exception Conv  in
        let rec conv =
          function
          | ((I.Null, s), (I.Null, s')) -> (s, s')
          | ((Decl (__g, Dec (_, __v)), s), (Decl (__g', Dec (_, __v')), s')) ->
              let (s1, s1') = conv ((__g, s), (__g', s')) in
              let (s2, s2') as ps = ((I.dot1 s1), (I.dot1 s1')) in
              if Conv.conv ((__v, s1), (__v', s1')) then ps else raise Conv
          | _ -> raise Conv in
        try conv (__Gs, __Gs'); true__ with | Conv -> false__
    let rec extend =
      function | (__g, nil) -> __g | (__g, (__d)::__l) -> extend ((I.Decl (__g, __d)), __l)
    let rec validBlock (Psi, k, (l, __g)) =
      let rec skipBlock =
        function
        | (I.Null, k) -> k
        | (Decl (__g', _), k) -> skipBlock (__g', (k - 1)) in
      let rec validBlock' =
        function
        | (Decl (Psi, Block (CtxBlock (l', __g'))), 0) ->
            if (l' = l) && (conv ((__g, I.id), (__g', I.id)))
            then ()
            else raise (Error "Typecheck Error: Not a valid block")
        | (Decl (Psi, Prim _), 0) ->
            raise (Error "Typecheck Error: Not a valid block")
        | (I.Null, k) -> raise (Error "Typecheck Error: Not a valid block")
        | (Decl (Psi, Block (CtxBlock (l', __g'))), k) ->
            validBlock' (Psi, (skipBlock (__g', k)))
        | (Decl (Psi, Prim (__d)), k) -> validBlock' (Psi, (k - 1)) in
      validBlock' (Psi, k)
    let rec raiseSub (__g, Psi') =
      let n = I.ctxLength __g in
      let m = I.ctxLength Psi' in
      let rec args =
        function
        | (0, a, S) -> S
        | (n', a, S) ->
            let Dec (_, __v) = I.ctxDec (__g, n') in
            if Subordinate.belowEq ((I.targetFam __v), a)
            then
              args ((n' - 1), a, (I.App ((I.Root ((I.BVar n'), I.Nil)), S)))
            else args ((n' - 1), a, S) in
      let rec term m' =
        let Dec (_, __v) = I.ctxDec (Psi', m') in
        I.Exp
          (I.Root ((I.BVar (n + m')), (args (n, (I.targetFam __v), I.Nil)))) in
      let rec raiseSub'' =
        function
        | (0, s) -> s
        | (m', s) -> raiseSub'' ((m' - 1), (I.Dot ((term m'), s))) in
      let rec raiseSub' =
        function
        | (0, s) -> raiseSub'' (m, s)
        | (n', s) -> raiseSub' ((n' - 1), (I.Dot ((I.Idx n'), s))) in
      raiseSub' (n, (I.Shift (n + m)))
    let rec raiseType (CtxBlock (l, __g), Psi') =
      let rec raiseType'' =
        function
        | (I.Null, Vn, a) -> Vn
        | (Decl (__g', (Dec (_, __v') as __d)), Vn, a) ->
            if Subordinate.belowEq ((I.targetFam __v'), a)
            then raiseType'' (__g', (Abstract.piDepend ((__d, I.Maybe), Vn)), a)
            else raiseType'' (__g', (Weaken.strengthenExp (Vn, I.shift)), a) in
      let rec raiseType' =
        function
        | (Psi1, nil) -> nil
        | (Psi1, (Prim (Dec (x, __v) as __d))::Psi1') ->
            let s = raiseSub (__g, Psi1) in
            let Vn = Whnf.normalize (__v, s) in
            let a = I.targetFam Vn in
            let __d' = I.Dec (x, (raiseType'' (__g, Vn, a))) in
            (F.Prim __d') :: (raiseType' ((I.Decl (Psi1, __d)), Psi1')) in
      raiseType' (I.Null, Psi')
    let rec raiseM =
      function
      | (B, nil) -> nil
      | (B, (MDec (xx, F))::__l) ->
          (::) (F.MDec (xx, (F.All ((F.Block B), F)))) raiseM (B, __l)
    let rec psub =
      function
      | (k, I.Null, s) -> s
      | (k, Decl (__g, _), s) -> psub ((k - 1), __g, (I.Dot ((I.Idx k), s)))
    let rec deltaSub =
      function
      | (I.Null, s) -> I.Null
      | (Decl (Delta, DD), s) ->
          I.Decl ((deltaSub (Delta, s)), (F.mdecSub (DD, s)))
    let rec shift (Delta) = deltaSub (Delta, I.shift)
    let rec shifts =
      function
      | (I.Null, Delta) -> Delta
      | (Decl (__g, _), Delta) -> shifts (__g, (shift Delta))
    let rec shiftBlock (CtxBlock (_, __g), Delta) = shifts (__g, Delta)
    let rec shiftSub =
      function
      | (I.Null, s) -> s
      | (Decl (__g, _), s) -> shiftSub (__g, (I.comp (I.shift, s)))
    let rec shiftSubBlock (CtxBlock (_, __g), s) = shiftSub (__g, s)
    let rec check =
      function
      | (Psi, Delta, F.Unit, (F.True, _)) -> ()
      | (Psi, Delta, Rec (DD, P), F) ->
          check (Psi, (I.Decl (Delta, DD)), P, F)
      | (Psi, Delta, Lam ((Prim (Dec (_, __v)) as LD), P),
         (All (Prim (Dec (_, __v')), __F'), s')) ->
          if Conv.conv ((__v, I.id), (__v', s'))
          then
            check ((I.Decl (Psi, LD)), (shift Delta), P, (__F', (I.dot1 s')))
          else raise (Error "Typecheck Error: Primitive Abstraction")
      | (Psi, Delta, Lam ((Block (CtxBlock (l, __g) as B) as LD), P),
         (All (Block (CtxBlock (l', __g')), __F'), s')) ->
          if (l = l') && (conv ((__g, I.id), (__g', s')))
          then
            check
              ((I.Decl (Psi, LD)), (shiftBlock (B, Delta)), P,
                (__F', (F.dot1n (__g, s'))))
          else raise (Error "Typecheck Error: Block Abstraction")
      | (Psi, Delta, Inx (M, P), (Ex (Dec (_, __v'), __F'), s')) ->
          (TypeCheck.typeCheck ((F.makectx Psi), (M, (I.EClo (__v', s'))));
           check (Psi, Delta, P, (__F', (I.Dot ((I.Exp M), s')))))
      | (Psi, Delta, Case (Opts (O)), (__F', s')) ->
          checkOpts (Psi, Delta, O, (__F', s'))
      | (Psi, Delta, Pair (__P1, __P2), (And (__F1', __F2'), s')) ->
          (check (Psi, Delta, __P1, (__F1', s'));
           check (Psi, Delta, __P2, (__F2', s')))
      | (Psi, Delta, Let (__Ds, P), (__F', s')) ->
          let (Psi', Delta', s'') = assume (Psi, Delta, __Ds) in
          check
            ((extend (Psi, Psi')), (extend (Delta, Delta')), P,
              (__F', (I.comp (s', s''))))
      | _ -> raise (Error "Typecheck Error: Term not well-typed")
    let rec infer (Delta, kk) = ((I.ctxLookup (Delta, kk)), I.id)
    let rec assume =
      function
      | (Psi, Delta, F.Empty) -> (nil, nil, I.id)
      | (Psi, Delta, Split (kk, __Ds)) ->
          (match infer (Delta, kk) with
           | (MDec (name, Ex (__d, F)), s) ->
               let LD = F.Prim (I.decSub (__d, s)) in
               let DD = F.MDec (name, (F.forSub (F, (I.dot1 s)))) in
               let (Psi', Delta', s') =
                 assume
                   ((I.Decl (Psi, LD)), (I.Decl ((shift Delta), DD)), __Ds) in
               ((LD :: Psi'), ((F.mdecSub (DD, s')) :: Delta'),
                 (I.comp (I.shift, s')))
           | _ -> raise (Error "Typecheck Error: Declaration"))
      | (Psi, Delta, New (B, __Ds)) ->
          let _ =
            TypeCheck.typeCheck
              ((F.makectx (I.Decl (Psi, (F.Block B)))),
                ((I.Uni I.Type), (I.Uni I.Kind))) in
          let (Psi', Delta', s') =
            assume ((I.Decl (Psi, (F.Block B))), (shiftBlock (B, Delta)), __Ds) in
          ((raiseType (B, Psi')), (raiseM (B, Delta')), s')
      | (Psi, Delta, App ((kk, __u), __Ds)) ->
          (match infer (Delta, kk) with
           | (MDec (name, All (Prim (Dec (_, __v)), F)), s) ->
               let _ =
                 try
                   TypeCheck.typeCheck
                     ((F.makectx Psi), (__u, (I.EClo (__v, s))))
                 with
                 | Error msg ->
                     raise
                       (Error
                          ((^) (((^) (((^) (msg ^ " ") Print.expToString
                                         ((F.makectx Psi), __u))
                                        ^ " has type ")
                                   Print.expToString
                                   ((F.makectx Psi),
                                     (TypeCheck.infer' ((F.makectx Psi), __u))))
                                  ^ " expected ")
                             Print.expToString
                             ((F.makectx Psi), (I.EClo (__v, s))))) in
               let DD = F.MDec (name, (F.forSub (F, (I.Dot ((I.Exp __u), s))))) in
               let (Psi', Delta', s') =
                 assume (Psi, (I.Decl (Delta, DD)), __Ds) in
               (Psi', ((F.mdecSub (DD, s')) :: Delta'), s')
           | (MDec (name, F), s) ->
               raise
                 (Error
                    ("Typecheck Error: Declaration App" ^
                       (FunPrint.forToString (I.Null, F) ["x"]))))
      | (Psi, Delta, PApp ((kk, k), __Ds)) ->
          (match infer (Delta, kk) with
           | (MDec (name, All (Block (CtxBlock (l, __g)), F)), s) ->
               let _ = validBlock (Psi, k, (l, __g)) in
               let DD = F.MDec (name, (F.forSub (F, (psub (k, __g, s))))) in
               let (Psi', Delta', s') =
                 assume (Psi, (I.Decl (Delta, DD)), __Ds) in
               (Psi', ((F.mdecSub (DD, s')) :: Delta'), s')
           | _ -> raise (Error "Typecheck Error: Declaration PApp"))
      | (Psi, Delta, Left (kk, __Ds)) ->
          (match infer (Delta, kk) with
           | (MDec (name, And (__F1, __F2)), s) ->
               let DD = F.MDec (name, (F.forSub (__F1, s))) in
               let (Psi', Delta', s') =
                 assume (Psi, (I.Decl (Delta, DD)), __Ds) in
               (Psi', ((F.mdecSub (DD, s')) :: Delta'), s')
           | _ -> raise (Error "Typecheck Error: Declaration Left"))
      | (Psi, Delta, Right (kk, __Ds)) ->
          (match infer (Delta, kk) with
           | (MDec (name, And (__F1, __F2)), s) ->
               let DD = F.MDec (name, (F.forSub (__F2, s))) in
               let (Psi', Delta', s') =
                 assume (Psi, (I.Decl (Delta, DD)), __Ds) in
               (Psi', ((F.mdecSub (DD, s')) :: Delta'), s')
           | _ -> raise (Error "Typecheck Error: Declaration Left"))
      | (Psi, Delta, Lemma (cc, __Ds)) ->
          let LemmaDec (names, _, F) = F.lemmaLookup cc in
          let name = foldr (^) "" names in
          let DD = F.MDec ((Some name), F) in
          let (Psi', Delta', s') = assume (Psi, (I.Decl (Delta, DD)), __Ds) in
          (Psi', ((F.mdecSub (DD, s')) :: Delta'), s')
    let rec checkSub =
      function
      | (I.Null, Shift 0, I.Null) -> ()
      | (Decl (Psi, Prim (__d)), Shift k, I.Null) ->
          if k > 0
          then checkSub (Psi, (I.Shift (k - 1)), I.Null)
          else raise (Error "Substitution not well-typed")
      | (Decl (Psi, Block (CtxBlock (_, __g))), Shift k, I.Null) ->
          let g = I.ctxLength __g in
          if k >= g
          then checkSub (Psi, (I.Shift (k - g)), I.Null)
          else raise (Error "Substitution not well-typed")
      | (Psi', Shift k, Psi) ->
          checkSub (Psi', (I.Dot ((I.Idx (k + 1)), (I.Shift (k + 1)))), Psi)
      | (Psi', Dot (Idx k, s'), Decl (Psi, Prim (Dec (_, V2)))) ->
          let __g' = F.makectx Psi' in
          let Dec (_, V1) = I.ctxDec (__g', k) in
          if Conv.conv ((V1, I.id), (V2, s'))
          then checkSub (Psi', s', Psi)
          else
            raise
              (Error
                 ((^) (((^) "Substitution not well-typed \n  found: "
                          Print.expToString (__g', V1))
                         ^ "\n  expected: ")
                    Print.expToString (__g', (I.EClo (V2, s')))))
      | (Psi', Dot (Exp (__u), s'), Decl (Psi, Prim (Dec (_, V2)))) ->
          let __g' = F.makectx Psi' in
          let _ = TypeCheck.typeCheck (__g', (__u, (I.EClo (V2, s')))) in
          checkSub (Psi', s', Psi)
      | (Psi', (Dot (Idx k, _) as s), Decl (Psi, Block (CtxBlock (l1, __g))))
          ->
          let (Block (CtxBlock (l2, __g')), w) = F.lfctxLFDec (Psi', k) in
          let rec checkSub' =
            function
            | ((I.Null, w1), s1, I.Null, _) -> s1
            | ((Decl (__g', Dec (_, __v')), w1), Dot (Idx k', s1), Decl
               (__g, Dec (_, __v)), m) ->
                if k' = m
                then
                  (if Conv.conv ((__v', w1), (__v, s1))
                   then
                     checkSub' ((__g', (I.comp (w1, I.shift))), s1, __g, (m + 1))
                   else
                     raise (Error "ContextBlock assignment not well-typed"))
                else raise (Error "ContextBlock assignment out of order") in
          checkSub (Psi', (checkSub' ((__g', w), s, __g, k)), Psi)
    let rec checkOpts =
      function
      | (Psi, Delta, nil, _) -> ()
      | (Psi, Delta, (Psi', t, P)::O, (__F', s')) ->
          (checkSub (Psi', t, Psi);
           check (Psi', (deltaSub (Delta, t)), P, (__F', (I.comp (s', t))));
           checkOpts (Psi, Delta, O, (__F', s')))
    let rec checkRec (P, T) = check (I.Null, I.Null, P, (T, I.id))
    let rec isFor =
      function
      | (__g, All (Prim (__d), F)) ->
          (try TypeCheck.checkDec (__g, (__d, I.id)); isFor ((I.Decl (__g, __d)), F)
           with | Error msg -> raise (Error msg))
      | (__g, All (Block (CtxBlock (_, G1)), F)) ->
          isForBlock (__g, (F.ctxToList G1), F)
      | (__g, Ex (__d, F)) ->
          (try TypeCheck.checkDec (__g, (__d, I.id)); isFor ((I.Decl (__g, __d)), F)
           with | Error msg -> raise (Error msg))
      | (__g, F.True) -> ()
      | (__g, And (__F1, __F2)) -> (isFor (__g, __F1); isFor (__g, __F2))
    let rec isForBlock =
      function
      | (__g, nil, F) -> isFor (__g, F)
      | (__g, (__d)::G1, F) -> isForBlock ((I.Decl (__g, __d)), G1, F)
    let rec checkTags' =
      function
      | (__v, Ex _) -> ()
      | (Pi (_, __v), All (_, F)) -> checkTags' (__v, F)
      | _ -> raise Domain
    let rec checkTags =
      function
      | (I.Null, I.Null) -> ()
      | (Decl (__g, Dec (_, __v)), Decl (B, T)) ->
          (checkTags (__g, B); (match T with | Lemma _ -> () | _ -> ()))
    let rec isState (State (n, (__g, B), (IH, OH), d, O, H, F)) =
      TypeCheck.typeCheckCtx __g;
      checkTags (__g, B);
      if not (Abstract.closedCtx __g)
      then raise (Error "State context not closed!")
      else ();
      map (function | (n', __F') -> isFor (__g, __F')) H;
      isFor (__g, F)
    (* conv ((__g, s), (__g', s')) = B

       Invariant:
       B iff __g [s]  == __g' [s']
       Might migrate in to conv module  --cs
    *)
    (* extend (__g, __l) = __g'

       Invariant:
       If   __g : 'a ctx
       and  __l : 'a list
       then __g' = __g, __l : 'a ctx
    *)
    (* validBlock (Psi, k, (l : __g)) = ()

       Invariant:
       If   |- Psi ctx
       and  |- k is a debruijn index (for LF context)
       and  |- l label
       and  |- __g LFctx
       then validBlock terminates with ()
       iff  Psi = Psi1, l': (x1:A1 .. xn:An), Psi2
       and  l = l'
       and  Psi(k) = x1
       and  __g == x1:A1 .. xn:An
    *)
    (* raiseSub (l:__g, Psi') = s'

       Invariant:
       If   |- Psi ctx
       and  Psi |- l:__g ctx
       and  Psi, l:__g |- Psi' ctx
       then Psi, {__g} Psi', l:__g|- s' : Psi, l:__g, Psi'
    *)
    (* raiseType (l:__g, __l) = __l'

       Invariant:
       __l contains no parameter block declarations
       Each x:A in __l is mapped xto  x:{__g}A in __l'
       __l' preserves the order of __l
    *)
    (* no case of F.Block by invariant *)
    (* raiseM (B, __l) = __l'

       Invariant
       Each xx in F in __l is mapped to xx in PI B. F in __l'
       __l' preserves the order of __l
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
        returns () if there exists a __F',
              s.t. Psi, Delta |- P  : __F'
              and  Psi |- __F' = F[s] formula
       otherwise Error is raised
    *)
    (* assume (Psi, Delta, __Ds) = (Psi', Delta', s')

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
    (* checkSub' ((__g', w), s, __g, m) = ()
          *)
    (* checkOpts (Psi, Delta, (O, s) *)
    (* [Psi' strict in  t] <------------------------- omission*)
    (* isState (S) = ()

       Invariant:

       Side effect:
       If it doesn't hold that |- S state, then exception Error is raised

       Remark: Function is only partially implemented
    *)
    (* ;          TextIO.print ("Checked: " ^ (FunPrint.Formatter.makestring_fmt (FunPrint.formatForBare (__g, __F'))) ^ "\n") *)
    (* n' is not checked for consistency   --cs *)
    let isFor = isFor
    let check = checkRec
    let checkSub = checkSub
    let isState = isState
  end ;;
