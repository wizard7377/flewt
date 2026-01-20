
module type FUNTYPECHECK  =
  sig
    module StateSyn : STATESYN
    exception Error of string 
    val isFor : IntSyn.dctx -> FunSyn.__For -> unit
    val check : FunSyn.__Pro -> FunSyn.__For -> unit
    val checkSub : FunSyn.lfctx -> IntSyn.__Sub -> FunSyn.lfctx -> unit
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
                                   module FunPrint : FUNPRINT
                                 end) : FUNTYPECHECK =
  struct
    module StateSyn = StateSyn'
    exception Error of string 
    module I = IntSyn
    module F = FunSyn
    module S = StateSyn
    let rec conv (__Gs) (__Gs') =
      let exception Conv  in
        let rec conv __0__ __1__ =
          match (__0__, __1__) with
          | ((I.Null, s), (I.Null, s')) -> (s, s')
          | ((Decl (__G, Dec (_, __V)), s), (Decl (__G', Dec (_, __V')), s'))
              ->
              let (s1, s1') = conv ((__G, s), (__G', s')) in
              let (s2, s2') as ps = ((I.dot1 s1), (I.dot1 s1')) in
              if Conv.conv ((__V, s1), (__V', s1')) then ps else raise Conv
          | _ -> raise Conv in
        try conv (__Gs, __Gs'); true with | Conv -> false
    let rec extend __2__ __3__ =
      match (__2__, __3__) with
      | (__G, nil) -> __G
      | (__G, (__D)::__L) -> extend ((I.Decl (__G, __D)), __L)
    let rec validBlock (Psi) k (l, __G) =
      let rec skipBlock __4__ __5__ =
        match (__4__, __5__) with
        | (I.Null, k) -> k
        | (Decl (__G', _), k) -> skipBlock (__G', (k - 1)) in
      let rec validBlock' __6__ __7__ =
        match (__6__, __7__) with
        | (Decl (Psi, Block (CtxBlock (l', __G'))), 0) ->
            if (l' = l) && (conv ((__G, I.id), (__G', I.id)))
            then ()
            else raise (Error "Typecheck Error: Not a valid block")
        | (Decl (Psi, Prim _), 0) ->
            raise (Error "Typecheck Error: Not a valid block")
        | (I.Null, k) -> raise (Error "Typecheck Error: Not a valid block")
        | (Decl (Psi, Block (CtxBlock (l', __G'))), k) ->
            validBlock' (Psi, (skipBlock (__G', k)))
        | (Decl (Psi, Prim (__D)), k) -> validBlock' (Psi, (k - 1)) in
      validBlock' (Psi, k)
    let rec raiseSub (__G) (Psi') =
      let n = I.ctxLength __G in
      let m = I.ctxLength Psi' in
      let rec args __8__ __9__ __10__ =
        match (__8__, __9__, __10__) with
        | (0, a, __S) -> __S
        | (n', a, __S) ->
            let Dec (_, __V) = I.ctxDec (__G, n') in
            if Subordinate.belowEq ((I.targetFam __V), a)
            then
              args
                ((n' - 1), a, (I.App ((I.Root ((I.BVar n'), I.Nil)), __S)))
            else args ((n' - 1), a, __S) in
      let rec term m' =
        let Dec (_, __V) = I.ctxDec (Psi', m') in
        I.Exp
          (I.Root ((I.BVar (n + m')), (args (n, (I.targetFam __V), I.Nil)))) in
      let rec raiseSub'' __11__ __12__ =
        match (__11__, __12__) with
        | (0, s) -> s
        | (m', s) -> raiseSub'' ((m' - 1), (I.Dot ((term m'), s))) in
      let rec raiseSub' __13__ __14__ =
        match (__13__, __14__) with
        | (0, s) -> raiseSub'' (m, s)
        | (n', s) -> raiseSub' ((n' - 1), (I.Dot ((I.Idx n'), s))) in
      raiseSub' (n, (I.Shift (n + m)))
    let rec raiseType (CtxBlock (l, __G)) (Psi') =
      let rec raiseType'' __15__ __16__ __17__ =
        match (__15__, __16__, __17__) with
        | (I.Null, Vn, a) -> Vn
        | (Decl (__G', (Dec (_, __V') as D)), Vn, a) ->
            if Subordinate.belowEq ((I.targetFam __V'), a)
            then
              raiseType'' (__G', (Abstract.piDepend ((__D, I.Maybe), Vn)), a)
            else raiseType'' (__G', (Weaken.strengthenExp (Vn, I.shift)), a) in
      let rec raiseType' __18__ __19__ =
        match (__18__, __19__) with
        | (Psi1, nil) -> nil
        | (Psi1, (Prim (Dec (x, __V) as D))::Psi1') ->
            let s = raiseSub (__G, Psi1) in
            let Vn = Whnf.normalize (__V, s) in
            let a = I.targetFam Vn in
            let __D' = I.Dec (x, (raiseType'' (__G, Vn, a))) in
            (F.Prim __D') :: (raiseType' ((I.Decl (Psi1, __D)), Psi1')) in
      ((raiseType' (I.Null, Psi'))
        (* no case of F.Block by invariant *))
    let rec raiseM __20__ __21__ =
      match (__20__, __21__) with
      | (__B, nil) -> nil
      | (__B, (MDec (xx, __F))::__L) ->
          (::) (F.MDec (xx, (F.All ((F.Block __B), __F)))) raiseM (__B, __L)
    let rec psub __22__ __23__ __24__ =
      match (__22__, __23__, __24__) with
      | (k, I.Null, s) -> s
      | (k, Decl (__G, _), s) -> psub ((k - 1), __G, (I.Dot ((I.Idx k), s)))
    let rec deltaSub __25__ __26__ =
      match (__25__, __26__) with
      | (I.Null, s) -> I.Null
      | (Decl (Delta, DD), s) ->
          I.Decl ((deltaSub (Delta, s)), (F.mdecSub (DD, s)))
    let rec shift (Delta) = deltaSub (Delta, I.shift)
    let rec shifts __27__ __28__ =
      match (__27__, __28__) with
      | (I.Null, Delta) -> Delta
      | (Decl (__G, _), Delta) -> shifts (__G, (shift Delta))
    let rec shiftBlock (CtxBlock (_, __G)) (Delta) = shifts (__G, Delta)
    let rec shiftSub __29__ __30__ =
      match (__29__, __30__) with
      | (I.Null, s) -> s
      | (Decl (__G, _), s) -> shiftSub (__G, (I.comp (I.shift, s)))
    let rec shiftSubBlock (CtxBlock (_, __G)) s = shiftSub (__G, s)
    let rec check __31__ __32__ __33__ __34__ =
      match (__31__, __32__, __33__, __34__) with
      | (Psi, Delta, F.Unit, (F.True, _)) -> ()
      | (Psi, Delta, Rec (DD, __P), __F) ->
          check (Psi, (I.Decl (Delta, DD)), __P, __F)
      | (Psi, Delta, Lam ((Prim (Dec (_, __V)) as LD), __P),
         (All (Prim (Dec (_, __V')), __F'), s')) ->
          if Conv.conv ((__V, I.id), (__V', s'))
          then
            check
              ((I.Decl (Psi, LD)), (shift Delta), __P, (__F', (I.dot1 s')))
          else raise (Error "Typecheck Error: Primitive Abstraction")
      | (Psi, Delta, Lam ((Block (CtxBlock (l, __G) as B) as LD), __P),
         (All (Block (CtxBlock (l', __G')), __F'), s')) ->
          if (l = l') && (conv ((__G, I.id), (__G', s')))
          then
            check
              ((I.Decl (Psi, LD)), (shiftBlock (__B, Delta)), __P,
                (__F', (F.dot1n (__G, s'))))
          else raise (Error "Typecheck Error: Block Abstraction")
      | (Psi, Delta, Inx (__M, __P), (Ex (Dec (_, __V'), __F'), s')) ->
          (TypeCheck.typeCheck ((F.makectx Psi), (__M, (I.EClo (__V', s'))));
           check (Psi, Delta, __P, (__F', (I.Dot ((I.Exp __M), s')))))
      | (Psi, Delta, Case (Opts (__O)), (__F', s')) ->
          checkOpts (Psi, Delta, __O, (__F', s'))
      | (Psi, Delta, Pair (__P1, __P2), (And (F1', F2'), s')) ->
          (check (Psi, Delta, __P1, (F1', s'));
           check (Psi, Delta, __P2, (F2', s')))
      | (Psi, Delta, Let (__Ds, __P), (__F', s')) ->
          let (Psi', Delta', s'') = assume (Psi, Delta, __Ds) in
          check
            ((extend (Psi, Psi')), (extend (Delta, Delta')), __P,
              (__F', (I.comp (s', s''))))
      | _ -> raise (Error "Typecheck Error: Term not well-typed")
    let rec infer (Delta) kk = ((I.ctxLookup (Delta, kk)), I.id)
    let rec assume __35__ __36__ __37__ =
      match (__35__, __36__, __37__) with
      | (Psi, Delta, F.Empty) -> (nil, nil, I.id)
      | (Psi, Delta, Split (kk, __Ds)) ->
          (match infer (Delta, kk) with
           | (MDec (name, Ex (__D, __F)), s) ->
               let LD = F.Prim (I.decSub (__D, s)) in
               let DD = F.MDec (name, (F.forSub (__F, (I.dot1 s)))) in
               let (Psi', Delta', s') =
                 assume
                   ((I.Decl (Psi, LD)), (I.Decl ((shift Delta), DD)), __Ds) in
               ((LD :: Psi'), ((F.mdecSub (DD, s')) :: Delta'),
                 (I.comp (I.shift, s')))
           | _ -> raise (Error "Typecheck Error: Declaration"))
      | (Psi, Delta, New (__B, __Ds)) ->
          let _ =
            TypeCheck.typeCheck
              ((F.makectx (I.Decl (Psi, (F.Block __B)))),
                ((I.Uni I.Type), (I.Uni I.Kind))) in
          let (Psi', Delta', s') =
            assume
              ((I.Decl (Psi, (F.Block __B))), (shiftBlock (__B, Delta)),
                __Ds) in
          ((((raiseType (__B, Psi')), (raiseM (__B, Delta')), s'))
            (* check B valid context block       <-------------- omission *))
      | (Psi, Delta, App ((kk, __U), __Ds)) ->
          (match infer (Delta, kk) with
           | (MDec (name, All (Prim (Dec (_, __V)), __F)), s) ->
               let _ =
                 try
                   TypeCheck.typeCheck
                     ((F.makectx Psi), (__U, (I.EClo (__V, s))))
                 with
                 | Error msg ->
                     raise
                       (Error
                          ((^) (((^) (((^) (msg ^ " ") Print.expToString
                                         ((F.makectx Psi), __U))
                                        ^ " has type ")
                                   Print.expToString
                                   ((F.makectx Psi),
                                     (TypeCheck.infer' ((F.makectx Psi), __U))))
                                  ^ " expected ")
                             Print.expToString
                             ((F.makectx Psi), (I.EClo (__V, s))))) in
               let DD =
                 F.MDec (name, (F.forSub (__F, (I.Dot ((I.Exp __U), s))))) in
               let (Psi', Delta', s') =
                 assume (Psi, (I.Decl (Delta, DD)), __Ds) in
               (Psi', ((F.mdecSub (DD, s')) :: Delta'), s')
           | (MDec (name, __F), s) ->
               raise
                 (Error
                    ("Typecheck Error: Declaration App" ^
                       (FunPrint.forToString (I.Null, __F) ["x"]))))
      | (Psi, Delta, PApp ((kk, k), __Ds)) ->
          (match infer (Delta, kk) with
           | (MDec (name, All (Block (CtxBlock (l, __G)), __F)), s) ->
               let _ = validBlock (Psi, k, (l, __G)) in
               let DD = F.MDec (name, (F.forSub (__F, (psub (k, __G, s))))) in
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
          let LemmaDec (names, _, __F) = F.lemmaLookup cc in
          let name = foldr (^) "" names in
          let DD = F.MDec ((Some name), __F) in
          let (Psi', Delta', s') = assume (Psi, (I.Decl (Delta, DD)), __Ds) in
          (Psi', ((F.mdecSub (DD, s')) :: Delta'), s')
    let rec checkSub __42__ __43__ __44__ =
      match (__42__, __43__, __44__) with
      | (I.Null, Shift 0, I.Null) -> ()
      | (Decl (Psi, Prim (__D)), Shift k, I.Null) ->
          if k > 0
          then checkSub (Psi, (I.Shift (k - 1)), I.Null)
          else raise (Error "Substitution not well-typed")
      | (Decl (Psi, Block (CtxBlock (_, __G))), Shift k, I.Null) ->
          let g = I.ctxLength __G in
          if k >= g
          then checkSub (Psi, (I.Shift (k - g)), I.Null)
          else raise (Error "Substitution not well-typed")
      | (Psi', Shift k, Psi) ->
          checkSub (Psi', (I.Dot ((I.Idx (k + 1)), (I.Shift (k + 1)))), Psi)
      | (Psi', Dot (Idx k, s'), Decl (Psi, Prim (Dec (_, __V2)))) ->
          let __G' = F.makectx Psi' in
          let Dec (_, __V1) = I.ctxDec (__G', k) in
          if Conv.conv ((__V1, I.id), (__V2, s'))
          then checkSub (Psi', s', Psi)
          else
            raise
              (Error
                 ((^) (((^) "Substitution not well-typed \n  found: "
                          Print.expToString (__G', __V1))
                         ^ "\n  expected: ")
                    Print.expToString (__G', (I.EClo (__V2, s')))))
      | (Psi', Dot (Exp (__U), s'), Decl (Psi, Prim (Dec (_, __V2)))) ->
          let __G' = F.makectx Psi' in
          let _ = TypeCheck.typeCheck (__G', (__U, (I.EClo (__V2, s')))) in
          checkSub (Psi', s', Psi)
      | (Psi', (Dot (Idx k, _) as s), Decl (Psi, Block (CtxBlock (l1, __G))))
          ->
          let (Block (CtxBlock (l2, __G')), w) = F.lfctxLFDec (Psi', k) in
          let rec checkSub' __38__ __39__ __40__ __41__ =
            match (__38__, __39__, __40__, __41__) with
            | ((I.Null, w1), s1, I.Null, _) -> s1
            | ((Decl (__G', Dec (_, __V')), w1), Dot (Idx k', s1), Decl
               (__G, Dec (_, __V)), m) ->
                if k' = m
                then
                  (if Conv.conv ((__V', w1), (__V, s1))
                   then
                     checkSub'
                       ((__G', (I.comp (w1, I.shift))), s1, __G, (m + 1))
                   else
                     raise (Error "ContextBlock assignment not well-typed"))
                else raise (Error "ContextBlock assignment out of order") in
          ((checkSub (Psi', (checkSub' ((__G', w), s, __G, k)), Psi))
            (* check that l1 = l2     <----------------------- omission *)
            (* checkSub' ((G', w), s, G, m) = ()
          *))
    let rec checkOpts __45__ __46__ __47__ __48__ =
      match (__45__, __46__, __47__, __48__) with
      | (Psi, Delta, nil, _) -> ()
      | (Psi, Delta, (Psi', t, __P)::__O, (__F', s')) ->
          (((checkSub (Psi', t, Psi);
             check
               (Psi', (deltaSub (Delta, t)), __P, (__F', (I.comp (s', t))));
             checkOpts (Psi, Delta, __O, (__F', s'))))
          (* [Psi' strict in  t] <------------------------- omission*))
    let rec checkRec (__P) (__T) = check (I.Null, I.Null, __P, (__T, I.id))
    let rec isFor __49__ __50__ =
      match (__49__, __50__) with
      | (__G, All (Prim (__D), __F)) ->
          (try
             TypeCheck.checkDec (__G, (__D, I.id));
             isFor ((I.Decl (__G, __D)), __F)
           with | Error msg -> raise (Error msg))
      | (__G, All (Block (CtxBlock (_, __G1)), __F)) ->
          isForBlock (__G, (F.ctxToList __G1), __F)
      | (__G, Ex (__D, __F)) ->
          (try
             TypeCheck.checkDec (__G, (__D, I.id));
             isFor ((I.Decl (__G, __D)), __F)
           with | Error msg -> raise (Error msg))
      | (__G, F.True) -> ()
      | (__G, And (__F1, __F2)) -> (isFor (__G, __F1); isFor (__G, __F2))
    let rec isForBlock __51__ __52__ __53__ =
      match (__51__, __52__, __53__) with
      | (__G, nil, __F) -> isFor (__G, __F)
      | (__G, (__D)::__G1, __F) ->
          isForBlock ((I.Decl (__G, __D)), __G1, __F)
    let rec checkTags' __54__ __55__ =
      match (__54__, __55__) with
      | (__V, Ex _) -> ()
      | (Pi (_, __V), All (_, __F)) -> checkTags' (__V, __F)
      | _ -> raise Domain
    let rec checkTags __56__ __57__ =
      match (__56__, __57__) with
      | (I.Null, I.Null) -> ()
      | (Decl (__G, Dec (_, __V)), Decl (__B, __T)) ->
          (checkTags (__G, __B); (match __T with | Lemma _ -> () | _ -> ()))
    let rec isState (State (n, (__G, __B), (IH, OH), d, __O, __H, __F)) =
      ((TypeCheck.typeCheckCtx __G;
        checkTags (__G, __B);
        if not (Abstract.closedCtx __G)
        then raise (Error "State context not closed!")
        else ();
        map
          (fun n' ->
             fun (__F') -> ((isFor (__G, __F'))
               (* ;          TextIO.print ("Checked: " ^ (FunPrint.Formatter.makestring_fmt (FunPrint.formatForBare (G, F'))) ^ "\n") *)))
          __H;
        isFor (__G, __F))
      (* n' is not checked for consistency   --cs *))
    let isFor = isFor
    let check = checkRec
    let checkSub = checkSub
    let isState = isState
  end ;;
