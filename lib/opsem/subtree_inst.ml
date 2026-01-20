
module MemoTableInst(MemoTableInst:sig
                                     module Conv : CONV
                                     module Whnf : WHNF
                                     module Match : MATCH
                                     module Assign : ASSIGN
                                     module AbstractTabled : ABSTRACTTABLED
                                     module Print : PRINT
                                   end) : MEMOTABLE =
  struct
    module AbstractTabled = AbstractTabled
    type nonrec normalSubsts =
      (((int * IntSyn.__Exp))(* local depth *)) RBSet.ordSet
    type nonrec exSubsts = IntSyn.__Front RBSet.ordSet
    let (nid : unit -> normalSubsts) = RBSet.new__
    let (asid : unit -> exSubsts) = RBSet.new__
    let aid = TableParam.aid
    let rec isId s = RBSet.isEmpty s
    type nonrec ctx = (int * IntSyn.__Dec) list ref
    let rec emptyCtx () = (ref [] : ctx)
    let rec copy (__L) = (ref (!__L) : ctx)
    let rec delete x (__L : ctx) =
      let rec del __0__ __1__ __2__ =
        match (__0__, __1__, __2__) with
        | (x, [], __L) -> None
        | (x, ((y, __E) as H)::__L, __L') ->
            if x = y
            then Some ((y, __E), ((rev __L') @ __L))
            else del (x, __L, (__H :: __L')) in
      match del (x, (!__L), []) with
      | None -> None
      | Some ((y, __E), __L') -> (__L := __L'; Some (y, __E))
    let rec member x (__L : ctx) =
      let rec memb __3__ __4__ =
        match (__3__, __4__) with
        | (x, []) -> None
        | (x, ((y, (Dec (n, __U) as E))::__L as H)) ->
            if x = y then Some (y, __E) else memb (x, __L)
        | (x, ((y, (ADec (n, d) as E))::__L as H)) ->
            if x = y then Some (y, __E) else memb (x, __L) in
      memb (x, (!__L))
    let rec insertList (__E) (__L) = __L := (__E :: (!__L))
    type __Tree =
      | Leaf of ((ctx * normalSubsts) *
      ((((((int * int))(* #G *)(* #EVar *))
          * ctx * IntSyn.dctx * TableParam.__ResEqn * TableParam.answer * int
          * TableParam.__Status))(* G *)(* D *))
      list ref) 
      | Node of ((ctx * normalSubsts) * __Tree ref list) 
    let rec makeTree () = ref (Node (((emptyCtx ()), (nid ())), []))
    let rec noChildren (__C) = __C = []
    type __Retrieval =
      | Variant of (int * IntSyn.__Exp) 
      | NotCompatible 
    type __CompSub =
      | SplitSub of ((((ctx * normalSubsts))(* sigma *)) *
      (((ctx * normalSubsts))(* rho1 *)) *
      (((ctx * normalSubsts))(* rho2 *))) 
      | InstanceSub of (exSubsts *
      (((ctx * normalSubsts))(* rho2 *))) 
      | VariantSub of (((ctx * normalSubsts))(* rho2 *)) 
      | NoCompatibleSub 
    let indexArray =
      Array.tabulate (Global.maxCid, (fun i -> ((ref 0), (makeTree ()))))
    exception Error of string 
    module I = IntSyn
    module C = CompSyn
    module S = RBSet
    module A = AbstractTabled
    module T = TableParam
    exception Assignment of string 
    exception Instance of string 
    exception Generalization of string 
    exception DifferentSpines 
    let rec emptyAnswer () = T.emptyAnsw ()
    let (answList : TableParam.answer list ref) = ref []
    let added = ref false
    type nonrec nvar = int
    type nonrec bvar = int
    type nonrec bdepth = int
    let rec expToS (__G) (__U) =
      try Print.expToString (__G, __U) with | _ -> " <_ >"
    let rec printSub __8__ __9__ =
      match (__8__, __9__) with
      | (__G, Shift n) -> print (((^) "I.Shift " Int.toString n) ^ "\n")
      | (__G, Dot (Idx n, s)) ->
          (print (((^) "Idx " Int.toString n) ^ " . "); printSub (__G, s))
      | (__G, Dot (Exp (EVar ({ contents = Some (__U) }, _, _, _) as X), s))
          ->
          (print (((^) "Exp ( EVar " expToS (__G, __X)) ^ ").");
           printSub (__G, s))
      | (__G, Dot (Exp (EVar (_, _, _, _) as X), s)) ->
          (print (((^) "Exp ( EVar  " expToS (__G, __X)) ^ ").");
           printSub (__G, s))
      | (__G, Dot (Exp (AVar _), s)) ->
          (print "Exp (AVar _ ). "; printSub (__G, s))
      | (__G, Dot (Exp (EClo (AVar { contents = Some (__U) }, s')), s)) ->
          (print (((^) "Exp (AVar " expToS (__G, (I.EClo (__U, s')))) ^ ").");
           printSub (__G, s))
      | (__G, Dot
         (Exp (EClo (EVar ({ contents = Some (__U) }, _, _, _), s') as X), s))
          ->
          (print
             (((^) "Exp (EVarClo " expToS (__G, (I.EClo (__U, s')))) ^ ") ");
           printSub (__G, s))
      | (__G, Dot (Exp (EClo (__U, s') as X), s)) ->
          (print
             (((^) "Exp (EClo " expToS (__G, (Whnf.normalize (__U, s')))) ^
                ") ");
           printSub (__G, s))
      | (__G, Dot (Exp (__E), s)) ->
          (print (((^) "Exp ( " expToS (__G, __E)) ^ " ). ");
           printSub (__G, s))
      | (__G, Dot (I.Undef, s)) -> (print "Undef . "; printSub (__G, s))
    let rec normalizeSub =
      function
      | Shift n -> I.Shift n
      | Dot (Exp (EClo (AVar { contents = Some (__U) }, s')), s) ->
          I.Dot ((I.Exp (Whnf.normalize (__U, s'))), (normalizeSub s))
      | Dot (Exp (EClo (EVar ({ contents = Some (__U) }, _, _, _), s')), s)
          -> I.Dot ((I.Exp (Whnf.normalize (__U, s'))), (normalizeSub s))
      | Dot (Exp (__U), s) ->
          I.Dot ((I.Exp (Whnf.normalize (__U, I.id))), (normalizeSub s))
      | Dot (Idx n, s) -> I.Dot ((I.Idx n), (normalizeSub s))
    let rec etaSpine __10__ __11__ =
      match (__10__, __11__) with
      | (I.Nil, n) -> n = 0
      | (App (Root (BVar k, I.Nil), __S), n) ->
          (k = n) && (etaSpine (__S, (n - 1)))
      | (App (__A, __S), n) -> false
    let rec cidFromHead = function | Const c -> c | Def c -> c
    let rec dotn __12__ __13__ =
      match (__12__, __13__) with
      | (0, s) -> s
      | (i, s) -> dotn ((i - 1), (I.dot1 s))
    let rec raiseType __14__ __15__ =
      match (__14__, __15__) with
      | (I.Null, __V) -> __V
      | (Decl (__G, __D), __V) -> raiseType (__G, (I.Lam (__D, __V)))
    let rec compose __16__ __17__ =
      match (__16__, __17__) with
      | (IntSyn.Null, __G) -> __G
      | (Decl (__G', __D), __G) -> IntSyn.Decl ((compose (__G', __G)), __D)
    let rec shift __18__ __19__ =
      match (__18__, __19__) with
      | (IntSyn.Null, s) -> s
      | (Decl (__G, __D), s) -> I.dot1 (shift (__G, s))
    let rec ctxToEVarSub __20__ __21__ =
      match (__20__, __21__) with
      | (I.Null, s) -> s
      | (Decl (__G, Dec (_, __A)), s) ->
          let __X = I.newEVar (I.Null, __A) in
          I.Dot ((I.Exp __X), (ctxToEVarSub (__G, s)))
    let rec lowerEVar' __22__ __23__ __24__ =
      match (__22__, __23__, __24__) with
      | (__X, __G, (Pi ((__D', _), __V'), s')) ->
          let D'' = I.decSub (__D', s') in
          let (__X', __U) =
            lowerEVar'
              (__X, (I.Decl (__G, D'')), (Whnf.whnf (__V', (I.dot1 s')))) in
          (__X', (I.Lam (D'', __U)))
      | (__X, __G, __Vs') -> let __X' = __X in (__X', __X')
    let rec lowerEVar1 __25__ __26__ __27__ =
      match (__25__, __26__, __27__) with
      | (__X, EVar (r, __G, _, _), ((Pi _ as V), s)) ->
          let (__X', __U) = lowerEVar' (__X, __G, (__V, s)) in
          I.EVar ((ref (Some __U)), I.Null, __V, (ref nil))
      | (_, __X, _) -> __X
    let rec lowerEVar __28__ __29__ =
      match (__28__, __29__) with
      | (__E, (EVar (r, __G, __V, { contents = nil }) as X)) ->
          lowerEVar1 (__E, __X, (Whnf.whnf (__V, I.id)))
      | (__E, EVar _) ->
          raise
            (Error
               "abstraction : LowerEVars: Typing ambiguous -- constraint of functional type cannot be simplified")
      (* pre-Twelf 1.2 code walk, Fri May  8 11:05:08 1998 *)(* It is not clear if this case can happen *)
    let rec ctxToAVarSub __30__ __31__ __32__ =
      match (__30__, __31__, __32__) with
      | (__G', I.Null, s) -> s
      | (__G', Decl (__D, Dec (_, __A)), s) ->
          let EVar (r, _, _, cnstr) as E = I.newEVar (I.Null, __A) in
          I.Dot ((I.Exp __E), (ctxToAVarSub (__G', __D, s)))
      | (__G', Decl (__D, ADec (_, d)), s) ->
          let __X = I.newAVar () in
          I.Dot
            ((I.Exp (I.EClo (__X, (I.Shift (~ d))))),
              (ctxToAVarSub (__G', __D, s)))
    let rec assign __33__ __34__ __35__ __36__ __37__ =
      match (__33__, __34__, __35__, __36__, __37__) with
      | (d, (Dec (n, __V) as Dec1), (Root (BVar k, __S1) as E1), __U, asub)
          ->
          let EVar (r, _, _, cnstr) as E = I.newEVar (I.Null, __V) in
          let __X =
            lowerEVar1
              (__E, (I.EVar (r, I.Null, __V, cnstr)),
                (Whnf.whnf (__V, I.id))) in
          let _ = (:=) r Some __U in S.insert asub ((k - d), (I.Exp __X))
      | (d, (ADec (n, d') as Dec1), (Root (BVar k, __S1) as E1), __U, asub)
          ->
          let AVar r as A = I.newAVar () in
          let _ = (:=) r Some __U in
          let __Us = Whnf.whnf (__U, (I.Shift (~ d'))) in
          S.insert asub ((k - d), (I.Exp (I.EClo (__A, (I.Shift (~ d'))))))
      (* it is an Avar and d = d' (k-d, AVar(Some(U)) *)
      (* total as (t, passed)*)(* it is an evar -- (k-d, EVar (Some(U), V)) *)
      (* total as (t, passed)*)
    let rec assignExp __38__ __39__ __40__ __41__ =
      match (__38__, __39__, __40__, __41__) with
      | (fasub, (((r, passed) as ctxTotal), d),
         (__D1, (Root (__H1, __S1) as U1)),
         (__D2, (Root (__H2, __S2) as U2))) ->
          (((match (__H1, __H2) with
             | (Const c1, Const c2) ->
                 if c1 = c2
                 then
                   assignSpine
                     (fasub, (ctxTotal, d), (__D1, __S1), (__D2, __S2))
                 else raise (Assignment "Constant clash")
             | (Def c1, Def c2) ->
                 if c1 = c2
                 then
                   assignSpine
                     (fasub, (ctxTotal, d), (__D1, __S1), (__D2, __S2))
                 else
                   (let U1' = Whnf.normalize (Whnf.expandDef (__U1, I.id)) in
                    let U2' = Whnf.normalize (Whnf.expandDef (__U2, I.id)) in
                    assignExp
                      (fasub, (ctxTotal, d), (__D1, U1'), (__D2, U2')))
             | (Def c1, _) ->
                 let U1' = Whnf.normalize (Whnf.expandDef (__U1, I.id)) in
                 assignExp (fasub, (ctxTotal, d), (__D1, U1'), (__D2, __U2))
             | (_, Def c2) ->
                 let U2' = Whnf.normalize (Whnf.expandDef (__U2, I.id)) in
                 assignExp (fasub, (ctxTotal, d), (__D1, __U1), (__D2, U2'))
             | (BVar k1, BVar k2) ->
                 ((if k1 <= (r + d)
                   then
                     (((if k2 <= (r + d)
                        then
                          (if k2 = k1
                           then fasub
                           else raise (Assignment "BVar clash"))
                        else raise (Assignment "BVar - EVar clash")))
                     (* k2 is globally bound *))
                   else
                     (match member (((k1 - d) + passed), __D1) with
                      | None -> raise (Assignment "EVar nonexistent")
                      | Some (x, Dec) ->
                          ((if k2 <= (r + d)
                            then raise (Assignment "EVar - BVar clash")
                            else
                              ((if k2 = k1
                                then
                                  (fun asub ->
                                     fasub asub;
                                     assign (((d, Dec, __U1, __U2, asub))
                                       (* ctxTotal,*)))
                                else
                                  raise
                                    (Assignment
                                       "EVars are different -- outside of the allowed fragment"))
                              (* denote the same evar *)))
                          (* k2 is globally bound *))))
                 (* if (k1 - d) >= l *)(* k1 is a globally bound variable *)
                 (* k1 is an existial variable *))
             | (Skonst c1, Skonst c2) ->
                 if c1 = c2
                 then
                   assignSpine
                     (fasub, (ctxTotal, d), (__D1, __S1), (__D2, __S2))
                 else raise (Assignment "Skolem constant clash")
             | _ -> raise (Assignment "Head mismatch ")))
          (* we do not expand definitions here -- this is very conservative! *)
          (* we do not expand definitions here -- this is very conservative! *)
          (* we do not expand definitions here -- this is very conservative! *)
          (* can this happen ? -- definitions should be already expanded ?*))
      | (fasub, (ctxTotal, d), (__D1, Lam (Dec1, __U1)),
         (__D2, Lam (Dec2, __U2))) ->
          assignExp (fasub, (ctxTotal, (d + 1)), (__D1, __U1), (__D2, __U2))
      | (fasub, (ctxTotal, d),
         (__D1, Pi (((Dec (_, __V1) as Dec1), _), __U1)),
         (__D2, Pi (((Dec (_, __V2) as Dec2), _), __U2))) ->
          let fasub' =
            assignExp (fasub, (ctxTotal, d), (__D1, __V1), (__D2, __V2)) in
          ((assignExp
              (fasub', (ctxTotal, (d + 1)), (__D1, __U1), (__D2, __U2)))
            (* is this necessary? Tue Aug  3 11:56:17 2004 -bp *))
      | (fasub, (ctxTotal, d), (__D1, EClo (__U, (Shift 0 as s'))),
         (__D2, __U2)) ->
          assignExp (fasub, (ctxTotal, d), (__D1, __U), (__D2, __U2))
      | (fasub, (ctxTotal, d), (__D1, __U1),
         (__D2, EClo (__U, (Shift 0 as s)))) ->
          assignExp (fasub, (ctxTotal, d), (__D1, __U1), (__D2, __U))
      (* the closure cases should be unnecessary, if everything is in nf *)
      (* type labels are ignored *)
    let rec assignSpine __42__ __43__ __44__ __45__ =
      match (__42__, __43__, __44__, __45__) with
      | (fasub, (ctxTotal, d), (__D1, I.Nil), (__D2, I.Nil)) -> fasub
      | (fasub, (ctxTotal, d), (__D1, App (__U1, __S1)),
         (__D2, App (__U2, __S2))) ->
          let fasub' =
            assignExp (fasub, (ctxTotal, d), (__D1, __U1), (__D2, __U2)) in
          assignSpine (fasub', (ctxTotal, d), (__D1, __S1), (__D2, __S2))
    let rec assignCtx __46__ __47__ __48__ __49__ =
      match (__46__, __47__, __48__, __49__) with
      | (fasub, ctxTotal, (__D1, I.Null), (__D2, I.Null)) -> fasub
      | (fasub, ((r, passed) as ctxTotal),
         (__D1, Decl (__G1, Dec (_, __V1))),
         (__D2, Decl (__G2, Dec (_, __V2)))) ->
          let fasub' =
            assignExp
              (fasub, (((r - 1), (passed + 1)), 0), (__D1, __V1),
                (__D2, __V2)) in
          assignCtx
            (fasub', ((r - 1), (passed + 1)), (__D1, __G1), (__D2, __G2))
    let nctr = ref 1
    let rec newNVar () = ((!) ((:=) nctr) nctr) + 1; I.NVar (!nctr)
    let rec equalDec __50__ __51__ =
      match (__50__, __51__) with
      | (Dec (_, __U), Dec (_, __U')) ->
          Conv.conv ((__U, I.id), (__U', I.id))
      | (ADec (_, d), ADec (_, d')) -> d = d'
      | (_, _) -> false
    let rec equalCtx __52__ __53__ __54__ __55__ =
      match (__52__, __53__, __54__, __55__) with
      | (I.Null, s, I.Null, s') -> true
      | (Decl (__G, (Dec (_, __A) as D)), s, Decl
         (__G', (Dec (_, __A') as D')), s') ->
          (Conv.convDec ((__D, s), (__D', s'))) &&
            (equalCtx (__G, (I.dot1 s), __G', (I.dot1 s')))
      | (_, s, _, s') -> false
    let rec equalEqn __56__ __57__ =
      match (__56__, __57__) with
      | (T.Trivial, T.Trivial) -> true
      | (Unify (__G, __X, __N, eqn), Unify (__G', __X', __N', eqn')) ->
          (equalCtx (__G, I.id, __G', I.id)) &&
            ((Conv.conv ((__X, I.id), (__X', I.id))) &&
               ((Conv.conv ((__N, I.id), (__N', I.id))) &&
                  (equalEqn (eqn, eqn'))))
      | (_, _) -> false
    let rec equalEqn' __58__ __59__ __60__ __61__ =
      match (__58__, __59__, __60__, __61__) with
      | (d, (__D, T.Trivial), (__D', T.Trivial), asub) -> true
      | (d,
         (__D, Unify
          (((__G, (Root (BVar k, __S) as X), __N, eqn))(* AVar *))),
         (__D', Unify
          (((__G', __X', __N', eqn'))(* AVar *))),
         asub) ->
          if
            (equalCtx (__G, I.id, __G', I.id)) &&
              ((Conv.conv ((__X, I.id), (__X', I.id))) &&
                 (Conv.conv ((__N, I.id), (__N', I.id))))
          then
            let d' = (+) d I.ctxLength __G' in
            (((((if (k - d') > 0
                 then
                   (((match member ((k - d'), __D') with
                      | None -> ()
                      | Some (x, Dec) ->
                          (match RBSet.lookup asub (k - d') with
                           | None ->
                               (((delete (x, __D');
                                  S.insert asub ((k - d'), (I.Idx (k - d')))))
                               (* it is not instantiated yet *))
                           | Some _ -> ())))
                   (* k refers to an evar *))
                 else
                   (print "Impossible -- Found BVar instead of EVar\n";
                    raise (Error "Impossibe -- Found BVar instead of EVar ")))
               (* it is instantiated;
                                          since eqn were solvable, eqn' would be solvable too *)
               (* k refers to a bound variable *));
               equalEqn' (d, (__D, eqn), (__D', eqn'), asub)))
              (* X is the evar in the query, X' is the evar in the index,
             potentially X' is not yet instantiated and X' in D' but X' not in asub *))
          else false
      | (d, _, _, asub) -> false
    let rec equalSub __62__ __63__ =
      match (__62__, __63__) with
      | (Shift k, Shift k') -> k = k'
      | (Dot (__F, __S), Dot (__F', __S')) ->
          (equalFront (__F, __F')) && (equalSub (__S, __S'))
      | (Dot (__F, __S), Shift k) -> false
      | (Shift k, Dot (__F, __S)) -> false
    let rec equalFront __64__ __65__ =
      match (__64__, __65__) with
      | (Idx n, Idx n') -> n = n'
      | (Exp (__U), Exp (__V)) -> Conv.conv ((__U, I.id), (__V, I.id))
      | (I.Undef, I.Undef) -> true
    let rec equalCtx' __66__ __67__ =
      match (__66__, __67__) with
      | (I.Null, I.Null) -> true
      | (Decl (Dk, Dec (_, __A)), Decl (__D1, Dec (_, __A1))) ->
          (Conv.conv ((__A, I.id), (__A1, I.id))) && (equalCtx' (Dk, __D1))
      | (Decl (Dk, ADec (_, d')), Decl (__D1, ADec (_, d))) ->
          (d = d') && (equalCtx' (Dk, __D1))
      | (_, _) -> false
    let rec instanceCtx asub (__D1, __G1) (__D2, __G2) =
      let d1 = I.ctxLength __G1 in
      let d2 = I.ctxLength __G2 in
      if d1 = d2
      then
        try
          let fasub =
            assignCtx ((fun asub -> ()), (d1, 0), (__D1, __G1), (__D2, __G2)) in
          fasub asub; true
        with | Assignment msg -> ((false)(* print msg;*))
      else false
    let rec collectEVar (__D) nsub =
      let __D' = emptyCtx () in
      let rec collectExp __68__ __69__ __70__ __71__ =
        match (__68__, __69__, __70__, __71__) with
        | (d, __D', __D, Lam (_, __U)) ->
            collectExp ((d + 1), __D', __D, __U)
        | (d, __D', __D, Root (Const c, __S)) ->
            collectSpine (d, __D', __D, __S)
        | (d, __D', __D, Root (BVar k, __S)) ->
            (match member ((k - d), __D) with
             | None -> collectSpine (d, __D', __D, __S)
             | Some (x, Dec) ->
                 (delete ((x - d), __D); insertList (((x - d), Dec), __D')))
        | (d, __D', __D, (Root (Def k, __S) as U)) ->
            let __U' = Whnf.normalize (Whnf.expandDef (__U, I.id)) in
            collectExp (d, __D', __D, __U')
      and collectSpine __72__ __73__ __74__ __75__ =
        match (__72__, __73__, __74__, __75__) with
        | (d, __D', __D, I.Nil) -> ()
        | (d, __D', __D, App (__U, __S)) ->
            (collectExp (d, __D', __D, __U); collectSpine (d, __D', __D, __S)) in
      S.forall nsub
        (fun nv -> fun (du, __U) -> collectExp (0, __D', __D, __U));
      (__D', __D)
    let rec convAssSub' (__G) idx_k (__D) asub d ((evars, avars) as evarsl) =
      match RBSet.lookup asub d with
      | None ->
          (((match member (d, __D) with
             | None -> IntSyn.Shift ((evars + avars)(* 0 *))
             | Some (x, Dec (n, __V)) ->
                 let s =
                   convAssSub' (__G, (idx_k + 1), __D, asub, (d + 1), evarsl) in
                 let EVar (r, _, _, cnstr) as E = I.newEVar (I.Null, __V) in
                 I.Dot ((I.Exp (I.EClo (__E, (I.Shift (evars + avars))))), s)
             | Some (x, ADec (n, __V)) ->
                 (print "convAssSub' -- Found an uninstantiated AVAR\n";
                  raise (Error "Unassigned AVar -- should never happen\n"))))
          (* Found an EVar which is not yet
                     instantiated -- must be instantiated when
                     solving residual equations! *)
          (* should never happen -- all avars should
                     have been assigned! *))
      | Some (Exp (__E) as F) ->
          let __E' = Whnf.normalize (__E, I.id) in
          I.Dot
            ((I.Exp __E'),
              (convAssSub' (__G, (idx_k + 1), __D, asub, (d + 1), evarsl)))
    let rec convAssSub (__G) asub (Glength) (__D') evarsl =
      convAssSub' (__G, 0, __D', asub, Glength, evarsl)
    let rec isExists d (BVar k) (__D) = member ((k - d), __D)
    let rec instance (D_t, (dt, __T)) (D_u, (du, __U)) rho_u ac =
      let rec instRoot __76__ __77__ __78__ __79__ =
        match (__76__, __77__, __78__, __79__) with
        | (depth, (Root ((Const k as H1), __S1) as T),
           (Root (Const k', __S2) as U), ac) ->
            if k = k'
            then instSpine (depth, __S1, __S2, ac)
            else raise (Instance "Constant mismatch\n")
        | (depth, (Root ((Def k as H1), __S1) as T),
           (Root (Def k', __S2) as U), ac) ->
            if k = k'
            then instSpine (depth, __S1, __S2, ac)
            else
              (let __T' = Whnf.normalize (Whnf.expandDef (__T, I.id)) in
               let __U' = Whnf.normalize (Whnf.expandDef (__U, I.id)) in
               instExp (depth, __T', __U', ac))
        | (depth, (Root ((Def k as H1), __S1) as T),
           (Root (__H2, __S2) as U), ac) ->
            let __T' = Whnf.normalize (Whnf.expandDef (__T, I.id)) in
            instExp (depth, __T', __U, ac)
        | (d, (Root ((BVar k as H1), __S1) as T),
           (Root (BVar k', __S2) as U), ac) ->
            ((if (k > d) && (k' > d)
              then
                let k1 = k - d in
                let k2 = k' - d in
                (((match ((member (k1, D_t)), (member (k2, D_u))) with
                   | (None, None) ->
                       ((if k1 = k2
                         then instSpine (d, __S1, __S2, ac)
                         else raise (Instance "Bound variable mismatch\n"))
                       (* both refer to the same globally bound variable in G *))
                   | (Some (x, Dec1), Some (x', Dec2)) ->
                       ((if (k1 = k2) && (equalDec (Dec1, Dec2))
                         then
                           let ac' = instSpine (d, __S1, __S2, ac) in
                           let ac'' asub =
                             ((ac' asub;
                               assign (((d, Dec1, __T, __U, asub))
                                 (* ctxTotal,*)))
                             (* S.insert asub (k - d, I.Idx (k-d)) *)) in
                           ((ac'')
                             (* this is unecessary *)
                             (* since existential variables have the same type
                             and need to be fully applied in order, S1 = S2 *))
                         else
                           (fun asub ->
                              ac asub;
                              assign (((d, Dec1, __T, __U, asub))
                                (* ctxTotal,*))))
                       (* they refer to the same existential variable *)
                       (* instance checking only Sun Oct 27 12:16:10 2002 -bp *))
                   | (Some (x, (ADec (n, d') as Dec1)), None) ->
                       (fun asub ->
                          ac asub;
                          assign (((d, Dec1, __T, __U, asub))
                            (* ctxTotal,*)))
                   | (Some (x, Dec1), None) ->
                       (fun asub ->
                          ac asub;
                          assign (((d, Dec1, __T, __U, asub))
                            (* ctxTotal,*)))
                   | (_, _) -> raise (Instance "Impossible\n")))
                  (* k, k' refer to the existential *)
                  (* instance checking only Sun Oct 27 12:18:53 2002 -bp *))
              else raise (Instance "Bound variable mismatch\n"))
            (* globally bound variable *)(* locally bound variables *))
        | (d, (Root ((BVar k as H1), __S1) as T),
           (Root (Const k', __S2) as U), ac) ->
            (match isExists (d, (I.BVar k), D_t) with
             | None -> raise (Instance "Impossible\n")
             | Some (x, (ADec (_, _) as Dec1)) ->
                 (fun asub ->
                    ac asub;
                    assign (((d, Dec1, __T, __U, asub))
                      (* ctxTotal,*)))
             | Some (x, Dec1) ->
                 (fun asub ->
                    ac asub;
                    assign (((d, Dec1, __T, __U, asub))
                      (* ctxTotal, *))))
        | (d, (Root ((BVar k as H1), __S1) as T), (Root (Def k', __S2) as U),
           ac) ->
            (match isExists (d, (I.BVar k), D_t) with
             | None -> raise (Instance "Impossible\n")
             | Some (x, (ADec (_, _) as Dec1)) ->
                 (fun asub ->
                    ac asub;
                    assign (((d, Dec1, __T, __U, asub))
                      (* ctxTotal,*)))
             | Some (x, Dec1) ->
                 (fun asub ->
                    ac asub;
                    assign (((d, Dec1, __T, __U, asub))
                      (* ctxTotal, *))))
        | (depth, (Root (__H1, __S1) as T), (Root (Def k', __S2) as U), ac)
            ->
            let __U' = Whnf.normalize (Whnf.expandDef (__U, I.id)) in
            instExp (depth, __T, __U', ac)
        | (d, (Root (__H1, __S1) as T), (Root (__H2, __S2) as U), ac) ->
            raise (Instance "Other Cases impossible\n")(* this case only should happen during instance checking *)
      (* this case only should happen during instance checking *)
      and instExp __80__ __81__ __82__ __83__ =
        match (__80__, __81__, __82__, __83__) with
        | (d, (NVar n as T), (Root (__H, __S) as U), ac) ->
            (S.insert rho_u (n, (d, __U)); ac)
        | (d, (Root (__H1, __S1) as T), (Root (__H2, __S2) as U), ac) ->
            instRoot (d, (I.Root (__H1, __S1)), (I.Root (__H2, __S2)), ac)
        | (d, Lam ((Dec (_, __A1) as D1), __T1), Lam
           ((Dec (_, __A2) as D2), __U2), ac) ->
            instExp ((d + 1), __T1, __U2, ac)
        | (d, __T, __U, ac) ->
            (print "instExp -- falls through?\n";
             raise (Instance "Impossible\n"))(* U = EVar, EClo -- can't happen -- Sun Oct 20 13:41:25 2002 -bp *)
      (* by invariant A1 = A2 -- actually this invariant may be violated, but we ignore it. *)
      and instSpine __84__ __85__ __86__ __87__ =
        match (__84__, __85__, __86__, __87__) with
        | (d, I.Nil, I.Nil, ac) -> ac
        | (d, App (__T, __S1), App (__U, __S2), ac) ->
            let ac' = instExp (d, __T, __U, ac) in
            let ac'' = instSpine (d, __S1, __S2, ac') in ac''
        | (d, I.Nil, App (_, _), ac) ->
            (print
               "Spines are not the same -- (first one is Nil) -- cannot happen!\n";
             raise (Instance "DifferentSpines\n"))
        | (d, App (_, _), I.Nil, ac) ->
            (print
               "Spines are not the same -- second one is Nil -- cannot happen!\n";
             raise (Instance "DifferentSpines\n"))
        | (d, SClo (_, _), _, ac) ->
            (print "Spine Closure!(1) -- cannot happen!\n";
             raise (Instance "DifferentSpines\n"))
        | (d, _, SClo (_, _), ac) ->
            (print "Spine Closure! (2) -- cannot happen!\n";
             raise (Instance " DifferentSpines\n")) in
      (((:=) ac instExp (dt, __T, __U, (!ac)))
        (* by invariant dt = du *)(* if it succeeds then it will return a continuation which will
         instantiate the "evars" and rho_t will contain all
         nvar instantiations
         otherwise it will raise Instance *))
    let rec compHeads __88__ __89__ =
      match (__88__, __89__) with
      | ((D_1, Const k), (D_2, Const k')) -> k = k'
      | ((D_1, Def k), (D_2, Def k')) -> k = k'
      | ((D_1, BVar k), (D_2, BVar k')) ->
          (match isExists (0, (I.BVar k), D_1) with
           | None -> k = k'
           | Some (x, Dec) -> true)
      | ((D_1, BVar k), (D_2, __H2)) ->
          (match isExists (0, (I.BVar k), D_1) with
           | None -> false
           | Some (x, Dec) -> true)
      | ((D_1, __H1), (D_2, __H2)) -> false
    let rec compatible' (D_t, (dt, __T)) (D_u, (du, __U)) (__Ds) rho_t rho_u
      =
      let rec genNVar (rho_t, __T) (rho_u, __U) =
        ((S.insert rho_t (((!nctr) + 1), __T);
          S.insert rho_u (((!nctr) + 1), __U);
          newNVar ())
        (* by invariant dt = du *)) in
      let rec genRoot __90__ __91__ __92__ =
        match (__90__, __91__, __92__) with
        | (d, (Root ((Const k as H1), __S1) as T),
           (Root (Const k', __S2) as U)) ->
            if k = k'
            then let __S' = genSpine (d, __S1, __S2) in I.Root (__H1, __S')
            else genNVar ((rho_t, (d, __T)), (rho_u, (d, __U)))
        | (d, (Root ((Def k as H1), __S1) as T), (Root (Def k', __S2) as U))
            ->
            ((if k = k'
              then let __S' = genSpine (d, __S1, __S2) in I.Root (__H1, __S')
              else genNVar ((rho_t, (d, __T)), (rho_u, (d, __U))))
            (* could expand definitions here ? -bp*))
        | (d, (Root ((BVar k as H1), __S1) as T),
           (Root (BVar k', __S2) as U)) ->
            ((if (k > d) && (k' > d)
              then
                let k1 = k - d in
                let k2 = k' - d in
                (((match ((member (k1, D_t)), (member (k2, D_u))) with
                   | (None, None) ->
                       if k1 = k2
                       then
                         (try
                            let __S' = genSpine (d, __S1, __S2) in
                            I.Root (__H1, __S')
                          with
                          | DifferentSpine ->
                              genNVar ((rho_t, (d, __T)), (rho_u, (d, __U))))
                       else genNVar ((rho_t, (d, __T)), (rho_u, (d, __U)))
                   | (Some (x, Dec1), Some (x', Dec2)) ->
                       ((if (k1 = k2) && (equalDec (Dec1, Dec2))
                         then
                           let __S' = genSpine (d, __S1, __S2) in
                           (((delete (x, D_t);
                              delete (x', D_u);
                              insertList ((x, Dec1), __Ds);
                              I.Root (__H1, __S')))
                             (* this is unecessary -- since existential variables have the same type
                            and need to be fully applied in order, S1 = S2 *))
                         else genNVar ((rho_t, (d, __T)), (rho_u, (d, __U))))
                       (* they refer to the same existential variable *)
                       (* variant checking only *))
                   | (_, _) -> genNVar ((rho_t, (d, __T)), (rho_u, (d, __U)))))
                  (* should never happen *)(* k, k' refer to the existential *))
              else
                if k = k'
                then
                  (try
                     let __S' = genSpine (d, __S1, __S2) in
                     I.Root (__H1, __S')
                   with
                   | DifferentSpines ->
                       genNVar ((rho_t, (d, __T)), (rho_u, (d, __U))))
                else genNVar ((rho_t, (d, __T)), (rho_u, (d, __U))))
            (* globally bound variable *)(* locally bound variables *))
        | (d, (Root ((BVar k as H1), __S1) as T),
           (Root (Const k', __S2) as U)) ->
            genNVar ((rho_t, (d, __T)), (rho_u, (d, __U)))
        | (d, (Root ((BVar k as H1), __S1) as T), (Root (Def k', __S2) as U))
            -> genNVar ((rho_t, (d, __T)), (rho_u, (d, __U)))
        | (d, (Root (__H1, __S1) as T), (Root (__H2, __S2) as U)) ->
            genNVar ((rho_t, (d, __T)), (rho_u, (d, __U)))
      and genExp __93__ __94__ __95__ =
        match (__93__, __94__, __95__) with
        | (d, (NVar n as T), (Root (__H, __S) as U)) ->
            (S.insert rho_u (n, (d, __U)); __T)
        | (d, (Root (__H1, __S1) as T), (Root (__H2, __S2) as U)) ->
            genRoot (d, (I.Root (__H1, __S1)), (I.Root (__H2, __S2)))
        | (d, Lam ((Dec (_, __A1) as D1), __T1), Lam
           ((Dec (_, __A2) as D2), __U2)) ->
            let __E = genExp ((d + 1), __T1, __U2) in I.Lam (__D1, __E)
        | (d, __T, __U) ->
            (print "genExp -- falls through?\n";
             genNVar ((rho_t, (d, __T)), (rho_u, (d, __U))))(* U = EVar, EClo -- can't happen -- Sun Oct 20 13:41:25 2002 -bp *)
      (* by invariant A1 = A2 *)
      and genSpine __96__ __97__ __98__ =
        match (__96__, __97__, __98__) with
        | (d, I.Nil, I.Nil) -> I.Nil
        | (d, App (__T, __S1), App (__U, __S2)) ->
            let __E = genExp (d, __T, __U) in
            let __S' = genSpine (d, __S1, __S2) in I.App (__E, __S')
        | (d, I.Nil, App (_, _)) -> raise DifferentSpines
        | (d, App (_, _), I.Nil) -> raise DifferentSpines
        | (d, SClo (_, _), _) -> raise DifferentSpines
        | (d, _, SClo (_, _)) -> raise DifferentSpines in
      ((Variant (dt, (genExp (dt, __T, __U))))
        (* by invariant dt = du *))
    let rec compatible __99__ __100__ __101__ __102__ __103__ =
      match (__99__, __100__, __101__, __102__, __103__) with
      | ((D_t, ((d1, Root (__H1, __S1)) as T)),
         (D_u, ((d2, Root (__H2, __S2)) as U)), __Ds, rho_t, rho_u) ->
          if compHeads ((D_t, __H1), (D_u, __H2))
          then compatible' ((D_t, __T), (D_u, __U), __Ds, rho_t, rho_u)
          else NotCompatible
      | ((D_t, __T), (D_u, __U), __Ds, rho_t, rho_u) ->
          compatible' ((D_t, __T), (D_u, __U), __Ds, rho_t, rho_u)
    let rec compatibleCtx __104__ __105__ __106__ =
      match (__104__, __105__, __106__) with
      | (asub, (Dsq, Gsq, eqn_sq), []) -> None
      | (asub, (Dsq, Gsq, eqn_sq),
         (_, Delta', __G', eqn', answRef', _, status')::GRlist) ->
          if instanceCtx (asub, (Dsq, Gsq), (Delta', __G'))
          then Some ((Delta', __G', eqn'), answRef', status')
          else compatibleCtx (asub, (Dsq, Gsq, eqn_sq), GRlist)
    let rec instanceSub (D_t, nsub_t) (Dsq, squery) asub =
      let rho_u = nid () in
      let D_r2 = copy Dsq in
      let ac = ref (fun asub -> ()) in
      ((try
          S.forall squery
            (fun nv ->
               fun (du, __U) ->
                 ((match S.lookup nsub_t nv with
                   | Some (dt, __T) ->
                       instance
                         ((D_t, (dt, __T)), (D_r2, (du, __U)), rho_u, ac)
                   | None -> S.insert rho_u (nv, (du, __U)))
                 (* note by invariant Glocal_e ~ Glocal_t *)
                 (* [ac]T = U *)(* if U is an instance of T then [ac][rc_u]T = U *)
                 (* once the continuations ac are triggered *)));
          (!) ac asub;
          InstanceSub (asub, (D_r2, rho_u))
        with | Instance msg -> NoCompatibleSub)
        (* by invariant rho_t = empty, since nsub_t <= squery *))
    let rec instChild __107__ __108__ __109__ =
      match (__107__, __108__, __109__) with
      | ((Leaf ((D_t, nsub_t), GList) as N), (D_sq, sq), asub) ->
          instanceSub ((D_t, nsub_t), (D_sq, sq), asub)
      | ((Node ((D_t, nsub_t), Children') as N), (D_sq, sq), asub) ->
          instanceSub ((D_t, nsub_t), (D_sq, sq), asub)
    let rec findAllInst (G_r) children (__Ds) asub =
      let rec findAllCands __110__ __111__ __112__ __113__ __114__ =
        match (__110__, __111__, __112__, __113__, __114__) with
        | (G_r, nil, (Dsq, sub_u), asub, IList) -> IList
        | (G_r, x::__L, (Dsq, sub_u), asub, IList) ->
            let asub' = S.copy asub in
            (((match instChild ((!x), (Dsq, sub_u), asub) with
               | NoCompatibleSub ->
                   findAllCands (G_r, __L, (Dsq, sub_u), asub', IList)
               | InstanceSub (asub, Drho2) ->
                   findAllCands
                     (G_r, __L, (Dsq, sub_u), asub',
                       ((x, Drho2, asub) :: IList))))
              (* will update asub *)) in
      findAllCands (G_r, children, __Ds, asub, nil)
    let rec solveEqn __115__ __116__ =
      match (__115__, __116__) with
      | ((T.Trivial, s), __G) -> true
      | ((Unify (((__G', e1, __N, eqns))(* evar *)), s),
         __G) ->
          let G'' = compose (__G', __G) in
          let s' = shift (G'', s) in
          (Assign.unifiable (G'', (__N, s'), (e1, s'))) &&
            (solveEqn ((eqns, s), __G))
    let rec solveEqn' __117__ __118__ =
      match (__117__, __118__) with
      | ((T.Trivial, s), __G) -> true
      | ((Unify (((__G', e1, __N, eqns))(* evar *)), s),
         __G) ->
          let G'' = compose (__G', __G) in
          let s' = shift (__G', s) in
          (Assign.unifiable (G'', (__N, s'), (e1, s'))) &&
            (solveEqn' ((eqns, s), __G))
    let rec solveEqnI' __119__ __120__ =
      match (__119__, __120__) with
      | ((T.Trivial, s), __G) -> true
      | ((Unify (((__G', e1, __N, eqns))(* evar *)), s),
         __G) ->
          let G'' = compose (__G', __G) in
          let s' = shift (__G', s) in
          (((Assign.instance (G'', (e1, s'), (__N, s'))) &&
              (solveEqnI' ((eqns, s), __G)))
            (* note: we check whether N[s'] is an instance of e1[s'] !!! *)
            (* at this point all AVars have been instantiated, and we could use Match.instance directly *))
    let rec retrieveInst (Nref) (Dq, sq) asub (GR) =
      let rec retrieve' __121__ __122__ __123__ __124__ =
        match (__121__, __122__, __123__, __124__) with
        | ((Leaf ((__D, s), GRlistRef) as N), (Dq, sq), asubst,
           ((((DEVars, DAVars) as DAEVars), G_r, eqn, stage, status) as GR'))
            ->
            let (Dsq, D_G) = collectEVar (Dq, sq) in
            (((match compatibleCtx (asubst, (D_G, G_r, eqn), (!GRlistRef))
               with
               | None ->
                   ((raise (Instance "Compatible path -- different ctx\n"))
                   (* compatible path -- but different ctx *))
               | Some ((__D', __G', eqn'), answRef', status') ->
                   ((let DAEVars = compose (DEVars, DAVars) in
                     let esub = ctxToAVarSub (__G', DAEVars, (I.Shift 0)) in
                     let asub =
                       convAssSub
                         (__G', asubst, ((I.ctxLength __G') + 1), __D',
                           ((I.ctxLength DAVars), (I.ctxLength DEVars))) in
                     let _ =
                       if
                         solveEqn' ((((eqn, (shift (__G', esub))), __G'))
                           (* = G_r *))
                       then ()
                       else print " failed to solve eqn_query\n" in
                     let easub = normalizeSub (I.comp (asub, esub)) in
                     ((if solveEqnI' ((eqn', (shift (__G', easub))), __G')
                       then T.RepeatedEntry ((esub, asub), answRef', status')
                       else
                         raise
                           (Instance
                              "Compatible path -- resdidual equ. not solvable\n"))
                       (*              if solveEqnI' (eqn', easub) *)
                       (* solve residual equations using higher-order matching Wed Dec 22 2004 -bp *)
                       (* Since there exists a path (D1, s1) ... (Dn,sn) from the root to the leaf (D,s)
                   D1', ...., Dn', D, D' = D*
                   and          G' |- esub' : DAEVars, G'        and       .   |- esub : DAEVars
                        DAEVars, G |- asub' : D*, G'                   DAEVars |- asub : D*

                  note: asub' may refer to free variables which denote evars in D*
                        which only occur in eqn' and hence have not yet been instantiated
                        however: all avars in D* have been instantiated!
                 *)
                       (* Residual equation of query:
                   DAEVars, G' |- eqn  hence we solve : G' |= [esub']eqn *)
                       (*              val _ = if solveEqn' (eqn, esub)
                          then () else print " failed to solve eqn_query\n"  *)
                       (* Residual equations in index:
                   D*, G' |- eqn'    where eqn' = AVar1 = E1 .... AVarn = En
                                      and  Ei may contain free variables
                      G'  |= [esub](asub) (eqn')

                      solve eqn' from path in index using instance or matching ONLY
                      to instantiate the free variables Ei

                   remark: DAEVars, G' |= [asub]eqn'   should work in theory too,
                           if the free variables in asub are created in such a way that they may depend on DAVars.
                           otherwise unification or instance checking will fail or the resulting instantiation
                           for the free variables in asub is too restrictive, s.t. retrieval fails
                   *)))
                   (* note: previously we checked eqn' = eqn! -- this is too restrictive
                 now - Dec  6 2004 -bp we check whether eqn is an instance of eqn'
                 note: this is very delicate code.
               *))))
              (* compatibleCtx may destructively update asub ! *)
              (* compatible path -- SAME ctx *)(* Dq = (Dsq' u Dg) where Dsq' = evars occurring in sq
                                      D_G = evars occuring in G_sq or only in eqn_sq

               and Dsq = D since there exists a path s1 ... sn from the root to the leaf (D,s)
                 s.t. [asub]s1 o s2 o ... sn o s corresponds to original query
             *))
        | ((Node ((__D, sub), children) as N), (Dq, sq), asub,
           ((DAEVars, G_r, eqn, stage, status) as GR)) ->
            let InstCand = findAllInst (G_r, children, (Dq, sq), asub) in
            let rec checkCandidates =
              function
              | nil -> raise (Instance "No compatible child\n")
              | (ChildRef, Drho2, asub)::ICands ->
                  (try retrieve' ((!ChildRef), Drho2, asub, GR)
                   with
                   | Instance msg -> ((checkCandidates ICands)
                       (* print msg; *)))(* there is an instance  *)
              (* no child is compatible with sq *) in
            checkCandidates InstCand(* [asub]s = sq   and there exists a path (D1, s1) ... (Dn,sn) from the root to the leaf (D,s)
           s.t. [asub]s1 o s2 o ... sn o s corresponds to original query
           *)
        (* s and sq are compatible by invariant *) in
      ((fun () -> ()), (retrieve' ((!Nref), (Dq, sq), asub, GR)))
    let rec compatibleSub (D_t, nsub_t) (Dsq, squery) =
      let (sigma, rho_t, rho_u) = ((nid ()), (nid ()), (nid ())) in
      let Dsigma = emptyCtx () in
      let D_r1 = copy D_t in
      let D_r2 = copy Dsq in
      let choose = ref (fun match__ -> ()) in
      let _ =
        S.forall squery
          (fun nv ->
             fun (__U) ->
               ((match S.lookup nsub_t nv with
                 | Some (__T) ->
                     (match compatible
                              ((D_r1, __T), (D_r2, __U), Dsigma, rho_t,
                                rho_u)
                      with
                      | NotCompatible ->
                          (S.insert rho_t (nv, __T); S.insert rho_u (nv, __U))
                      | Variant (__T') ->
                          let restc = !choose in
                          (S.insert sigma (nv, __T');
                           choose :=
                             ((fun match__ ->
                                 restc match__; if match__ then () else ()))))
                 | None -> S.insert rho_u (nv, __U))
               (* note by invariant Glocal_e ~ Glocal_t *)
               (* here Glocal_t will be only approximately correct! *))) in
      ((if isId rho_t
        then ((!) choose true; VariantSub (D_r2, rho_u))
        else
          ((((!) choose false;
             if isId sigma
             then NoCompatibleSub
             else SplitSub ((Dsigma, sigma), (D_r1, rho_t), (D_r2, rho_u))))
          (* split -- asub is unchanged *)))
        (* perfect match under asub and rho_t = nsub_t
           sigma = rho_t and sigma o asub = rho_u *)
        (* by invariant rho_t = empty, since nsub_t <= squery *)
        (* Dsigma |~ sigma, D_r1 |~ rho_t, D_r1 |~ rho_u *))
    let rec mkNode __125__ __126__ __127__ __128__ __129__ =
      match (__125__, __126__, __127__, __128__, __129__) with
      | (Node (_, Children), ((__Ds, sigma) as Dsigma),
         ((__D1, rho1) as Drho1),
         (((evarl, l), dp, eqn, answRef, stage, status) as GR),
         ((__D2, rho2) as Drho2)) ->
          let (D_rho2, D_G2) = collectEVar (__D2, rho2) in
          let GR' = ((evarl, l), D_G2, dp, eqn, answRef, stage, status) in
          let (sizeSigma, sizeRho1, sizeRho2) =
            ((S.size sigma), (S.size rho1), (S.size rho2)) in
          Node
            (Dsigma,
              [ref (Leaf ((D_rho2, rho2), (ref [GR'])));
              ref (Node (Drho1, Children))])
      | (Leaf (c, GRlist), ((__Ds, sigma) as Dsigma),
         ((__D1, rho1) as Drho1),
         (((evarl, l), dp, eqn, answRef, stage, status) as GR2),
         ((__D2, rho2) as Drho2)) ->
          let (D_rho2, D_G2) = collectEVar (__D2, rho2) in
          let GR2' = ((evarl, l), D_G2, dp, eqn, answRef, stage, status) in
          Node
            (Dsigma,
              [ref (Leaf ((D_rho2, rho2), (ref [GR2'])));
              ref (Leaf (Drho1, GRlist))])
    let rec compChild __130__ __131__ =
      match (__130__, __131__) with
      | ((Leaf ((D_t, nsub_t), GList) as N), (D_e, nsub_e)) ->
          compatibleSub ((D_t, nsub_t), (D_e, nsub_e))
      | ((Node ((D_t, nsub_t), Children') as N), (D_e, nsub_e)) ->
          compatibleSub ((D_t, nsub_t), (D_e, nsub_e))
    let rec findAllCandidates (G_r) children (__Ds) =
      let rec findAllCands __132__ __133__ __134__ __135__ __136__ =
        match (__132__, __133__, __134__, __135__, __136__) with
        | (G_r, nil, (Dsq, sub_u), VList, SList) -> (VList, SList)
        | (G_r, x::__L, (Dsq, sub_u), VList, SList) ->
            (match compChild ((!x), (Dsq, sub_u)) with
             | NoCompatibleSub ->
                 findAllCands (G_r, __L, (Dsq, sub_u), VList, SList)
             | SplitSub (Dsigma, Drho1, Drho2) ->
                 findAllCands
                   (G_r, __L, (Dsq, sub_u), VList,
                     ((x, (Dsigma, Drho1, Drho2)) :: SList))
             | VariantSub ((D_r2, rho2) as Drho2) ->
                 findAllCands
                   (G_r, __L, (Dsq, sub_u), ((x, Drho2, I.id) :: VList),
                     SList)) in
      findAllCands (G_r, children, __Ds, nil, nil)
    let rec divergingCtx stage (__G) (GRlistRef) =
      let l = (I.ctxLength __G) + 3 in
      ((List.exists
          (fun (_, l) ->
             fun (__D) ->
               fun (__G') ->
                 fun _ ->
                   fun _ ->
                     fun stage' ->
                       fun _ -> (stage = stage') && (l > (I.ctxLength __G')))
          (!GRlistRef))
        (* this 3 is arbitrary -- lockstep *))
    let rec eqHeads __137__ __138__ =
      match (__137__, __138__) with
      | (Const k, Const k') -> k = k'
      | (BVar k, BVar k') -> k = k'
      | (Def k, Def k') -> k = k'
      | (_, _) -> false
    let rec eqTerm __139__ __140__ =
      match (__139__, __140__) with
      | (Root (__H2, __S2), ((Root (__H, __S) as t), rho1)) ->
          if eqHeads (__H2, __H)
          then eqSpine (__S2, (__S, rho1))
          else false
      | (__T2, (NVar n, rho1)) ->
          (match S.lookup rho1 n with
           | None -> false
           | Some (dt1, __T1) -> eqTerm (__T2, (__T1, (nid ()))))
      | (Lam (__D2, __T2), (Lam (__D, __T), rho1)) ->
          eqTerm (__T2, (__T, rho1))
      | (_, (_, _)) -> false
    let rec eqSpine __141__ __142__ =
      match (__141__, __142__) with
      | (I.Nil, (I.Nil, rho1)) -> true
      | (App (__T2, __S2), (App (__T, __S), rho1)) ->
          (eqTerm (__T2, (__T, rho1))) && (eqSpine (__S2, (__S, rho1)))
    let rec divergingSub (__Ds, sigma) (Dr1, rho1) (Dr2, rho2) =
      S.exists rho2
        (fun n2 ->
           fun (dt2, t2) ->
             S.exists sigma (fun _ -> fun (d, t) -> eqTerm (t2, (t, rho1))))
    let rec variantCtx __143__ __144__ =
      match (__143__, __144__) with
      | ((__G, eqn), []) -> None
      | ((__G, eqn), (l', D_G, __G', eqn', answRef', _, status')::GRlist) ->
          if (equalCtx' (__G, __G')) && (equalEqn (eqn, eqn'))
          then Some (l', answRef', status')
          else variantCtx ((__G, eqn), GRlist)
    let rec insert (Nref) (Dsq, sq) (GR) =
      let rec insert' __147__ __148__ __149__ =
        match (__147__, __148__, __149__) with
        | ((Leaf (_, GRlistRef) as N), (Dsq, sq),
           ((l, G_r, eqn, answRef, stage, status) as GR)) ->
            (match variantCtx ((G_r, eqn), (!GRlistRef)) with
             | None ->
                 ((let (D_nsub, D_G) = collectEVar (Dsq, sq) in
                   let GR' = (l, D_G, G_r, eqn, answRef, stage, status) in
                   (((((fun () ->
                          GRlistRef := (GR' :: (!GRlistRef));
                          answList := (answRef :: (!answList)))),
                       (T.NewEntry answRef)))
                     (* D_G contains evars occurring only in eqn or G
                        D_nsub contains evars occurring only in sq
                        furthermore: D_nsub = D where Leaf((D,s), GRlistRef)
                     *)))
                 (* compatible path -- but different ctx! *))
             | Some (_, answRef', status') ->
                 (((((fun () -> ())),
                     (T.RepeatedEntry ((I.id, I.id), answRef', status'))))
                 (* compatible path -- SAME ctx and SAME eqn!
                                          this implies: SAME D_G *)))
        | ((Node ((__D, sub), children) as N), (Dsq, sq),
           ((l, G_r, eqn, answRef, stage, status) as GR)) ->
            let (VariantCand, SplitCand) =
              findAllCandidates (G_r, children, (Dsq, sq)) in
            let (D_nsub, D_G) = collectEVar (Dsq, sq) in
            let GR' = (l, D_G, G_r, eqn, answRef, stage, status) in
            let rec checkCandidates __145__ __146__ =
              match (__145__, __146__) with
              | (nil, nil) ->
                  (((fun () ->
                       (:=) Nref Node
                         ((__D, sub),
                           ((ref (Leaf ((D_nsub, sq), (ref [GR'])))) ::
                              children));
                       answList := (answRef :: (!answList)))),
                    (T.NewEntry answRef))
              | (nil, (ChildRef, (Dsigma, Drho1, Drho2))::_) ->
                  if
                    (!TableParam.divHeuristic) &&
                      (divergingSub (Dsigma, Drho1, Drho2))
                  then
                    (((((fun () ->
                           (:=) ChildRef mkNode
                             ((!ChildRef), Dsigma, Drho1, GR, Drho2);
                           answList := (answRef :: (!answList)))),
                        (T.DivergingEntry (I.id, answRef))))
                    (* substree diverging -- splitting node *))
                  else
                    (((((fun () ->
                           (:=) ChildRef mkNode
                             ((!ChildRef), Dsigma, Drho1, GR, Drho2);
                           answList := (answRef :: (!answList)))),
                        (T.NewEntry answRef)))
                    (* split existing node *))
              | ((ChildRef, Drho2, asub)::nil, _) ->
                  insert (ChildRef, Drho2, GR)
              | ((ChildRef, Drho2, asub)::__L, SCands) ->
                  (match insert (ChildRef, Drho2, GR) with
                   | (_, NewEntry answRef) -> checkCandidates (__L, SCands)
                   | (f, RepeatedEntry (asub, answRef, status)) ->
                       (f, (T.RepeatedEntry (asub, answRef, status)))
                   | (f, DivergingEntry (asub, answRef)) ->
                       (f, (T.DivergingEntry (asub, answRef))))(* there are several "perfect" candidates *)
              (* unique "perfect" candidate (left) *)
              (* split an existing node *)(* no child is compatible with sq *) in
            checkCandidates (VariantCand, SplitCand) in
      insert' ((!Nref), (Dsq, sq), GR)
    let rec answCheckVariant s' answRef (__O) =
      let rec member __150__ __151__ =
        match (__150__, __151__) with
        | ((__D, sk), []) -> false
        | ((__D, sk), ((__D1, s1), _)::__S) ->
            if (equalSub (sk, s1)) && (equalCtx' (__D, __D1))
            then true
            else member ((__D, sk), __S) in
      let (DEVars, sk) = A.abstractAnswSub s' in
      if member ((DEVars, sk), (T.solutions answRef))
      then T.repeated
      else (T.addSolution (((DEVars, sk), __O), answRef); T.new__)
    let rec reset () =
      ((nctr := 1;
        Array.modify
          (fun n ->
             fun (Tree) ->
               n := 0;
               (!) ((:=) Tree) (makeTree ());
               answList := [];
               added := false;
               (n, Tree)) indexArray)
      (* Reset Subsitution Tree *))
    let rec makeCtx __152__ __153__ __154__ =
      match (__152__, __153__, __154__) with
      | (n, I.Null, (DEVars : ctx)) -> ()
      | (n, Decl (__G, __D), (DEVars : ctx)) ->
          (insertList ((n, __D), DEVars); makeCtx ((n + 1), __G, DEVars))
    let rec callCheck a (DAVars) (DEVars) (__G) (__U) eqn status =
      let (n, Tree) = Array.sub (indexArray, a) in
      let sq = S.new__ () in
      let DAEVars = compose (DEVars, DAVars) in
      let Dq = emptyCtx () in
      let n = I.ctxLength __G in
      let _ = makeCtx ((n + 1), DAEVars, (Dq : ctx)) in
      let l = I.ctxLength DAEVars in
      let _ = S.insert sq (1, (0, __U)) in
      let GR =
        ((l, (n + 1)), __G, eqn, (emptyAnswer ()), (!TableParam.stageCtr),
          status) in
      let GR' = ((DEVars, DAVars), __G, eqn, (!TableParam.stageCtr), status) in
      let result =
        try
          retrieveInst (((Tree, (Dq, sq), (asid ()), GR'))
            (* assignable subst *))
        with
        | Instance msg -> ((insert (Tree, (Dq, sq), GR))
            (* sq not in index --> insert it *)) in
      ((match result with
        | (sf, NewEntry answRef) ->
            (sf (); added := true; T.NewEntry answRef)
        | (_, RepeatedEntry (asub, answRef, status)) ->
            T.RepeatedEntry (asub, answRef, status)
        | (sf, DivergingEntry (asub, answRef)) ->
            (sf (); added := true; T.DivergingEntry (asub, answRef)))
        (* n = |G| *)(* Dq = DAVars, DEVars *)(* l = |D| *))
    let rec insertIntoTree a (DAVars) (DEVars) (__G) (__U) eqn answRef status
      =
      let (n, Tree) = Array.sub (indexArray, a) in
      let sq = S.new__ () in
      let DAEVars = compose (DEVars, DAVars) in
      let Dq = emptyCtx () in
      let n = I.ctxLength __G in
      let _ = makeCtx ((n + 1), DAEVars, (Dq : ctx)) in
      let l = I.ctxLength DAEVars in
      let _ = S.insert sq (1, (0, __U)) in
      let GR =
        ((l, (n + 1)), __G, eqn, (emptyAnswer ()), (!TableParam.stageCtr),
          status) in
      let result =
        insert
          (Tree, (Dq, sq),
            ((l, (n + 1)), __G, eqn, answRef, (!TableParam.stageCtr), status)) in
      ((match result with
        | (sf, NewEntry answRef) ->
            (sf (); added := true; T.NewEntry answRef)
        | (_, RepeatedEntry (asub, answRef, status)) ->
            T.RepeatedEntry (asub, answRef, status)
        | (sf, DivergingEntry (asub, answRef)) ->
            (sf (); added := true; T.DivergingEntry (asub, answRef)))
        (* sq = query substitution *))
    let rec answCheck s' answRef (__O) = answCheckVariant (s', answRef, __O)
    let rec updateTable () =
      let rec update __155__ __156__ =
        match (__155__, __156__) with
        | ([], Flag) -> Flag
        | (answRef::AList, Flag) ->
            let l = length (T.solutions answRef) in
            ((if (=) l T.lookup answRef
              then update AList Flag
              else (T.updateAnswLookup (l, answRef); update AList true))
              (* no new solutions were added in the previous stage *)
              (* new solutions were added *)) in
      let Flag = update (!answList) false in
      let r = Flag || (!added) in added := false; r
    let reset = reset
    let callCheck (DAVars) (DEVars) (__G) (__U) eqn status =
      callCheck
        ((cidFromHead (I.targetHead __U)), DAVars, DEVars, __G, __U, eqn,
          status)
    let insertIntoTree (DAVars) (DEVars) (__G) (__U) eqn answRef status =
      insertIntoTree
        ((cidFromHead (I.targetHead __U)), DAVars, DEVars, __G, __U, eqn,
          answRef, status)
    let answerCheck = answCheck
    let updateTable = updateTable
    let tableSize () = length (!answList)
    let rec memberCtx (__G, __V) (__G') =
      let rec instanceCtx' __5__ __6__ __7__ =
        match (__5__, __6__, __7__) with
        | ((__G, __V), I.Null, n) -> None
        | ((__G, __V), Decl (__G', (Dec (_, __V') as D')), n) ->
            if Match.instance (__G, (__V, I.id), (__V', (I.Shift n)))
            then Some __D'
            else instanceCtx' ((__G, __V), __G', (n + 1)) in
      instanceCtx' ((__G, __V), __G', 1)
  end ;;
