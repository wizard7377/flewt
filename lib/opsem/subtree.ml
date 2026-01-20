
module type MEMOTABLE  =
  sig
    val callCheck :
      IntSyn.dctx ->
        IntSyn.dctx ->
          IntSyn.dctx ->
            IntSyn.__Exp -> TableParam.__ResEqn -> TableParam.callCheckResult
    val answerCheck :
      IntSyn.__Sub ->
        TableParam.answer -> CompSyn.pskeleton -> TableParam.answState
    val reset : unit -> unit
    val updateTable : unit -> bool
    val tableSize : unit -> int
  end;;




module MemoTable(MemoTable:sig
                             module Conv : CONV
                             module Whnf : WHNF
                             module AbstractTabled : ABSTRACTTABLED
                             module Print : PRINT
                           end) : MEMOTABLE =
  struct
    module AbstractTabled = AbstractTabled
    type nonrec normalSubsts = IntSyn.__Exp RBSet.ordSet
    type nonrec exSubsts = IntSyn.__Exp RBSet.ordSet
    let (nid : unit -> normalSubsts) = RBSet.new__
    let aid = TableParam.aid
    let (existId : unit -> normalSubsts) = RBSet.new__
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
        | (x, ((y, __E)::__L as H)) ->
            if x = y then Some (y, __E) else memb (x, __L) in
      memb (x, (!__L))
    let rec insertList (__E) (__L) = __L := (__E :: (!__L)); __L
    let rec ctxToEVarSub __5__ __6__ =
      match (__5__, __6__) with
      | (IntSyn.Null, s) -> s
      | (Decl (__G, Dec (_, __A)), s) ->
          let s' = ctxToEVarSub (__G, s) in
          let __X = IntSyn.newEVar (IntSyn.Null, (IntSyn.EClo (__A, s'))) in
          IntSyn.Dot ((IntSyn.Exp __X), s')
    type __Tree =
      | Leaf of ((ctx * normalSubsts) *
      ((((((int * int))(* #G *)(* #EVar *))
          * IntSyn.dctx * TableParam.__ResEqn * TableParam.answer * int *
          TableParam.__Status))(* G *))
      list ref) 
      | Node of ((ctx * normalSubsts) * __Tree ref list) 
    let rec makeTree () = ref (Node (((emptyCtx ()), (nid ())), []))
    let rec noChildren (__C) = __C = []
    type __Retrieval =
      | Variant of IntSyn.__Exp 
      | NotCompatible 
    type __CompSub =
      | SplitSub of ((((ctx * normalSubsts))(* sigma *)) *
      (((ctx * normalSubsts))(* rho1 *)) *
      (((ctx * normalSubsts))(* rho2 *))) 
      | VariantSub of
      (((ctx * normalSubsts))(* normalSubsts * *)(* rho2 *))
      
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
    exception Generalization of string 
    exception DifferentSpines 
    let rec emptyAnswer () = T.emptyAnsw ()
    let (answList : TableParam.answer list ref) = ref []
    let added = ref false
    type nonrec nvar = int
    type nonrec bvar = int
    type nonrec bdepth = int
    let rec cidFromHead = function | Const c -> c | Def c -> c
    let rec dotn __10__ __11__ =
      match (__10__, __11__) with
      | (0, s) -> s
      | (i, s) -> dotn ((i - 1), (I.dot1 s))
    let rec compose __12__ __13__ =
      match (__12__, __13__) with
      | (IntSyn.Null, __G) -> __G
      | (Decl (__G, __D), __G') -> IntSyn.Decl ((compose (__G, __G')), __D)
    let rec shift __14__ __15__ =
      match (__14__, __15__) with
      | (IntSyn.Null, s) -> s
      | (Decl (__G, __D), s) -> I.dot1 (shift (__G, s))
    let rec raiseType __16__ __17__ =
      match (__16__, __17__) with
      | (I.Null, __U) -> __U
      | (Decl (__G, __D), __U) -> raiseType (__G, (I.Lam (__D, __U)))
    let rec ctxToAVarSub __18__ __19__ __20__ =
      match (__18__, __19__, __20__) with
      | (__G', I.Null, s) -> s
      | (__G', Decl (__D, Dec (_, __A)), s) ->
          let EVar (r, _, _, cnstr) as E = I.newEVar (I.Null, __A) in
          I.Dot ((I.Exp __E), (ctxToAVarSub (__G', __D, s)))
      | (__G', Decl (__D, ADec (_, d)), s) ->
          let __X = I.newAVar () in
          I.Dot
            ((I.Exp (I.EClo (__X, (I.Shift (~ d))))),
              (ctxToAVarSub (__G', __D, s)))
    let rec solveEqn' __21__ __22__ =
      match (__21__, __22__) with
      | ((T.Trivial, s), __G) -> true
      | ((Unify (((__G', e1, __N, eqns))(* evar *)), s),
         __G) ->
          let G'' = compose (__G', __G) in
          let s' = shift (__G', s) in
          (Assign.unifiable (G'', (__N, s'), (e1, s'))) &&
            (solveEqn' ((eqns, s), __G))
    let nctr = ref 1
    let rec newNVar () = ((!) ((:=) nctr) nctr) + 1; I.NVar (!nctr)
    let rec equalDec __23__ __24__ =
      match (__23__, __24__) with
      | (Dec (_, __U), Dec (_, __U')) ->
          Conv.conv ((__U, I.id), (__U', I.id))
      | (ADec (_, d), ADec (_, d')) -> d = d'
      | (_, _) -> false
    let rec equalCtx __25__ __26__ __27__ __28__ =
      match (__25__, __26__, __27__, __28__) with
      | (I.Null, s, I.Null, s') -> true
      | (Decl (__G, __D), s, Decl (__G', __D'), s') ->
          (Conv.convDec ((__D, s), (__D', s'))) &&
            (equalCtx (__G, (I.dot1 s), __G', (I.dot1 s')))
      | (_, _, _, _) -> false
    let rec equalEqn __29__ __30__ =
      match (__29__, __30__) with
      | (T.Trivial, T.Trivial) -> true
      | (Unify (__G, __X, __N, eqn), Unify (__G', __X', __N', eqn')) ->
          (equalCtx (__G, I.id, __G', I.id)) &&
            ((Conv.conv ((__X, I.id), (__X', I.id))) &&
               ((Conv.conv ((__N, I.id), (__N', I.id))) &&
                  (equalEqn (eqn, eqn'))))
      | (_, _) -> false
    let rec equalSub __31__ __32__ =
      match (__31__, __32__) with
      | (Shift k, Shift k') -> k = k'
      | (Dot (__F, __S), Dot (__F', __S')) ->
          (equalFront (__F, __F')) && (equalSub (__S, __S'))
      | (Dot (__F, __S), Shift k) -> false
      | (Shift k, Dot (__F, __S)) -> false
    let rec equalFront __33__ __34__ =
      match (__33__, __34__) with
      | (Idx n, Idx n') -> n = n'
      | (Exp (__U), Exp (__V)) -> Conv.conv ((__U, I.id), (__V, I.id))
      | (I.Undef, I.Undef) -> true
    let rec equalSub1 (Dot (ms, s)) (Dot (ms', s')) = equalSub (s, s')
    let rec equalCtx' __35__ __36__ =
      match (__35__, __36__) with
      | (I.Null, I.Null) -> true
      | (Decl (Dk, Dec (_, __A)), Decl (__D1, Dec (_, __A1))) ->
          (Conv.conv ((__A, I.id), (__A1, I.id))) && (equalCtx' (Dk, __D1))
      | (Decl (Dk, ADec (_, d')), Decl (__D1, ADec (_, d))) ->
          (d = d') && (equalCtx' (Dk, __D1))
      | (_, _) -> false
    let rec compareCtx (__G) (__G') = equalCtx' (__G, __G')
    let rec isExists d (BVar k) (__D) = member ((k - d), __D)
    let rec compHeads __37__ __38__ =
      match (__37__, __38__) with
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
    let rec compatible' (D_t, __T) (D_u, __U) (__Ds) rho_t rho_u =
      let rec genNVar (rho_t, __T) (rho_u, __U) =
        S.insert rho_t (((!nctr) + 1), __T);
        S.insert rho_u (((!nctr) + 1), __U);
        newNVar () in
      let rec genRoot __39__ __40__ __41__ =
        match (__39__, __40__, __41__) with
        | (depth, (Root ((Const k as H1), __S1) as T),
           (Root (Const k', __S2) as U)) ->
            if k = k'
            then
              let __S' = genSpine (depth, __S1, __S2) in I.Root (__H1, __S')
            else genNVar ((rho_t, __T), (rho_u, __U))
        | (depth, (Root ((Def k as H1), __S1) as T),
           (Root (Def k', __S2) as U)) ->
            if k = k'
            then
              let __S' = genSpine (depth, __S1, __S2) in I.Root (__H1, __S')
            else genNVar ((rho_t, __T), (rho_u, __U))
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
                              genNVar ((rho_t, __T), (rho_u, __U)))
                       else genNVar ((rho_t, __T), (rho_u, __U))
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
                         else genNVar ((rho_t, __T), (rho_u, __U)))
                       (* they refer to the same existential variable *)
                       (* variant checking only *))
                   | (_, _) -> genNVar ((rho_t, __T), (rho_u, __U))))
                  (* k, k' refer to the existential *))
              else
                if k = k'
                then
                  (try
                     let __S' = genSpine (d, __S1, __S2) in
                     I.Root (__H1, __S')
                   with
                   | DifferentSpines -> genNVar ((rho_t, __T), (rho_u, __U)))
                else genNVar ((rho_t, __T), (rho_u, __U)))
            (* globally bound variable *)(* locally bound variables *))
        | (d, (Root ((BVar k as H1), __S1) as T),
           (Root (Const k', __S2) as U)) ->
            genNVar ((rho_t, __T), (rho_u, __U))
        | (d, (Root (__H1, __S1) as T), (Root (__H2, __S2) as U)) ->
            genNVar ((rho_t, __T), (rho_u, __U))
      and genExp __42__ __43__ __44__ =
        match (__42__, __43__, __44__) with
        | (d, (NVar n as T), (Root (__H, __S) as U)) ->
            (S.insert rho_u (n, __U); __T)
        | (d, (Root (__H1, __S1) as T), (Root (__H2, __S2) as U)) ->
            genRoot (d, (I.Root (__H1, __S1)), (I.Root (__H2, __S2)))
        | (d, Lam ((Dec (_, __A1) as D1), __T1), Lam
           ((Dec (_, __A2) as D2), __U2)) ->
            let __E = genExp ((d + 1), __T1, __U2) in I.Lam (__D1, __E)
        | (d, __T, __U) ->
            (print "genExp -- falls through?\n";
             genNVar ((rho_t, __T), (rho_u, __U)))(* U = EVar, EClo -- can't happen -- Sun Oct 20 13:41:25 2002 -bp *)
      (* by invariant A1 = A2 *)
      and genSpine __45__ __46__ __47__ =
        match (__45__, __46__, __47__) with
        | (d, I.Nil, I.Nil) -> I.Nil
        | (d, App (__T, __S1), App (__U, __S2)) ->
            let __E = genExp (d, __T, __U) in
            let __S' = genSpine (d, __S1, __S2) in I.App (__E, __S')
        | (d, I.Nil, App (_, _)) -> raise DifferentSpines
        | (d, App (_, _), I.Nil) -> raise DifferentSpines
        | (d, SClo (_, _), _) -> raise DifferentSpines
        | (d, _, SClo (_, _)) -> raise DifferentSpines in
      let __E = genExp (0, __T, __U) in Variant __E
    let rec compatible __48__ __49__ __50__ __51__ __52__ =
      match (__48__, __49__, __50__, __51__, __52__) with
      | ((D_t, (Root (__H1, __S1) as T)), (D_u, (Root (__H2, __S2) as U)),
         __Ds, rho_t, rho_u) ->
          if compHeads ((D_t, __H1), (D_u, __H2))
          then compatible' ((D_t, __T), (D_u, __U), __Ds, rho_t, rho_u)
          else NotCompatible
      | ((D_t, __T), (D_u, __U), __Ds, rho_t, rho_u) ->
          compatible' ((D_t, __T), (D_u, __U), __Ds, rho_t, rho_u)
    let rec compatibleSub (D_t, nsub_t) (D_u, nsub_u) =
      let (sigma, rho_t, rho_u) = ((nid ()), (nid ()), (nid ())) in
      let Dsigma = emptyCtx () in
      let D_r1 = copy D_t in
      let D_r2 = copy D_u in
      let choose = ref (fun match__ -> ()) in
      let _ =
        S.forall nsub_u
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
        (* by invariant rho_t = empty, since nsub_t <= nsub_u *)
        (* Dsigma |~ sigma, D_r1 |~ rho_t, D_r1 |~ rho_u *))
    let rec mkLeaf (__Ds) (GR) n = Leaf (__Ds, GR)
    let rec mkNode __53__ __54__ __55__ __56__ __57__ =
      match (__53__, __54__, __55__, __56__, __57__) with
      | (Node (_, Children), Dsigma, Drho1, GR, Drho2) ->
          Node
            (Dsigma,
              [ref (Leaf (Drho2, (ref [GR]))); ref (Node (Drho1, Children))])
      | (Leaf (c, GRlist), Dsigma, Drho1, GR2, Drho2) ->
          Node
            (Dsigma,
              [ref (Leaf (Drho2, (ref [GR2]))); ref (Leaf (Drho1, GRlist))])
    let rec compatibleCtx __58__ __59__ =
      match (__58__, __59__) with
      | ((__G, eqn), []) -> None
      | ((__G, eqn), (l', __G', eqn', answRef', _, status')::GRlist) ->
          if (equalCtx' (__G, __G')) && (equalEqn (eqn, eqn'))
          then Some (l', answRef', status')
          else compatibleCtx ((__G, eqn), GRlist)(* we may not need to check that the DAVars are the same *)
    let rec compChild __60__ __61__ =
      match (__60__, __61__) with
      | ((Leaf ((D_t, nsub_t), GList) as N), (D_e, nsub_e)) ->
          compatibleSub ((D_t, nsub_t), (D_e, nsub_e))
      | ((Node ((D_t, nsub_t), Children') as N), (D_e, nsub_e)) ->
          compatibleSub ((D_t, nsub_t), (D_e, nsub_e))
    let rec findAllCandidates (G_r) children (__Ds) =
      let rec findAllCands __62__ __63__ __64__ __65__ __66__ =
        match (__62__, __63__, __64__, __65__, __66__) with
        | (G_r, nil, (D_u, sub_u), VList, SList) -> (VList, SList)
        | (G_r, x::__L, (D_u, sub_u), VList, SList) ->
            (match compChild ((!x), (D_u, sub_u)) with
             | NoCompatibleSub ->
                 findAllCands (G_r, __L, (D_u, sub_u), VList, SList)
             | SplitSub (Dsigma, Drho1, Drho2) ->
                 findAllCands
                   (G_r, __L, (D_u, sub_u), VList,
                     ((x, (Dsigma, Drho1, Drho2)) :: SList))
             | VariantSub ((D_r2, rho2) as Drho2) ->
                 findAllCands
                   (G_r, __L, (D_u, sub_u), ((x, Drho2, I.id) :: VList),
                     SList)) in
      findAllCands (G_r, children, __Ds, nil, nil)
    let rec divergingCtx stage (__G) (GRlistRef) =
      let l = I.ctxLength __G in
      List.exists
        (fun (evar, l) ->
           fun (__G') ->
             fun _ ->
               fun _ ->
                 fun stage' ->
                   fun _ -> (stage = stage') && (l > (I.ctxLength __G')))
        (!GRlistRef)
    let rec eqHeads __67__ __68__ =
      match (__67__, __68__) with
      | (Const k, Const k') -> k = k'
      | (BVar k, BVar k') -> k = k'
      | (Def k, Def k') -> k = k'
      | (_, _) -> false
    let rec eqTerm __69__ __70__ =
      match (__69__, __70__) with
      | (Root (__H2, __S2), ((Root (__H, __S) as t), rho1)) ->
          if eqHeads (__H2, __H)
          then eqSpine (__S2, (__S, rho1))
          else false
      | (__T2, (NVar n, rho1)) ->
          (match S.lookup rho1 n with
           | None -> false
           | Some (__T1) -> eqTerm (__T2, (__T1, (nid ()))))
      | (Lam (__D2, __T2), (Lam (__D, __T), rho1)) ->
          eqTerm (__T2, (__T, rho1))
      | (_, (_, _)) -> false
    let rec eqSpine __71__ __72__ =
      match (__71__, __72__) with
      | (I.Nil, (I.Nil, rho1)) -> true
      | (App (__T2, __S2), (App (__T, __S), rho1)) ->
          (eqTerm (__T2, (__T, rho1))) && (eqSpine (__S2, (__S, rho1)))
      | (_, _) -> false
    let rec divergingSub (__Ds, sigma) (Dr1, rho1) (Dr2, rho2) =
      S.exists rho2
        (fun n2 ->
           fun t2 ->
             S.exists sigma (fun _ -> fun t -> eqTerm (t2, (t, rho1))))
    let rec insert (Nref) (D_u, nsub_u) (GR) =
      let rec insert' __75__ __76__ __77__ =
        match (__75__, __76__, __77__) with
        | ((Leaf ((__D, _), GRlistRef) as N), (D_u, nsub_u),
           (((evarl, l), G_r, eqn, answRef, stage, status) as GR)) ->
            (match compatibleCtx ((G_r, eqn), (!GRlistRef)) with
             | None ->
                 ((if
                     (!TableParam.divHeuristic) &&
                       (divergingCtx (stage, G_r, GRlistRef))
                   then
                     (((((fun () ->
                            GRlistRef := (GR :: (!GRlistRef));
                            answList := (answRef :: (!answList)))),
                         (T.DivergingEntry (I.id, answRef))))
                     (* ctx are diverging --- force suspension *))
                   else
                     (((fun () ->
                          GRlistRef := (GR :: (!GRlistRef));
                          answList := (answRef :: (!answList)))),
                       (T.NewEntry answRef)))
                 (* compatible path (variant) -- ctx are different *)
                 (* compatible path -- but different ctx! *))
             | Some ((evarl', Glength), answRef', status') ->
                 (((((fun () -> ())),
                     (T.RepeatedEntry ((I.id, I.id), answRef', status'))))
                 (* compatible path -- SAME ctx *)))
        | ((Node ((__D, sub), children) as N), (D_u, nsub_u),
           ((l, G_r, eqn, answRef, stage, status) as GR)) ->
            let (VariantCand, SplitCand) =
              findAllCandidates (G_r, children, (D_u, nsub_u)) in
            let rec checkCandidates __73__ __74__ =
              match (__73__, __74__) with
              | (nil, nil) ->
                  (((((fun () ->
                         (:=) Nref Node
                           ((__D, sub),
                             ((ref (Leaf ((D_u, nsub_u), (ref [GR])))) ::
                                children));
                         answList := (answRef :: (!answList)))),
                      (T.NewEntry answRef)))
                  (* no child is compatible with nsub_u *))
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
                    (* substree divering -- splitting node *))
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
              (* split an existing node *) in
            checkCandidates (VariantCand, SplitCand)(* need to compare D and D_u *) in
      insert' ((!Nref), (D_u, nsub_u), GR)
    let rec answCheckVariant s' answRef (__O) =
      let rec member __78__ __79__ =
        match (__78__, __79__) with
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
      nctr := 1;
      Array.modify
        (fun n ->
           fun (Tree) ->
             n := 0;
             (!) ((:=) Tree) (makeTree ());
             answList := [];
             added := false;
             (n, Tree)) indexArray
    let rec makeCtx __80__ __81__ __82__ =
      match (__80__, __81__, __82__) with
      | (n, I.Null, (DEVars : ctx)) -> n
      | (n, Decl (__G, __D), (DEVars : ctx)) ->
          (insertList ((n, __D), DEVars); makeCtx ((n + 1), __G, DEVars))
    let rec callCheck a (DAVars) (DEVars) (__G) (__U) eqn status =
      let (n, Tree) = Array.sub (indexArray, a) in
      let nsub_goal = S.new__ () in
      let DAEVars = compose (DEVars, DAVars) in
      let __D = emptyCtx () in
      let n = I.ctxLength __G in
      let _ = makeCtx ((n + 1), DAEVars, (__D : ctx)) in
      let l = I.ctxLength DAEVars in
      let _ = S.insert nsub_goal (1, __U) in
      let result =
        insert
          (Tree, (__D, nsub_goal),
            ((l, (n + 1)), __G, eqn, (emptyAnswer ()),
              (!TableParam.stageCtr), status)) in
      let esub = ctxToAVarSub (__G, DAEVars, (I.Shift 0)) in
      let _ =
        if solveEqn' ((eqn, (shift (__G, esub))), __G)
        then ()
        else print " failed to solve eqn_query\n" in
      match result with
      | (sf, NewEntry answRef) ->
          (sf ();
           added := true;
           if (!Global.chatter) >= 5 then print "\t -- Add goal \n" else ();
           T.NewEntry answRef)
      | (_, RepeatedEntry (((_, asub) as s), answRef, status)) ->
          (if (!Global.chatter) >= 5
           then print "\t -- Suspend goal\n"
           else ();
           T.RepeatedEntry ((esub, asub), answRef, status))
      | (sf, DivergingEntry answRef) ->
          (sf ();
           added := true;
           if (!Global.chatter) >= 5
           then print "\t -- Add diverging goal\n"
           else ();
           T.DivergingEntry answRef)
    let rec insertIntoTree a (DAVars) (DEVars) (__G) (__U) eqn answRef status
      =
      let (n, Tree) = Array.sub (indexArray, a) in
      let nsub_goal = S.new__ () in
      let DAEVars = compose (DEVars, DAVars) in
      let __D = emptyCtx () in
      let n = I.ctxLength __G in
      let _ = makeCtx ((n + 1), DAEVars, (__D : ctx)) in
      let l = I.ctxLength DAEVars in
      let _ = S.insert nsub_goal (1, __U) in
      let result =
        insert
          (Tree, (__D, nsub_goal),
            ((l, (n + 1)), __G, eqn, answRef, (!TableParam.stageCtr), status)) in
      match result with
      | (sf, NewEntry answRef) ->
          (added := true;
           if (!Global.chatter) >= 5 then print "\t -- Add goal \n" else ();
           T.NewEntry answRef)
      | (_, RepeatedEntry (asub, answRef, status)) ->
          (if (!Global.chatter) >= 5
           then print "\t -- Suspend goal\n"
           else ();
           T.RepeatedEntry (asub, answRef, status))
      | (sf, DivergingEntry answRef) ->
          (sf ();
           added := true;
           if (!Global.chatter) >= 5
           then print "\t -- Add diverging goal\n"
           else ();
           T.DivergingEntry answRef)
    let rec answCheck s' answRef (__O) = answCheckVariant (s', answRef, __O)
    let rec updateTable () =
      let rec update __83__ __84__ =
        match (__83__, __84__) with
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
      let rec memberCtx' __7__ __8__ __9__ =
        match (__7__, __8__, __9__) with
        | ((__G, __V), I.Null, n) -> None
        | ((__G, __V), Decl (__G', (Dec (_, __V') as D')), n) ->
            if Conv.conv ((__V, I.id), (__V', (I.Shift n)))
            then Some __D'
            else memberCtx' ((__G, __V), __G', (n + 1)) in
      memberCtx' ((__G, __V), __G', 1)
  end ;;
