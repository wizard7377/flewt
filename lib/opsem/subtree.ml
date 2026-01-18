
(* Indexing *)
(* Author: Brigitte Pientka *)
module type MEMOTABLE  =
  sig
    (*! structure IntSyn : INTSYN !*)
    (*! structure CompSyn : COMPSYN !*)
    (*! structure TableParam : TABLEPARAM !*)
    (* call check/insert *)
    (* callCheck (G, D, U, eqn)
   *
   * if D, G |- U & eqn     in table  then RepeatedEntry (entries)
   * if D, G |- U & eqn not in table  then NewEntry (ptrAnswer)
   * SIDE EFFECT: D, G |- U added to table
   *)
    val callCheck :
      (IntSyn.dctx * IntSyn.dctx * IntSyn.dctx * IntSyn.__Exp *
        TableParam.__ResEqn) -> TableParam.callCheckResult
    (* answer check/insert *)
    (* answerCheck (G, D, (U,s))
   * 
   * Assupmtion: D, G |- U is in table
   *             and A represents the corresponding solutions
   * 
   * G |- s : D, G
   * Dk, G |- sk : D, G
   *
   * If  (Dk, sk) in A then repeated
   *  else new
   *)
    val answerCheck :
      (IntSyn.__Sub * TableParam.answer * CompSyn.pskeleton) ->
        TableParam.answState
    (* reset table *)
    val reset : unit -> unit
    (* updateTable 
   *
   * SIDE EFFECT: 
   *   for each table entry: 
   *       advance lookup pointer
   *
   * if Table did not change during last stage 
   *    then updateTable () =  false
   * else updateTable () = true
   *)
    val updateTable : unit -> bool
    val tableSize : unit -> int
  end;;




(* Linear Substitution Tree indexing *)
(* Linearity: Any variables occurring inside the substitution tree are linear *)
(* Any term we insert into the substitution tree is in normalform *)
(* Variant Checking *)
(* Author: Brigitte Pientka *)
module MemoTable(MemoTable:sig
                             (*! structure IntSyn' : INTSYN !*)
                             (*! structure CompSyn' : COMPSYN !*)
                             (*! sharing CompSyn'.IntSyn = IntSyn' !*)
                             module Conv : CONV
                             module Whnf : WHNF
                             module AbstractTabled : ABSTRACTTABLED
                             (*! sharing Conv.IntSyn = IntSyn' !*)
                             (*! sharing Whnf.IntSyn = IntSyn' !*)
                             (*! structure RBSet : RBSET !*)
                             (*! structure TableParam : TABLEPARAM !*)
                             (*! sharing TableParam.IntSyn = IntSyn' !*)
                             (*! sharing TableParam.CompSyn = CompSyn' !*)
                             (*! sharing TableParam.RBSet = RBSet !*)
                             (*! sharing AbstractTabled.IntSyn = IntSyn' !*)
                             module Print : PRINT
                           end) : MEMOTABLE =
  struct
    (*! sharing Print.IntSyn = IntSyn'!*)
    (*! structure IntSyn = IntSyn' !*)
    (*! structure CompSyn = CompSyn' !*)
    module AbstractTabled = AbstractTabled
    (*! structure TableParam = TableParam !*)
    (* ---------------------------------------------------------------------- *)
    (* Linear substitution tree for linear terms *)
    (* normalSubsts: key = int = nvar *)
    (* property: linear *)
    type nonrec normalSubsts = IntSyn.__Exp RBSet.ordSet
    type nonrec exSubsts = IntSyn.__Exp RBSet.ordSet
    let (nid : unit -> normalSubsts) = RBSet.new__
    let aid = TableParam.aid
    let (existId : unit -> normalSubsts) = RBSet.new__
    let rec isId s = RBSet.isEmpty s
    (* ---------------------------------------------------------------------- *)
    type nonrec ctx = (int * IntSyn.__Dec) list ref
    let rec emptyCtx () = (ref [] : ctx)
    let rec copy (L) = (ref (!L) : ctx)
    (* destructively updates L *)
    let rec delete (x, (L : ctx)) =
      let rec del =
        function
        | (x, [], L) -> NONE
        | (x, ((y, E) as H)::L, L') ->
            if x = y
            then SOME ((y, E), ((rev L') @ L))
            else del (x, L, (H :: L')) in
      match del (x, (!L), []) with
      | NONE -> NONE
      | SOME ((y, E), L') -> (L := L'; SOME (y, E))
    let rec member (x, (L : ctx)) =
      let rec memb =
        function
        | (x, []) -> NONE
        | (x, ((y, E)::L as H)) -> if x = y then SOME (y, E) else memb (x, L) in
      memb (x, (!L))
    let rec insertList (E, L) = L := (E :: (!L)); L
    (* ctxToEVarSub D = s

     if D is a context for existential variables,
        s.t. u_1:: A_1,.... u_n:: A_n = D
     then . |- s : D where s = X_n....X_1.id

    *)
    let rec ctxToEVarSub =
      function
      | (IntSyn.Null, s) -> s
      | (Decl (G, Dec (_, A)), s) ->
          let s' = ctxToEVarSub (G, s) in
          let X = IntSyn.newEVar (IntSyn.Null, (IntSyn.EClo (A, s'))) in
          IntSyn.Dot ((IntSyn.Exp X), s')
    (* ---------------------------------------------------------------------- *)
    (* Substitution Tree *)
    (* it is only possible to distribute the evar-ctx because
     all evars occur exactly once! -- linear
     this allows us to maintain invariant, that every occurrence of an evar is
     defined in its evar-ctx
     *)
    type __Tree =
      | Leaf of ((ctx * normalSubsts) * ((int * int) * IntSyn.dctx *
      TableParam.__ResEqn * TableParam.answer * int * TableParam.__Status)
      list ref) 
      | Node of ((ctx * normalSubsts) * __Tree ref list) 
    (* #G *)
    (* G *)
    (* #EVar *)
    let rec makeTree () = ref (Node (((emptyCtx ()), (nid ())), []))
    let rec noChildren (C) = C = []
    type __Retrieval =
      | Variant of IntSyn.__Exp 
      | NotCompatible 
    type __CompSub =
      | SplitSub of ((ctx * normalSubsts) * (ctx * normalSubsts) * (ctx *
      normalSubsts)) 
      | VariantSub of (ctx * normalSubsts) 
      | NoCompatibleSub 
    (* sigma *)
    (* rho1 *)
    (* rho2 *)
    (* normalSubsts * *)
    (* rho2 *)
    (* Index array

     All type families have their own substitution tree and all substitution trees
     are stored in an array [a1,...,an]   where ai is a substitution tree for type family ai
     *)
    let indexArray =
      Array.tabulate
        (Global.maxCid, (function | i -> ((ref 0), (makeTree ()))))
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
    let added = ref false__
    type nonrec nvar = int
    type nonrec bvar = int
    type nonrec bdepth = int
    let rec cidFromHead = function | Const c -> c | Def c -> c
    let rec dotn =
      function | (0, s) -> s | (i, s) -> dotn ((i - 1), (I.dot1 s))
    let rec compose =
      function
      | (IntSyn.Null, G) -> G
      | (Decl (G, D), G') -> IntSyn.Decl ((compose (G, G')), D)
    let rec shift =
      function
      | (IntSyn.Null, s) -> s
      | (Decl (G, D), s) -> I.dot1 (shift (G, s))
    let rec raiseType =
      function
      | (I.Null, U) -> U
      | (Decl (G, D), U) -> raiseType (G, (I.Lam (D, U)))
    let rec ctxToAVarSub =
      function
      | (G', I.Null, s) -> s
      | (G', Decl (D, Dec (_, A)), s) ->
          let EVar (r, _, _, cnstr) as E = I.newEVar (I.Null, A) in
          I.Dot ((I.Exp E), (ctxToAVarSub (G', D, s)))
      | (G', Decl (D, ADec (_, d)), s) ->
          let X = I.newAVar () in
          I.Dot
            ((I.Exp (I.EClo (X, (I.Shift (~ d))))),
              (ctxToAVarSub (G', D, s)))
    let rec solveEqn' =
      function
      | ((T.Trivial, s), G) -> true__
      | ((Unify (G', e1, N, eqns), s), G) ->
          let G'' = compose (G', G) in
          let s' = shift (G', s) in
          (Assign.unifiable (G'', (N, s'), (e1, s'))) &&
            (solveEqn' ((eqns, s), G))
    let nctr = ref 1
    let rec newNVar () = ((!) ((:=) nctr) nctr) + 1; I.NVar (!nctr)
    let rec equalDec =
      function
      | (Dec (_, U), Dec (_, U')) -> Conv.conv ((U, I.id), (U', I.id))
      | (ADec (_, d), ADec (_, d')) -> d = d'
      | (_, _) -> false__
    let rec equalCtx =
      function
      | (I.Null, s, I.Null, s') -> true__
      | (Decl (G, D), s, Decl (G', D'), s') ->
          (Conv.convDec ((D, s), (D', s'))) &&
            (equalCtx (G, (I.dot1 s), G', (I.dot1 s')))
      | (_, _, _, _) -> false__
    let rec equalEqn =
      function
      | (T.Trivial, T.Trivial) -> true__
      | (Unify (G, X, N, eqn), Unify (G', X', N', eqn')) ->
          (equalCtx (G, I.id, G', I.id)) &&
            ((Conv.conv ((X, I.id), (X', I.id))) &&
               ((Conv.conv ((N, I.id), (N', I.id))) && (equalEqn (eqn, eqn'))))
      | (_, _) -> false__
    let rec equalSub =
      function
      | (Shift k, Shift k') -> k = k'
      | (Dot (F, S), Dot (F', S')) ->
          (equalFront (F, F')) && (equalSub (S, S'))
      | (Dot (F, S), Shift k) -> false__
      | (Shift k, Dot (F, S)) -> false__
    let rec equalFront =
      function
      | (Idx n, Idx n') -> n = n'
      | (Exp (U), Exp (V)) -> Conv.conv ((U, I.id), (V, I.id))
      | (I.Undef, I.Undef) -> true__
    let rec equalSub1 (Dot (ms, s), Dot (ms', s')) = equalSub (s, s')
    let rec equalCtx' =
      function
      | (I.Null, I.Null) -> true__
      | (Decl (Dk, Dec (_, A)), Decl (D1, Dec (_, A1))) ->
          (Conv.conv ((A, I.id), (A1, I.id))) && (equalCtx' (Dk, D1))
      | (Decl (Dk, ADec (_, d')), Decl (D1, ADec (_, d))) ->
          (d = d') && (equalCtx' (Dk, D1))
      | (_, _) -> false__
    let rec compareCtx (G, G') = equalCtx' (G, G')
    let rec isExists (d, BVar k, D) = member ((k - d), D)
    let rec compHeads =
      function
      | ((D_1, Const k), (D_2, Const k')) -> k = k'
      | ((D_1, Def k), (D_2, Def k')) -> k = k'
      | ((D_1, BVar k), (D_2, BVar k')) ->
          (match isExists (0, (I.BVar k), D_1) with
           | NONE -> k = k'
           | SOME (x, Dec) -> true__)
      | ((D_1, BVar k), (D_2, H2)) ->
          (match isExists (0, (I.BVar k), D_1) with
           | NONE -> false__
           | SOME (x, Dec) -> true__)
      | ((D_1, H1), (D_2, H2)) -> false__
    let rec compatible' ((D_t, T), (D_u, U), Ds, rho_t, rho_u) =
      let rec genNVar ((rho_t, T), (rho_u, U)) =
        S.insert rho_t (((!nctr) + 1), T);
        S.insert rho_u (((!nctr) + 1), U);
        newNVar () in
      let rec genRoot =
        function
        | (depth, (Root ((Const k as H1), S1) as T),
           (Root (Const k', S2) as U)) ->
            if k = k'
            then let S' = genSpine (depth, S1, S2) in I.Root (H1, S')
            else genNVar ((rho_t, T), (rho_u, U))
        | (depth, (Root ((Def k as H1), S1) as T), (Root (Def k', S2) as U))
            ->
            if k = k'
            then let S' = genSpine (depth, S1, S2) in I.Root (H1, S')
            else genNVar ((rho_t, T), (rho_u, U))
        | (d, (Root ((BVar k as H1), S1) as T), (Root (BVar k', S2) as U)) ->
            if (k > d) && (k' > d)
            then
              let k1 = k - d in
              let k2 = k' - d in
              (match ((member (k1, D_t)), (member (k2, D_u))) with
               | (NONE, NONE) ->
                   if k1 = k2
                   then
                     (try let S' = genSpine (d, S1, S2) in I.Root (H1, S')
                      with
                      | DifferentSpine -> genNVar ((rho_t, T), (rho_u, U)))
                   else genNVar ((rho_t, T), (rho_u, U))
               | (SOME (x, Dec1), SOME (x', Dec2)) ->
                   if (k1 = k2) && (equalDec (Dec1, Dec2))
                   then
                     let S' = genSpine (d, S1, S2) in
                     (delete (x, D_t);
                      delete (x', D_u);
                      insertList ((x, Dec1), Ds);
                      I.Root (H1, S'))
                   else genNVar ((rho_t, T), (rho_u, U))
               | (_, _) -> genNVar ((rho_t, T), (rho_u, U)))
            else
              if k = k'
              then
                (try let S' = genSpine (d, S1, S2) in I.Root (H1, S')
                 with | DifferentSpines -> genNVar ((rho_t, T), (rho_u, U)))
              else genNVar ((rho_t, T), (rho_u, U))
        | (d, (Root ((BVar k as H1), S1) as T), (Root (Const k', S2) as U))
            -> genNVar ((rho_t, T), (rho_u, U))
        | (d, (Root (H1, S1) as T), (Root (H2, S2) as U)) ->
            genNVar ((rho_t, T), (rho_u, U))
      and genExp =
        function
        | (d, (NVar n as T), (Root (H, S) as U)) ->
            (S.insert rho_u (n, U); T)
        | (d, (Root (H1, S1) as T), (Root (H2, S2) as U)) ->
            genRoot (d, (I.Root (H1, S1)), (I.Root (H2, S2)))
        | (d, Lam ((Dec (_, A1) as D1), T1), Lam ((Dec (_, A2) as D2), U2))
            -> let E = genExp ((d + 1), T1, U2) in I.Lam (D1, E)
        | (d, T, U) ->
            (print "genExp -- falls through?\n";
             genNVar ((rho_t, T), (rho_u, U)))
      and genSpine =
        function
        | (d, I.Nil, I.Nil) -> I.Nil
        | (d, App (T, S1), App (U, S2)) ->
            let E = genExp (d, T, U) in
            let S' = genSpine (d, S1, S2) in I.App (E, S')
        | (d, I.Nil, App (_, _)) -> raise DifferentSpines
        | (d, App (_, _), I.Nil) -> raise DifferentSpines
        | (d, SClo (_, _), _) -> raise DifferentSpines
        | (d, _, SClo (_, _)) -> raise DifferentSpines in
      let E = genExp (0, T, U) in Variant E
    let rec compatible =
      function
      | ((D_t, (Root (H1, S1) as T)), (D_u, (Root (H2, S2) as U)), Ds, rho_t,
         rho_u) ->
          if compHeads ((D_t, H1), (D_u, H2))
          then compatible' ((D_t, T), (D_u, U), Ds, rho_t, rho_u)
          else NotCompatible
      | ((D_t, T), (D_u, U), Ds, rho_t, rho_u) ->
          compatible' ((D_t, T), (D_u, U), Ds, rho_t, rho_u)
    let rec compatibleSub ((D_t, nsub_t), (D_u, nsub_u)) =
      let (sigma, rho_t, rho_u) = ((nid ()), (nid ()), (nid ())) in
      let Dsigma = emptyCtx () in
      let D_r1 = copy D_t in
      let D_r2 = copy D_u in
      let choose = ref (function | (match__ : bool) -> ()) in
      let _ =
        S.forall nsub_u
          (function
           | (nv, U) ->
               (match S.lookup nsub_t nv with
                | SOME (T) ->
                    (match compatible
                             ((D_r1, T), (D_r2, U), Dsigma, rho_t, rho_u)
                     with
                     | NotCompatible ->
                         (S.insert rho_t (nv, T); S.insert rho_u (nv, U))
                     | Variant (T') ->
                         let restc = !choose in
                         (S.insert sigma (nv, T');
                          choose :=
                            ((function
                              | match__ ->
                                  (restc match__; if match__ then () else ())))))
                | NONE -> S.insert rho_u (nv, U))) in
      if isId rho_t
      then ((!) choose true__; VariantSub (D_r2, rho_u))
      else
        ((!) choose false__;
         if isId sigma
         then NoCompatibleSub
         else SplitSub ((Dsigma, sigma), (D_r1, rho_t), (D_r2, rho_u)))
    let rec mkLeaf (Ds, GR, n) = Leaf (Ds, GR)
    let rec mkNode =
      function
      | (Node (_, Children), Dsigma, Drho1, GR, Drho2) ->
          Node
            (Dsigma,
              [ref (Leaf (Drho2, (ref [GR]))); ref (Node (Drho1, Children))])
      | (Leaf (c, GRlist), Dsigma, Drho1, GR2, Drho2) ->
          Node
            (Dsigma,
              [ref (Leaf (Drho2, (ref [GR2]))); ref (Leaf (Drho1, GRlist))])
    let rec compatibleCtx =
      function
      | ((G, eqn), []) -> NONE
      | ((G, eqn), (l', G', eqn', answRef', _, status')::GRlist) ->
          if (equalCtx' (G, G')) && (equalEqn (eqn, eqn'))
          then SOME (l', answRef', status')
          else compatibleCtx ((G, eqn), GRlist)
    let rec compChild =
      function
      | ((Leaf ((D_t, nsub_t), GList) as N), (D_e, nsub_e)) ->
          compatibleSub ((D_t, nsub_t), (D_e, nsub_e))
      | ((Node ((D_t, nsub_t), Children') as N), (D_e, nsub_e)) ->
          compatibleSub ((D_t, nsub_t), (D_e, nsub_e))
    let rec findAllCandidates (G_r, children, Ds) =
      let rec findAllCands =
        function
        | (G_r, nil, (D_u, sub_u), VList, SList) -> (VList, SList)
        | (G_r, x::L, (D_u, sub_u), VList, SList) ->
            (match compChild ((!x), (D_u, sub_u)) with
             | NoCompatibleSub ->
                 findAllCands (G_r, L, (D_u, sub_u), VList, SList)
             | SplitSub (Dsigma, Drho1, Drho2) ->
                 findAllCands
                   (G_r, L, (D_u, sub_u), VList,
                     ((x, (Dsigma, Drho1, Drho2)) :: SList))
             | VariantSub ((D_r2, rho2) as Drho2) ->
                 findAllCands
                   (G_r, L, (D_u, sub_u), ((x, Drho2, I.id) :: VList), SList)) in
      findAllCands (G_r, children, Ds, nil, nil)
    let rec divergingCtx (stage, G, GRlistRef) =
      let l = I.ctxLength G in
      List.exists
        (function
         | ((evar, l), G', _, _, stage', _) ->
             (stage = stage') && (l > (I.ctxLength G'))) (!GRlistRef)
    let rec eqHeads =
      function
      | (Const k, Const k') -> k = k'
      | (BVar k, BVar k') -> k = k'
      | (Def k, Def k') -> k = k'
      | (_, _) -> false__
    let rec eqTerm =
      function
      | (Root (H2, S2), ((Root (H, S) as t), rho1)) ->
          if eqHeads (H2, H) then eqSpine (S2, (S, rho1)) else false__
      | (T2, (NVar n, rho1)) ->
          (match S.lookup rho1 n with
           | NONE -> false__
           | SOME (T1) -> eqTerm (T2, (T1, (nid ()))))
      | (Lam (D2, T2), (Lam (D, T), rho1)) -> eqTerm (T2, (T, rho1))
      | (_, (_, _)) -> false__
    let rec eqSpine =
      function
      | (I.Nil, (I.Nil, rho1)) -> true__
      | (App (T2, S2), (App (T, S), rho1)) ->
          (eqTerm (T2, (T, rho1))) && (eqSpine (S2, (S, rho1)))
      | (_, _) -> false__
    let rec divergingSub ((Ds, sigma), (Dr1, rho1), (Dr2, rho2)) =
      S.exists rho2
        (function
         | (n2, t2) ->
             S.exists sigma (function | (_, t) -> eqTerm (t2, (t, rho1))))
    let rec insert (Nref, (D_u, nsub_u), GR) =
      let rec insert' =
        function
        | ((Leaf ((D, _), GRlistRef) as N), (D_u, nsub_u),
           (((evarl, l), G_r, eqn, answRef, stage, status) as GR)) ->
            (match compatibleCtx ((G_r, eqn), (!GRlistRef)) with
             | NONE ->
                 if
                   (!TableParam.divHeuristic) &&
                     (divergingCtx (stage, G_r, GRlistRef))
                 then
                   (((function
                      | () ->
                          (GRlistRef := (GR :: (!GRlistRef));
                           answList := (answRef :: (!answList))))),
                     (T.DivergingEntry (I.id, answRef)))
                 else
                   (((function
                      | () ->
                          (GRlistRef := (GR :: (!GRlistRef));
                           answList := (answRef :: (!answList))))),
                     (T.NewEntry answRef))
             | SOME ((evarl', Glength), answRef', status') ->
                 (((function | () -> ())),
                   (T.RepeatedEntry ((I.id, I.id), answRef', status'))))
        | ((Node ((D, sub), children) as N), (D_u, nsub_u),
           ((l, G_r, eqn, answRef, stage, status) as GR)) ->
            let (VariantCand, SplitCand) =
              findAllCandidates (G_r, children, (D_u, nsub_u)) in
            let rec checkCandidates =
              function
              | (nil, nil) ->
                  (((function
                     | () ->
                         ((:=) Nref Node
                            ((D, sub),
                              ((ref (Leaf ((D_u, nsub_u), (ref [GR])))) ::
                                 children));
                          answList := (answRef :: (!answList))))),
                    (T.NewEntry answRef))
              | (nil, (ChildRef, (Dsigma, Drho1, Drho2))::_) ->
                  if
                    (!TableParam.divHeuristic) &&
                      (divergingSub (Dsigma, Drho1, Drho2))
                  then
                    (((function
                       | () ->
                           ((:=) ChildRef mkNode
                              ((!ChildRef), Dsigma, Drho1, GR, Drho2);
                            answList := (answRef :: (!answList))))),
                      (T.DivergingEntry (I.id, answRef)))
                  else
                    (((function
                       | () ->
                           ((:=) ChildRef mkNode
                              ((!ChildRef), Dsigma, Drho1, GR, Drho2);
                            answList := (answRef :: (!answList))))),
                      (T.NewEntry answRef))
              | ((ChildRef, Drho2, asub)::nil, _) ->
                  insert (ChildRef, Drho2, GR)
              | ((ChildRef, Drho2, asub)::L, SCands) ->
                  (match insert (ChildRef, Drho2, GR) with
                   | (_, NewEntry answRef) -> checkCandidates (L, SCands)
                   | (f, RepeatedEntry (asub, answRef, status)) ->
                       (f, (T.RepeatedEntry (asub, answRef, status)))
                   | (f, DivergingEntry (asub, answRef)) ->
                       (f, (T.DivergingEntry (asub, answRef)))) in
            checkCandidates (VariantCand, SplitCand) in
      insert' ((!Nref), (D_u, nsub_u), GR)
    let rec answCheckVariant (s', answRef, O) =
      let rec member =
        function
        | ((D, sk), []) -> false__
        | ((D, sk), ((D1, s1), _)::S) ->
            if (equalSub (sk, s1)) && (equalCtx' (D, D1))
            then true__
            else member ((D, sk), S) in
      let (DEVars, sk) = A.abstractAnswSub s' in
      if member ((DEVars, sk), (T.solutions answRef))
      then T.repeated
      else (T.addSolution (((DEVars, sk), O), answRef); T.new__)
    let rec reset () =
      nctr := 1;
      Array.modify
        (function
         | (n, Tree) ->
             (n := 0;
              (!) ((:=) Tree) (makeTree ());
              answList := [];
              added := false__;
              (n, Tree))) indexArray
    let rec makeCtx =
      function
      | (n, I.Null, (DEVars : ctx)) -> n
      | (n, Decl (G, D), (DEVars : ctx)) ->
          (insertList ((n, D), DEVars); makeCtx ((n + 1), G, DEVars))
    let rec callCheck (a, DAVars, DEVars, G, U, eqn, status) =
      let (n, Tree) = Array.sub (indexArray, a) in
      let nsub_goal = S.new__ () in
      let DAEVars = compose (DEVars, DAVars) in
      let D = emptyCtx () in
      let n = I.ctxLength G in
      let _ = makeCtx ((n + 1), DAEVars, (D : ctx)) in
      let l = I.ctxLength DAEVars in
      let _ = S.insert nsub_goal (1, U) in
      let result =
        insert
          (Tree, (D, nsub_goal),
            ((l, (n + 1)), G, eqn, (emptyAnswer ()), (!TableParam.stageCtr),
              status)) in
      let esub = ctxToAVarSub (G, DAEVars, (I.Shift 0)) in
      let _ =
        if solveEqn' ((eqn, (shift (G, esub))), G)
        then ()
        else print " failed to solve eqn_query\n" in
      match result with
      | (sf, NewEntry answRef) ->
          (sf ();
           added := true__;
           if (!Global.chatter) >= 5 then print "\t -- Add goal \n" else ();
           T.NewEntry answRef)
      | (_, RepeatedEntry (((_, asub) as s), answRef, status)) ->
          (if (!Global.chatter) >= 5
           then print "\t -- Suspend goal\n"
           else ();
           T.RepeatedEntry ((esub, asub), answRef, status))
      | (sf, DivergingEntry answRef) ->
          (sf ();
           added := true__;
           if (!Global.chatter) >= 5
           then print "\t -- Add diverging goal\n"
           else ();
           T.DivergingEntry answRef)
    let rec insertIntoTree (a, DAVars, DEVars, G, U, eqn, answRef, status) =
      let (n, Tree) = Array.sub (indexArray, a) in
      let nsub_goal = S.new__ () in
      let DAEVars = compose (DEVars, DAVars) in
      let D = emptyCtx () in
      let n = I.ctxLength G in
      let _ = makeCtx ((n + 1), DAEVars, (D : ctx)) in
      let l = I.ctxLength DAEVars in
      let _ = S.insert nsub_goal (1, U) in
      let result =
        insert
          (Tree, (D, nsub_goal),
            ((l, (n + 1)), G, eqn, answRef, (!TableParam.stageCtr), status)) in
      match result with
      | (sf, NewEntry answRef) ->
          (added := true__;
           if (!Global.chatter) >= 5 then print "\t -- Add goal \n" else ();
           T.NewEntry answRef)
      | (_, RepeatedEntry (asub, answRef, status)) ->
          (if (!Global.chatter) >= 5
           then print "\t -- Suspend goal\n"
           else ();
           T.RepeatedEntry (asub, answRef, status))
      | (sf, DivergingEntry answRef) ->
          (sf ();
           added := true__;
           if (!Global.chatter) >= 5
           then print "\t -- Add diverging goal\n"
           else ();
           T.DivergingEntry answRef)
    let rec answCheck (s', answRef, O) = answCheckVariant (s', answRef, O)
    let rec updateTable () =
      let rec update arg__0 arg__1 =
        match (arg__0, arg__1) with
        | ([], Flag) -> Flag
        | (answRef::AList, Flag) ->
            let l = length (T.solutions answRef) in
            if (=) l T.lookup answRef
            then update AList Flag
            else (T.updateAnswLookup (l, answRef); update AList true__) in
      let Flag = update (!answList) false__ in
      let r = Flag || (!added) in added := false__; r
    (* index for normal variables *)
    (* index for bound variables *)
    (* depth of locally bound variables *)
    (* ------------------------------------------------------ *)
    (* Auxiliary functions *)
    (* solveEqn' ((VarDef, s), G) = bool

     if G'' |- VarDef and G   |- s : G''
       G   |- VarDef[s]
    then
      return true, if VarDefs are solvable
      false otherwise
      *)
    (* evar *)
    (* ------------------------------------------------------ *)
    (*  Variable b    : bound variable
     Variable n    : index variable
     linear term  U ::=  Root(c, S) | Lam (D, U) | Root(b, S)
     linear Spine S ::= p ; S | NIL
     indexed term t ::= Root(n, NIL) |  Root(c, S) | Lam (D, p) | Root(b, S)
     indexed spines S_i ::= t ; S_i | NIL
     Types   A
     Context G : context for bound variables (bvars)
     (type information is stored in the context)
        G ::= . | G, x : A
        Set of all index variables:  N

        linear terms are approximately well-typed in G:  G |- p
        after erasing all typing dependencies.


        Let s be a path in the substitution tree such that
        s1 o s2 o .... o sn = s,



        Let N1 ... Nn be the path from the root N1 to the leaf Nn,
        and si the substitution associated with node Ni.

       IMAGE(sn) = empty
       s1 o s2 o ... o sn = s and IMAGE(s) = empty
       i.e. index variables are only internally used and no
       index variable is left.

       A linear term U (and an indexed term t) can be decomposed into a term t' together with
       a sequenence of substitutions s1, s2, ..., sn such that s1 o s2 o .... o sn = s
       and the following holds:

       If    N  ; G |- t
       then  N' ; G |- t'
             N  ; G |- s : N' ; G
             N  ; G |- t'[s]     and t'[s] = t

      if we have a linear term then N will be empty, but the same holds.

      In addition:
      all expressions in the index are closed and linear, i.e.
      an expression is first linearized before it is inserted into the index
      (this makes retrieving all axpressions from the index which unify with
      a given expression simpler, because we can omit the occurs check)

   *)
    (* ---------------------------------------------------------------*)
    (* nctr = |D| =  #index variables *)
    (* We require order of both eqn must be the same Sun Sep  8 20:37:48 2002 -bp *)
    (* s = s' = I.id *)
    (* in general, we need to carry around and build up a substitution *)
    (* ---------------------------------------------------------------*)
    (* ---------------------------------------------------------------*)
    (* most specific linear common generalization *)
    (* compatible (T, U) = (T', rho_u, rho_t) opt
    if T is an indexed term
       U is a linear term
       U and T share at least the top function symbol
   then
       T'[rho_u] = U and T'[rho_t] = T
   *)
    (* globally bound variable *)
    (* k, k' refer to the existential *)
    (* they refer to the same existential variable *)
    (* this is unecessary -- since existential variables have the same type
                                and need to be fully applied in order, S1 = S2 *)
    (* variant checking only *)
    (* locally bound variables *)
    (* by invariant A1 = A2 *)
    (* U = EVar, EClo -- can't happen -- Sun Oct 20 13:41:25 2002 -bp *)
    (* ---------------------------------------------------------------*)
    (* compatibleSub(nsub_t, nsub_u) = (sigma, rho_t, rho_u) opt

   if DOM(nsub_t) <= DOM(nsub_u)
      CODOM(nsub_t) : index terms
      CODOM(nsub_u) : linear terms
        G_u, Glocal_u |- nsub_u
    N ; G_t, Glocal_t |- nsub_t
   then
     nsub_t = sigma o rho_t
     nsub_e = sigma o rho_u

    Glocal_e ~ Glocal_t  (have "approximately" the same type)

   *)
    (* by invariant rho_t = empty, since nsub_t <= nsub_u *)
    (* note by invariant Glocal_e ~ Glocal_t *)
    (* here Glocal_t will be only approximately correct! *)
    (* perfect match under asub and rho_t = nsub_t
           sigma = rho_t and sigma o asub = rho_u *)
    (* split -- asub is unchanged *)
    (* Dsigma |~ sigma, D_r1 |~ rho_t, D_r1 |~ rho_u *)
    (* ---------------------------------------------------------------------- *)
    (* ---------------------------------------------------------------------- *)
    (* we may not need to check that the DAVars are the same *)
    (* ---------------------------------------------------------------------- *)
    (* eqTerm (t2, (t, rho1)) = bool
    returns true iff t2 = t[rho1]
  t2 is a linear term which may not contain any nvars!
  t may contain nvars
 *)
    (* ---------------------------------------------------------------------- *)
    (* Insert via variant checking *)
    (* insert' (N, (D, nsub), GR) = (f, callCheckResult)

     invariant:

       N is a substitution tree
       nsub is a normal substitution
       D contains all the existential variables in nsub
       GR = (G : bound variable context,
             eqn: residual equations
             answRef : ptr to answer list

     if there exists a path p in N s.t. p ~ nsub
      then
       f is the identity, and callCheckResult = RepeatedEntry(_,_,answRef)
     otherwise (f is a function which destructively updates N
                and once executed, will add a path p ~ nsub to N,
                 callCheckResult = NewEntry (answRef)

  *)
    (* need to compare D and D_u *)
    (* compatible path -- but different ctx! *)
    (* ctx are diverging --- force suspension *)
    (* compatible path (variant) -- ctx are different *)
    (* compatible path -- SAME ctx *)
    (* no child is compatible with nsub_u *)
    (* split an existing node *)
    (* substree divering -- splitting node *)
    (* split existing node *)
    (* unique "perfect" candidate (left) *)
    (* there are several "perfect" candidates *)
    (* ---------------------------------------------------------------------- *)
    (* answer check and insert

     Invariant:
        D |- Pi G.U
          |- (Pi G.U)[s]
       .  |- s : D
       {{K}} are all the free variables in s
        D_k is the linear context of all free variables in {{K}}
        D_k |- s_k : D  and eqn
        D_k |- (Pi G.U)[s_k] and eqn

      answerCheck (G, s, answRef, 0) = repeated
         if (D_k, s_k, eqn)  already occurs in answRef
      answerCheck (G,s, answRef, O) = new
         if (D_k, s_k, eqn) did not occur in answRef
         Sideeffect: update answer list for U
     *)
    (* ---------------------------------------------------------------------- *)
    (* callCheck (a, DA, DE, G, U eqn) = callCheckResult

       invariant:
       DA, DE, G |- U
       a is the type family of U

       if U is not already in the index, then it is inserted.
       otherwise we return
             a pointer answRef to the answer list.
             (for variant checking, asub = I.id, and varDefs = NONE)
     *)
    (* insertIntoSTre (a, DA, DE, G, U eqn) = Succeeds

       invariant:
       DA, DE, G |- U
       a is the type family of U

       U is not already in the index, then it is inserted.
       otherwise we return
             a pointer answRef to the answer list.
             (for variant checking, asub = I.id, and varDefs = NONE)
     *)
    (* no new solutions were added in the previous stage *)
    (* new solutions were added *)
    let reset = reset
    let callCheck =
      function
      | (DAVars, DEVars, G, U, eqn, status) ->
          callCheck
            ((cidFromHead (I.targetHead U)), DAVars, DEVars, G, U, eqn,
              status)
    let insertIntoTree =
      function
      | (DAVars, DEVars, G, U, eqn, answRef, status) ->
          insertIntoTree
            ((cidFromHead (I.targetHead U)), DAVars, DEVars, G, U, eqn,
              answRef, status)
    let answerCheck = answCheck
    let updateTable = updateTable
    let tableSize = function | () -> length (!answList)
    (* memberCtx ((G,V), G', n) = bool

       if G |- V and |- G' ctx
          exists a V' in G s.t. V = V'[^n]
       then return true
         otherwise false
     *)
    let rec memberCtx ((G, V), G') =
      let rec memberCtx' =
        function
        | ((G, V), I.Null, n) -> NONE
        | ((G, V), Decl (G', (Dec (_, V') as D')), n) ->
            if Conv.conv ((V, I.id), (V', (I.Shift n)))
            then SOME D'
            else memberCtx' ((G, V), G', (n + 1)) in
      memberCtx' ((G, V), G', 1)
  end ;;
