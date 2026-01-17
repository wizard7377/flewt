
module MemoTableInst(MemoTableInst:sig
                                     module Conv : CONV
                                     module Whnf : WHNF
                                     module Match : MATCH
                                     module Assign : ASSIGN
                                     module AbstractTabled : ABSTRACTTABLED
                                     module Print :
                                     ((PRINT)(* Linear Substitution Tree indexing *)
                                     (* Linearity: Any variables occurring inside the substitution tree are linear *)
                                     (* Any term we insert into the substitution tree is in normalform ! *)
                                     (* Instance Checking *)
                                     (* Author: Brigitte Pientka *)
                                     (*! structure IntSyn' : INTSYN !*)
                                     (*! structure CompSyn' : COMPSYN !*)
                                     (*! sharing CompSyn'.IntSyn = IntSyn' !*)
                                     (*! sharing Conv.IntSyn = IntSyn' !*)
                                     (*! sharing Whnf.IntSyn = IntSyn' !*)
                                     (*! structure RBSet : RBSET !*)
                                     (*! structure TableParam : TABLEPARAM !*)
                                     (*! sharing TableParam.IntSyn = IntSyn' !*)
                                     (*! sharing TableParam.CompSyn = CompSyn' !*)
                                     (*! sharing TableParam.RBSet = RBSet !*)
                                     (*! sharing AbstractTabled.IntSyn = IntSyn' !*))
                                   end) : MEMOTABLE =
  struct
    module AbstractTabled =
      ((AbstractTabled)(*! sharing Print.IntSyn = IntSyn'!*)
      (*! structure IntSyn = IntSyn' !*)(*! structure CompSyn = CompSyn' !*))
    type nonrec normalSubsts =
      (((int)(* property: linear *)(* normalSubsts: key = int = nvar  (key, (depth, U))

   example:  \x. f( i1, a)   then i1 = (1, X) = X[x/x]

   *)
        (* Linear substitution tree for linear terms *)
        (* ---------------------------------------------------------------------- *)
        (*! structure TableParam = TableParam !*)) *
        ((IntSyn.__Exp)(* local depth *))) RBSet.ordSet
    type nonrec exSubsts = IntSyn.__Front RBSet.ordSet
    let (nid : unit -> normalSubsts) = RBSet.new__
    let (asid : unit -> exSubsts) = RBSet.new__
    let aid = TableParam.aid
    let rec isId s = RBSet.isEmpty s
    type nonrec ctx =
      (((int)(* Context for existential variable *)(* ---------------------------------------------------------------------- *))
        * IntSyn.__Dec) list ref
    let rec emptyCtx
      ((())(* functions for handling context for existential variables *))
      = (ref [] : ctx)
    let rec copy (L) = (ref (!L) : ctx)
    let rec delete
      (((x)(* destructively updates L *)), (L : ctx)) =
      let del =
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
      let memb =
        function
        | (x, []) -> NONE
        | (x, ((y, (Dec (n, U) as E))::L as H)) ->
            if x = y then SOME (y, E) else memb (x, L)
        | (x, ((y, (ADec (n, d) as E))::L as H)) ->
            if x = y then SOME (y, E) else memb (x, L) in
      memb (x, (!L))
    let rec insertList (E, L) = L := (E :: (!L))
    type __Tree =
      | Leaf of
      ((((ctx)(* It is only possible to distribute the evar-ctx because
     all evars occur exactly once, i.e. they are linear.
     This allows us to maintain invariant, that every occurrence of an evar is
     defined in its evar-ctx
  *)
      (* Substitution Tree *)(* ---------------------------------------------------------------------- *))
      * normalSubsts) *
      ((((int * ((int)(* #EVar *))))(* #g *))
      * ctx * ((IntSyn.dctx)(* D *)) *
      ((TableParam.__ResEqn)(* g *)) * TableParam.answer *
      int * TableParam.__Status) list ref) 
      | Node of ((ctx * normalSubsts) * __Tree ref list) 
    let rec makeTree () = ref (Node (((emptyCtx ()), (nid ())), []))
    let rec noChildren (C) = C = []
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
    let ((indexArray)(* Index array

   All type families have their own substitution tree and all substitution trees
   are stored in an array [a1,...,an]   where ai is a substitution tree for type family ai
   *))
      =
      Array.tabulate
        (Global.maxCid, (function | i -> ((ref 0), (makeTree ()))))
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
    let added = ref false__
    type nonrec nvar = int
    type nonrec bvar = int
    type nonrec bdepth = int
    let rec expToS (g, U) = try Print.expToString (g, U) with | _ -> " <_ >"
    let rec printSub =
      function
      | (g, Shift n) -> print (((^) "I.Shift " Int.toString n) ^ "\n")
      | (g, Dot (Idx n, s)) ->
          (print (((^) "Idx " Int.toString n) ^ " . "); printSub (g, s))
      | (g, Dot (Exp (EVar (ref (SOME (U)), _, _, _) as X), s)) ->
          (print (((^) "Exp ( EVar " expToS (g, X)) ^ ")."); printSub (g, s))
      | (g, Dot (Exp (EVar (_, _, _, _) as X), s)) ->
          (print (((^) "Exp ( EVar  " expToS (g, X)) ^ ")."); printSub (g, s))
      | (g, Dot (Exp (AVar _), s)) ->
          (print "Exp (AVar _ ). "; printSub (g, s))
      | (g, Dot (Exp (EClo (AVar (ref (SOME (U))), s')), s)) ->
          (print (((^) "Exp (AVar " expToS (g, (I.EClo (U, s')))) ^ ").");
           printSub (g, s))
      | (g, Dot (Exp (EClo (EVar (ref (SOME (U)), _, _, _), s') as X), s)) ->
          (print (((^) "Exp (EVarClo " expToS (g, (I.EClo (U, s')))) ^ ") ");
           printSub (g, s))
      | (g, Dot (Exp (EClo (U, s') as X), s)) ->
          (print
             (((^) "Exp (EClo " expToS (g, (Whnf.normalize (U, s')))) ^ ") ");
           printSub (g, s))
      | (g, Dot (Exp (E), s)) ->
          (print (((^) "Exp ( " expToS (g, E)) ^ " ). "); printSub (g, s))
      | (g, Dot (I.Undef, s)) -> (print "Undef . "; printSub (g, s))
    let rec normalizeSub =
      function
      | Shift n -> I.Shift n
      | Dot (Exp (EClo (AVar (ref (SOME (U))), s')), s) ->
          I.Dot ((I.Exp (Whnf.normalize (U, s'))), (normalizeSub s))
      | Dot (Exp (EClo (EVar (ref (SOME (U)), _, _, _), s')), s) ->
          I.Dot ((I.Exp (Whnf.normalize (U, s'))), (normalizeSub s))
      | Dot (Exp (U), s) ->
          I.Dot ((I.Exp (Whnf.normalize (U, I.id))), (normalizeSub s))
      | Dot (Idx n, s) -> I.Dot ((I.Idx n), (normalizeSub s))
    let rec etaSpine =
      function
      | (I.Nil, n) -> n = 0
      | (App (Root (BVar k, I.Nil), S), n) ->
          (k = n) && (etaSpine (S, (n - 1)))
      | (App (A, S), n) -> false__
    let rec cidFromHead = function | Const c -> c | Def c -> c
    let rec dotn =
      function | (0, s) -> s | (i, s) -> dotn ((i - 1), (I.dot1 s))
    let rec raiseType =
      function
      | (I.Null, V) -> V
      | (Decl (g, D), V) -> raiseType (g, (I.Lam (D, V)))
    let rec compose =
      function
      | (IntSyn.Null, g) -> g
      | (Decl (g', D), g) -> IntSyn.Decl ((compose (g', g)), D)
    let rec shift =
      function
      | (IntSyn.Null, s) -> s
      | (Decl (g, D), s) -> I.dot1 (shift (g, s))
    let rec ctxToEVarSub =
      function
      | (I.Null, s) -> s
      | (Decl (g, Dec (_, A)), s) ->
          let X = I.newEVar (I.Null, A) in
          I.Dot ((I.Exp X), (ctxToEVarSub (g, s)))
    let rec lowerEVar' =
      function
      | (X, g, (Pi ((D', _), V'), s')) ->
          let D'' = I.decSub (D', s') in
          let (X', U) =
            lowerEVar' (X, (I.Decl (g, D'')), (Whnf.whnf (V', (I.dot1 s')))) in
          (X', (I.Lam (D'', U)))
      | (X, g, Vs') -> let X' = X in (X', X')
    let rec lowerEVar1 =
      function
      | (X, EVar (r, g, _, _), ((Pi _ as V), s)) ->
          let (X', U) = lowerEVar' (X, g, (V, s)) in
          I.EVar ((ref (SOME U)), I.Null, V, (ref nil))
      | (_, X, _) -> X
    let rec lowerEVar =
      function
      | (E, (EVar (r, g, V, ref nil) as X)) ->
          lowerEVar1 (E, X, (Whnf.whnf (V, I.id)))
      | (E, EVar _) ->
          raise
            (Error
               "abstraction : LowerEVars: Typing ambiguous -- constraint of functional type cannot be simplified")
    let rec ctxToAVarSub =
      function
      | (g', I.Null, s) -> s
      | (g', Decl (D, Dec (_, A)), s) ->
          let EVar (r, _, _, cnstr) as E = I.newEVar (I.Null, A) in
          I.Dot ((I.Exp E), (ctxToAVarSub (g', D, s)))
      | (g', Decl (D, ADec (_, d)), s) ->
          let X = I.newAVar () in
          I.Dot
            ((I.Exp (I.EClo (X, (I.Shift (~ d))))),
              (ctxToAVarSub (g', D, s)))
    let rec assign =
      function
      | (d, (Dec (n, V) as Dec1), (Root (BVar k, s1) as E1), U, asub) ->
          let EVar (r, _, _, cnstr) as E = I.newEVar (I.Null, V) in
          let X =
            lowerEVar1
              (E, (I.EVar (r, I.Null, V, cnstr)), (Whnf.whnf (V, I.id))) in
          let _ = (:=) r SOME U in S.insert asub ((k - d), (I.Exp X))
      | (d, (ADec (n, d') as Dec1), (Root (BVar k, s1) as E1), U, asub) ->
          let AVar r as A = I.newAVar () in
          let _ = (:=) r SOME U in
          let Us = Whnf.whnf (U, (I.Shift (~ d'))) in
          S.insert asub ((k - d), (I.Exp (I.EClo (A, (I.Shift (~ d'))))))
    let rec assignExp =
      function
      | (fasub, (((r, passed) as ctxTotal), d), (D1, (Root (H1, s1) as u1)),
         (D2, (Root (H2, s2) as u2))) ->
          (match (H1, H2) with
           | (Const c1, Const c2) ->
               if c1 = c2
               then assignSpine (fasub, (ctxTotal, d), (D1, s1), (D2, s2))
               else raise (Assignment "Constant clash")
           | (Def c1, Def c2) ->
               if c1 = c2
               then assignSpine (fasub, (ctxTotal, d), (D1, s1), (D2, s2))
               else
                 (let u1' = Whnf.normalize (Whnf.expandDef (u1, I.id)) in
                  let u2' = Whnf.normalize (Whnf.expandDef (u2, I.id)) in
                  assignExp (fasub, (ctxTotal, d), (D1, u1'), (D2, u2')))
           | (Def c1, _) ->
               let u1' = Whnf.normalize (Whnf.expandDef (u1, I.id)) in
               assignExp (fasub, (ctxTotal, d), (D1, u1'), (D2, u2))
           | (_, Def c2) ->
               let u2' = Whnf.normalize (Whnf.expandDef (u2, I.id)) in
               assignExp (fasub, (ctxTotal, d), (D1, u1), (D2, u2'))
           | (BVar k1, BVar k2) ->
               if k1 <= (r + d)
               then
                 (if k2 <= (r + d)
                  then
                    (if k2 = k1
                     then fasub
                     else raise (Assignment "BVar clash"))
                  else raise (Assignment "BVar - EVar clash"))
               else
                 (match member (((k1 - d) + passed), D1) with
                  | NONE -> raise (Assignment "EVar nonexistent")
                  | SOME (x, Dec) ->
                      if k2 <= (r + d)
                      then raise (Assignment "EVar - BVar clash")
                      else
                        if k2 = k1
                        then
                          (function
                           | asub ->
                               (fasub asub; assign (d, Dec, u1, u2, asub)))
                        else
                          raise
                            (Assignment
                               "EVars are different -- outside of the allowed fragment"))
           | (Skonst c1, Skonst c2) ->
               if c1 = c2
               then assignSpine (fasub, (ctxTotal, d), (D1, s1), (D2, s2))
               else raise (Assignment "Skolem constant clash")
           | _ -> raise (Assignment "Head mismatch "))
      | (fasub, (ctxTotal, d), (D1, Lam (Dec1, u1)), (D2, Lam (Dec2, u2))) ->
          assignExp (fasub, (ctxTotal, (d + 1)), (D1, u1), (D2, u2))
      | (fasub, (ctxTotal, d), (D1, Pi (((Dec (_, V1) as Dec1), _), u1)),
         (D2, Pi (((Dec (_, V2) as Dec2), _), u2))) ->
          let fasub' = assignExp (fasub, (ctxTotal, d), (D1, V1), (D2, V2)) in
          assignExp (fasub', (ctxTotal, (d + 1)), (D1, u1), (D2, u2))
      | (fasub, (ctxTotal, d), (D1, EClo (U, (Shift 0 as s'))), (D2, u2)) ->
          assignExp (fasub, (ctxTotal, d), (D1, U), (D2, u2))
      | (fasub, (ctxTotal, d), (D1, u1), (D2, EClo (U, (Shift 0 as s)))) ->
          assignExp (fasub, (ctxTotal, d), (D1, u1), (D2, U))
    let rec assignSpine =
      function
      | (fasub, (ctxTotal, d), (D1, I.Nil), (D2, I.Nil)) -> fasub
      | (fasub, (ctxTotal, d), (D1, App (u1, s1)), (D2, App (u2, s2))) ->
          let fasub' = assignExp (fasub, (ctxTotal, d), (D1, u1), (D2, u2)) in
          assignSpine (fasub', (ctxTotal, d), (D1, s1), (D2, s2))
    let rec assignCtx =
      function
      | (fasub, ctxTotal, (D1, I.Null), (D2, I.Null)) -> fasub
      | (fasub, ((r, passed) as ctxTotal), (D1, Decl (G1, Dec (_, V1))),
         (D2, Decl (G2, Dec (_, V2)))) ->
          let fasub' =
            assignExp
              (fasub, (((r - 1), (passed + 1)), 0), (D1, V1), (D2, V2)) in
          assignCtx (fasub', ((r - 1), (passed + 1)), (D1, G1), (D2, G2))
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
      | (Decl (g, (Dec (_, A) as D)), s, Decl (g', (Dec (_, A') as D')), s')
          ->
          (Conv.convDec ((D, s), (D', s'))) &&
            (equalCtx (g, (I.dot1 s), g', (I.dot1 s')))
      | (_, s, _, s') -> false__
    let rec equalEqn =
      function
      | (T.Trivial, T.Trivial) -> true__
      | (Unify (g, X, N, eqn), Unify (g', X', N', eqn')) ->
          (equalCtx (g, I.id, g', I.id)) &&
            ((Conv.conv ((X, I.id), (X', I.id))) &&
               ((Conv.conv ((N, I.id), (N', I.id))) && (equalEqn (eqn, eqn'))))
      | (_, _) -> false__
    let rec equalEqn' =
      function
      | (d, (D, T.Trivial), (D', T.Trivial), asub) -> true__
      | (d, (D, Unify (g, (Root (BVar k, S) as X), N, eqn)),
         (D', Unify (g', X', N', eqn')), asub) ->
          if
            (equalCtx (g, I.id, g', I.id)) &&
              ((Conv.conv ((X, I.id), (X', I.id))) &&
                 (Conv.conv ((N, I.id), (N', I.id))))
          then
            let d' = (+) d I.ctxLength g' in
            (if (k - d') > 0
             then
               (match member ((k - d'), D') with
                | NONE -> ()
                | SOME (x, Dec) ->
                    (match RBSet.lookup asub (k - d') with
                     | NONE ->
                         (delete (x, D');
                          S.insert asub ((k - d'), (I.Idx (k - d'))))
                     | SOME _ -> ()))
             else
               (print "Impossible -- Found BVar instead of EVar\n";
                raise (Error "Impossibe -- Found BVar instead of EVar "));
             equalEqn' (d, (D, eqn), (D', eqn'), asub))
          else false__
      | (d, _, _, asub) -> false__
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
    let rec equalCtx' =
      function
      | (I.Null, I.Null) -> true__
      | (Decl (Dk, Dec (_, A)), Decl (D1, Dec (_, A1))) ->
          (Conv.conv ((A, I.id), (A1, I.id))) && (equalCtx' (Dk, D1))
      | (Decl (Dk, ADec (_, d')), Decl (D1, ADec (_, d))) ->
          (d = d') && (equalCtx' (Dk, D1))
      | (_, _) -> false__
    let rec instanceCtx (asub, (D1, G1), (D2, G2)) =
      let d1 = I.ctxLength G1 in
      let d2 = I.ctxLength G2 in
      if d1 = d2
      then
        try
          let fasub =
            assignCtx ((function | asub -> ()), (d1, 0), (D1, G1), (D2, G2)) in
          fasub asub; true__
        with | Assignment msg -> false__
      else false__
    let rec collectEVar (D, nsub) =
      let D' = emptyCtx () in
      let collectExp =
        function
        | (d, D', D, Lam (_, U)) -> collectExp ((d + 1), D', D, U)
        | (d, D', D, Root (Const c, S)) -> collectSpine (d, D', D, S)
        | (d, D', D, Root (BVar k, S)) ->
            (match member ((k - d), D) with
             | NONE -> collectSpine (d, D', D, S)
             | SOME (x, Dec) ->
                 (delete ((x - d), D); insertList (((x - d), Dec), D')))
        | (d, D', D, (Root (Def k, S) as U)) ->
            let U' = Whnf.normalize (Whnf.expandDef (U, I.id)) in
            collectExp (d, D', D, U')
      and collectSpine =
        function
        | (d, D', D, I.Nil) -> ()
        | (d, D', D, App (U, S)) ->
            (collectExp (d, D', D, U); collectSpine (d, D', D, S)) in
      S.forall nsub (function | (nv, (du, U)) -> collectExp (0, D', D, U));
      (D', D)
    let rec convAssSub' (g, idx_k, D, asub, d, ((evars, avars) as evarsl)) =
      match RBSet.lookup asub d with
      | NONE ->
          (match member (d, D) with
           | NONE -> IntSyn.Shift (evars + avars)
           | SOME (x, Dec (n, V)) ->
               let s = convAssSub' (g, (idx_k + 1), D, asub, (d + 1), evarsl) in
               let EVar (r, _, _, cnstr) as E = I.newEVar (I.Null, V) in
               I.Dot ((I.Exp (I.EClo (E, (I.Shift (evars + avars))))), s)
           | SOME (x, ADec (n, V)) ->
               (print "convAssSub' -- Found an uninstantiated AVAR\n";
                raise (Error "Unassigned AVar -- should never happen\n")))
      | SOME (Exp (E) as F) ->
          let E' = Whnf.normalize (E, I.id) in
          I.Dot
            ((I.Exp E'),
              (convAssSub' (g, (idx_k + 1), D, asub, (d + 1), evarsl)))
    let rec convAssSub (g, asub, Glength, D', evarsl) =
      convAssSub' (g, 0, D', asub, Glength, evarsl)
    let rec isExists (d, BVar k, D) = member ((k - d), D)
    let rec instance ((D_t, (dt, T)), (D_u, (du, U)), rho_u, ac) =
      let instRoot =
        function
        | (depth, (Root ((Const k as H1), s1) as T),
           (Root (Const k', s2) as U), ac) ->
            if k = k'
            then instSpine (depth, s1, s2, ac)
            else raise (Instance "Constant mismatch\n")
        | (depth, (Root ((Def k as H1), s1) as T), (Root (Def k', s2) as U),
           ac) ->
            if k = k'
            then instSpine (depth, s1, s2, ac)
            else
              (let T' = Whnf.normalize (Whnf.expandDef (T, I.id)) in
               let U' = Whnf.normalize (Whnf.expandDef (U, I.id)) in
               instExp (depth, T', U', ac))
        | (depth, (Root ((Def k as H1), s1) as T), (Root (H2, s2) as U), ac)
            ->
            let T' = Whnf.normalize (Whnf.expandDef (T, I.id)) in
            instExp (depth, T', U, ac)
        | (d, (Root ((BVar k as H1), s1) as T), (Root (BVar k', s2) as U),
           ac) ->
            if (k > d) && (k' > d)
            then
              let k1 = k - d in
              let k2 = k' - d in
              (match ((member (k1, D_t)), (member (k2, D_u))) with
               | (NONE, NONE) ->
                   if k1 = k2
                   then instSpine (d, s1, s2, ac)
                   else raise (Instance "Bound variable mismatch\n")
               | (SOME (x, Dec1), SOME (x', Dec2)) ->
                   if (k1 = k2) && (equalDec (Dec1, Dec2))
                   then
                     let ac' = instSpine (d, s1, s2, ac) in
                     let ac'' =
                       function
                       | asub -> (ac' asub; assign (d, Dec1, T, U, asub)) in
                     ac''
                   else
                     (function
                      | asub -> (ac asub; assign (d, Dec1, T, U, asub)))
               | (SOME (x, (ADec (n, d') as Dec1)), NONE) ->
                   (function
                    | asub -> (ac asub; assign (d, Dec1, T, U, asub)))
               | (SOME (x, Dec1), NONE) ->
                   (function
                    | asub -> (ac asub; assign (d, Dec1, T, U, asub)))
               | (_, _) -> raise (Instance "Impossible\n"))
            else raise (Instance "Bound variable mismatch\n")
        | (d, (Root ((BVar k as H1), s1) as T), (Root (Const k', s2) as U),
           ac) ->
            (match isExists (d, (I.BVar k), D_t) with
             | NONE -> raise (Instance "Impossible\n")
             | SOME (x, (ADec (_, _) as Dec1)) ->
                 (function | asub -> (ac asub; assign (d, Dec1, T, U, asub)))
             | SOME (x, Dec1) ->
                 (function | asub -> (ac asub; assign (d, Dec1, T, U, asub))))
        | (d, (Root ((BVar k as H1), s1) as T), (Root (Def k', s2) as U), ac)
            ->
            (match isExists (d, (I.BVar k), D_t) with
             | NONE -> raise (Instance "Impossible\n")
             | SOME (x, (ADec (_, _) as Dec1)) ->
                 (function | asub -> (ac asub; assign (d, Dec1, T, U, asub)))
             | SOME (x, Dec1) ->
                 (function | asub -> (ac asub; assign (d, Dec1, T, U, asub))))
        | (depth, (Root (H1, s1) as T), (Root (Def k', s2) as U), ac) ->
            let U' = Whnf.normalize (Whnf.expandDef (U, I.id)) in
            instExp (depth, T, U', ac)
        | (d, (Root (H1, s1) as T), (Root (H2, s2) as U), ac) ->
            raise (Instance "Other Cases impossible\n")
      and instExp =
        function
        | (d, (NVar n as T), (Root (H, S) as U), ac) ->
            (S.insert rho_u (n, (d, U)); ac)
        | (d, (Root (H1, s1) as T), (Root (H2, s2) as U), ac) ->
            instRoot (d, (I.Root (H1, s1)), (I.Root (H2, s2)), ac)
        | (d, Lam ((Dec (_, A1) as D1), T1), Lam ((Dec (_, A2) as D2), u2),
           ac) -> instExp ((d + 1), T1, u2, ac)
        | (d, T, U, ac) ->
            (print "instExp -- falls through?\n";
             raise (Instance "Impossible\n"))
      and instSpine =
        function
        | (d, I.Nil, I.Nil, ac) -> ac
        | (d, App (T, s1), App (U, s2), ac) ->
            let ac' = instExp (d, T, U, ac) in
            let ac'' = instSpine (d, s1, s2, ac') in ac''
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
      (:=) ac instExp (dt, T, U, (!ac))
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
    let rec compatible' ((D_t, (dt, T)), (D_u, (du, U)), Ds, rho_t, rho_u) =
      let genNVar ((rho_t, T), (rho_u, U)) =
        S.insert rho_t (((!nctr) + 1), T);
        S.insert rho_u (((!nctr) + 1), U);
        newNVar () in
      let genRoot =
        function
        | (d, (Root ((Const k as H1), s1) as T), (Root (Const k', s2) as U))
            ->
            if k = k'
            then let S' = genSpine (d, s1, s2) in I.Root (H1, S')
            else genNVar ((rho_t, (d, T)), (rho_u, (d, U)))
        | (d, (Root ((Def k as H1), s1) as T), (Root (Def k', s2) as U)) ->
            if k = k'
            then let S' = genSpine (d, s1, s2) in I.Root (H1, S')
            else genNVar ((rho_t, (d, T)), (rho_u, (d, U)))
        | (d, (Root ((BVar k as H1), s1) as T), (Root (BVar k', s2) as U)) ->
            if (k > d) && (k' > d)
            then
              let k1 = k - d in
              let k2 = k' - d in
              (match ((member (k1, D_t)), (member (k2, D_u))) with
               | (NONE, NONE) ->
                   if k1 = k2
                   then
                     (try let S' = genSpine (d, s1, s2) in I.Root (H1, S')
                      with
                      | DifferentSpine ->
                          genNVar ((rho_t, (d, T)), (rho_u, (d, U))))
                   else genNVar ((rho_t, (d, T)), (rho_u, (d, U)))
               | (SOME (x, Dec1), SOME (x', Dec2)) ->
                   if (k1 = k2) && (equalDec (Dec1, Dec2))
                   then
                     let S' = genSpine (d, s1, s2) in
                     (delete (x, D_t);
                      delete (x', D_u);
                      insertList ((x, Dec1), Ds);
                      I.Root (H1, S'))
                   else genNVar ((rho_t, (d, T)), (rho_u, (d, U)))
               | (_, _) -> genNVar ((rho_t, (d, T)), (rho_u, (d, U))))
            else
              if k = k'
              then
                (try let S' = genSpine (d, s1, s2) in I.Root (H1, S')
                 with
                 | DifferentSpines ->
                     genNVar ((rho_t, (d, T)), (rho_u, (d, U))))
              else genNVar ((rho_t, (d, T)), (rho_u, (d, U)))
        | (d, (Root ((BVar k as H1), s1) as T), (Root (Const k', s2) as U))
            -> genNVar ((rho_t, (d, T)), (rho_u, (d, U)))
        | (d, (Root ((BVar k as H1), s1) as T), (Root (Def k', s2) as U)) ->
            genNVar ((rho_t, (d, T)), (rho_u, (d, U)))
        | (d, (Root (H1, s1) as T), (Root (H2, s2) as U)) ->
            genNVar ((rho_t, (d, T)), (rho_u, (d, U)))
      and genExp =
        function
        | (d, (NVar n as T), (Root (H, S) as U)) ->
            (S.insert rho_u (n, (d, U)); T)
        | (d, (Root (H1, s1) as T), (Root (H2, s2) as U)) ->
            genRoot (d, (I.Root (H1, s1)), (I.Root (H2, s2)))
        | (d, Lam ((Dec (_, A1) as D1), T1), Lam ((Dec (_, A2) as D2), u2))
            -> let E = genExp ((d + 1), T1, u2) in I.Lam (D1, E)
        | (d, T, U) ->
            (print "genExp -- falls through?\n";
             genNVar ((rho_t, (d, T)), (rho_u, (d, U))))
      and genSpine =
        function
        | (d, I.Nil, I.Nil) -> I.Nil
        | (d, App (T, s1), App (U, s2)) ->
            let E = genExp (d, T, U) in
            let S' = genSpine (d, s1, s2) in I.App (E, S')
        | (d, I.Nil, App (_, _)) -> raise DifferentSpines
        | (d, App (_, _), I.Nil) -> raise DifferentSpines
        | (d, SClo (_, _), _) -> raise DifferentSpines
        | (d, _, SClo (_, _)) -> raise DifferentSpines in
      Variant (dt, (genExp (dt, T, U)))
    let rec compatible =
      function
      | ((D_t, ((d1, Root (H1, s1)) as T)),
         (D_u, ((d2, Root (H2, s2)) as U)), Ds, rho_t, rho_u) ->
          if compHeads ((D_t, H1), (D_u, H2))
          then compatible' ((D_t, T), (D_u, U), Ds, rho_t, rho_u)
          else NotCompatible
      | ((D_t, T), (D_u, U), Ds, rho_t, rho_u) ->
          compatible' ((D_t, T), (D_u, U), Ds, rho_t, rho_u)
    let rec compatibleCtx =
      function
      | (asub, (Dsq, Gsq, eqn_sq), []) -> NONE
      | (asub, (Dsq, Gsq, eqn_sq),
         (_, Delta', g', eqn', answRef', _, status')::GRlist) ->
          if instanceCtx (asub, (Dsq, Gsq), (Delta', g'))
          then SOME ((Delta', g', eqn'), answRef', status')
          else compatibleCtx (asub, (Dsq, Gsq, eqn_sq), GRlist)
    let rec instanceSub ((D_t, nsub_t), (Dsq, squery), asub) =
      let rho_u = nid () in
      let D_r2 = copy Dsq in
      let ac = ref (function | (asub : exSubsts) -> ()) in
      try
        S.forall squery
          (function
           | (nv, (du, U)) ->
               (match S.lookup nsub_t nv with
                | SOME (dt, T) ->
                    instance ((D_t, (dt, T)), (D_r2, (du, U)), rho_u, ac)
                | NONE -> S.insert rho_u (nv, (du, U))));
        (!) ac asub;
        InstanceSub (asub, (D_r2, rho_u))
      with | Instance msg -> NoCompatibleSub
    let rec instChild =
      function
      | ((Leaf ((D_t, nsub_t), GList) as N), (D_sq, sq), asub) ->
          instanceSub ((D_t, nsub_t), (D_sq, sq), asub)
      | ((Node ((D_t, nsub_t), Children') as N), (D_sq, sq), asub) ->
          instanceSub ((D_t, nsub_t), (D_sq, sq), asub)
    let rec findAllInst (G_r, children, Ds, asub) =
      let findAllCands =
        function
        | (G_r, nil, (Dsq, sub_u), asub, IList) -> IList
        | (G_r, x::L, (Dsq, sub_u), asub, IList) ->
            let asub' = S.copy asub in
            (match instChild ((!x), (Dsq, sub_u), asub) with
             | NoCompatibleSub ->
                 findAllCands (G_r, L, (Dsq, sub_u), asub', IList)
             | InstanceSub (asub, Drho2) ->
                 findAllCands
                   (G_r, L, (Dsq, sub_u), asub', ((x, Drho2, asub) :: IList))) in
      findAllCands (G_r, children, Ds, asub, nil)
    let rec solveEqn =
      function
      | ((T.Trivial, s), g) -> true__
      | ((Unify (g', e1, N, eqns), s), g) ->
          let g'' = compose (g', g) in
          let s' = shift (g'', s) in
          (Assign.unifiable (g'', (N, s'), (e1, s'))) &&
            (solveEqn ((eqns, s), g))
    let rec solveEqn' =
      function
      | ((T.Trivial, s), g) -> true__
      | ((Unify (g', e1, N, eqns), s), g) ->
          let g'' = compose (g', g) in
          let s' = shift (g', s) in
          (Assign.unifiable (g'', (N, s'), (e1, s'))) &&
            (solveEqn' ((eqns, s), g))
    let rec solveEqnI' =
      function
      | ((T.Trivial, s), g) -> true__
      | ((Unify (g', e1, N, eqns), s), g) ->
          let g'' = compose (g', g) in
          let s' = shift (g', s) in
          (Assign.instance (g'', (e1, s'), (N, s'))) &&
            (solveEqnI' ((eqns, s), g))
    let rec retrieveInst (Nref, (Dq, sq), asub, GR) =
      let retrieve' =
        function
        | ((Leaf ((D, s), GRlistRef) as N), (Dq, sq), asubst,
           ((((DEVars, DAVars) as DAEVars), G_r, eqn, stage, status) as GR'))
            ->
            let (Dsq, D_G) = collectEVar (Dq, sq) in
            (match compatibleCtx (asubst, (D_G, G_r, eqn), (!GRlistRef)) with
             | NONE -> raise (Instance "Compatible path -- different ctx\n")
             | SOME ((D', g', eqn'), answRef', status') ->
                 let DAEVars = compose (DEVars, DAVars) in
                 let esub = ctxToAVarSub (g', DAEVars, (I.Shift 0)) in
                 let asub =
                   convAssSub
                     (g', asubst, ((I.ctxLength g') + 1), D',
                       ((I.ctxLength DAVars), (I.ctxLength DEVars))) in
                 let _ =
                   if solveEqn' ((eqn, (shift (g', esub))), g')
                   then ()
                   else print " failed to solve eqn_query\n" in
                 let easub = normalizeSub (I.comp (asub, esub)) in
                 if solveEqnI' ((eqn', (shift (g', easub))), g')
                 then T.RepeatedEntry ((esub, asub), answRef', status')
                 else
                   raise
                     (Instance
                        "Compatible path -- resdidual equ. not solvable\n"))
        | ((Node ((D, sub), children) as N), (Dq, sq), asub,
           ((DAEVars, G_r, eqn, stage, status) as GR)) ->
            let InstCand = findAllInst (G_r, children, (Dq, sq), asub) in
            let checkCandidates =
              function
              | nil -> raise (Instance "No compatible child\n")
              | (ChildRef, Drho2, asub)::ICands ->
                  (try retrieve' ((!ChildRef), Drho2, asub, GR)
                   with | Instance msg -> checkCandidates ICands) in
            checkCandidates InstCand in
      ((function | () -> ()), (retrieve' ((!Nref), (Dq, sq), asub, GR)))
    let rec compatibleSub ((D_t, nsub_t), (Dsq, squery)) =
      let (sigma, rho_t, rho_u) = ((nid ()), (nid ()), (nid ())) in
      let Dsigma = emptyCtx () in
      let D_r1 = copy D_t in
      let D_r2 = copy Dsq in
      let choose = ref (function | (match__ : bool) -> ()) in
      let _ =
        S.forall squery
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
    let rec mkNode =
      function
      | (Node (_, Children), ((Ds, sigma) as Dsigma), ((D1, rho1) as Drho1),
         (((evarl, l), dp, eqn, answRef, stage, status) as GR),
         ((D2, rho2) as Drho2)) ->
          let (D_rho2, D_G2) = collectEVar (D2, rho2) in
          let GR' = ((evarl, l), D_G2, dp, eqn, answRef, stage, status) in
          let (sizeSigma, sizeRho1, sizeRho2) =
            ((S.size sigma), (S.size rho1), (S.size rho2)) in
          Node
            (Dsigma,
              [ref (Leaf ((D_rho2, rho2), (ref [GR'])));
              ref (Node (Drho1, Children))])
      | (Leaf (c, GRlist), ((Ds, sigma) as Dsigma), ((D1, rho1) as Drho1),
         (((evarl, l), dp, eqn, answRef, stage, status) as GR2),
         ((D2, rho2) as Drho2)) ->
          let (D_rho2, D_G2) = collectEVar (D2, rho2) in
          let GR2' = ((evarl, l), D_G2, dp, eqn, answRef, stage, status) in
          Node
            (Dsigma,
              [ref (Leaf ((D_rho2, rho2), (ref [GR2'])));
              ref (Leaf (Drho1, GRlist))])
    let rec compChild =
      function
      | ((Leaf ((D_t, nsub_t), GList) as N), (D_e, nsub_e)) ->
          compatibleSub ((D_t, nsub_t), (D_e, nsub_e))
      | ((Node ((D_t, nsub_t), Children') as N), (D_e, nsub_e)) ->
          compatibleSub ((D_t, nsub_t), (D_e, nsub_e))
    let rec findAllCandidates (G_r, children, Ds) =
      let findAllCands =
        function
        | (G_r, nil, (Dsq, sub_u), VList, SList) -> (VList, SList)
        | (G_r, x::L, (Dsq, sub_u), VList, SList) ->
            (match compChild ((!x), (Dsq, sub_u)) with
             | NoCompatibleSub ->
                 findAllCands (G_r, L, (Dsq, sub_u), VList, SList)
             | SplitSub (Dsigma, Drho1, Drho2) ->
                 findAllCands
                   (G_r, L, (Dsq, sub_u), VList,
                     ((x, (Dsigma, Drho1, Drho2)) :: SList))
             | VariantSub ((D_r2, rho2) as Drho2) ->
                 findAllCands
                   (G_r, L, (Dsq, sub_u), ((x, Drho2, I.id) :: VList), SList)) in
      findAllCands (G_r, children, Ds, nil, nil)
    let rec divergingCtx (stage, g, GRlistRef) =
      let l = (I.ctxLength g) + 3 in
      List.exists
        (function
         | ((_, l), D, g', _, _, stage', _) ->
             (stage = stage') && (l > (I.ctxLength g'))) (!GRlistRef)
    let rec eqHeads =
      function
      | (Const k, Const k') -> k = k'
      | (BVar k, BVar k') -> k = k'
      | (Def k, Def k') -> k = k'
      | (_, _) -> false__
    let rec eqTerm =
      function
      | (Root (H2, s2), ((Root (H, S) as t), rho1)) ->
          if eqHeads (H2, H) then eqSpine (s2, (S, rho1)) else false__
      | (T2, (NVar n, rho1)) ->
          (match S.lookup rho1 n with
           | NONE -> false__
           | SOME (dt1, T1) -> eqTerm (T2, (T1, (nid ()))))
      | (Lam (D2, T2), (Lam (D, T), rho1)) -> eqTerm (T2, (T, rho1))
      | (_, (_, _)) -> false__
    let rec eqSpine =
      function
      | (I.Nil, (I.Nil, rho1)) -> true__
      | (App (T2, s2), (App (T, S), rho1)) ->
          (eqTerm (T2, (T, rho1))) && (eqSpine (s2, (S, rho1)))
    let rec divergingSub ((Ds, sigma), (Dr1, rho1), (Dr2, rho2)) =
      S.exists rho2
        (function
         | (n2, (dt2, t2)) ->
             S.exists sigma
               (function | (_, (d, t)) -> eqTerm (t2, (t, rho1))))
    let rec variantCtx =
      function
      | ((g, eqn), []) -> NONE
      | ((g, eqn), (l', D_G, g', eqn', answRef', _, status')::GRlist) ->
          if (equalCtx' (g, g')) && (equalEqn (eqn, eqn'))
          then SOME (l', answRef', status')
          else variantCtx ((g, eqn), GRlist)
    let rec insert (Nref, (Dsq, sq), GR) =
      let insert' =
        function
        | ((Leaf (_, GRlistRef) as N), (Dsq, sq),
           ((l, G_r, eqn, answRef, stage, status) as GR)) ->
            (match variantCtx ((G_r, eqn), (!GRlistRef)) with
             | NONE ->
                 let (D_nsub, D_G) = collectEVar (Dsq, sq) in
                 let GR' = (l, D_G, G_r, eqn, answRef, stage, status) in
                 (((function
                    | () ->
                        (GRlistRef := (GR' :: (!GRlistRef));
                         answList := (answRef :: (!answList))))),
                   (T.NewEntry answRef))
             | SOME (_, answRef', status') ->
                 (((function | () -> ())),
                   (T.RepeatedEntry ((I.id, I.id), answRef', status'))))
        | ((Node ((D, sub), children) as N), (Dsq, sq),
           ((l, G_r, eqn, answRef, stage, status) as GR)) ->
            let (VariantCand, SplitCand) =
              findAllCandidates (G_r, children, (Dsq, sq)) in
            let (D_nsub, D_G) = collectEVar (Dsq, sq) in
            let GR' = (l, D_G, G_r, eqn, answRef, stage, status) in
            let checkCandidates =
              function
              | (nil, nil) ->
                  (((function
                     | () ->
                         ((:=) Nref Node
                            ((D, sub),
                              ((ref (Leaf ((D_nsub, sq), (ref [GR'])))) ::
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
      insert' ((!Nref), (Dsq, sq), GR)
    let rec answCheckVariant (s', answRef, O) =
      let member =
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
      | (n, I.Null, (DEVars : ctx)) -> ()
      | (n, Decl (g, D), (DEVars : ctx)) ->
          (insertList ((n, D), DEVars); makeCtx ((n + 1), g, DEVars))
    let rec callCheck (a, DAVars, DEVars, g, U, eqn, status) =
      let (n, Tree) = Array.sub (indexArray, a) in
      let sq = S.new__ () in
      let DAEVars = compose (DEVars, DAVars) in
      let Dq = emptyCtx () in
      let n = I.ctxLength g in
      let _ = makeCtx ((n + 1), DAEVars, (Dq : ctx)) in
      let l = I.ctxLength DAEVars in
      let _ = S.insert sq (1, (0, U)) in
      let GR =
        ((l, (n + 1)), g, eqn, (emptyAnswer ()), (!TableParam.stageCtr),
          status) in
      let GR' = ((DEVars, DAVars), g, eqn, (!TableParam.stageCtr), status) in
      let result =
        try retrieveInst (Tree, (Dq, sq), (asid ()), GR')
        with | Instance msg -> insert (Tree, (Dq, sq), GR) in
      match result with
      | (sf, NewEntry answRef) ->
          (sf (); added := true__; T.NewEntry answRef)
      | (_, RepeatedEntry (asub, answRef, status)) ->
          T.RepeatedEntry (asub, answRef, status)
      | (sf, DivergingEntry (asub, answRef)) ->
          (sf (); added := true__; T.DivergingEntry (asub, answRef))
    let rec insertIntoTree (a, DAVars, DEVars, g, U, eqn, answRef, status) =
      let (n, Tree) = Array.sub (indexArray, a) in
      let sq = S.new__ () in
      let DAEVars = compose (DEVars, DAVars) in
      let Dq = emptyCtx () in
      let n = I.ctxLength g in
      let _ = makeCtx ((n + 1), DAEVars, (Dq : ctx)) in
      let l = I.ctxLength DAEVars in
      let _ = S.insert sq (1, (0, U)) in
      let GR =
        ((l, (n + 1)), g, eqn, (emptyAnswer ()), (!TableParam.stageCtr),
          status) in
      let result =
        insert
          (Tree, (Dq, sq),
            ((l, (n + 1)), g, eqn, answRef, (!TableParam.stageCtr), status)) in
      match result with
      | (sf, NewEntry answRef) ->
          (sf (); added := true__; T.NewEntry answRef)
      | (_, RepeatedEntry (asub, answRef, status)) ->
          T.RepeatedEntry (asub, answRef, status)
      | (sf, DivergingEntry (asub, answRef)) ->
          (sf (); added := true__; T.DivergingEntry (asub, answRef))
    let rec answCheck (s', answRef, O) = answCheckVariant (s', answRef, O)
    let rec updateTable () =
      let update arg__0 arg__1 =
        match (arg__0, arg__1) with
        | ([], Flag) -> Flag
        | (answRef::AList, Flag) ->
            let l = length (T.solutions answRef) in
            if (=) l T.lookup answRef
            then update AList Flag
            else (T.updateAnswLookup (l, answRef); update AList true__) in
      let Flag = update (!answList) false__ in
      let r = Flag || (!added) in added := false__; r
    let ((reset)(* index for normal variables *)(* index for bound variables *)
      (* depth of locally bound variables *)(* ------------------------------------------------------ *)
      (* for debugging only *)(* auxiliary function  -- needed to dereference AVars -- expensive?*)
      (* ------------------------------------------------------ *)
      (* Auxiliary functions *)(* etaSpine (S, n) = true

   iff S is a spine n;n-1;..;1;nil

   no permutations or eta-expansion of arguments are allowed
   *)
      (* compose (Decl(g',D1'), g) =   G. .... D3'. D2'.D1'
       where g' = Dn'....D3'.D2'.D1' *)
      (* ---------------------------------------------------------------------- *)
      (* ctxToEVarSub D = s

     if D is a context for existential variables,
        s.t. u_1:: A_1,.... u_n:: A_n = D
     then . |- s : D where s = X_n....X_1.id

    *)
      (* ---------------------------------------------------------------------- *)
      (* Matching for linear terms based on assignment *)
      (* lowerEVar' (g, V[s]) = (X', U), see lowerEVar *)
      (* lowerEVar1 (X, V[s]), V[s] in whnf, see lowerEVar *)(* lowerEVar1 (X, I.EVar (r, g, _, _), (V as I.Pi _, s)) = *)
      (* lowerEVar (X) = X'

       Invariant:
       If   g |- X : {{g'}} P
            X not subject to any constraints
       then g, g' |- X' : P

       Effect: X is instantiated to [[g']] X' if g' is empty
               otherwise X = X' and no effect occurs.
    *)
      (* It is not clear if this case can happen *)(* pre-Twelf 1.2 code walk, Fri May  8 11:05:08 1998 *)
      (* assign(d, Dec(n, V), X as I.Root(BVar k, S), U, asub) = ()
      Invariant:
      if D ; g |- U : V
         D ; g |- X : V
      then
         add (X, U) to asub
         where  assub is a set of substitutions for existential variables)
    *)
      (* [asub]E1  = U *)(* total as (t, passed)*)
      (* it is an evar -- (k-d, EVar (SOME(U), V)) *)
      (* total as (t, passed)*)(* it is an Avar and d = d' (k-d, AVar(SOME(U)) *)
      (* terms are in normal form *)(* exception Assignment of string *)
      (* assignExp (fasub, (l, ctxTotal as (r, passed), d) (D1, u1), (D2, u2))) = fasub'

     invariant:
      g, G0 |- u1 : V1   u1 in nf
      g, G0 |- u2 : V2   u2 in nf
     and u1, u2 are linear higher-order patterns
      D1 contains all existential variables of u1
      D2 contains all existential variables of u2

      ctxTotal = (r + passed) = |g|
            where g refers to the globally bound variables
      d = |G0| where g' refers to the locally bound variables

      then fasub' is a success continuation
        which builds up a substitution s
              with domain D1 and  u1[s] = u2

      NOTE: We only allow assignment for fully applied evars --
      and we will fail otherwise. This essentially only allows first-order assignment.
      To generalize this, we would need to linearize the ctx and have more complex
      abstraction algorithm.

   *)
      (* we do not expand definitions here -- this is very conservative! *)
      (* we do not expand definitions here -- this is very conservative! *)
      (* we do not expand definitions here -- this is very conservative! *)
      (* if (k1 - d) >= l *)(* k1 is a globally bound variable *)
      (* k2 is globally bound *)(* k1 is an existial variable *)
      (* k2 is globally bound *)(* denote the same evar *)
      (* ctxTotal,*)(* can this happen ? -- definitions should be already expanded ?*)
      (* type labels are ignored *)(* is this necessary? Tue Aug  3 11:56:17 2004 -bp *)
      (* the closure cases should be unnecessary, if everything is in nf *)
      (* assignCtx (fasub, ctxTotal as (r, passed), (D1, g), (D2, g')) = fasub'
      invariant
         |g| = |g'| = r
         |G0| = |G0'| = passed
         |g, G0| = |g', G0'| = (r + passed) = ctxTotal

         D1 contains all existential variables occuring in (g, G0)
         D2 contains all existential variables occuring in (g', G0')

         fasub' is a success continuation
            which builds up a substitution s
              with domain D1 and  (g, G0)[s] = (g, G0)

         NOTE : [fasub]g = g' Sun Nov 28 18:55:21 2004 -bp
    *)
      (* ------------------------------------------------------ *)
      (*  Variable b    : bound variable
    Variable n    : index variable
    linear term  U ::=  Root(c, S) | Lam (D, U) | Root(b, S)
    linear Spine S ::= p ; S | NIL
    indexed term t ::= Root(n, NIL) |  Root(c, S) | Lam (D, p) | Root(b, S)
    indexed spines S_i ::= t ; S_i | NIL
    Types   A
    Context g : context for bound variables (bvars)
    (type information is stored in the context)

       g ::= . | g, x : A
       Set of all index variables:  N

    linear terms are well-typed in g:     g |- p
    indexed terms are well-typed in (N ; g) |- t

    Let s is a substitution for index variables (nvar)
    and s1 o s2 o .... o sn = s, s.t.
    forall nvar in CODOM(sk).
     exists i . nvar in DOM(si) and i > k.

    IMAGE (s) = the index variables occurring in the CODOM(s)

    Let N1 ... Nn be the path from the root N1 to the leaf Nn,
    and si the substitution associated with node Ni.

    IMAGE(sn) = empty
    s1 o s2 o ... o sn = s and IMAGE(s) = empty
    i.e. index variables are only internally used and no
         index variable is left.

    A linear term U (and an indexed term t) can be decomposed into a term t' together with
    a sequenence of substitutions s1, s2, ..., sn such that s1 o s2 o .... o sn = s
    and the following holds:

    If    N  ; g |- t
    then  N' ; g |- t'
          N  ; g |- s : N' ; g
          N  ; g |- t'[s]     and t'[s] = t

   if we have a linear term then N will be empty, but the same holds.

   In addition:
   all expressions in the index are closed and linear and in normalform i.e.
   an expression is first linearized before it is inserted into the index

   *)
      (* ---------------------------------------------------------------*)
      (* nctr = |D| =  #index variables *)(* too restrictive if we require order of both eqn must be the same ?
     Sun Sep  8 20:37:48 2002 -bp *)
      (* s = s' = I.id *)(* equalEqn (e, e') = (e = e') *)
      (* equalEqn' (d, (D, e), (D', e'), asub) = (e = e')

       destructively updates asub such that all the evars occurring in D'
       will be instantiated and  D |- asub : D'

       if D |- e and D' |- e'  and d = depth of context g'
          asub partially instantiates variables from D'
       then
         D |- asub : D'

    *)
      (* AVar *)(* AVar *)(* X is the evar in the query, X' is the evar in the index,
             potentially X' is not yet instantiated and X' in D' but X' not in asub *)
      (* k refers to an evar *)(* it is not instantiated yet *)
      (* it is instantiated;
                                          since eqn were solvable, eqn' would be solvable too *)
      (* k refers to a bound variable *)(* equalSub (s, s') = (s=s') *)
      (* equalFront (F, F') = (F=F') *)(* equalCtx' (g, g') = (g=g') *)
      (* ---------------------------------------------------------------*)
      (* destructively may update asub ! *)(* print msg;*)
      (* ---------------------------------------------------------------*)
      (* collect EVars in sub *)(* collectEVar (D, sq) = (D_sub, D')
     if D |- sq where D is a set of free variables
     then Dsq |- sq  and (Dsq u D') = D
          Dsq contains all the free variables occuring in sq
          D' contains all the free variables corresponding to Gsq
   *)
      (* ---------------------------------------------------------------*)
      (* most specific linear common generalization *)
      (* compatible (T, U) = (T', rho_u, rho_t) opt
    if T is an indexed term
       U is a linear term
       U and T share at least the top function symbol
   then
       T'[rho_u] = U and T'[rho_t] = T
   *)
      (* 0 *)(* Found an EVar which is not yet
                     instantiated -- must be instantiated when
                     solving residual equations! *)
      (* should never happen -- all avars should
                     have been assigned! *)
      (* [s']T = U so U = query and T is in the index *)
      (* globally bound variable *)(* both refer to the same globally bound variable in g *)
      (* k, k' refer to the existential *)(* they refer to the same existential variable *)
      (* this is unecessary *)(* since existential variables have the same type
                             and need to be fully applied in order, s1 = s2 *)
      (* S.insert asub (k - d, I.Idx (k-d)) *)(* ctxTotal,*)
      (* instance checking only Sun Oct 27 12:16:10 2002 -bp *)(* ctxTotal,*)
      (* instance checking only Sun Oct 27 12:18:53 2002 -bp *)(* ctxTotal,*)
      (* ctxTotal,*)(* locally bound variables *)
      (* this case only should happen during instance checking *)
      (* ctxTotal,*)(* ctxTotal, *)
      (* this case only should happen during instance checking *)
      (* ctxTotal,*)(* ctxTotal, *)
      (* by invariant A1 = A2 -- actually this invariant may be violated, but we ignore it. *)
      (* U = EVar, EClo -- can't happen -- Sun Oct 20 13:41:25 2002 -bp *)
      (* by invariant dt = du *)(* if it succeeds then it will return a continuation which will
         instantiate the "evars" and rho_t will contain all
         nvar instantiations
         otherwise it will raise Instance *)
      (* by invariant dt = du *)(* could expand definitions here ? -bp*)
      (* globally bound variable *)(* should never happen *)
      (* k, k' refer to the existential *)(* they refer to the same existential variable *)
      (* this is unecessary -- since existential variables have the same type
                            and need to be fully applied in order, s1 = s2 *)
      (* variant checking only *)(* locally bound variables *)
      (* by invariant A1 = A2 *)(* U = EVar, EClo -- can't happen -- Sun Oct 20 13:41:25 2002 -bp *)
      (* by invariant dt = du *)(* compatibleCtx (asub, (Dsq, Gsq, eqn_sq), GR) = option

    if Dsq is a subset of Dsq_complete
       where Dsq_complete encompasses all evars and avars in the original query
       Dsq |- Gsq ctx
       Dsq, Gsq |- eqn_sq
       there exists (_, D', g', eqn', ansRef', _, status') in GR
       s.t.
       Gsq is an instance of g'
       (andalso eqn_sq = eqn')
    then
      SOME((D', g', eqn'), answRef', status)
      and asub is destructively updated s.t. Dsq_complete |- Gsq = [asub]g'

    else
      NONE
   *)
      (* ---------------------------------------------------------------*)
      (* instanceSub(nsub_t, squery) = (rho_u, asub)

   if DOM(nsub_t) <= DOM(nsub_u)
      CODOM(nsub_t) : index terms
      CODOM(nsub_u) : linear terms
        G_u, Glocal_u |- nsub_u
    N ; G_t, Glocal_t |- nsub_t
   then
     nsub_t = sigma o rho_t
     nsub_e = sigma o rho_u

    Glocal_e ~ Glocal_t  (have "approximately" the same type)
    l_g = |Glocal_u|


    [asub]nsub_t = squery
   *)
      (* by invariant rho_t = empty, since nsub_t <= squery *)(* note by invariant Glocal_e ~ Glocal_t *)
      (* [ac]T = U *)(* if U is an instance of T then [ac][rc_u]T = U *)
      (* once the continuations ac are triggered *)(* [asub]nsub_t = sq  where sq is the query substitution *)
      (* will update asub *)(* Solving  variable definitions *)
      (* solveEqn ((VarDef, s), g) = bool

    if g'' |- VarDef and g   |- s : g''
       g   |- VarDef[s]
    then
       return true, if VarDefs are solvable
              false otherwise
 *)
      (* evar *)(* Mon Dec 27 11:57:35 2004 -bp *)
      (* solveEqn' ((VarDef, s), g) = bool

    if g'' |- VarDef and g   |- s : g''
       g   |- VarDef[s]
    then
       return true, if VarDefs are solvable
              false otherwise
 *)
      (* evar *)(* Mon Dec 27 12:20:45 2004 -bp
  solveEqn' ((VarDef, s), g) = bool

    if g'' |- VarDef and g   |- s : g''
       g   |- VarDef[s]
    then
       return true, if VarDefs are solvable
              false otherwise
 *)
      (* evar *)(* solveEqnI' ((VarDef, s), g) = bool

    if g'' |- VarDef and g   |- s : g''
       g   |- VarDef[s]
    then
       return true, if VarDefs are solvable
              false otherwise
 *)
      (* evar *)(* note: we check whether N[s'] is an instance of e1[s'] !!! *)
      (* at this point all AVars have been instantiated, and we could use Match.instance directly *)
      (* solveEqnI' ((VarDef, s), g) = bool

    if g'' |- VarDef and g   |- s : g''
       g   |- VarDef[s]
    then
       return true, if VarDefs are solvable
              false otherwise
 *)
      (* evar *)(* note: we check whether N[s'] is an instance of e1[s'] !!! *)
      (* at this point all AVars have been instantiated, and we could use Match.instance directly *)
      (* retrieve all Instances from substitution tree *)
      (* retreiveInst (Nref, (Dq, sq), s', GR) = callCheckResult

      Invariant:

      If there exists a path r1 ... rn = p
         in the substitution tree with root Nref
         and there exists an assignable substitution s' (D
         s.t. [r']
      then
         return RepeatedEntry
      else raises exception instance
    *)
      (* s and sq are compatible by invariant *)(* [asub]s = sq   and there exists a path (D1, s1) ... (Dn,sn) from the root to the leaf (D,s)
           s.t. [asub]s1 o s2 o ... sn o s corresponds to original query
           *)
      (* Dq = (Dsq' u Dg) where Dsq' = evars occurring in sq
                                      D_G = evars occuring in G_sq or only in eqn_sq

               and Dsq = D since there exists a path s1 ... sn from the root to the leaf (D,s)
                 s.t. [asub]s1 o s2 o ... sn o s corresponds to original query
             *)
      (* compatibleCtx may destructively update asub ! *)
      (* compatible path -- but different ctx *)(* compatible path -- SAME ctx *)
      (* note: previously we checked eqn' = eqn! -- this is too restrictive
                 now - Dec  6 2004 -bp we check whether eqn is an instance of eqn'
                 note: this is very delicate code.
               *)
      (* Since there exists a path (D1, s1) ... (Dn,sn) from the root to the leaf (D,s)
                   D1', ...., Dn', D, D' = D*
                   and          g' |- esub' : DAEVars, g'        and       .   |- esub : DAEVars
                        DAEVars, g |- asub' : D*, g'                   DAEVars |- asub : D*

                  note: asub' may refer to free variables which denote evars in D*
                        which only occur in eqn' and hence have not yet been instantiated
                        however: all avars in D* have been instantiated!
                 *)
      (* Residual equation of query:
                   DAEVars, g' |- eqn  hence we solve : g' |= [esub']eqn *)
      (* = G_r *)(*              val _ = if solveEqn' (eqn, esub)
                          then () else print " failed to solve eqn_query\n"  *)
      (* Residual equations in index:
                   D*, g' |- eqn'    where eqn' = AVar1 = E1 .... AVarn = En
                                      and  Ei may contain free variables
                      g'  |= [esub](asub) (eqn')

                      solve eqn' from path in index using instance or matching ONLY
                      to instantiate the free variables Ei

                   remark: DAEVars, g' |= [asub]eqn'   should work in theory too,
                           if the free variables in asub are created in such a way that they may depend on DAVars.
                           otherwise unification or instance checking will fail or the resulting instantiation
                           for the free variables in asub is too restrictive, s.t. retrieval fails
                   *)
      (*              if solveEqnI' (eqn', easub) *)
      (* solve residual equations using higher-order matching Wed Dec 22 2004 -bp *)
      (* no child is compatible with sq *)(* there is an instance  *)
      (* print msg; *)(*---------------------------------------------------------------------------*)
      (* insert new entry into substitution tree *)(* assuming there is no compatible entry already *)
      (* compatibleSub(nsub_t, squery) = (sigma, rho_t, rho_u) opt

   if DOM(nsub_t) <= DOM(squery)
      CODOM(nsub_t) : index terms
      CODOM(squery) : linear terms
        G_u, Glocal_u |- squery
    N ; G_t, Glocal_t |- nsub_t
   then
     nsub_t = sigma o rho_t
     nsub_e = sigma o rho_u

    Glocal_e ~ Glocal_t  (have "approximately" the same type)

   *)
      (* by invariant rho_t = empty, since nsub_t <= squery *)(* note by invariant Glocal_e ~ Glocal_t *)
      (* here Glocal_t will be only approximately correct! *)(* perfect match under asub and rho_t = nsub_t
           sigma = rho_t and sigma o asub = rho_u *)
      (* split -- asub is unchanged *)(* Dsigma |~ sigma, D_r1 |~ rho_t, D_r1 |~ rho_u *)
      (* ---------------------------------------------------------------------- *)
      (*  fun mkLeaf (Ds, GR, n) = Leaf (Ds, GR)*)(* ---------------------------------------------------------------------- *)
      (* ---------------------------------------------------------------------- *)
      (* this 3 is arbitrary -- lockstep *)(* eqTerm (t2, (t, rho1)) = bool
    returns true iff t2 = t[rho1]
  t2 is a linear term which may not contain any nvars!
  t may contain nvars
 *)
      (* ---------------------------------------------------------------------- *)
      (* Insert via variant checking *)(* insert (Nref, (Dq, sq), GR) = TableResult *)
      (* compatible path -- but different ctx! *)(* D_G contains evars occurring only in eqn or g
                        D_nsub contains evars occurring only in sq
                        furthermore: D_nsub = D where Leaf((D,s), GRlistRef)
                     *)
      (* compatible path -- SAME ctx and SAME eqn!
                                          this implies: SAME D_G *)
      (* no child is compatible with sq *)(* split an existing node *)
      (* substree diverging -- splitting node *)(* split existing node *)
      (* unique "perfect" candidate (left) *)(* there are several "perfect" candidates *)
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

      answerCheck (g, s, answRef, 0) = repeated
         if (D_k, s_k, eqn)  already occurs in answRef
      answerCheck (g,s, answRef, O) = new
         if (D_k, s_k, eqn) did not occur in answRef
         Sideeffect: update answer list for U
     *)
      (* ---------------------------------------------------------------------- *)
      (* Reset Subsitution Tree *)(* makeCtx (n, g, g') =  unit
     if g LF ctx
     then
      g' is a set
      where (i,Di) corresponds to the i-th declaration in g

    note: g' is destructively updated
    *)
      (* callCheck (a, DAVars, DEVars, g, U, eqn, status) = TableResult
    if
      U is atomic (or base type) i.e. U = a S

      DAVars, DEVars, g |- U
      DAVars, DEVars, g |- eqn

      Tree is the substitution trie associated with type family a

   then
      if there exists a path r1 o r2 o ... o rn = p in Tree
         together with some (g',eqn', answRef') at the leaf
         and DAVars', DEVars', g' |- p
      and there exists a substitution s' s.t.

          DAVars, DEVars |- s' : DAVars', DEVars'
          [s']g' = g and [s']p = U

      and moreover
          there exists a substitution r' s.t.  g |- r' : DAVars, DEVars, g
          (which re-instantiates evars)

      and
            g |= [r']eqn    and [s']g' |= [r'][s']eqn'
     then
       TableResult = RepeatedEntry(s', answRef')

     otherwise

       TableResult = NewEntry (answRef')
       and there exists a path r1 o r2 o ... o rk = U in Tree
           together with (g,eqn, answRef) at the leaf

   *)
      (* n = |g| *)(* Dq = DAVars, DEVars *)(* l = |D| *)
      (* assignable subst *)(* sq not in index --> insert it *)
      (* we assume we alsways insert new things into the tree *)
      (* sq = query substitution *)(* no new solutions were added in the previous stage *)
      (* new solutions were added *)) = reset
    let callCheck =
      function
      | (DAVars, DEVars, g, U, eqn, status) ->
          callCheck
            ((cidFromHead (I.targetHead U)), DAVars, DEVars, g, U, eqn,
              status)
    let insertIntoTree =
      function
      | (DAVars, DEVars, g, U, eqn, answRef, status) ->
          insertIntoTree
            ((cidFromHead (I.targetHead U)), DAVars, DEVars, g, U, eqn,
              answRef, status)
    let answerCheck = answCheck
    let updateTable = updateTable
    let tableSize = function | () -> length (!answList)
    let rec memberCtx
      ((((g)(* memberCtxS ((g,V), g', n) = bool

       if g |- V and |- g' ctx
          exists a V' in g s.t.  V'[^n]  is an instance of V
       then return true
         otherwise false
    *)),
        V),
       g')
      =
      let instanceCtx' =
        function
        | ((g, V), I.Null, n) -> NONE
        | ((g, V), Decl (g', (Dec (_, V') as D')), n) ->
            if Match.instance (g, (V, I.id), (V', (I.Shift n)))
            then SOME D'
            else instanceCtx' ((g, V), g', (n + 1)) in
      instanceCtx' ((g, V), g', 1)
  end ;;
