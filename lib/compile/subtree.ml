
module type SUBTREE  =
  sig
    type nonrec nvar = int
    type nonrec bvar = int
    type nonrec bdepth = int
    type typeLabel =
      | TypeLabel 
      | Body 
    type nonrec normalSubsts = (typeLabel * IntSyn.__Exp) RBSet.ordSet
    type nonrec querySubsts =
      (IntSyn.__Dec IntSyn.__Ctx * (typeLabel * IntSyn.__Exp)) RBSet.ordSet
    type __CGoal =
      | CGoals of (CompSyn.__AuxGoal * IntSyn.cid * CompSyn.__Conjunction *
      int) 
    type __AssSub =
      | Assign of (IntSyn.__Dec IntSyn.__Ctx * IntSyn.__Exp) 
    type nonrec assSubsts = __AssSub RBSet.ordSet
    type __Cnstr =
      | Eqn of (IntSyn.__Dec IntSyn.__Ctx * IntSyn.__Exp * IntSyn.__Exp) 
    type __Tree =
      | Leaf of (normalSubsts * IntSyn.__Dec IntSyn.__Ctx * __CGoal) 
      | Node of (normalSubsts * __Tree RBSet.ordSet) 
    val indexArray : (int ref * __Tree ref) Array.array
    val sProgReset : unit -> unit
    val sProgInstall :
      IntSyn.cid -> CompSyn.__CompHead -> CompSyn.__Conjunction -> unit
    val matchSig :
      IntSyn.cid ->
        IntSyn.__Dec IntSyn.__Ctx ->
          IntSyn.eclo ->
            ((CompSyn.__Conjunction * IntSyn.__Sub) -> IntSyn.cid -> unit) ->
              unit
  end;;




module SubTree(SubTree:sig
                         module Whnf : WHNF
                         module Unify : UNIFY
                         module Print : PRINT
                         module CPrint : CPRINT
                         module Formatter : FORMATTER
                         module Names : NAMES
                         module CSManager : CS_MANAGER
                       end) : SUBTREE =
  struct
    type nonrec nvar = int
    type nonrec bvar = int
    type nonrec bdepth = int
    type typeLabel =
      | TypeLabel 
      | Body 
    type nonrec normalSubsts = (typeLabel * IntSyn.__Exp) RBSet.ordSet
    type __AssSub =
      | Assign of (IntSyn.__Dec IntSyn.__Ctx * IntSyn.__Exp) 
    type nonrec assSubsts = __AssSub RBSet.ordSet
    type nonrec querySubsts =
      (IntSyn.__Dec IntSyn.__Ctx * (typeLabel * IntSyn.__Exp)) RBSet.ordSet
    type __Cnstr =
      | Eqn of (IntSyn.__Dec IntSyn.__Ctx * IntSyn.__Exp * IntSyn.__Exp) 
    type nonrec cnstrSubsts = IntSyn.__Exp RBSet.ordSet
    type __CGoal =
      | CGoals of (CompSyn.__AuxGoal * IntSyn.cid * CompSyn.__Conjunction *
      int) 
    type genType =
      | Top 
      | Regular 
    type __Tree =
      | Leaf of (normalSubsts * IntSyn.__Dec IntSyn.__Ctx * __CGoal) 
      | Node of (normalSubsts * __Tree RBSet.ordSet) 
    type nonrec candidate =
      (assSubsts * normalSubsts * cnstrSubsts * __Cnstr * IntSyn.__Dec
        IntSyn.__Ctx * __CGoal)
    let (nid : unit -> normalSubsts) = RBSet.new__
    let (assignSubId : unit -> assSubsts) = RBSet.new__
    let (cnstrSubId : unit -> cnstrSubsts) = RBSet.new__
    let (querySubId : unit -> querySubsts) = RBSet.new__
    let rec isId s = RBSet.isEmpty s
    let rec makeTree () = ref (Node ((nid ()), (RBSet.new__ ())))
    let rec noChildren (__C) = RBSet.isEmpty __C
    let indexArray =
      Array.tabulate (Global.maxCid, (fun i -> ((ref 0), (makeTree ()))))
    module I = IntSyn
    module C = CompSyn
    module S = RBSet
    exception Error of string 
    exception Assignment of string 
    exception Generalization of string 
    let rec cidFromHead = function | Const c -> c | Def c -> c
    let rec dotn __0__ __1__ =
      match (__0__, __1__) with
      | (0, s) -> s
      | (i, s) -> dotn ((i - 1), (I.dot1 s))
    let rec compose' __2__ __3__ =
      match (__2__, __3__) with
      | (IntSyn.Null, __G) -> __G
      | (Decl (__G, __D), __G') -> IntSyn.Decl ((compose' (__G, __G')), __D)
    let rec shift __4__ __5__ =
      match (__4__, __5__) with
      | (IntSyn.Null, s) -> s
      | (Decl (__G, __D), s) -> I.dot1 (shift (__G, s))
    let rec raiseType __6__ __7__ =
      match (__6__, __7__) with
      | (I.Null, __V) -> __V
      | (Decl (__G, __D), __V) -> raiseType (__G, (I.Lam (__D, __V)))
    let rec printSub =
      function
      | Shift n -> print (((^) "Shift " Int.toString n) ^ "\n")
      | Dot (Idx n, s) ->
          (print (((^) "Idx " Int.toString n) ^ " . "); printSub s)
      | Dot (Exp (EVar (_, _, _, _)), s) ->
          (print "Exp (EVar _ ). "; printSub s)
      | Dot (Exp (AVar _), s) -> (print "Exp (AVar _ ). "; printSub s)
      | Dot (Exp (EClo (AVar _, _)), s) ->
          (print "Exp (AVar _ ). "; printSub s)
      | Dot (Exp (EClo (_, _)), s) -> (print "Exp (EClo _ ). "; printSub s)
      | Dot (Exp _, s) -> (print "Exp (_ ). "; printSub s)
      | Dot (IntSyn.Undef, s) -> (print "Undef . "; printSub s)
    let nctr = ref 1
    let rec newNVar () = ((!) ((:=) nctr) nctr) + 1; I.NVar (!nctr)
    let rec eqHeads __8__ __9__ =
      match (__8__, __9__) with
      | (Const k, Const k') -> k = k'
      | (BVar k, BVar k') -> k = k'
      | (Def k, Def k') -> k = k'
      | (_, _) -> false__
    let rec compatible label (__T) (__U) rho_t rho_u =
      let rec genExp __10__ __11__ __12__ __13__ =
        match (__10__, __11__, __12__, __13__) with
        | (label, b, (NVar n as T), (Root (__H, __S) as U)) ->
            (S.insert rho_u (n, (label, __U)); __T)
        | (label, b, (Root (__H1, __S1) as T), (Root (__H2, __S2) as U)) ->
            if eqHeads (__H1, __H2)
            then I.Root (__H1, (genSpine (label, b, __S1, __S2)))
            else
              (match b with
               | Regular ->
                   (S.insert rho_t (((!nctr) + 1), (label, __T));
                    S.insert rho_u (((!nctr) + 1), (label, __U));
                    newNVar ())
               | _ -> raise (Generalization "Should never happen!"))
        | (label, b, Lam ((Dec (__N, __A1) as D1), __T1), Lam
           ((Dec (_, __A2) as D2), __U2)) ->
            I.Lam
              ((I.Dec (__N, (genExp (TypeLabel, Regular, __A1, __A2)))),
                (genExp (label, b, __T1, __U2)))
        | (label, b, Pi (((__D1, I.No) as DD1), __E1), Pi
           (((__D2, I.No) as DD2), __E2)) ->
            I.Pi
              (((genDec (TypeLabel, Regular, __D1, __D2)), I.No),
                (genExp (label, b, __E1, __E2)))
        | (label, b, Pi (((__D1, I.Maybe) as DD1), __E1), Pi
           (((__D2, I.Maybe) as DD2), __E2)) ->
            I.Pi
              (((genDec (TypeLabel, Regular, __D1, __D2)), I.Maybe),
                (genExp (label, b, __E1, __E2)))
        | (label, b, Pi (((__D1, I.Meta) as DD1), __E1), Pi
           (((__D2, I.Meta) as DD2), __E2)) ->
            I.Pi
              (((genDec (TypeLabel, Regular, __D1, __D2)), I.Meta),
                (genExp (label, b, __E1, __E2)))
        | (label, b, __T, __U) ->
            raise
              (Generalization
                 "Cases where U= EVar or EClo should never happen!")(* NOTE: by invariant A1 =/= A2 *)
      (* find *i in rho_t and rho_u such that T/*i in rho_t and U/*i in rho_u *)
      (* = S.existsOpt (fn U' => equalTerm (U, U')) *)
      and genSpine __14__ __15__ __16__ __17__ =
        match (__14__, __15__, __16__, __17__) with
        | (label, b, I.Nil, I.Nil) -> I.Nil
        | (label, b, App (__T, __S1), App (__U, __S2)) ->
            I.App
              ((genExp (label, b, __T, __U)),
                (genSpine (label, b, __S1, __S2)))
      and genDec label b (Dec (__N, __E1)) (Dec (__N', __E2)) =
        I.Dec (__N, (genExp (label, b, __E1, __E2))) in
      let rec genTop __18__ __19__ __20__ =
        match (__18__, __19__, __20__) with
        | (label, (Root (__H1, __S1) as T), (Root (__H2, __S2) as U)) ->
            if eqHeads (__H1, __H2)
            then I.Root (__H1, (genSpine (label, Regular, __S1, __S2)))
            else
              raise (Generalization "Top-level function symbol not shared")
        | (label, Lam ((Dec (__N, __A1) as D1), __T1), Lam
           ((Dec (_, __A2) as D2), __U2)) ->
            I.Lam
              ((I.Dec (__N, (genExp (label, Regular, __A1, __A2)))),
                (genTop (label, __T1, __U2)))
        | (_, _, _) ->
            raise (Generalization "Top-level function symbol not shared")
        (* by invariant A1 =/= A2 *) in
      try Some (genTop (label, __T, __U)) with | Generalization msg -> NONE
    let rec compatibleSub nsub_t nsub_e =
      let (sg, rho_t, rho_e) = ((nid ()), (nid ()), (nid ())) in
      let _ =
        S.forall nsub_e
          (fun nv ->
             fun (l', __E) ->
               ((match S.lookup nsub_t nv with
                 | Some (l, __T) ->
                     if l = l'
                     then
                       (match compatible (l, __T, __E, rho_t, rho_e) with
                        | NONE ->
                            (S.insert rho_t (nv, (l, __T));
                             S.insert rho_e (nv, (l, __E)))
                        | Some (__T') -> S.insert sg (nv, (l, __T')))
                     else raise (Generalization "Labels don't agree\n")
                 | NONE -> S.insert rho_e (nv, (l', __E)))
               (* by invariant d = d'
                                     therefore T and E have the same approximate type A *))) in
      ((if isId sg then NONE else Some (sg, rho_t, rho_e))
        (* by invariant rho_t = empty, since nsub_t <= nsub_e *))
    let rec mkNode __21__ __22__ __23__ __24__ __25__ =
      match (__21__, __22__, __23__, __24__, __25__) with
      | (Node (_, Children), sg, rho1, ((__G, RC) as GR), rho2) ->
          let c = S.new__ () in
          (S.insertList c
             [(1, (Node (rho1, Children))); (2, (Leaf (rho2, __G, RC)))];
           Node (sg, c))
      | (Leaf (_, __G1, RC1), sg, rho1, ((__G2, RC2) as GR), rho2) ->
          let c = S.new__ () in
          (S.insertList c
             [(1, (Leaf (rho1, __G1, RC1))); (2, (Leaf (rho2, __G2, RC2)))];
           Node (sg, c))
    let rec compareChild children (n, child) nsub_t nsub_e
      ((G_clause2, Res_clause2) as GR) =
      match compatibleSub (nsub_t, nsub_e) with
      | NONE ->
          S.insert children
            ((n + 1), (Leaf (nsub_e, G_clause2, Res_clause2)))
      | Some (sg, rho1, rho2) ->
          if isId rho1
          then
            (((if isId rho2
               then
                 S.insertShadow children
                   (n, (mkNode (child, sg, rho1, GR, rho2)))
               else S.insertShadow children (n, (insert (child, rho2, GR)))))
            (* sg = nsub_t = nsub_e *)(* sg = nsub_t and nsub_e = sg o rho2 *))
          else
            S.insertShadow children (n, (mkNode (child, sg, rho1, GR, rho2)))
    let rec insert __26__ __27__ __28__ =
      match (__26__, __27__, __28__) with
      | ((Leaf (nsub_t, G_clause1, __R1) as N), nsub_e,
         ((G_clause2, __R2) as GR)) ->
          (match compatibleSub (nsub_t, nsub_e) with
           | NONE -> raise (Error "Leaf is not compatible substitution r")
           | Some (sg, rho1, rho2) -> mkNode (__N, sg, rho1, GR, rho2))
      | ((Node (_, children) as N), nsub_e, ((G_clause2, RC) as GR)) ->
          ((if noChildren children
            then (S.insert children (1, (Leaf (nsub_e, G_clause2, RC))); __N)
            else
              (match S.last children with
               | (n, (Node (nsub_t, children') as child)) ->
                   (compareChild (children, (n, child), nsub_t, nsub_e, GR);
                    __N)
               | (n, (Leaf (nsub_t, __G1, RC1) as child)) ->
                   (compareChild (children, (n, child), nsub_t, nsub_e, GR);
                    __N)))
          (* initial *))
    let rec normalizeNExp __29__ __30__ =
      match (__29__, __30__) with
      | (NVar n, csub) ->
          let __A = I.newAVar () in (S.insert csub (n, __A); __A)
      | (Root (__H, __S), nsub) ->
          I.Root (__H, (normalizeNSpine (__S, nsub)))
      | (Lam (__D, __U), nsub) ->
          I.Lam ((normalizeNDec (__D, nsub)), (normalizeNExp (__U, nsub)))
      | (Pi ((__D, __P), __U), nsub) ->
          I.Pi
            (((normalizeNDec (__D, nsub)), __P), (normalizeNExp (__U, nsub)))
      (* cannot happen -bp *)
    let rec normalizeNSpine __31__ __32__ =
      match (__31__, __32__) with
      | (I.Nil, _) -> I.Nil
      | (App (__U, __S), nsub) ->
          I.App ((normalizeNExp (__U, nsub)), (normalizeNSpine (__S, nsub)))
    let rec normalizeNDec (Dec (__N, __E)) nsub =
      I.Dec (__N, (normalizeNExp (__E, nsub)))
    let rec assign nvaronly (Glocal_u1) (__Us1) (__U2) nsub_goal asub csub
      cnstr =
      let depth = I.ctxLength Glocal_u1 in
      let rec assignHead nvaronly depth (Glocal_u1)
        ((Root (__H1, __S1), s1) as Us1) (Root (__H2, __S2) as U2) cnstr =
        ((match (__H1, __H2) with
          | (Const c1, Const c2) ->
              if c1 = c2
              then
                assignSpine
                  (nvaronly, depth, Glocal_u1, (__S1, s1), __S2, cnstr)
              else raise (Assignment "Constant clash")
          | (Skonst c1, Skonst c2) ->
              if c1 = c2
              then
                assignSpine
                  (nvaronly, depth, Glocal_u1, (__S1, s1), __S2, cnstr)
              else raise (Assignment "Skolem constant clash")
          | (Def d1, _) ->
              assignExp
                (nvaronly, depth, Glocal_u1, (Whnf.expandDef __Us1), __U2,
                  cnstr)
          | (FgnConst (cs1, ConDec (n1, _, _, _, _, _)), FgnConst
             (cs2, ConDec (n2, _, _, _, _, _))) ->
              if (cs1 = cs2) && (n1 = n2)
              then cnstr
              else raise (Assignment "Foreign Constant clash")
          | (FgnConst (cs1, ConDef (n1, _, _, __W1, _, _, _)), FgnConst
             (cs2, ConDef (n2, _, _, __V, __W2, _, _))) ->
              if (cs1 = cs2) && (n1 = n2)
              then cnstr
              else
                assignExp
                  (nvaronly, depth, Glocal_u1, (__W1, s1), __W2, cnstr)
          | (FgnConst (_, ConDef (_, _, _, __W1, _, _, _)), _) ->
              assignExp (nvaronly, depth, Glocal_u1, (__W1, s1), __U2, cnstr)
          | (_, FgnConst (_, ConDef (_, _, _, __W2, _, _, _))) ->
              assignExp (nvaronly, depth, Glocal_u1, __Us1, __W2, cnstr)
          | (_, _) -> raise (Assignment "Head mismatch "))
        (* we require unique string representation of external constants *))
      and assignExpW __33__ __34__ __35__ __36__ __37__ __38__ =
        match (__33__, __34__, __35__, __36__, __37__, __38__) with
        | (nvaronly, depth, Glocal_u1, (Uni (__L1), s1), Uni (__L2), cnstr)
            -> cnstr
        | (nvaronly, depth, Glocal_u1, __Us1, NVar n, cnstr) ->
            (S.insert nsub_goal (n, (Glocal_u1, (nvaronly, (I.EClo __Us1))));
             cnstr)
        | (Body, depth, Glocal_u1, ((Root (__H1, __S1), s1) as Us1),
           (Root (__H2, __S2) as U2), cnstr) ->
            (match __H2 with
             | BVar k2 ->
                 ((if k2 > depth
                   then
                     (S.insert asub
                        (((-) k2 I.ctxLength Glocal_u1),
                          (Assign (Glocal_u1, (I.EClo __Us1))));
                      cnstr)
                   else
                     (match __H1 with
                      | BVar k1 ->
                          if k1 = k2
                          then
                            assignSpine
                              (Body, depth, Glocal_u1, (__S1, s1), __S2,
                                cnstr)
                          else raise (Assignment "Bound variable clash")
                      | _ -> raise (Assignment "Head mismatch")))
                 (* BVar(k2) stands for an existential variable *)
                 (* S2 is an etaSpine by invariant *))
             | _ -> assignHead (Body, depth, Glocal_u1, __Us1, __U2, cnstr))
        | (TypeLabel, depth, Glocal_u1, ((Root (__H1, __S1), s1) as Us1),
           (Root (__H2, __S2) as U2), cnstr) ->
            (match __H2 with
             | BVar k2 ->
                 ((if k2 > depth
                   then cnstr
                   else
                     (match __H1 with
                      | BVar k1 ->
                          if k1 = k2
                          then
                            assignSpine
                              (TypeLabel, depth, Glocal_u1, (__S1, s1), __S2,
                                cnstr)
                          else raise (Assignment "Bound variable clash")
                      | _ -> raise (Assignment "Head mismatch")))
                 (* BVar(k2) stands for an existential variable *)
                 (* then by invariant, it must have been already instantiated *))
             | _ ->
                 assignHead (TypeLabel, depth, Glocal_u1, __Us1, __U2, cnstr))
        | (nvaronly, depth, Glocal_u1, __Us1, (Root (BVar k2, __S) as U2),
           cnstr) ->
            ((if k2 > depth
              then
                (match nvaronly with
                 | TypeLabel -> cnstr
                 | Body ->
                     (S.insert asub
                        ((k2 - depth), (Assign (Glocal_u1, (I.EClo __Us1))));
                      cnstr))
              else
                (match nvaronly with
                 | TypeLabel -> cnstr
                 | Body ->
                     (match __Us1 with
                      | (EVar (r, _, __V, Cnstr), s) ->
                          let U2' = normalizeNExp (__U2, csub) in
                          (Eqn (Glocal_u1, (I.EClo __Us1), U2')) :: cnstr
                      | (EClo (__U, s'), s) ->
                          assignExp
                            (Body, depth, Glocal_u1, (__U, (I.comp (s', s))),
                              __U2, cnstr)
                      | (FgnExp (_, ops), _) ->
                          let U2' = normalizeNExp (__U2, csub) in
                          (Eqn (Glocal_u1, (I.EClo __Us1), U2')) :: cnstr)))
            (* BVar(k2) stands for an existential variable *)(* I.Root (BVar k2, S) will be fully applied (invariant from compilation) *)
            (* Glocal_u1 |- Us1 *))
        | (nvaronly, depth, Glocal_u1,
           (Lam ((Dec (_, __A1) as D1), __U1), s1), Lam
           ((Dec (_, __A2) as D2), __U2), cnstr) ->
            let cnstr' =
              assignExp
                (TypeLabel, depth, Glocal_u1, (__A1, s1), __A2, cnstr) in
            ((assignExp
                (nvaronly, (depth + 1),
                  (I.Decl (Glocal_u1, (I.decSub (__D1, s1)))),
                  (__U1, (I.dot1 s1)), __U2, cnstr'))
              (* nsub_goal may be destructively updated,
               asub does not change (i.e. existential variables are not instantiated,
               by invariant they must have been already instantiated
             *))
        | (nvaronly, depth, Glocal_u1,
           (Pi (((Dec (_, __A1) as D1), _), __U1), s1), Pi
           (((Dec (_, __A2) as D2), _), __U2), cnstr) ->
            let cnstr' =
              assignExp
                (TypeLabel, depth, Glocal_u1, (__A1, s1), __A2, cnstr) in
            ((assignExp
                (nvaronly, (depth + 1),
                  (I.Decl (Glocal_u1, (I.decSub (__D1, s1)))),
                  (__U1, (I.dot1 s1)), __U2, cnstr'))
              (* nsub_goal may be destructively updated,
               asub does not change (i.e. existential variables are not instantiated,
               by invariant they must have been already instantiated
            *))
        | (nvaronly, depth, Glocal_u1, ((EVar (r, _, __V, Cnstr), s) as Us1),
           __U2, cnstr) ->
            let U2' = normalizeNExp (__U2, csub) in
            (Eqn (Glocal_u1, (I.EClo __Us1), U2')) :: cnstr
        | (nvaronly, depth, Glocal_u1, ((EClo (__U, s'), s) as Us1), __U2,
           cnstr) ->
            assignExp
              (nvaronly, depth, Glocal_u1, (__U, (I.comp (s', s))), __U2,
                cnstr)
        | (nvaronly, depth, Glocal_u1, ((FgnExp (_, ops), _) as Us1), __U2,
           cnstr) ->
            let U2' = normalizeNExp (__U2, csub) in
            (Eqn (Glocal_u1, (I.EClo __Us1), U2')) :: cnstr
        | (nvaronly, depth, Glocal_u1, __Us1, (FgnExp (_, ops) as U2), cnstr)
            -> (Eqn (Glocal_u1, (I.EClo __Us1), __U2)) :: cnstr(* by invariant Us2 cannot contain any FgnExp *)
      (* generate cnstr substitution for all nvars occurring in U2 *)
      (* assignExp (nvaronly, depth+1, I.Decl (Glocal_u1, D2), (U1, I.dot1 s1), U2, cnstr) *)
      (* it does matter what we put in Glocal_u1! since D2 will only be approximately the same as D1 at this point! *)
      (* D1[s1] = D2[s2]  by invariant *)(* D1[s1] = D2[s2]  by invariant *)
      (* by invariant Us2 cannot contain any FgnExp *)
      (* here spine associated with k2 might not be Nil ? *)(* L1 = L2 by invariant *)
      and assignSpine __39__ __40__ __41__ __42__ __43__ __44__ =
        match (__39__, __40__, __41__, __42__, __43__, __44__) with
        | (nvaronly, depth, Glocal_u1, (I.Nil, _), I.Nil, cnstr) -> cnstr
        | (nvaronly, depth, Glocal_u1, (SClo (__S1, s1'), s1), __S, cnstr) ->
            assignSpine
              (nvaronly, depth, Glocal_u1, (__S1, (I.comp (s1', s1))), __S,
                cnstr)
        | (nvaronly, depth, Glocal_u1, (App (__U1, __S1), s1), App
           (__U2, __S2), cnstr) ->
            let cnstr' =
              assignExp (nvaronly, depth, Glocal_u1, (__U1, s1), __U2, cnstr) in
            ((assignSpine
                (nvaronly, depth, Glocal_u1, (__S1, s1), __S2, cnstr'))
              (* nsub_goal, asub may be destructively updated *))
      and assignExp nvaronly depth (Glocal_u1) (__Us1) (__U2) cnstr =
        assignExpW
          (nvaronly, depth, Glocal_u1, (Whnf.whnf __Us1), __U2, cnstr) in
      ((assignExp (nvaronly, depth, Glocal_u1, __Us1, __U2, cnstr))
        (*      | assignExpW (nvaronly, depth, Glocal_u1, (U1, s1), I.Lam (D2, U2), cnstr) =
           Cannot occur if expressions are eta expanded *)
        (*      | assignExpW (nvaronly, depth, Glocal_u1, (I.Lam (D1, U1), s1), U2, cnstr) =
       ETA: can't occur if eta expanded *)
        (* same reasoning holds as above *))
    let rec assignableLazy nsub nsub_query assignSub (nsub_left, cnstrSub)
      cnstr =
      let nsub_query' = querySubId () in
      let cref = ref cnstr in
      let rec assign' nsub_query nsub =
        let (nsub_query_left, nsub_left1) =
          S.differenceModulo nsub_query nsub
            (fun (Glocal_u) ->
               fun (l, __U) ->
                 fun l' ->
                   fun (__T) ->
                     (:=) cref assign
                       (((l, Glocal_u, (__U, I.id), __T, nsub_query',
                           assignSub, cnstrSub, (!cref)))
                       (* = l' *))) in
        let nsub_left' =
          S.update nsub_left1
            (fun l -> fun (__U) -> (l, (normalizeNExp (__U, cnstrSub)))) in
        Some
          ((S.union nsub_query_left nsub_query'),
            ((S.union nsub_left nsub_left'), cnstrSub), (!cref)) in
      try assign' (nsub_query, nsub) with | Assignment msg -> NONE
    let rec assignableEager nsub nsub_query assignSub cnstrSub cnstr =
      let nsub_query' = querySubId () in
      let cref = ref cnstr in
      let rec assign' nsub_query nsub =
        let (nsub_query_left, nsub_left) =
          S.differenceModulo nsub_query nsub
            (fun (Glocal_u) ->
               fun (l, __U) ->
                 fun l' ->
                   fun (__T) ->
                     (:=) cref assign
                       (((l', Glocal_u, (__U, I.id), __T, nsub_query',
                           assignSub, cnstrSub, (!cref)))
                       (* = l *))) in
        let _ =
          S.forall nsub_left
            (fun nv ->
               fun (nvaronly, __U) ->
                 match S.lookup cnstrSub nv with
                 | NONE -> raise (Error "Left-over nsubstitution")
                 | Some (AVar (__A)) ->
                     (:=) __A Some (normalizeNExp (__U, cnstrSub))) in
        ((Some ((S.union nsub_query_left nsub_query'), cnstrSub, (!cref)))
          (* normalize nsub_left (or require that it is normalized
             collect all left-over nsubs and later combine it with cnstrsub
           *)
          (* cnstr[rsub] *)(* nsub_goal1 = rgoal u nsub_goal'  remaining substitutions to be checked *)) in
      try assign' (nsub_query, nsub) with | Assignment msg -> NONE
    let rec unifyW __45__ __46__ __47__ =
      match (__45__, __46__, __47__) with
      | (__G, ((AVar ({ contents = NONE } as r) as X), Shift 0), __Us2) ->
          (:=) r Some (I.EClo __Us2)
      | (__G, ((AVar ({ contents = NONE } as r) as X), s),
         ((__U, s2) as Us2)) ->
          (print "unifyW -- not s = Id\n";
           print
             (((^) "Us2 = " Print.expToString (__G, (I.EClo __Us2))) ^ "\n");
           (:=) r Some (I.EClo __Us2))
      | (__G, __Xs1, __Us2) -> Unify.unifyW (__G, __Xs1, __Us2)(* Xs1 should not contain any uninstantiated AVar anymore *)
    let rec unify (__G) (__Xs1) (__Us2) =
      unifyW (__G, (Whnf.whnf __Xs1), (Whnf.whnf __Us2))
    let rec unifiable (__G) (__Us1) (__Us2) =
      try unify (__G, __Us1, __Us2); true__ with | Unify msg -> false__
    let rec ctxToExplicitSub __48__ __49__ __50__ __51__ =
      match (__48__, __49__, __50__, __51__) with
      | (i, Gquery, I.Null, asub) -> I.id
      | (i, Gquery, Decl (Gclause, Dec (_, __A)), asub) ->
          let s = ctxToExplicitSub ((i + 1), Gquery, Gclause, asub) in
          let EVar (__X', _, _, _) as U' =
            I.newEVar (Gquery, (I.EClo (__A, s))) in
          ((match S.lookup asub i with
            | NONE -> ()
            | Some (Assign (Glocal_u, __U)) ->
                (:=) __X' Some (raiseType (Glocal_u, __U)));
           I.Dot ((I.Exp __U'), s))
      | (i, Gquery, Decl (Gclause, ADec (_, d)), asub) ->
          let AVar (__X') as U' = I.newAVar () in
          ((((match S.lookup asub i with
              | NONE -> ()
              | Some (Assign (Glocal_u, __U)) -> (:=) __X' Some __U);
             I.Dot
               ((I.Exp (I.EClo (__U', (I.Shift (~ d))))),
                 (ctxToExplicitSub ((i + 1), Gquery, Gclause, asub)))))
            (* d = I.ctxLength Glocal_u *))
    let rec solveAuxG __52__ __53__ __54__ =
      match (__52__, __53__, __54__) with
      | (C.Trivial, s, Gquery) -> true__
      | (UnifyEq (Glocal, e1, __N, eqns), s, Gquery) ->
          let __G = compose' (Glocal, Gquery) in
          let s' = shift (Glocal, s) in
          if unifiable (__G, (__N, s'), (e1, s'))
          then solveAuxG (eqns, s, Gquery)
          else false__(* succeed *)
    let rec solveCnstr __55__ __56__ __57__ __58__ =
      match (__55__, __56__, __57__, __58__) with
      | (Gquery, Gclause, nil, s) -> true__
      | (Gquery, Gclause, (Eqn (Glocal, __U1, __U2))::Cnstr, s) ->
          (Unify.unifiable
             ((compose' (Gquery, Glocal)), (__U1, I.id),
               (__U2, (shift (Glocal, s)))))
            && (solveCnstr (Gquery, Gclause, Cnstr, s))
    let rec solveResiduals (Gquery) (Gclause) (CGoals
      (AuxG, cid, ConjGoals, i)) asub cnstr' sc =
      let s = ctxToExplicitSub (1, Gquery, Gclause, asub) in
      let success =
        (solveAuxG (AuxG, s, Gquery)) &&
          (solveCnstr (Gquery, Gclause, cnstr', s)) in
      if success
      then sc ((((ConjGoals, s), cid))(* B *))
      else ()
    let rec ithChild (CGoals (_, _, _, i)) n = i = n
    let rec retrieveChild num (Child) nsub_query assignSub cnstr (Gquery) sc
      =
      let rec retrieve __59__ __60__ __61__ __62__ __63__ =
        match (__59__, __60__, __61__, __62__, __63__) with
        | (Leaf (nsub, Gclause, Residuals), nsub_query, assignSub, cnstrSub,
           cnstr) ->
            (((match assignableEager
                       (nsub, nsub_query, assignSub, cnstrSub, cnstr)
               with
               | NONE -> ()
               | Some (nsub_query', cnstrSub', cnstr') ->
                   ((if isId nsub_query'
                     then
                       (if ithChild (Residuals, (!num))
                        then
                          solveResiduals
                            (Gquery, Gclause, Residuals, assignSub, cnstr',
                              sc)
                        else
                          CSManager.trail
                            (fun () ->
                               solveResiduals
                                 (Gquery, Gclause, Residuals, assignSub,
                                   cnstr', sc)))
                     else raise (Error "Left-over normal substitutions!"))
                   (* cnstrSub' = empty? by invariant *)
                   (* LCO optimization *))))
            (* destructively updates assignSub, might initiate backtracking  *))
        | (Node (nsub, Children), nsub_query, assignSub, cnstrSub, cnstr) ->
            (((match assignableEager
                       (nsub, nsub_query, assignSub, cnstrSub, cnstr)
               with
               | NONE -> ()
               | Some (nsub_query', cnstrSub', cnstr') ->
                   S.forall Children
                     (fun n ->
                        fun (Child) ->
                          retrieve
                            (Child, nsub_query', (S.copy assignSub),
                              (S.copy cnstrSub'), cnstr'))))
            (* destructively updates nsub_query, assignSub,  might fail and initiate backtracking *)
            (* we must undo any changes to assignSub and whatever else is destructively updated,
             cnstrSub?, cnstr? or keep them separate from different branches!*)) in
      retrieve (Child, nsub_query, assignSub, (cnstrSubId ()), cnstr)
    let rec retrieval n (Node (s, Children) as STree) (__G) r sc =
      let (nsub_query, assignSub) = ((querySubId ()), (assignSubId ())) in
      S.insert nsub_query (1, (I.Null, (Body, r)));
      S.forall Children
        (fun _ ->
           fun (__C) ->
             retrieveChild (n, __C, nsub_query, assignSub, nil, __G, sc))
      (* s = id *)
    let rec retrieveAll num (Child) nsub_query assignSub cnstr candSet =
      let i = ref 0 in
      let rec retrieve __64__ __65__ __66__ __67__ __68__ =
        match (__64__, __65__, __66__, __67__, __68__) with
        | (Leaf (nsub, Gclause, Residuals), nsub_query, assignSub,
           (nsub_left, cnstrSub), cnstr) ->
            (((match assignableLazy
                       (nsub, nsub_query, assignSub, (nsub_left, cnstrSub),
                         cnstr)
               with
               | NONE -> ()
               | Some (nsub_query', (nsub_left', cnstrSub'), cnstr') ->
                   ((if isId nsub_query'
                     then
                       (((!) ((:=) i) i) + 1;
                        S.insert candSet
                          ((!i),
                            (assignSub, nsub_left', cnstrSub', cnstr',
                              Gclause, Residuals));
                        ())
                     else raise (Error "Left-over normal substitutions!"))
                   (* LCO optimization *))))
            (* destructively updates assignSub, might initiate backtracking  *))
        | (Node (nsub, Children), nsub_query, assignSub,
           (nsub_left, cnstrSub), cnstr) ->
            (((match assignableLazy
                       (nsub, nsub_query, assignSub, (nsub_left, cnstrSub),
                         cnstr)
               with
               | NONE -> ()
               | Some (nsub_query', (nsub_left', cnstrSub'), cnstr') ->
                   S.forall Children
                     (fun n ->
                        fun (Child) ->
                          retrieve
                            (Child, nsub_query', (S.copy assignSub),
                              ((S.copy nsub_left'), (S.copy cnstrSub')),
                              cnstr'))))
            (* destructively updates nsub_query, assignSub,  might fail and initiate backtracking *)
            (* we must undo any changes to assignSub and whatever else is destructively updated,
             cnstrSub?, cnstr? or keep them separate from different branches!*)) in
      retrieve
        (Child, nsub_query, assignSub, ((nid ()), (cnstrSubId ())), cnstr)
    let rec retrieveCandidates n (Node (s, Children) as STree) (Gquery) r sc
      =
      let (nsub_query, assignSub) = ((querySubId ()), (assignSubId ())) in
      let candSet = S.new__ () in
      let rec solveCandidate i candSet =
        match S.lookup candSet i with
        | NONE -> ((())
            (* print "No candidate left anymore\n" ;*))
        | Some
            (((assignSub, nsub_left, cnstrSub, cnstr, Gclause, Residuals))
            (* CGoals(AuxG, cid, ConjGoals, i) *)) ->
            (CSManager.trail
               (fun () ->
                  S.forall nsub_left
                    (fun nv ->
                       fun (l, __U) ->
                         match S.lookup cnstrSub nv with
                         | NONE -> raise (Error "Left-over nsubstitution")
                         | Some (AVar (__A)) -> (:=) __A Some __U);
                  solveResiduals
                    (Gquery, Gclause, Residuals, assignSub, cnstr, sc));
             solveCandidate ((((i + 1), candSet))
               (* sc = (fn S => (O::S)) *))) in
      ((S.insert nsub_query (1, (I.Null, (Body, r)));
        S.forall Children
          (fun _ ->
             fun (__C) ->
               retrieveAll (n, __C, nsub_query, assignSub, nil, candSet));
        solveCandidate (1, candSet))
        (* execute one by one all candidates : here ! *))
      (* s = id *)
    let rec matchSig a (__G) ((Root (Ha, __S), s) as ps) sc =
      let (n, Tree) = Array.sub (indexArray, a) in
      ((retrieveCandidates (n, (!Tree), __G, (I.EClo ps), sc))
        (* retrieval (n, !Tree, G, I.EClo(ps), sc)   *))
    let rec matchSigIt a (__G) ((Root (Ha, __S), s) as ps) sc =
      let (n, Tree) = Array.sub (indexArray, a) in
      retrieval (n, (!Tree), __G, (I.EClo ps), sc)
    let rec sProgReset () =
      nctr := 1;
      Array.modify
        (fun n ->
           fun (Tree) -> n := 0; (!) ((:=) Tree) (makeTree ()); (n, Tree))
        indexArray
    let rec sProgInstall a (Head (__E, __G, Eqs, cid)) (__R) =
      let (n, Tree) = Array.sub (indexArray, a) in
      let nsub_goal = S.new__ () in
      S.insert nsub_goal (1, (Body, __E));
      (:=) Tree insert
        ((!Tree), nsub_goal, (__G, (CGoals (Eqs, cid, __R, ((!n) + 1)))));
      ((!) ((:=) n) n) + 1
    let sProgReset = sProgReset
    let sProgInstall = sProgInstall
    let matchSig = matchSigIt
  end ;;
