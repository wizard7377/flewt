
module type SUBTREE  =
  sig
    type nonrec nvar =
      ((int)(*! structure RBSet : RBSET  !*)(*! structure CompSyn : COMPSYN     !*)
      (*! structure IntSyn : INTSYN !*)(* Author: Brigitte Pientka *)
      (* Substitution Trees *))
    type nonrec bvar =
      ((int)(* index for normal variables *))
    type nonrec bdepth =
      ((int)(* index for bound variables *))
    type typeLabel =
      | TypeLabel 
      | Body (*  type normalSubsts = (IntSyn.Dec IntSyn.Ctx * IntSyn.Exp) RBSet.ordSet *)
    (* normal (linear) substitutions *)(* depth of locally bound variables *)
    type nonrec normalSubsts = (typeLabel * IntSyn.__Exp) RBSet.ordSet
    type nonrec querySubsts =
      (IntSyn.__Dec IntSyn.__Ctx * (typeLabel * IntSyn.__Exp)) RBSet.ordSet
    type __CGoal =
      | CGoals of (CompSyn.__AuxGoal * IntSyn.cid * CompSyn.__Conjunction *
      int) 
    type __AssSub =
      | Assign of
      (((IntSyn.__Dec)(* assignable (linear) subsitutions *))
      IntSyn.__Ctx * IntSyn.__Exp) 
    type nonrec assSubsts = __AssSub RBSet.ordSet
    type __Cnstr =
      | Eqn of (((IntSyn.__Dec)(* key = int = bvar *))
      IntSyn.__Ctx * IntSyn.__Exp * IntSyn.__Exp) 
    type __Tree =
      | Leaf of (normalSubsts * IntSyn.__Dec IntSyn.__Ctx * __CGoal) 
      | Node of (normalSubsts * __Tree RBSet.ordSet) 
    val indexArray :
      (((int)(*  type candidate = assSubsts * normalSubsts * cnstrSubsts * Cnstr * IntSyn.Dec IntSyn.Ctx * CGoal *))
        ref * __Tree ref) Array.array
    val sProgReset : unit -> unit
    val sProgInstall :
      (IntSyn.cid * CompSyn.__CompHead * CompSyn.__Conjunction) -> unit
    val matchSig :
      (IntSyn.cid * IntSyn.__Dec IntSyn.__Ctx * IntSyn.eclo *
        (((CompSyn.__Conjunction * IntSyn.__Sub) * IntSyn.cid) -> unit)) ->
        unit
  end;;




module SubTree(SubTree:sig
                         module Whnf : WHNF
                         module Unify : UNIFY
                         module Print : PRINT
                         module CPrint : CPRINT
                         module Formatter : FORMATTER
                         module Names : NAMES
                         module CSManager :
                         ((CS_MANAGER)(* Substitution Tree indexing *)
                         (* Author: Brigitte Pientka *)
                         (*! structure IntSyn' : INTSYN !*)
                         (*!structure CompSyn' : COMPSYN !*)
                         (*!  sharing CompSyn'.IntSyn = IntSyn' !*)
                         (*!  sharing Whnf.IntSyn = IntSyn' !*)(*!  sharing Unify.IntSyn = IntSyn'!*)
                         (*!  sharing Print.IntSyn = IntSyn' !*)
                         (* CPrint currently unused *)
                         (*!  sharing CPrint.IntSyn = IntSyn' !*)
                         (*!  sharing CPrint.CompSyn = CompSyn' !*)
                         (* unused *)(*!  sharing Print.Formatter = Formatter !*)
                         (* unused *)(*!  sharing Names.IntSyn = IntSyn' !*))
                       end) : SUBTREE =
  struct
    type nonrec nvar =
      ((int)(*!  structure RBSet = RBSet !*)(*!  structure CompSyn = CompSyn' !*)
      (*!  structure IntSyn = IntSyn' !*)(*! structure RBSet : RBSET !*)
      (*!  sharing CSManager.IntSyn = IntSyn'!*))
    type nonrec bvar =
      ((int)(* index for normal variables *))
    type nonrec bdepth =
      ((int)(* index for bound variables *))
    type typeLabel =
      | TypeLabel 
      | Body (* typeLabel distinguish between declarations (=type labels)
   which are subject to indexing, but only the internal nvars will
   be instantiated during asssignment and Body which are subject to
   indexing and existential variables and nvars will be instantiated
   during assignment
 *)
    (* A substitution tree is defined as follows:
     Node := Leaf (ns, G, sgoal) | Node(ns, Set of Nodes)
     normal linear modal substitutions ns := . | R/n, ns

   For each node we have the following invariant:
        S |- ns : S'    i.e. ns substitutes for internal variables
        G'|- as : G     i.e. as substitutes for assignable variables
        G |- qs : G     i.e. qs substitutes for modal variables
                             occuring in the query term

  NOTE: Since lambda-abstraction carries a type-label, we must generalize
   the type-label, and hence perform indexing on type-labels. -- On
   the other hand during unification or assignment an instantiation of
   the existential variables occurring in the type-label is not
   necessary. They must have been instantiated already. However, we
   must still instantiate internal nvars.

  Example: given the following two terms:
   hilnd ((A imp (B imp C)) imp ((A imp B) imp (A imp C))) (s) (impi [u:nd (A imp B imp C)]
                     impi [v:nd (A imp B)]
                     impi [w:nd A] impe (impe u w) (impe v w)).

   hilnd (A imp (B imp A)) (s) (impi [u:nd A]
                     impi [v:nd B]
                     impi [w:nd A] impe (impe u w) (impe v w)).


  if we generalize (A imp B imp C) then we must obtain

  hilnd (n1 imp (n2 imp n3)) (s) (impi [u:nd n4]
             impi [v:nd n5]
             impi [w:nd A] impe (impe u w) (impe v w)).

  otherwise we could obtain a term which is not well-typed.

  *)
    (* depth of locally bound variables *)
    type nonrec normalSubsts = (typeLabel * IntSyn.__Exp) RBSet.ordSet
    type __AssSub =
      | Assign of (((IntSyn.__Dec)(* key = int = bvar *))
      IntSyn.__Ctx * IntSyn.__Exp) 
    type nonrec assSubsts = __AssSub RBSet.ordSet
    type nonrec querySubsts =
      (((IntSyn.__Dec)(* key = int = bvar *)) IntSyn.__Ctx *
        (typeLabel * IntSyn.__Exp)) RBSet.ordSet
    type __Cnstr =
      | Eqn of (IntSyn.__Dec IntSyn.__Ctx * IntSyn.__Exp * IntSyn.__Exp) 
    type nonrec cnstrSubsts = IntSyn.__Exp RBSet.ordSet
    type __CGoal =
      | CGoals of
      (((CompSyn.__AuxGoal)(* key = int = bvar *)) *
      IntSyn.cid * CompSyn.__Conjunction * int) 
    type genType =
      | Top 
      | Regular (* cid of clause *)
    type __Tree =
      | Leaf of (normalSubsts * IntSyn.__Dec IntSyn.__Ctx * __CGoal) 
      | Node of (normalSubsts * __Tree RBSet.ordSet) 
    type nonrec candidate =
      (assSubsts * normalSubsts * cnstrSubsts * __Cnstr * IntSyn.__Dec
        IntSyn.__Ctx * __CGoal)
    let (nid :
      unit ->
        ((normalSubsts)(* Initialization of substitutions *)))
      = RBSet.new__
    let (assignSubId : unit -> assSubsts) = RBSet.new__
    let (cnstrSubId : unit -> cnstrSubsts) = RBSet.new__
    let (querySubId : unit -> querySubsts) = RBSet.new__
    let rec isId ((s)(* Identity substitution *)) =
      RBSet.isEmpty s
    let rec makeTree
      ((())(* Initialize substitution tree *)) =
      ref (Node ((nid ()), (RBSet.new__ ())))
    let rec noChildren
      ((C)(* Test if node has any children *)) =
      RBSet.isEmpty C
    let ((indexArray)(* Index array

   Invariant:
   For all type families  a  indexArray = [a1,...,an]
   where a1,...,an is a substitution tree consisting of all constants
   for target family ai

   *))
      =
      Array.tabulate
        (Global.maxCid, (function | i -> ((ref 0), (makeTree ()))))
    module I = IntSyn
    module C = CompSyn
    module S = RBSet
    exception Error of string 
    exception Assignment of string 
    exception Generalization of string 
    let rec cidFromHead = function | Const c -> c | Def c -> c
    let rec dotn =
      function | (0, s) -> s | (i, s) -> dotn ((i - 1), (I.dot1 s))
    let rec compose' =
      function
      | (IntSyn.Null, G) -> G
      | (Decl (G, D), G') -> IntSyn.Decl ((compose' (G, G')), D)
    let rec shift =
      function
      | (IntSyn.Null, s) -> s
      | (Decl (G, D), s) -> I.dot1 (shift (G, s))
    let rec raiseType =
      function
      | (I.Null, V) -> V
      | (Decl (G, D), V) -> raiseType (G, (I.Lam (D, V)))
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
    let rec eqHeads =
      function
      | (Const k, Const k') -> k = k'
      | (BVar k, BVar k') -> k = k'
      | (Def k, Def k') -> k = k'
      | (_, _) -> false__
    let rec compatible (label, T, U, rho_t, rho_u) =
      let genExp =
        function
        | (label, b, (NVar n as T), (Root (H, S) as U)) ->
            (S.insert rho_u (n, (label, U)); T)
        | (label, b, (Root (H1, S1) as T), (Root (H2, S2) as U)) ->
            if eqHeads (H1, H2)
            then I.Root (H1, (genSpine (label, b, S1, S2)))
            else
              (match b with
               | Regular ->
                   (S.insert rho_t (((!nctr) + 1), (label, T));
                    S.insert rho_u (((!nctr) + 1), (label, U));
                    newNVar ())
               | _ -> raise (Generalization "Should never happen!"))
        | (label, b, Lam ((Dec (N, A1) as D1), T1), Lam
           ((Dec (_, A2) as D2), U2)) ->
            I.Lam
              ((I.Dec (N, (genExp (TypeLabel, Regular, A1, A2)))),
                (genExp (label, b, T1, U2)))
        | (label, b, Pi (((D1, I.No) as DD1), E1), Pi
           (((D2, I.No) as DD2), E2)) ->
            I.Pi
              (((genDec (TypeLabel, Regular, D1, D2)), I.No),
                (genExp (label, b, E1, E2)))
        | (label, b, Pi (((D1, I.Maybe) as DD1), E1), Pi
           (((D2, I.Maybe) as DD2), E2)) ->
            I.Pi
              (((genDec (TypeLabel, Regular, D1, D2)), I.Maybe),
                (genExp (label, b, E1, E2)))
        | (label, b, Pi (((D1, I.Meta) as DD1), E1), Pi
           (((D2, I.Meta) as DD2), E2)) ->
            I.Pi
              (((genDec (TypeLabel, Regular, D1, D2)), I.Meta),
                (genExp (label, b, E1, E2)))
        | (label, b, T, U) ->
            raise
              (Generalization
                 "Cases where U= EVar or EClo should never happen!")
      and genSpine =
        function
        | (label, b, I.Nil, I.Nil) -> I.Nil
        | (label, b, App (T, S1), App (U, S2)) ->
            I.App ((genExp (label, b, T, U)), (genSpine (label, b, S1, S2)))
      and genDec (label, b, Dec (N, E1), Dec (N', E2)) =
        I.Dec (N, (genExp (label, b, E1, E2))) in
      let genTop =
        function
        | (label, (Root (H1, S1) as T), (Root (H2, S2) as U)) ->
            if eqHeads (H1, H2)
            then I.Root (H1, (genSpine (label, Regular, S1, S2)))
            else
              raise (Generalization "Top-level function symbol not shared")
        | (label, Lam ((Dec (N, A1) as D1), T1), Lam
           ((Dec (_, A2) as D2), U2)) ->
            I.Lam
              ((I.Dec (N, (genExp (label, Regular, A1, A2)))),
                (genTop (label, T1, U2)))
        | (_, _, _) ->
            raise (Generalization "Top-level function symbol not shared") in
      try SOME (genTop (label, T, U)) with | Generalization msg -> NONE
    let rec compatibleSub (nsub_t, nsub_e) =
      let (sg, rho_t, rho_e) = ((nid ()), (nid ()), (nid ())) in
      let _ =
        S.forall nsub_e
          (function
           | (nv, (l', E)) ->
               (match S.lookup nsub_t nv with
                | SOME (l, T) ->
                    if l = l'
                    then
                      (match compatible (l, T, E, rho_t, rho_e) with
                       | NONE ->
                           (S.insert rho_t (nv, (l, T));
                            S.insert rho_e (nv, (l, E)))
                       | SOME (T') -> S.insert sg (nv, (l, T')))
                    else raise (Generalization "Labels don't agree\n")
                | NONE -> S.insert rho_e (nv, (l', E)))) in
      if isId sg then NONE else SOME (sg, rho_t, rho_e)
    let rec mkNode =
      function
      | (Node (_, Children), sg, rho1, ((G, RC) as GR), rho2) ->
          let c = S.new__ () in
          (S.insertList c
             [(1, (Node (rho1, Children))); (2, (Leaf (rho2, G, RC)))];
           Node (sg, c))
      | (Leaf (_, G1, RC1), sg, rho1, ((G2, RC2) as GR), rho2) ->
          let c = S.new__ () in
          (S.insertList c
             [(1, (Leaf (rho1, G1, RC1))); (2, (Leaf (rho2, G2, RC2)))];
           Node (sg, c))
    let rec compareChild
      (children, (n, child), nsub_t, nsub_e,
       ((G_clause2, Res_clause2) as GR))
      =
      match compatibleSub (nsub_t, nsub_e) with
      | NONE ->
          S.insert children
            ((n + 1), (Leaf (nsub_e, G_clause2, Res_clause2)))
      | SOME (sg, rho1, rho2) ->
          if isId rho1
          then
            (if isId rho2
             then
               S.insertShadow children
                 (n, (mkNode (child, sg, rho1, GR, rho2)))
             else S.insertShadow children (n, (insert (child, rho2, GR))))
          else
            S.insertShadow children (n, (mkNode (child, sg, rho1, GR, rho2)))
    let rec insert =
      function
      | ((Leaf (nsub_t, G_clause1, R1) as N), nsub_e,
         ((G_clause2, R2) as GR)) ->
          (match compatibleSub (nsub_t, nsub_e) with
           | NONE -> raise (Error "Leaf is not compatible substitution r")
           | SOME (sg, rho1, rho2) -> mkNode (N, sg, rho1, GR, rho2))
      | ((Node (_, children) as N), nsub_e, ((G_clause2, RC) as GR)) ->
          if noChildren children
          then (S.insert children (1, (Leaf (nsub_e, G_clause2, RC))); N)
          else
            (match S.last children with
             | (n, (Node (nsub_t, children') as child)) ->
                 (compareChild (children, (n, child), nsub_t, nsub_e, GR); N)
             | (n, (Leaf (nsub_t, G1, RC1) as child)) ->
                 (compareChild (children, (n, child), nsub_t, nsub_e, GR); N))
    let rec normalizeNExp =
      function
      | (NVar n, csub) -> let A = I.newAVar () in (S.insert csub (n, A); A)
      | (Root (H, S), nsub) -> I.Root (H, (normalizeNSpine (S, nsub)))
      | (Lam (D, U), nsub) ->
          I.Lam ((normalizeNDec (D, nsub)), (normalizeNExp (U, nsub)))
      | (Pi ((D, P), U), nsub) ->
          I.Pi (((normalizeNDec (D, nsub)), P), (normalizeNExp (U, nsub)))
    let rec normalizeNSpine =
      function
      | (I.Nil, _) -> I.Nil
      | (App (U, S), nsub) ->
          I.App ((normalizeNExp (U, nsub)), (normalizeNSpine (S, nsub)))
    let rec normalizeNDec (Dec (N, E), nsub) =
      I.Dec (N, (normalizeNExp (E, nsub)))
    let rec assign
      (nvaronly, Glocal_u1, Us1, U2, nsub_goal, asub, csub, cnstr) =
      let depth = I.ctxLength Glocal_u1 in
      let assignHead
        (nvaronly, depth, Glocal_u1, ((Root (H1, S1), s1) as Us1),
         (Root (H2, S2) as U2), cnstr)
        =
        match (H1, H2) with
        | (Const c1, Const c2) ->
            if c1 = c2
            then
              assignSpine (nvaronly, depth, Glocal_u1, (S1, s1), S2, cnstr)
            else raise (Assignment "Constant clash")
        | (Skonst c1, Skonst c2) ->
            if c1 = c2
            then
              assignSpine (nvaronly, depth, Glocal_u1, (S1, s1), S2, cnstr)
            else raise (Assignment "Skolem constant clash")
        | (Def d1, _) ->
            assignExp
              (nvaronly, depth, Glocal_u1, (Whnf.expandDef Us1), U2, cnstr)
        | (FgnConst (cs1, ConDec (n1, _, _, _, _, _)), FgnConst
           (cs2, ConDec (n2, _, _, _, _, _))) ->
            if (cs1 = cs2) && (n1 = n2)
            then cnstr
            else raise (Assignment "Foreign Constant clash")
        | (FgnConst (cs1, ConDef (n1, _, _, W1, _, _, _)), FgnConst
           (cs2, ConDef (n2, _, _, V, W2, _, _))) ->
            if (cs1 = cs2) && (n1 = n2)
            then cnstr
            else assignExp (nvaronly, depth, Glocal_u1, (W1, s1), W2, cnstr)
        | (FgnConst (_, ConDef (_, _, _, W1, _, _, _)), _) ->
            assignExp (nvaronly, depth, Glocal_u1, (W1, s1), U2, cnstr)
        | (_, FgnConst (_, ConDef (_, _, _, W2, _, _, _))) ->
            assignExp (nvaronly, depth, Glocal_u1, Us1, W2, cnstr)
        | (_, _) -> raise (Assignment "Head mismatch ")
      and assignExpW =
        function
        | (nvaronly, depth, Glocal_u1, (Uni (L1), s1), Uni (L2), cnstr) ->
            cnstr
        | (nvaronly, depth, Glocal_u1, Us1, NVar n, cnstr) ->
            (S.insert nsub_goal (n, (Glocal_u1, (nvaronly, (I.EClo Us1))));
             cnstr)
        | (Body, depth, Glocal_u1, ((Root (H1, S1), s1) as Us1),
           (Root (H2, S2) as U2), cnstr) ->
            (match H2 with
             | BVar k2 ->
                 if k2 > depth
                 then
                   (S.insert asub
                      (((-) k2 I.ctxLength Glocal_u1),
                        (Assign (Glocal_u1, (I.EClo Us1))));
                    cnstr)
                 else
                   (match H1 with
                    | BVar k1 ->
                        if k1 = k2
                        then
                          assignSpine
                            (Body, depth, Glocal_u1, (S1, s1), S2, cnstr)
                        else raise (Assignment "Bound variable clash")
                    | _ -> raise (Assignment "Head mismatch"))
             | _ -> assignHead (Body, depth, Glocal_u1, Us1, U2, cnstr))
        | (TypeLabel, depth, Glocal_u1, ((Root (H1, S1), s1) as Us1),
           (Root (H2, S2) as U2), cnstr) ->
            (match H2 with
             | BVar k2 ->
                 if k2 > depth
                 then cnstr
                 else
                   (match H1 with
                    | BVar k1 ->
                        if k1 = k2
                        then
                          assignSpine
                            (TypeLabel, depth, Glocal_u1, (S1, s1), S2,
                              cnstr)
                        else raise (Assignment "Bound variable clash")
                    | _ -> raise (Assignment "Head mismatch"))
             | _ -> assignHead (TypeLabel, depth, Glocal_u1, Us1, U2, cnstr))
        | (nvaronly, depth, Glocal_u1, Us1, (Root (BVar k2, S) as U2), cnstr)
            ->
            if k2 > depth
            then
              (match nvaronly with
               | TypeLabel -> cnstr
               | Body ->
                   (S.insert asub
                      ((k2 - depth), (Assign (Glocal_u1, (I.EClo Us1))));
                    cnstr))
            else
              (match nvaronly with
               | TypeLabel -> cnstr
               | Body ->
                   (match Us1 with
                    | (EVar (r, _, V, Cnstr), s) ->
                        let U2' = normalizeNExp (U2, csub) in
                        (Eqn (Glocal_u1, (I.EClo Us1), U2')) :: cnstr
                    | (EClo (U, s'), s) ->
                        assignExp
                          (Body, depth, Glocal_u1, (U, (I.comp (s', s))), U2,
                            cnstr)
                    | (FgnExp (_, ops), _) ->
                        let U2' = normalizeNExp (U2, csub) in
                        (Eqn (Glocal_u1, (I.EClo Us1), U2')) :: cnstr))
        | (nvaronly, depth, Glocal_u1, (Lam ((Dec (_, A1) as D1), U1), s1),
           Lam ((Dec (_, A2) as D2), U2), cnstr) ->
            let cnstr' =
              assignExp (TypeLabel, depth, Glocal_u1, (A1, s1), A2, cnstr) in
            assignExp
              (nvaronly, (depth + 1),
                (I.Decl (Glocal_u1, (I.decSub (D1, s1)))), (U1, (I.dot1 s1)),
                U2, cnstr')
        | (nvaronly, depth, Glocal_u1,
           (Pi (((Dec (_, A1) as D1), _), U1), s1), Pi
           (((Dec (_, A2) as D2), _), U2), cnstr) ->
            let cnstr' =
              assignExp (TypeLabel, depth, Glocal_u1, (A1, s1), A2, cnstr) in
            assignExp
              (nvaronly, (depth + 1),
                (I.Decl (Glocal_u1, (I.decSub (D1, s1)))), (U1, (I.dot1 s1)),
                U2, cnstr')
        | (nvaronly, depth, Glocal_u1, ((EVar (r, _, V, Cnstr), s) as Us1),
           U2, cnstr) ->
            let U2' = normalizeNExp (U2, csub) in
            (Eqn (Glocal_u1, (I.EClo Us1), U2')) :: cnstr
        | (nvaronly, depth, Glocal_u1, ((EClo (U, s'), s) as Us1), U2, cnstr)
            ->
            assignExp
              (nvaronly, depth, Glocal_u1, (U, (I.comp (s', s))), U2, cnstr)
        | (nvaronly, depth, Glocal_u1, ((FgnExp (_, ops), _) as Us1), U2,
           cnstr) ->
            let U2' = normalizeNExp (U2, csub) in
            (Eqn (Glocal_u1, (I.EClo Us1), U2')) :: cnstr
        | (nvaronly, depth, Glocal_u1, Us1, (FgnExp (_, ops) as U2), cnstr)
            -> (Eqn (Glocal_u1, (I.EClo Us1), U2)) :: cnstr
      and assignSpine =
        function
        | (nvaronly, depth, Glocal_u1, (I.Nil, _), I.Nil, cnstr) -> cnstr
        | (nvaronly, depth, Glocal_u1, (SClo (S1, s1'), s1), S, cnstr) ->
            assignSpine
              (nvaronly, depth, Glocal_u1, (S1, (I.comp (s1', s1))), S,
                cnstr)
        | (nvaronly, depth, Glocal_u1, (App (U1, S1), s1), App (U2, S2),
           cnstr) ->
            let cnstr' =
              assignExp (nvaronly, depth, Glocal_u1, (U1, s1), U2, cnstr) in
            assignSpine (nvaronly, depth, Glocal_u1, (S1, s1), S2, cnstr')
      and assignExp (nvaronly, depth, Glocal_u1, Us1, U2, cnstr) =
        assignExpW (nvaronly, depth, Glocal_u1, (Whnf.whnf Us1), U2, cnstr) in
      assignExp (nvaronly, depth, Glocal_u1, Us1, U2, cnstr)
    let rec assignableLazy
      (nsub, nsub_query, assignSub, (nsub_left, cnstrSub), cnstr) =
      let nsub_query' = querySubId () in
      let cref = ref cnstr in
      let assign' (nsub_query, nsub) =
        let (nsub_query_left, nsub_left1) =
          S.differenceModulo nsub_query nsub
            (function
             | (Glocal_u, (l, U)) ->
                 (function
                  | (l', T) ->
                      (:=) cref assign
                        (l, Glocal_u, (U, I.id), T, nsub_query', assignSub,
                          cnstrSub, (!cref)))) in
        let nsub_left' =
          S.update nsub_left1
            (function | (l, U) -> (l, (normalizeNExp (U, cnstrSub)))) in
        SOME
          ((S.union nsub_query_left nsub_query'),
            ((S.union nsub_left nsub_left'), cnstrSub), (!cref)) in
      try assign' (nsub_query, nsub) with | Assignment msg -> NONE
    let rec assignableEager (nsub, nsub_query, assignSub, cnstrSub, cnstr) =
      let nsub_query' = querySubId () in
      let cref = ref cnstr in
      let assign' (nsub_query, nsub) =
        let (nsub_query_left, nsub_left) =
          S.differenceModulo nsub_query nsub
            (function
             | (Glocal_u, (l, U)) ->
                 (function
                  | (l', T) ->
                      (:=) cref assign
                        (l', Glocal_u, (U, I.id), T, nsub_query', assignSub,
                          cnstrSub, (!cref)))) in
        let _ =
          S.forall nsub_left
            (function
             | (nv, (nvaronly, U)) ->
                 (match S.lookup cnstrSub nv with
                  | NONE -> raise (Error "Left-over nsubstitution")
                  | SOME (AVar (A)) ->
                      (:=) A SOME (normalizeNExp (U, cnstrSub)))) in
        SOME ((S.union nsub_query_left nsub_query'), cnstrSub, (!cref)) in
      try assign' (nsub_query, nsub) with | Assignment msg -> NONE
    let rec unifyW =
      function
      | (G, ((AVar (ref (NONE) as r) as X), Shift 0), Us2) ->
          (:=) r SOME (I.EClo Us2)
      | (G, ((AVar (ref (NONE) as r) as X), s), ((U, s2) as Us2)) ->
          (print "unifyW -- not s = Id\n";
           print (((^) "Us2 = " Print.expToString (G, (I.EClo Us2))) ^ "\n");
           (:=) r SOME (I.EClo Us2))
      | (G, Xs1, Us2) -> Unify.unifyW (G, Xs1, Us2)
    let rec unify (G, Xs1, Us2) =
      unifyW (G, (Whnf.whnf Xs1), (Whnf.whnf Us2))
    let rec unifiable (G, Us1, Us2) =
      try unify (G, Us1, Us2); true__ with | Unify msg -> false__
    let rec ctxToExplicitSub =
      function
      | (i, Gquery, I.Null, asub) -> I.id
      | (i, Gquery, Decl (Gclause, Dec (_, A)), asub) ->
          let s = ctxToExplicitSub ((i + 1), Gquery, Gclause, asub) in
          let EVar (X', _, _, _) as U' = I.newEVar (Gquery, (I.EClo (A, s))) in
          ((match S.lookup asub i with
            | NONE -> ()
            | SOME (Assign (Glocal_u, U)) ->
                (:=) X' SOME (raiseType (Glocal_u, U)));
           I.Dot ((I.Exp U'), s))
      | (i, Gquery, Decl (Gclause, ADec (_, d)), asub) ->
          let AVar (X') as U' = I.newAVar () in
          ((match S.lookup asub i with
            | NONE -> ()
            | SOME (Assign (Glocal_u, U)) -> (:=) X' SOME U);
           I.Dot
             ((I.Exp (I.EClo (U', (I.Shift (~ d))))),
               (ctxToExplicitSub ((i + 1), Gquery, Gclause, asub))))
    let rec solveAuxG =
      function
      | (C.Trivial, s, Gquery) -> true__
      | (UnifyEq (Glocal, e1, N, eqns), s, Gquery) ->
          let G = compose' (Glocal, Gquery) in
          let s' = shift (Glocal, s) in
          if unifiable (G, (N, s'), (e1, s'))
          then solveAuxG (eqns, s, Gquery)
          else false__
    let rec solveCnstr =
      function
      | (Gquery, Gclause, nil, s) -> true__
      | (Gquery, Gclause, (Eqn (Glocal, U1, U2))::Cnstr, s) ->
          (Unify.unifiable
             ((compose' (Gquery, Glocal)), (U1, I.id),
               (U2, (shift (Glocal, s)))))
            && (solveCnstr (Gquery, Gclause, Cnstr, s))
    let rec solveResiduals
      (Gquery, Gclause, CGoals (AuxG, cid, ConjGoals, i), asub, cnstr', sc) =
      let s = ctxToExplicitSub (1, Gquery, Gclause, asub) in
      let success =
        (solveAuxG (AuxG, s, Gquery)) &&
          (solveCnstr (Gquery, Gclause, cnstr', s)) in
      if success then sc ((ConjGoals, s), cid) else ()
    let rec ithChild (CGoals (_, _, _, i), n) = i = n
    let rec retrieveChild
      (num, Child, nsub_query, assignSub, cnstr, Gquery, sc) =
      let retrieve =
        function
        | (Leaf (nsub, Gclause, Residuals), nsub_query, assignSub, cnstrSub,
           cnstr) ->
            (match assignableEager
                     (nsub, nsub_query, assignSub, cnstrSub, cnstr)
             with
             | NONE -> ()
             | SOME (nsub_query', cnstrSub', cnstr') ->
                 if isId nsub_query'
                 then
                   (if ithChild (Residuals, (!num))
                    then
                      solveResiduals
                        (Gquery, Gclause, Residuals, assignSub, cnstr', sc)
                    else
                      CSManager.trail
                        (function
                         | () ->
                             solveResiduals
                               (Gquery, Gclause, Residuals, assignSub,
                                 cnstr', sc)))
                 else raise (Error "Left-over normal substitutions!"))
        | (Node (nsub, Children), nsub_query, assignSub, cnstrSub, cnstr) ->
            (match assignableEager
                     (nsub, nsub_query, assignSub, cnstrSub, cnstr)
             with
             | NONE -> ()
             | SOME (nsub_query', cnstrSub', cnstr') ->
                 S.forall Children
                   (function
                    | (n, Child) ->
                        retrieve
                          (Child, nsub_query', (S.copy assignSub),
                            (S.copy cnstrSub'), cnstr'))) in
      retrieve (Child, nsub_query, assignSub, (cnstrSubId ()), cnstr)
    let rec retrieval (n, (Node (s, Children) as STree), G, r, sc) =
      let (nsub_query, assignSub) = ((querySubId ()), (assignSubId ())) in
      S.insert nsub_query (1, (I.Null, (Body, r)));
      S.forall Children
        (function
         | (_, C) -> retrieveChild (n, C, nsub_query, assignSub, nil, G, sc))
    let rec retrieveAll (num, Child, nsub_query, assignSub, cnstr, candSet) =
      let i = ref 0 in
      let retrieve =
        function
        | (Leaf (nsub, Gclause, Residuals), nsub_query, assignSub,
           (nsub_left, cnstrSub), cnstr) ->
            (match assignableLazy
                     (nsub, nsub_query, assignSub, (nsub_left, cnstrSub),
                       cnstr)
             with
             | NONE -> ()
             | SOME (nsub_query', (nsub_left', cnstrSub'), cnstr') ->
                 if isId nsub_query'
                 then
                   (((!) ((:=) i) i) + 1;
                    S.insert candSet
                      ((!i),
                        (assignSub, nsub_left', cnstrSub', cnstr', Gclause,
                          Residuals));
                    ())
                 else raise (Error "Left-over normal substitutions!"))
        | (Node (nsub, Children), nsub_query, assignSub,
           (nsub_left, cnstrSub), cnstr) ->
            (match assignableLazy
                     (nsub, nsub_query, assignSub, (nsub_left, cnstrSub),
                       cnstr)
             with
             | NONE -> ()
             | SOME (nsub_query', (nsub_left', cnstrSub'), cnstr') ->
                 S.forall Children
                   (function
                    | (n, Child) ->
                        retrieve
                          (Child, nsub_query', (S.copy assignSub),
                            ((S.copy nsub_left'), (S.copy cnstrSub')),
                            cnstr'))) in
      retrieve
        (Child, nsub_query, assignSub, ((nid ()), (cnstrSubId ())), cnstr)
    let rec retrieveCandidates
      (n, (Node (s, Children) as STree), Gquery, r, sc) =
      let (nsub_query, assignSub) = ((querySubId ()), (assignSubId ())) in
      let candSet = S.new__ () in
      let solveCandidate (i, candSet) =
        match S.lookup candSet i with
        | NONE -> ()
        | SOME (assignSub, nsub_left, cnstrSub, cnstr, Gclause, Residuals) ->
            (CSManager.trail
               (function
                | () ->
                    (S.forall nsub_left
                       (function
                        | (nv, (l, U)) ->
                            (match S.lookup cnstrSub nv with
                             | NONE ->
                                 raise (Error "Left-over nsubstitution")
                             | SOME (AVar (A)) -> (:=) A SOME U));
                     solveResiduals
                       (Gquery, Gclause, Residuals, assignSub, cnstr, sc)));
             solveCandidate ((i + 1), candSet)) in
      S.insert nsub_query (1, (I.Null, (Body, r)));
      S.forall Children
        (function
         | (_, C) -> retrieveAll (n, C, nsub_query, assignSub, nil, candSet));
      solveCandidate (1, candSet)
    let rec matchSig (a, G, ((Root (Ha, S), s) as ps), sc) =
      let (n, Tree) = Array.sub (indexArray, a) in
      retrieveCandidates (n, (!Tree), G, (I.EClo ps), sc)
    let rec matchSigIt (a, G, ((Root (Ha, S), s) as ps), sc) =
      let (n, Tree) = Array.sub (indexArray, a) in
      retrieval (n, (!Tree), G, (I.EClo ps), sc)
    let rec sProgReset () =
      nctr := 1;
      Array.modify
        (function
         | (n, Tree) -> (n := 0; (!) ((:=) Tree) (makeTree ()); (n, Tree)))
        indexArray
    let rec sProgInstall (a, Head (E, G, Eqs, cid), R) =
      let (n, Tree) = Array.sub (indexArray, a) in
      let nsub_goal = S.new__ () in
      S.insert nsub_goal (1, (Body, E));
      (:=) Tree insert
        ((!Tree), nsub_goal, (G, (CGoals (Eqs, cid, R, ((!n) + 1)))));
      ((!) ((:=) n) n) + 1
    let ((sProgReset)(* Auxiliary functions *)(*
     Linear normal higher-order patterns
           p ::= n | Root(c, S) | Root(b, S) | Lam (D, p)

                 where n is a linear bound "normalized" variable

          SP ::= p ; S | NIL

     Context
        G : context for bound variables (bvars)
            (type information is stored in the context)
        G ::= . | G, x : A

        S : context for linear normalized bound variables (nvars)
            (no type information is stored in the context)
            (these are the types of the variables definitions)
        S ::= . | S, n

     Templates: G ; S |- p
     Substitutions: G ; S |- nsub : S'

    Let s is a substitution for normalized bound variables (nvars)
    and nsub1 o nsub2 o .... o nsubn = s, s.t.
     G, S_2|- nsub1 : S_1
     G, S_3|- nsub2 : S_2
      ....
     G |- nsubn : S_n
      . ; G |- s : G, S_1

    A term U can be decomposed into a term p together with a sequenence of
    substitutions s1, s2, ..., sn such that s1 o s2 o .... o sn = s
    and the following holds:

    If    G |- U

    then

       G, S |- p

        G |- s : G, S

        G |- p[s]     and p[s] = U

   In addition:
   all expressions in the index are linear, i.e.
   an expression is first linearized before it is inserted into the index
   (this makes retrieving all axpressions from the index which unify with
    a given expression simpler, because we can omit the occurs check)

   *)
      (* ---------------------------------------------------------------*)
      (* nctr = |D| =  #normal variables *)(* most specific linear common generalization *)
      (* compatible (T, U) = (C, rho_u', rho_t') opt
    if
       U, T are both in normal form
       U and T share at least the top function symbol
   then
     C[rho_u'] = U and C[rho_t'] = T
   *)
      (* = S.existsOpt (fn U' => equalTerm (U, U')) *)
      (* find *i in rho_t and rho_u such that T/*i in rho_t and U/*i in rho_u *)
      (* NOTE: by invariant A1 =/= A2 *)(* by invariant A1 =/= A2 *)
      (* compatibleSub(nsub_t, nsub_e) = (sg, rho_t, rho_e) opt

   if dom(nsub_t) <= dom(nsub_e)
      codom(nsub_t) : linear hop in normal form (may contain normal vars)
      codom(nsub_e) : linear hop in normal form (does not contain normal vars)
   then
     nsub_t = [rho_t]sg
     nsub_e = [rho_e]sg

    G_e, Glocal_e |- nsub_e : Sigma
    G_t, Glocal_t |- nsub_t : Sigma'
    Sigma' <= Sigma

    Glocal_e ~ Glocal_t  (have approximately the same type)

   *)
      (* by invariant rho_t = empty, since nsub_t <= nsub_e *)(* by invariant d = d'
                                     therefore T and E have the same approximate type A *)
      (* mkNode (N, sg, r1, (G, RC), r2) = N'    *)(* Insertion *)
      (* compareChild (children, (n, child), n, n', (G, R)) = ()

   *)
      (* sg = nsub_t = nsub_e *)(* sg = nsub_t and nsub_e = sg o rho2 *)
      (* insert (N, nsub_e, (G, R2)) = N'

     if s is the substitution in node N
        G |- nsub_e : S and
    G, S' |- s : S
    then
     N' contains a path n_1 .... n_n s.t.
     [n_n] ...[n_1] s = nsub_e
  *)
      (* initial *)(* retrieval (U,s)
     retrieves all clauses which unify with (U,s)

     backtracking implemented via SML failure continuation

   *)
      (* cannot happen -bp *)(* assign (G, Us1, U2, nsub_goal, asub, csub, cnstr) = cnstr
   if G = local assumptions, G' context of query
      G1 |- U1 : V1
     G', G  |- s1 : G1
     G', G  |- U1[s1]     and s1 is an explicit substitution

      G2 |- U2 : V2
  G', G  |- asub' : G2 and asub is a assignable substitution

      U2 is eta-expanded
   then
   G2, N |- cnstr
      G2 |- csub : N
      G2 |- cnstr[csub]

      G  |- nsub_goal : N
     *)
      (* we require unique string representation of external constants *)
      (* L1 = L2 by invariant *)(* BVar(k2) stands for an existential variable *)
      (* S2 is an etaSpine by invariant *)(* BVar(k2) stands for an existential variable *)
      (* then by invariant, it must have been already instantiated *)
      (* here spine associated with k2 might not be Nil ? *)
      (* BVar(k2) stands for an existential variable *)
      (* I.Root (BVar k2, S) will be fully applied (invariant from compilation) *)
      (* Glocal_u1 |- Us1 *)(* by invariant Us2 cannot contain any FgnExp *)
      (* D1[s1] = D2[s2]  by invariant *)(* nsub_goal may be destructively updated,
               asub does not change (i.e. existential variables are not instantiated,
               by invariant they must have been already instantiated
             *)
      (* D1[s1] = D2[s2]  by invariant *)(* nsub_goal may be destructively updated,
               asub does not change (i.e. existential variables are not instantiated,
               by invariant they must have been already instantiated
            *)
      (* it does matter what we put in Glocal_u1! since D2 will only be approximately the same as D1 at this point! *)
      (* assignExp (nvaronly, depth+1, I.Decl (Glocal_u1, D2), (U1, I.dot1 s1), U2, cnstr) *)
      (* generate cnstr substitution for all nvars occurring in U2 *)
      (* by invariant Us2 cannot contain any FgnExp *)
      (*      | assignExpW (nvaronly, depth, Glocal_u1, (U1, s1), I.Lam (D2, U2), cnstr) =
           Cannot occur if expressions are eta expanded *)
      (*      | assignExpW (nvaronly, depth, Glocal_u1, (I.Lam (D1, U1), s1), U2, cnstr) =
       ETA: can't occur if eta expanded *)
      (* same reasoning holds as above *)(* nsub_goal, asub may be destructively updated *)
      (* assignable (g, nsub, nsub_goal, asub, csub, cnstr) = (nsub_goal', csub, cnstr') option

    nsub, nsub_goal, nsub_goal' are  well-formed normal substitutions
    asub is a well-formed assignable substitution
    csub is maps normal variables to avars

        G  |- nsub_goal
        G' |- nsub : N
        G  |- asub : G'

    G'     |- csub : N'
    G', N' |- cnstr
    G'     |- cnstr[csub]

   *)
      (* = l' *)(* = l *)(* normalize nsub_left (or require that it is normalized
             collect all left-over nsubs and later combine it with cnstrsub
           *)
      (* cnstr[rsub] *)(* nsub_goal1 = rgoal u nsub_goal'  remaining substitutions to be checked *)
      (* Unification *)(* Xs1 should not contain any uninstantiated AVar anymore *)
      (* Convert context G into explicit substitution *)
      (* ctxToEVarSub (i, G, G', asub, s) = s' *)(* d = I.ctxLength Glocal_u *)
      (* succeed *)(* B *)(* destructively updates assignSub, might initiate backtracking  *)
      (* cnstrSub' = empty? by invariant *)(* LCO optimization *)
      (* destructively updates nsub_query, assignSub,  might fail and initiate backtracking *)
      (* we must undo any changes to assignSub and whatever else is destructively updated,
             cnstrSub?, cnstr? or keep them separate from different branches!*)
      (* s = id *)(*----------------------------------------------------------------------------*)
      (* Retrieval via set of candidates *)(* destructively updates assignSub, might initiate backtracking  *)
      (* LCO optimization *)(* destructively updates nsub_query, assignSub,  might fail and initiate backtracking *)
      (* we must undo any changes to assignSub and whatever else is destructively updated,
             cnstrSub?, cnstr? or keep them separate from different branches!*)
      (* s = id *)(* print "No candidate left anymore\n" ;*)
      (* CGoals(AuxG, cid, ConjGoals, i) *)(* sc = (fn S => (O::S)) *)
      (* execute one by one all candidates : here ! *)
      (* retrieval (n, !Tree, G, I.EClo(ps), sc)   *)) =
      sProgReset
    let sProgInstall = sProgInstall
    let matchSig = matchSigIt
  end ;;
