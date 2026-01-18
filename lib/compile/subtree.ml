
(* Substitution Trees *)
(* Author: Brigitte Pientka *)
module type SUBTREE  =
  sig
    (*! structure IntSyn : INTSYN !*)
    (*! structure CompSyn : COMPSYN     !*)
    (*! structure RBSet : RBSET  !*)
    type nonrec nvar = int
    (* index for normal variables *)
    type nonrec bvar = int
    (* index for bound variables *)
    type nonrec bdepth = int
    (* depth of locally bound variables *)
    (* normal (linear) substitutions *)
    (*  type normalSubsts = (IntSyn.Dec IntSyn.Ctx * IntSyn.Exp) RBSet.ordSet *)
    type typeLabel =
      | TypeLabel 
      | Body 
    type nonrec normalSubsts = (typeLabel * IntSyn.__Exp) RBSet.ordSet
    type nonrec querySubsts =
      (IntSyn.__Dec IntSyn.__Ctx * (typeLabel * IntSyn.__Exp)) RBSet.ordSet
    type __CGoal =
      | CGoals of (CompSyn.__AuxGoal * IntSyn.cid * CompSyn.__Conjunction *
      int) 
    (* assignable (linear) subsitutions *)
    type __AssSub =
      | Assign of (IntSyn.__Dec IntSyn.__Ctx * IntSyn.__Exp) 
    type nonrec assSubsts = __AssSub RBSet.ordSet
    (* key = int = bvar *)
    type __Cnstr =
      | Eqn of (IntSyn.__Dec IntSyn.__Ctx * IntSyn.__Exp * IntSyn.__Exp) 
    type __Tree =
      | Leaf of (normalSubsts * IntSyn.__Dec IntSyn.__Ctx * __CGoal) 
      | Node of (normalSubsts * __Tree RBSet.ordSet) 
    (*  type candidate = assSubsts * normalSubsts * cnstrSubsts * Cnstr * IntSyn.Dec IntSyn.Ctx * CGoal *)
    val indexArray : (int ref * __Tree ref) Array.array
    val sProgReset : unit -> unit
    val sProgInstall :
      (IntSyn.cid * CompSyn.__CompHead * CompSyn.__Conjunction) -> unit
    val matchSig :
      (IntSyn.cid * IntSyn.__Dec IntSyn.__Ctx * IntSyn.eclo *
        (((CompSyn.__Conjunction * IntSyn.__Sub) * IntSyn.cid) -> unit)) ->
        unit
  end;;




(* Substitution Tree indexing *)
(* Author: Brigitte Pientka *)
module SubTree(SubTree:sig
                         (*! structure IntSyn' : INTSYN !*)
                         (*!structure CompSyn' : COMPSYN !*)
                         (*!  sharing CompSyn'.IntSyn = IntSyn' !*)
                         module Whnf : WHNF
                         module Unify : UNIFY
                         module Print : PRINT
                         module CPrint : CPRINT
                         module Formatter : FORMATTER
                         module Names : NAMES
                         (*!  sharing Whnf.IntSyn = IntSyn' !*)
                         (*!  sharing Unify.IntSyn = IntSyn'!*)
                         (*!  sharing Print.IntSyn = IntSyn' !*)
                         (* CPrint currently unused *)
                         (*!  sharing CPrint.IntSyn = IntSyn' !*)
                         (*!  sharing CPrint.CompSyn = CompSyn' !*)
                         (* unused *)
                         (*!  sharing Print.Formatter = Formatter !*)
                         (* unused *)
                         (*!  sharing Names.IntSyn = IntSyn' !*)
                         module CSManager : CS_MANAGER
                       end) : SUBTREE =
  struct
    (*!  sharing CSManager.IntSyn = IntSyn'!*)
    (*! structure RBSet : RBSET !*)
    (*!  structure IntSyn = IntSyn' !*)
    (*!  structure CompSyn = CompSyn' !*)
    (*!  structure RBSet = RBSet !*)
    type nonrec nvar = int
    (* index for normal variables *)
    type nonrec bvar = int
    (* index for bound variables *)
    type nonrec bdepth = int
    (* depth of locally bound variables *)
    (* A substitution tree is defined as follows:
     Node := Leaf (ns, __g, sgoal) | Node(ns, Set of Nodes)
     normal linear modal substitutions ns := . | R/n, ns

   For each node we have the following invariant:
        S |- ns : S'    i.e. ns substitutes for internal variables
        __g'|- as : __g     i.e. as substitutes for assignable variables
        __g |- qs : __g     i.e. qs substitutes for modal variables
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
    (* typeLabel distinguish between declarations (=type labels)
   which are subject to indexing, but only the internal nvars will
   be instantiated during asssignment and Body which are subject to
   indexing and existential variables and nvars will be instantiated
   during assignment
 *)
    type typeLabel =
      | TypeLabel 
      | Body 
    type nonrec normalSubsts = (typeLabel * IntSyn.__Exp) RBSet.ordSet
    (* key = int = bvar *)
    type __AssSub =
      | Assign of (IntSyn.__Dec IntSyn.__Ctx * IntSyn.__Exp) 
    type nonrec assSubsts = __AssSub RBSet.ordSet
    (* key = int = bvar *)
    type nonrec querySubsts =
      (IntSyn.__Dec IntSyn.__Ctx * (typeLabel * IntSyn.__Exp)) RBSet.ordSet
    type __Cnstr =
      | Eqn of (IntSyn.__Dec IntSyn.__Ctx * IntSyn.__Exp * IntSyn.__Exp) 
    type nonrec cnstrSubsts = IntSyn.__Exp RBSet.ordSet
    (* key = int = bvar *)
    type __CGoal =
      | CGoals of (CompSyn.__AuxGoal * IntSyn.cid * CompSyn.__Conjunction *
      int) 
    (* cid of clause *)
    type genType =
      | Top 
      | Regular 
    type __Tree =
      | Leaf of (normalSubsts * IntSyn.__Dec IntSyn.__Ctx * __CGoal) 
      | Node of (normalSubsts * __Tree RBSet.ordSet) 
    type nonrec candidate =
      (assSubsts * normalSubsts * cnstrSubsts * __Cnstr * IntSyn.__Dec
        IntSyn.__Ctx * __CGoal)
    (* Initialization of substitutions *)
    let (nid : unit -> normalSubsts) = RBSet.new__
    let (assignSubId : unit -> assSubsts) = RBSet.new__
    let (cnstrSubId : unit -> cnstrSubsts) = RBSet.new__
    let (querySubId : unit -> querySubsts) = RBSet.new__
    (* Identity substitution *)
    let rec isId s = RBSet.isEmpty s
    (* Initialize substitution tree *)
    let rec makeTree () = ref (Node ((nid ()), (RBSet.new__ ())))
    (* Test if node has any children *)
    let rec noChildren (C) = RBSet.isEmpty C
    (* Index array

   Invariant:
   For all type families  a  indexArray = [a1,...,an]
   where a1,...,an is a substitution tree consisting of all constants
   for target family ai

   *)
    let indexArray =
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
      | (IntSyn.Null, __g) -> __g
      | (Decl (__g, __d), __g') -> IntSyn.Decl ((compose' (__g, __g')), __d)
    let rec shift =
      function
      | (IntSyn.Null, s) -> s
      | (Decl (__g, __d), s) -> I.dot1 (shift (__g, s))
    let rec raiseType =
      function
      | (I.Null, __v) -> __v
      | (Decl (__g, __d), __v) -> raiseType (__g, (I.Lam (__d, __v)))
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
    let rec compatible (label, T, __u, rho_t, rho_u) =
      let rec genExp =
        function
        | (label, b, (NVar n as T), (Root (H, S) as __u)) ->
            (S.insert rho_u (n, (label, __u)); T)
        | (label, b, (Root (H1, S1) as T), (Root (H2, S2) as __u)) ->
            if eqHeads (H1, H2)
            then I.Root (H1, (genSpine (label, b, S1, S2)))
            else
              (match b with
               | Regular ->
                   (S.insert rho_t (((!nctr) + 1), (label, T));
                    S.insert rho_u (((!nctr) + 1), (label, __u));
                    newNVar ())
               | _ -> raise (Generalization "Should never happen!"))
        | (label, b, Lam ((Dec (N, A1) as D1), T1), Lam
           ((Dec (_, A2) as D2), __U2)) ->
            I.Lam
              ((I.Dec (N, (genExp (TypeLabel, Regular, A1, A2)))),
                (genExp (label, b, T1, __U2)))
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
        | (label, b, T, __u) ->
            raise
              (Generalization
                 "Cases where __u= EVar or EClo should never happen!")
      and genSpine =
        function
        | (label, b, I.Nil, I.Nil) -> I.Nil
        | (label, b, App (T, S1), App (__u, S2)) ->
            I.App ((genExp (label, b, T, __u)), (genSpine (label, b, S1, S2)))
      and genDec (label, b, Dec (N, E1), Dec (N', E2)) =
        I.Dec (N, (genExp (label, b, E1, E2))) in
      let rec genTop =
        function
        | (label, ((Root (H1, S1)) as T), ((Root (H2, S2)) as __u)) ->
            if eqHeads (H1, H2)
            then I.Root (H1, (genSpine (label, Regular, S1, S2)))
            else
              raise (Generalization "Top-level function symbol not shared")
        | (label, Lam ((Dec (N, A1) as D1), T1), Lam
           ((Dec (_, A2) as D2), __U2)) ->
            I.Lam
              ((I.Dec (N, (genExp (label, Regular, A1, A2)))),
                (genTop (label, T1, __U2)))
        | (_, _, _) ->
            raise (Generalization "Top-level function symbol not shared") in
      try Some (genTop (label, T, __u)) with | Generalization msg -> None
    let rec compatibleSub (nsub_t, nsub_e) =
      let (sg, rho_t, rho_e) = ((nid ()), (nid ()), (nid ())) in
      let _ =
        S.forall nsub_e
          (function
           | (nv, (l', E)) ->
               (match S.lookup nsub_t nv with
                | Some (l, T) ->
                    if l = l'
                    then
                      (match compatible (l, T, E, rho_t, rho_e) with
                       | None ->
                           (S.insert rho_t (nv, (l, T));
                            S.insert rho_e (nv, (l, E)))
                       | Some (T') -> S.insert sg (nv, (l, T')))
                    else raise (Generalization "Labels don't agree\n")
                | None -> S.insert rho_e (nv, (l', E)))) in
      if isId sg then None else Some (sg, rho_t, rho_e)
    let rec mkNode =
      function
      | (Node (_, Children), sg, rho1, ((__g, RC) as GR), rho2) ->
          let c = S.new__ () in
          (S.insertList c
             [(1, (Node (rho1, Children))); (2, (Leaf (rho2, __g, RC)))];
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
      | None ->
          S.insert children
            ((n + 1), (Leaf (nsub_e, G_clause2, Res_clause2)))
      | Some (sg, rho1, rho2) ->
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
           | None -> raise (Error "Leaf is not compatible substitution r")
           | Some (sg, rho1, rho2) -> mkNode (N, sg, rho1, GR, rho2))
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
      | (Lam (__d, __u), nsub) ->
          I.Lam ((normalizeNDec (__d, nsub)), (normalizeNExp (__u, nsub)))
      | (Pi ((__d, P), __u), nsub) ->
          I.Pi (((normalizeNDec (__d, nsub)), P), (normalizeNExp (__u, nsub)))
    let rec normalizeNSpine =
      function
      | (I.Nil, _) -> I.Nil
      | (App (__u, S), nsub) ->
          I.App ((normalizeNExp (__u, nsub)), (normalizeNSpine (S, nsub)))
    let rec normalizeNDec (Dec (N, E), nsub) =
      I.Dec (N, (normalizeNExp (E, nsub)))
    let rec assign
      (nvaronly, Glocal_u1, us1, __U2, nsub_goal, asub, csub, cnstr) =
      let depth = I.ctxLength Glocal_u1 in
      let rec assignHead
        (nvaronly, depth, Glocal_u1, ((Root (H1, S1), s1) as us1),
         (Root (H2, S2) as __U2), cnstr)
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
              (nvaronly, depth, Glocal_u1, (Whnf.expandDef us1), __U2, cnstr)
        | (FgnConst (cs1, ConDec (n1, _, _, _, _, _)), FgnConst
           (cs2, ConDec (n2, _, _, _, _, _))) ->
            if (cs1 = cs2) && (n1 = n2)
            then cnstr
            else raise (Assignment "Foreign Constant clash")
        | (FgnConst (cs1, ConDef (n1, _, _, W1, _, _, _)), FgnConst
           (cs2, ConDef (n2, _, _, __v, W2, _, _))) ->
            if (cs1 = cs2) && (n1 = n2)
            then cnstr
            else assignExp (nvaronly, depth, Glocal_u1, (W1, s1), W2, cnstr)
        | (FgnConst (_, ConDef (_, _, _, W1, _, _, _)), _) ->
            assignExp (nvaronly, depth, Glocal_u1, (W1, s1), __U2, cnstr)
        | (_, FgnConst (_, ConDef (_, _, _, W2, _, _, _))) ->
            assignExp (nvaronly, depth, Glocal_u1, us1, W2, cnstr)
        | (_, _) -> raise (Assignment "Head mismatch ")
      and assignExpW =
        function
        | (nvaronly, depth, Glocal_u1, (Uni (L1), s1), Uni (L2), cnstr) ->
            cnstr
        | (nvaronly, depth, Glocal_u1, us1, NVar n, cnstr) ->
            (S.insert nsub_goal (n, (Glocal_u1, (nvaronly, (I.EClo us1))));
             cnstr)
        | (Body, depth, Glocal_u1, ((Root (H1, S1), s1) as us1),
           (Root (H2, S2) as __U2), cnstr) ->
            (match H2 with
             | BVar k2 ->
                 if k2 > depth
                 then
                   (S.insert asub
                      (((-) k2 I.ctxLength Glocal_u1),
                        (Assign (Glocal_u1, (I.EClo us1))));
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
             | _ -> assignHead (Body, depth, Glocal_u1, us1, __U2, cnstr))
        | (TypeLabel, depth, Glocal_u1, ((Root (H1, S1), s1) as us1),
           (Root (H2, S2) as __U2), cnstr) ->
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
             | _ -> assignHead (TypeLabel, depth, Glocal_u1, us1, __U2, cnstr))
        | (nvaronly, depth, Glocal_u1, us1, (Root (BVar k2, S) as __U2), cnstr)
            ->
            if k2 > depth
            then
              (match nvaronly with
               | TypeLabel -> cnstr
               | Body ->
                   (S.insert asub
                      ((k2 - depth), (Assign (Glocal_u1, (I.EClo us1))));
                    cnstr))
            else
              (match nvaronly with
               | TypeLabel -> cnstr
               | Body ->
                   (match us1 with
                    | (EVar (r, _, __v, Cnstr), s) ->
                        let __U2' = normalizeNExp (__U2, csub) in
                        (Eqn (Glocal_u1, (I.EClo us1), __U2')) :: cnstr
                    | (EClo (__u, s'), s) ->
                        assignExp
                          (Body, depth, Glocal_u1, (__u, (I.comp (s', s))), __U2,
                            cnstr)
                    | (FgnExp (_, ops), _) ->
                        let __U2' = normalizeNExp (__U2, csub) in
                        (Eqn (Glocal_u1, (I.EClo us1), __U2')) :: cnstr))
        | (nvaronly, depth, Glocal_u1, (Lam ((Dec (_, A1) as D1), __U1), s1),
           Lam ((Dec (_, A2) as D2), __U2), cnstr) ->
            let cnstr' =
              assignExp (TypeLabel, depth, Glocal_u1, (A1, s1), A2, cnstr) in
            assignExp
              (nvaronly, (depth + 1),
                (I.Decl (Glocal_u1, (I.decSub (D1, s1)))), (__U1, (I.dot1 s1)),
                __U2, cnstr')
        | (nvaronly, depth, Glocal_u1,
           (Pi (((Dec (_, A1) as D1), _), __U1), s1), Pi
           (((Dec (_, A2) as D2), _), __U2), cnstr) ->
            let cnstr' =
              assignExp (TypeLabel, depth, Glocal_u1, (A1, s1), A2, cnstr) in
            assignExp
              (nvaronly, (depth + 1),
                (I.Decl (Glocal_u1, (I.decSub (D1, s1)))), (__U1, (I.dot1 s1)),
                __U2, cnstr')
        | (nvaronly, depth, Glocal_u1, ((EVar (r, _, __v, Cnstr), s) as us1),
           __U2, cnstr) ->
            let __U2' = normalizeNExp (__U2, csub) in
            (Eqn (Glocal_u1, (I.EClo us1), __U2')) :: cnstr
        | (nvaronly, depth, Glocal_u1, ((EClo (__u, s'), s) as us1), __U2, cnstr)
            ->
            assignExp
              (nvaronly, depth, Glocal_u1, (__u, (I.comp (s', s))), __U2, cnstr)
        | (nvaronly, depth, Glocal_u1, ((FgnExp (_, ops), _) as us1), __U2,
           cnstr) ->
            let __U2' = normalizeNExp (__U2, csub) in
            (Eqn (Glocal_u1, (I.EClo us1), __U2')) :: cnstr
        | (nvaronly, depth, Glocal_u1, us1, (FgnExp (_, ops) as __U2), cnstr)
            -> (Eqn (Glocal_u1, (I.EClo us1), __U2)) :: cnstr
      and assignSpine =
        function
        | (nvaronly, depth, Glocal_u1, (I.Nil, _), I.Nil, cnstr) -> cnstr
        | (nvaronly, depth, Glocal_u1, (SClo (S1, s1'), s1), S, cnstr) ->
            assignSpine
              (nvaronly, depth, Glocal_u1, (S1, (I.comp (s1', s1))), S,
                cnstr)
        | (nvaronly, depth, Glocal_u1, (App (__U1, S1), s1), App (__U2, S2),
           cnstr) ->
            let cnstr' =
              assignExp (nvaronly, depth, Glocal_u1, (__U1, s1), __U2, cnstr) in
            assignSpine (nvaronly, depth, Glocal_u1, (S1, s1), S2, cnstr')
      and assignExp (nvaronly, depth, Glocal_u1, us1, __U2, cnstr) =
        assignExpW (nvaronly, depth, Glocal_u1, (Whnf.whnf us1), __U2, cnstr) in
      assignExp (nvaronly, depth, Glocal_u1, us1, __U2, cnstr)
    let rec assignableLazy
      (nsub, nsub_query, assignSub, (nsub_left, cnstrSub), cnstr) =
      let nsub_query' = querySubId () in
      let cref = ref cnstr in
      let rec assign' (nsub_query, nsub) =
        let (nsub_query_left, nsub_left1) =
          S.differenceModulo nsub_query nsub
            (function
             | (Glocal_u, (l, __u)) ->
                 (function
                  | (l', T) ->
                      (:=) cref assign
                        (l, Glocal_u, (__u, I.id), T, nsub_query', assignSub,
                          cnstrSub, (!cref)))) in
        let nsub_left' =
          S.update nsub_left1
            (function | (l, __u) -> (l, (normalizeNExp (__u, cnstrSub)))) in
        Some
          ((S.union nsub_query_left nsub_query'),
            ((S.union nsub_left nsub_left'), cnstrSub), (!cref)) in
      try assign' (nsub_query, nsub) with | Assignment msg -> None
    let rec assignableEager (nsub, nsub_query, assignSub, cnstrSub, cnstr) =
      let nsub_query' = querySubId () in
      let cref = ref cnstr in
      let rec assign' (nsub_query, nsub) =
        let (nsub_query_left, nsub_left) =
          S.differenceModulo nsub_query nsub
            (function
             | (Glocal_u, (l, __u)) ->
                 (function
                  | (l', T) ->
                      (:=) cref assign
                        (l', Glocal_u, (__u, I.id), T, nsub_query', assignSub,
                          cnstrSub, (!cref)))) in
        let _ =
          S.forall nsub_left
            (function
             | (nv, (nvaronly, __u)) ->
                 (match S.lookup cnstrSub nv with
                  | None -> raise (Error "Left-over nsubstitution")
                  | Some (AVar (A)) ->
                      (:=) A Some (normalizeNExp (__u, cnstrSub)))) in
        Some ((S.union nsub_query_left nsub_query'), cnstrSub, (!cref)) in
      try assign' (nsub_query, nsub) with | Assignment msg -> None
    let rec unifyW =
      function
      | (__g, ((AVar (ref (None) as r) as x), Shift 0), us2) ->
          (:=) r Some (I.EClo us2)
      | (__g, ((AVar (ref (None) as r) as x), s), ((__u, s2) as us2)) ->
          (print "unifyW -- not s = Id\n";
           print (((^) "us2 = " Print.expToString (__g, (I.EClo us2))) ^ "\n");
           (:=) r Some (I.EClo us2))
      | (__g, Xs1, us2) -> Unify.unifyW (__g, Xs1, us2)
    let rec unify (__g, Xs1, us2) =
      unifyW (__g, (Whnf.whnf Xs1), (Whnf.whnf us2))
    let rec unifiable (__g, us1, us2) =
      try unify (__g, us1, us2); true__ with | Unify msg -> false__
    let rec ctxToExplicitSub =
      function
      | (i, Gquery, I.Null, asub) -> I.id
      | (i, Gquery, Decl (Gclause, Dec (_, A)), asub) ->
          let s = ctxToExplicitSub ((i + 1), Gquery, Gclause, asub) in
          let EVar (x', _, _, _) as __u' = I.newEVar (Gquery, (I.EClo (A, s))) in
          ((match S.lookup asub i with
            | None -> ()
            | Some (Assign (Glocal_u, __u)) ->
                (:=) x' Some (raiseType (Glocal_u, __u)));
           I.Dot ((I.Exp __u'), s))
      | (i, Gquery, Decl (Gclause, ADec (_, d)), asub) ->
          let AVar (x') as __u' = I.newAVar () in
          ((match S.lookup asub i with
            | None -> ()
            | Some (Assign (Glocal_u, __u)) -> (:=) x' Some __u);
           I.Dot
             ((I.Exp (I.EClo (__u', (I.Shift (~- d))))),
               (ctxToExplicitSub ((i + 1), Gquery, Gclause, asub))))
    let rec solveAuxG =
      function
      | (C.Trivial, s, Gquery) -> true__
      | (UnifyEq (Glocal, e1, N, eqns), s, Gquery) ->
          let __g = compose' (Glocal, Gquery) in
          let s' = shift (Glocal, s) in
          if unifiable (__g, (N, s'), (e1, s'))
          then solveAuxG (eqns, s, Gquery)
          else false__
    let rec solveCnstr =
      function
      | (Gquery, Gclause, nil, s) -> true__
      | (Gquery, Gclause, (Eqn (Glocal, __U1, __U2))::Cnstr, s) ->
          (Unify.unifiable
             ((compose' (Gquery, Glocal)), (__U1, I.id),
               (__U2, (shift (Glocal, s)))))
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
      let rec retrieve =
        function
        | (Leaf (nsub, Gclause, Residuals), nsub_query, assignSub, cnstrSub,
           cnstr) ->
            (match assignableEager
                     (nsub, nsub_query, assignSub, cnstrSub, cnstr)
             with
             | None -> ()
             | Some (nsub_query', cnstrSub', cnstr') ->
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
             | None -> ()
             | Some (nsub_query', cnstrSub', cnstr') ->
                 S.forall Children
                   (function
                    | (n, Child) ->
                        retrieve
                          (Child, nsub_query', (S.copy assignSub),
                            (S.copy cnstrSub'), cnstr'))) in
      retrieve (Child, nsub_query, assignSub, (cnstrSubId ()), cnstr)
    let rec retrieval (n, (Node (s, Children) as STree), __g, r, sc) =
      let (nsub_query, assignSub) = ((querySubId ()), (assignSubId ())) in
      S.insert nsub_query (1, (I.Null, (Body, r)));
      S.forall Children
        (function
         | (_, C) -> retrieveChild (n, C, nsub_query, assignSub, nil, __g, sc))
    let rec retrieveAll (num, Child, nsub_query, assignSub, cnstr, candSet) =
      let i = ref 0 in
      let rec retrieve =
        function
        | (Leaf (nsub, Gclause, Residuals), nsub_query, assignSub,
           (nsub_left, cnstrSub), cnstr) ->
            (match assignableLazy
                     (nsub, nsub_query, assignSub, (nsub_left, cnstrSub),
                       cnstr)
             with
             | None -> ()
             | Some (nsub_query', (nsub_left', cnstrSub'), cnstr') ->
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
             | None -> ()
             | Some (nsub_query', (nsub_left', cnstrSub'), cnstr') ->
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
      let rec solveCandidate (i, candSet) =
        match S.lookup candSet i with
        | None -> ()
        | Some (assignSub, nsub_left, cnstrSub, cnstr, Gclause, Residuals) ->
            (CSManager.trail
               (function
                | () ->
                    (S.forall nsub_left
                       (function
                        | (nv, (l, __u)) ->
                            (match S.lookup cnstrSub nv with
                             | None ->
                                 raise (Error "Left-over nsubstitution")
                             | Some (AVar (A)) -> (:=) A Some __u));
                     solveResiduals
                       (Gquery, Gclause, Residuals, assignSub, cnstr, sc)));
             solveCandidate ((i + 1), candSet)) in
      S.insert nsub_query (1, (I.Null, (Body, r)));
      S.forall Children
        (function
         | (_, C) -> retrieveAll (n, C, nsub_query, assignSub, nil, candSet));
      solveCandidate (1, candSet)
    let rec matchSig (a, __g, ((Root (Ha, S), s) as ps), sc) =
      let (n, Tree) = Array.sub (indexArray, a) in
      retrieveCandidates (n, (!Tree), __g, (I.EClo ps), sc)
    let rec matchSigIt (a, __g, ((Root (Ha, S), s) as ps), sc) =
      let (n, Tree) = Array.sub (indexArray, a) in
      retrieval (n, (!Tree), __g, (I.EClo ps), sc)
    let rec sProgReset () =
      nctr := 1;
      Array.modify
        (function
         | (n, Tree) -> (n := 0; (!) ((:=) Tree) (makeTree ()); (n, Tree)))
        indexArray
    let rec sProgInstall (a, Head (E, __g, Eqs, cid), R) =
      let (n, Tree) = Array.sub (indexArray, a) in
      let nsub_goal = S.new__ () in
      S.insert nsub_goal (1, (Body, E));
      (:=) Tree insert
        ((!Tree), nsub_goal, (__g, (CGoals (Eqs, cid, R, ((!n) + 1)))));
      ((!) ((:=) n) n) + 1
    (* Auxiliary functions *)
    (*
     Linear normal higher-order patterns
           p ::= n | Root(c, S) | Root(b, S) | Lam (__d, p)

                 where n is a linear bound "normalized" variable

          SP ::= p ; S | NIL

     Context
        __g : context for bound variables (bvars)
            (type information is stored in the context)
        __g ::= . | __g, x : A

        S : context for linear normalized bound variables (nvars)
            (no type information is stored in the context)
            (these are the types of the variables definitions)
        S ::= . | S, n

     Templates: __g ; S |- p
     Substitutions: __g ; S |- nsub : S'

    Let s is a substitution for normalized bound variables (nvars)
    and nsub1 o nsub2 o .... o nsubn = s, s.t.
     __g, S_2|- nsub1 : S_1
     __g, S_3|- nsub2 : S_2
      ....
     __g |- nsubn : S_n
      . ; __g |- s : __g, S_1

    A term __u can be decomposed into a term p together with a sequenence of
    substitutions s1, s2, ..., sn such that s1 o s2 o .... o sn = s
    and the following holds:

    If    __g |- __u

    then

       __g, S |- p

        __g |- s : __g, S

        __g |- p[s]     and p[s] = __u

   In addition:
   all expressions in the index are linear, i.e.
   an expression is first linearized before it is inserted into the index
   (this makes retrieving all axpressions from the index which unify with
    a given expression simpler, because we can omit the occurs check)

   *)
    (* ---------------------------------------------------------------*)
    (* nctr = |__d| =  #normal variables *)
    (* most specific linear common generalization *)
    (* compatible (T, __u) = (C, rho_u', rho_t') opt
    if
       __u, T are both in normal form
       __u and T share at least the top function symbol
   then
     C[rho_u'] = __u and C[rho_t'] = T
   *)
    (* = S.existsOpt (fn __u' => equalTerm (__u, __u')) *)
    (* find *i in rho_t and rho_u such that T/*i in rho_t and __u/*i in rho_u *)
    (* NOTE: by invariant A1 =/= A2 *)
    (* by invariant A1 =/= A2 *)
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
    (* by invariant rho_t = empty, since nsub_t <= nsub_e *)
    (* by invariant d = d'
                                     therefore T and E have the same approximate type A *)
    (* mkNode (N, sg, r1, (__g, RC), r2) = N'    *)
    (* Insertion *)
    (* compareChild (children, (n, child), n, n', (__g, R)) = ()

   *)
    (* sg = nsub_t = nsub_e *)
    (* sg = nsub_t and nsub_e = sg o rho2 *)
    (* insert (N, nsub_e, (__g, R2)) = N'

     if s is the substitution in node N
        __g |- nsub_e : S and
    __g, S' |- s : S
    then
     N' contains a path n_1 .... n_n s.t.
     [n_n] ...[n_1] s = nsub_e
  *)
    (* initial *)
    (* retrieval (__u,s)
     retrieves all clauses which unify with (__u,s)

     backtracking implemented via SML failure continuation

   *)
    (* cannot happen -bp *)
    (* assign (__g, us1, __U2, nsub_goal, asub, csub, cnstr) = cnstr
   if __g = local assumptions, __g' context of query
      G1 |- __U1 : V1
     __g', __g  |- s1 : G1
     __g', __g  |- __U1[s1]     and s1 is an explicit substitution

      G2 |- __U2 : V2
  __g', __g  |- asub' : G2 and asub is a assignable substitution

      __U2 is eta-expanded
   then
   G2, N |- cnstr
      G2 |- csub : N
      G2 |- cnstr[csub]

      __g  |- nsub_goal : N
     *)
    (* we require unique string representation of external constants *)
    (* L1 = L2 by invariant *)
    (* BVar(k2) stands for an existential variable *)
    (* S2 is an etaSpine by invariant *)
    (* BVar(k2) stands for an existential variable *)
    (* then by invariant, it must have been already instantiated *)
    (* here spine associated with k2 might not be Nil ? *)
    (* BVar(k2) stands for an existential variable *)
    (* I.Root (BVar k2, S) will be fully applied (invariant from compilation) *)
    (* Glocal_u1 |- us1 *)
    (* by invariant us2 cannot contain any FgnExp *)
    (* D1[s1] = D2[s2]  by invariant *)
    (* nsub_goal may be destructively updated,
               asub does not change (i.e. existential variables are not instantiated,
               by invariant they must have been already instantiated
             *)
    (* D1[s1] = D2[s2]  by invariant *)
    (* nsub_goal may be destructively updated,
               asub does not change (i.e. existential variables are not instantiated,
               by invariant they must have been already instantiated
            *)
    (* it does matter what we put in Glocal_u1! since D2 will only be approximately the same as D1 at this point! *)
    (* assignExp (nvaronly, depth+1, I.Decl (Glocal_u1, D2), (__U1, I.dot1 s1), __U2, cnstr) *)
    (* generate cnstr substitution for all nvars occurring in __U2 *)
    (* by invariant us2 cannot contain any FgnExp *)
    (*      | assignExpW (nvaronly, depth, Glocal_u1, (__U1, s1), I.Lam (D2, __U2), cnstr) =
           Cannot occur if expressions are eta expanded *)
    (*      | assignExpW (nvaronly, depth, Glocal_u1, (I.Lam (D1, __U1), s1), __U2, cnstr) =
       ETA: can't occur if eta expanded *)
    (* same reasoning holds as above *)
    (* nsub_goal, asub may be destructively updated *)
    (* assignable (g, nsub, nsub_goal, asub, csub, cnstr) = (nsub_goal', csub, cnstr') option

    nsub, nsub_goal, nsub_goal' are  well-formed normal substitutions
    asub is a well-formed assignable substitution
    csub is maps normal variables to avars

        __g  |- nsub_goal
        __g' |- nsub : N
        __g  |- asub : __g'

    __g'     |- csub : N'
    __g', N' |- cnstr
    __g'     |- cnstr[csub]

   *)
    (* = l' *)
    (* = l *)
    (* normalize nsub_left (or require that it is normalized
             collect all left-over nsubs and later combine it with cnstrsub
           *)
    (* cnstr[rsub] *)
    (* nsub_goal1 = rgoal u nsub_goal'  remaining substitutions to be checked *)
    (* Unification *)
    (* Xs1 should not contain any uninstantiated AVar anymore *)
    (* Convert context __g into explicit substitution *)
    (* ctxToEVarSub (i, __g, __g', asub, s) = s' *)
    (* d = I.ctxLength Glocal_u *)
    (* succeed *)
    (* B *)
    (* destructively updates assignSub, might initiate backtracking  *)
    (* cnstrSub' = empty? by invariant *)
    (* LCO optimization *)
    (* destructively updates nsub_query, assignSub,  might fail and initiate backtracking *)
    (* we must undo any changes to assignSub and whatever else is destructively updated,
             cnstrSub?, cnstr? or keep them separate from different branches!*)
    (* s = id *)
    (*----------------------------------------------------------------------------*)
    (* Retrieval via set of candidates *)
    (* destructively updates assignSub, might initiate backtracking  *)
    (* LCO optimization *)
    (* destructively updates nsub_query, assignSub,  might fail and initiate backtracking *)
    (* we must undo any changes to assignSub and whatever else is destructively updated,
             cnstrSub?, cnstr? or keep them separate from different branches!*)
    (* s = id *)
    (* print "No candidate left anymore\n" ;*)
    (* CGoals(AuxG, cid, ConjGoals, i) *)
    (* sc = (fn S => (O::S)) *)
    (* execute one by one all candidates : here ! *)
    (* retrieval (n, !Tree, __g, I.EClo(ps), sc)   *)
    let sProgReset = sProgReset
    let sProgInstall = sProgInstall
    let matchSig = matchSigIt
  end ;;
