
(* Splitting *)
(* Author: Carsten Schuermann *)
module type SPLITTING  =
  sig
    module MetaSyn : METASYN
    exception Error of string 
    type nonrec operator
    val expand : MetaSyn.__State -> operator list
    val apply : operator -> MetaSyn.__State list
    val var : operator -> int
    val menu : operator -> string
    val index : operator -> int
  end;;




(* Splitting *)
(* Author: Carsten Schuermann *)
module Splitting(Splitting:sig
                             module Global : GLOBAL
                             module MetaSyn' : METASYN
                             module MetaAbstract : METAABSTRACT
                             module MetaPrint : METAPRINT
                             module ModeTable : MODETABLE
                             module Whnf : WHNF
                             module Index : INDEX
                             module Print : PRINT
                             (*! sharing ModeSyn.IntSyn = MetaSyn'.IntSyn !*)
                             (*! sharing Whnf.IntSyn = MetaSyn'.IntSyn !*)
                             (*! sharing Index.IntSyn = MetaSyn'.IntSyn !*)
                             (*! sharing Print.IntSyn = MetaSyn'.IntSyn !*)
                             module Unify : UNIFY
                           end) : SPLITTING =
  struct
    (*! sharing Unify.IntSyn = MetaSyn'.IntSyn !*)
    (*! structure CSManager : CS_MANAGER !*)
    (*! sharing CSManager.IntSyn = MetaSyn'.IntSyn !*)
    module MetaSyn = MetaSyn'
    exception Error of string 
    (* Invariant:
     Case analysis generates a list of successor states
     (the cases) from a given state.

     'a flag marks cases where unification of the types
     succeeded as "Active", and cases where there were
     leftover constraints after unification as "Inactive".

     NB: cases where unification fails are not considered

     Consequence: Only those splitting operators can be
     applied which do not generate inactive cases.
  *)
    type 'a flag =
      | Active of 'a 
      | InActive 
    type nonrec operator =
      ((MetaSyn.__State * int) * MetaSyn.__State flag list)
    module M = MetaSyn
    module I = IntSyn
    let rec constCases =
      function
      | (__g, __Vs, nil, abstract, ops) -> ops
      | (__g, __Vs, (Const c)::Sgn, abstract, ops) ->
          let (__u, __Vs') = M.createAtomConst (__g, (I.Const c)) in
          constCases
            (__g, __Vs, Sgn, abstract,
              (CSManager.trail
                 (function
                  | () ->
                      (try
                         if Unify.unifiable (__g, __Vs, __Vs')
                         then
                           (Active
                              (abstract
                                 (((I.conDecName (I.sgnLookup c)) ^ "/"), __u)))
                             :: ops
                         else ops
                       with | Error _ -> InActive :: ops))))
    let rec paramCases =
      function
      | (__g, __Vs, 0, abstract, ops) -> ops
      | (__g, __Vs, k, abstract, ops) ->
          let (__u, __Vs') = M.createAtomBVar (__g, k) in
          paramCases
            (__g, __Vs, (k - 1), abstract,
              (CSManager.trail
                 (function
                  | () ->
                      (try
                         if Unify.unifiable (__g, __Vs, __Vs')
                         then
                           (Active (abstract (((Int.toString k) ^ "/"), __u)))
                             :: ops
                         else ops
                       with | Error _ -> InActive :: ops))))
    let rec lowerSplitDest =
      function
      | (__g, ((Root (Const c, _) as __v), s'), abstract) ->
          constCases
            (__g, (__v, s'), (Index.lookup c), abstract,
              (paramCases (__g, (__v, s'), (I.ctxLength __g), abstract, nil)))
      | (__g, (Pi ((__d, P), __v), s'), abstract) ->
          let __d' = I.decSub (__d, s') in
          lowerSplitDest
            ((I.Decl (__g, __d')), (__v, (I.dot1 s')),
              (function | (name, __u) -> abstract (name, (I.Lam (__d', __u)))))
    let rec split (Prefix (__g, M, B), ((Dec (_, __v) as __d), s), abstract) =
      lowerSplitDest
        (I.Null, (__v, s),
          (function
           | (name', __u') ->
               abstract
                 (name', (M.Prefix (__g, M, B)), (I.Dot ((I.Exp __u'), s)))))
    let rec occursInExp =
      function
      | (k, Uni _) -> false__
      | (k, Pi (DP, __v)) ->
          (occursInDecP (k, DP)) || (occursInExp ((k + 1), __v))
      | (k, Root (C, S)) -> (occursInCon (k, C)) || (occursInSpine (k, S))
      | (k, Lam (__d, __v)) -> (occursInDec (k, __d)) || (occursInExp ((k + 1), __v))
      | (k, FgnExp csfe) ->
          I.FgnExpStd.fold csfe
            (function
             | (__u, B) -> B || (occursInExp (k, (Whnf.normalize (__u, I.id)))))
            false__
    let rec occursInCon =
      function
      | (k, BVar k') -> k = k'
      | (k, Const _) -> false__
      | (k, Def _) -> false__
      | (k, Skonst _) -> false__
    let rec occursInSpine =
      function
      | (_, I.Nil) -> false__
      | (k, App (__u, S)) -> (occursInExp (k, __u)) || (occursInSpine (k, S))
    let rec occursInDec (k, Dec (_, __v)) = occursInExp (k, __v)
    let rec occursInDecP (k, (__d, _)) = occursInDec (k, __d)
    let rec isIndexInit k = false__
    let rec isIndexSucc (__d, isIndex) k =
      (occursInDec (k, __d)) || (isIndex (k + 1))
    let rec isIndexFail (__d, isIndex) k = isIndex (k + 1)
    let rec checkVar =
      function
      | (Decl (M, M.Top), 1) -> true__
      | (Decl (M, M.Bot), 1) -> false__
      | (Decl (M, _), k) -> checkVar (M, (k - 1))
    let rec checkExp =
      function
      | (M, Uni _) -> true__
      | (M, Pi ((__d, P), __v)) ->
          (checkDec (M, __d)) && (checkExp ((I.Decl (M, M.Top)), __v))
      | (M, Lam (__d, __v)) ->
          (checkDec (M, __d)) && (checkExp ((I.Decl (M, M.Top)), __v))
      | (M, Root (BVar k, S)) -> (checkVar (M, k)) && (checkSpine (M, S))
      | (M, Root (_, S)) -> checkSpine (M, S)
    let rec checkSpine =
      function
      | (M, I.Nil) -> true__
      | (M, App (__u, S)) -> (checkExp (M, __u)) && (checkSpine (M, S))
    let rec checkDec (M, Dec (_, __v)) = checkExp (M, __v)
    let rec modeEq =
      function
      | (Marg (ModeSyn.Plus, _), M.Top) -> true__
      | (Marg (ModeSyn.Minus, _), M.Bot) -> true__
      | _ -> false__
    let rec inheritBelow =
      function
      | (b', k', Lam (__d', __u'), Bdd') ->
          inheritBelow
            (b', (k' + 1), __u', (inheritBelowDec (b', k', __d', Bdd')))
      | (b', k', Pi ((__d', _), __v'), Bdd') ->
          inheritBelow
            (b', (k' + 1), __v', (inheritBelowDec (b', k', __d', Bdd')))
      | (b', k', Root (BVar n', S'), (B', d, d')) ->
          if ((n' = k') + d') && (n' > k')
          then
            inheritBelowSpine (b', k', S', ((I.Decl (B', b')), d, (d' - 1)))
          else inheritBelowSpine (b', k', S', (B', d, d'))
      | (b', k', Root (C, S'), Bdd') -> inheritBelowSpine (b', k', S', Bdd')
    let rec inheritBelowSpine =
      function
      | (b', k', I.Nil, Bdd') -> Bdd'
      | (b', k', App (__u', S'), Bdd') ->
          inheritBelowSpine (b', k', S', (inheritBelow (b', k', __u', Bdd')))
    let rec inheritBelowDec (b', k', Dec (x, __v'), Bdd') =
      inheritBelow (b', k', __v', Bdd')
    let rec skip =
      function
      | (k, Lam (__d, __u), Bdd') -> skip ((k + 1), __u, (skipDec (k, __d, Bdd')))
      | (k, Pi ((__d, _), __v), Bdd') ->
          skip ((k + 1), __v, (skipDec (k, __d, Bdd')))
      | (k, Root (BVar n, S), (B', d, d')) ->
          if ((n = k) + d) && (n > k)
          then skipSpine (k, S, (B', (d - 1), d'))
          else skipSpine (k, S, (B', d, d'))
      | (k, Root (C, S), Bdd') -> skipSpine (k, S, Bdd')
    let rec skipSpine =
      function
      | (k, I.Nil, Bdd') -> Bdd'
      | (k, App (__u, S), Bdd') -> skipSpine (k, S, (skip (k, __u, Bdd')))
    let rec skipDec (k, Dec (x, __v), Bdd') = skip (k, __v, Bdd')
    let rec inheritExp =
      function
      | (B, k, Lam (__d, __u), k', Lam (__d', __u'), Bdd') ->
          inheritExp
            (B, (k + 1), __u, (k' + 1), __u',
              (inheritDec (B, k, __d, k', __d', Bdd')))
      | (B, k, Pi ((__d, _), __v), k', Pi ((__d', _), __v'), Bdd') ->
          inheritExp
            (B, (k + 1), __v, (k' + 1), __v',
              (inheritDec (B, k, __d, k', __d', Bdd')))
      | (B, k, (Root (BVar n, S) as __v), k', __v', (B', d, d')) ->
          if ((n = k) + d) && (n > k)
          then
            skipSpine
              (k, S,
                (inheritNewRoot
                   (B, (I.ctxLookup (B, (n - k))), k, __v, k', __v', (B', d, d'))))
          else
            if (n > k) + d
            then
              skipSpine
                (k, S,
                  (inheritBelow
                     (((I.ctxLookup (B, (n - k))) - 1), k', __v', (B', d, d'))))
            else
              (let Root (C', S') = __v' in
               inheritSpine (B, k, S, k', S', (B', d, d')))
      | (B, k, Root (C, S), k', Root (C', S'), Bdd') ->
          inheritSpine (B, k, S, k', S', Bdd')
    let rec inheritNewRoot =
      function
      | (B, b, k, Root (BVar n, S), k', (Root (BVar n', S') as __v'),
         (B', d, d')) ->
          if ((n' = k') + d') && (n' > k')
          then inheritBelow (b, k', __v', (B', (d - 1), d'))
          else inheritBelow ((b - 1), k', __v', (B', (d - 1), d'))
      | (B, b, k, __v, k', __v', (B', d, d')) ->
          inheritBelow ((b - 1), k', __v', (B', (d - 1), d'))
    let rec inheritSpine =
      function
      | (B, k, I.Nil, k', I.Nil, Bdd') -> Bdd'
      | (B, k, App (__u, S), k', App (__u', S'), Bdd') ->
          inheritSpine
            (B, k, S, k', S', (inheritExp (B, k, __u, k', __u', Bdd')))
    let rec inheritDec (B, k, Dec (_, __v), k', Dec (_, __v'), Bdd') =
      inheritExp (B, k, __v, k', __v', Bdd')
    let rec inheritDTop =
      function
      | (B, k, Pi ((Dec (_, V1), I.No), V2), k', Pi
         ((Dec (_, V1'), I.No), V2'), Bdd') ->
          inheritG
            (B, k, V1, k', V1',
              (inheritDTop (B, (k + 1), V2, (k' + 1), V2', Bdd')))
      | (B, k, (Root (Const cid, S) as __v), k', (Root (Const cid', S') as __v'),
         Bdd') ->
          let mS = valOf (ModeTable.modeLookup cid) in
          inheritSpineMode (M.Top, mS, B, k, S, k', S', Bdd')
    let rec inheritDBot =
      function
      | (B, k, Pi ((Dec (_, V1), I.No), V2), k', Pi
         ((Dec (_, V1'), I.No), V2'), Bdd') ->
          inheritDBot (B, (k + 1), V2, (k' + 1), V2', Bdd')
      | (B, k, Root (Const cid, S), k', Root (Const cid', S'), Bdd') ->
          let mS = valOf (ModeTable.modeLookup cid) in
          inheritSpineMode (M.Bot, mS, B, k, S, k', S', Bdd')
    let rec inheritG
      (B, k, Root (Const cid, S), k', (Root (Const cid', S') as __v'), Bdd') =
      let mS = valOf (ModeTable.modeLookup cid) in
      inheritSpineMode
        (M.Bot, mS, B, k, S, k', S',
          (inheritSpineMode (M.Top, mS, B, k, S, k', S', Bdd')))
    let rec inheritSpineMode =
      function
      | (mode, ModeSyn.Mnil, B, k, I.Nil, k', I.Nil, Bdd') -> Bdd'
      | (mode, Mapp (m, mS), B, k, App (__u, S), k', App (__u', S'), Bdd') ->
          if modeEq (m, mode)
          then
            inheritSpineMode
              (mode, mS, B, k, S, k', S',
                (inheritExp (B, k, __u, k', __u', Bdd')))
          else inheritSpineMode (mode, mS, B, k, S, k', S', Bdd')
    let rec inheritSplitDepth
      ((State (_, Prefix (__g, M, B), __v) as S),
       (State (name', Prefix (__g', M', B'), __v') as S'))
      =
      let d = I.ctxLength __g in
      let d' = I.ctxLength __g' in
      let __v = Whnf.normalize (__v, I.id) in
      let __v' = Whnf.normalize (__v', I.id) in
      let (B'', 0, 0) =
        inheritDBot
          (B, 0, __v, 0, __v', (inheritDTop (B, 0, __v, 0, __v', (I.Null, d, d')))) in
      M.State (name', (M.Prefix (__g', M', B'')), __v')
    let rec abstractInit (State (name, GM, __v))
      (name', Prefix (__g', M', B'), s') =
      inheritSplitDepth
        ((M.State (name, GM, __v)),
          (MetaAbstract.abstract
             (M.State
                ((name ^ name'), (M.Prefix (__g', M', B')), (I.EClo (__v, s'))))))
    let rec abstractCont ((__d, mode, b), abstract)
      (name', Prefix (__g', M', B'), s') =
      abstract
        (name',
          (M.Prefix
             ((I.Decl (__g', (I.decSub (__d, s')))), (I.Decl (M', mode)),
               (I.Decl (B', b)))), (I.dot1 s'))
    let rec makeAddressInit (S) k = (S, k)
    let rec makeAddressCont makeAddress k = makeAddress (k + 1)
    let rec expand' =
      function
      | (Prefix (I.Null, I.Null, I.Null), isIndex, abstract, makeAddress) ->
          ((M.Prefix (I.Null, I.Null, I.Null)), I.id, nil)
      | (Prefix (Decl (__g, __d), Decl (M, (M.Top as mode)), Decl (B, b)),
         isIndex, abstract, makeAddress) ->
          let (Prefix (__g', M', B'), s', ops) =
            expand'
              ((M.Prefix (__g, M, B)), (isIndexSucc (__d, isIndex)),
                (abstractCont ((__d, mode, b), abstract)),
                (makeAddressCont makeAddress)) in
          let Dec (xOpt, __v) = __d in
          let x = I.newEVar (__g', (I.EClo (__v, s'))) in
          let ops' =
            if (b > 0) && ((not (isIndex 1)) && (checkDec (M, __d)))
            then
              ((makeAddress 1),
                (split ((M.Prefix (__g', M', B')), (__d, s'), abstract))) :: ops
            else ops in
          ((M.Prefix (__g', M', B')), (I.Dot ((I.Exp x), s')), ops')
      | (Prefix (Decl (__g, __d), Decl (M, (M.Bot as mode)), Decl (B, b)),
         isIndex, abstract, makeAddress) ->
          let (Prefix (__g', M', B'), s', ops) =
            expand'
              ((M.Prefix (__g, M, B)), (isIndexSucc (__d, isIndex)),
                (abstractCont ((__d, mode, b), abstract)),
                (makeAddressCont makeAddress)) in
          ((M.Prefix
              ((I.Decl (__g', (I.decSub (__d, s')))), (I.Decl (M', M.Bot)),
                (I.Decl (B', b)))), (I.dot1 s'), ops)
    let rec expand (State (name, Prefix (__g, M, B), __v) as S) =
      let (_, _, ops) =
        expand'
          ((M.Prefix (__g, M, B)), isIndexInit, (abstractInit S),
            (makeAddressInit S)) in
      ops
    let rec index (_, Sl) = List.length Sl
    let rec apply (_, Sl) =
      map
        (function
         | Active (S) -> S
         | InActive -> raise (Error "Not applicable: leftover constraints"))
        Sl
    let rec menu (((State (name, Prefix (__g, M, B), __v), i), Sl) as Op) =
      let rec active =
        function
        | (nil, n) -> n
        | ((InActive)::__l, n) -> active (__l, n)
        | ((Active _)::__l, n) -> active (__l, (n + 1)) in
      let rec inactive =
        function
        | (nil, n) -> n
        | ((InActive)::__l, n) -> inactive (__l, (n + 1))
        | ((Active _)::__l, n) -> inactive (__l, n) in
      let rec indexToString =
        function
        | 0 -> "zero cases"
        | 1 -> "1 case"
        | n -> (Int.toString n) ^ " cases" in
      let rec flagToString =
        function
        | (_, 0) -> ""
        | (n, m) ->
            (((" [active: " ^ (Int.toString n)) ^ " inactive: ") ^
               (Int.toString m))
              ^ "]" in
      (((((^) "Splitting : " Print.decToString (__g, (I.ctxDec (__g, i)))) ^ " (")
          ^ (indexToString (index Op)))
         ^ (flagToString ((active (Sl, 0)), (inactive (Sl, 0)))))
        ^ ")"
    let rec var ((_, i), _) = i
    (* constCases (__g, (__v, s), I, abstract, C) = C'

       Invariant:
       If   __g |- s : __g'  __g' |- __v : type
       and  I a list of of constant declarations
       and  abstract an abstraction function
       and  C a list of possible cases
       then C' is a list extending C, containing all possible
         cases from I
    *)
    (* paramCases (__g, (__v, s), k, abstract, C) = C'

       Invariant:
       If   __g |- s : __g'  __g' |- __v : type
       and  k a variable
       and  abstract an abstraction function
       and  C a list of possible cases
       then C' is a list extending C, containing all possible
         cases introduced by parameters <= k in __g
    *)
    (* lowerSplitDest (__g, (__v, s'), abstract) = C'

       Invariant:
       If   G0, __g |- s' : G1  G1 |- __v: type
       and  __g is the context of local parameters
       and  abstract abstraction function
       then C' is a list of all cases unifying with __v[s']
            (it contains constant and parameter cases)
    *)
    (* split ((__g, M), (x:__d, s), abstract) = C'

       Invariant :
       If   |- __g ctx
       and  __g |- M mtx
       and  __g |- s : G1   and  G1 |- __d : __l
       and  abstract abstraction function
       then C' = (C1, ... Cn) are resulting cases from splitting __d[s]
    *)
    (* rename to add N prefix? *)
    (* occursIn (k, __u) = B,

       Invariant:
       If    __u in nf
       then  B iff k occurs in __u
    *)
    (* no case for Redex, EVar, EClo *)
    (* no case for FVar *)
    (* no case for SClo *)
    (* checkExp (M, __u) = B

       Invariant:
       If   __g |- M
       and  __g |- __u : __v
       and  __u in nf
       then B holds iff __u does not contain any Bot variables
    *)
    (* copied from meta-abstract *)
    (* modeEq (marg, st) = B'

       Invariant:
       If   (marg = + and st = top) or (marg = - and st = bot)
       then B' = true
       else B' = false
    *)
    (*
       The inherit functions below copy the splitting depth attribute
       between successive states, using a simultaneous traversal
       in mode dependency order.

       Invariant:
       (__g,M,B) |- __v type
       __g = G0, G1, G2
       |G2| = k       (length of local context)
       d = |G1, G2|   (last BVar seen)
       let n < |__g|
       if   n>d then n is an index of a variable already seen in mdo
       if   n=d then n is an index of a variable now seen for the first
                     time
       if   n<=k then n is a local parameter
       it is impossible for     k < n < d
    *)
    (* invariants on inheritXXX functions? -fp *)
    (* necessary for d' = 0 *)
    (* skip *)
    (* necessary for d = 0 *)
    (* Uni impossible *)
    (* new original variable *)
    (* inheritBelow (I.ctxLookup (B, n-k) - 1, k', __v', (B', d-1, d')) *)
    (* already seen original variable *)
    (* then (B', d, d') *)
    (* previous line avoids redundancy,
                  but may violate invariant outside pattern fragment *)
    (* must correspond *)
    (* C' = BVar (n) *)
    (* C ~ C' *)
    (* n = k+d *)
    (* n' also new --- same variable: do not decrease *)
    (* n' not new --- decrease the splitting depth of all variables in __v' *)
    (* cid = cid' *)
    (* cid = cid' *)
    (* mode dependency in Goal: first M.Top, then M.Bot *)
    (* S' *)
    (* current first occurrence depth in __v *)
    (* current first occurrence depth in __v' *)
    (* mode dependency in Clause: first M.Top then M.Bot *)
    (* check proper traversal *)
    (* abstractInit (M.State (name, M.Prefix (__g, M, B), __v)) = __F'

       State is the state before splitting, to inherit splitting depths.
       Invariant:
       If   __g |- __v : __l
       then forall |- __g' ctx
            and    __g' |- M' ctx
            and    __g' |- s' : __g
            and    names name'
            then   following holds: S' = __F' (name', __g', M', s')
                                    S' is a new state
    *)
    (* abstractInit (x:__d, mode, F) = __F'

       Invariant:
       If   __g |- __d : __l
       and  forall |- __g' ctx
            and    __g' |- M' ctx
            and    __g' |- s' : __g
            and    names name'
            then   S' = F (name', __g', M', s')
       then forall |- __g' ctx
            and    __g' |- M' ctx
            and    __g' |- s' : __g
            then   following holds: S' = F (name', (__g', __d[s]) , (M', mode) , 1 . s' o ^)
                                    is a new state
    *)
    (* expand' (M.Prefix (__g, M), isIndex, abstract, makeAddress) = (M.Prefix (__g', M'), s', ops')

       Invariant:
       If   |- __g ctx
       and  __g |- M mtx
       and  isIndex (k) = B function s.t. B holds iff k index
       and  abstract, dynamic abstraction function
       and  makeAddress, a function which calculates the index of the variable
            to be split
       then |- __g' ctx
       and  __g' |- M' mtx
       and  __g' is a subcontext of __g where all Top variables have been replaced
            by EVars'
       and  __g' |- s' : __g
       and  ops' is a list of all possiblie splitting operators
    *)
    (* check if splitting bound > 0 *)
    (* -###- *)
    (* b = 0 *)
    (* expand ((__g, M), __v) = ops'

       Invariant:
       If   |- __g ctx
       and  __g |- M mtx
       and  __g |- __v : __l
       then ops' is a list of all possiblie splitting operators
    *)
    (* index (Op) = k

       Invariant:
       If   Op = (_, S) then k = |S|
    *)
    (* apply (Op) = Sl'

       Invariant:
       If   Op = (_, Sl) then Sl' = Sl
    *)
    (* menu (Op) = s'

       Invariant:
       If   Op = ((__g, __d), Sl)
       and  __g |- __d : __l
       then s' = string describing the operator
    *)
    let expand = expand
    let apply = apply
    let var = var
    let index = index
    let menu = menu
  end ;;
