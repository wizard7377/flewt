
module type SPLITTING  =
  sig
    module MetaSyn :
    ((METASYN)(* Splitting *)(* Author: Carsten Schuermann *))
    exception Error of string 
    type nonrec operator
    val expand : MetaSyn.__State -> operator list
    val apply : operator -> MetaSyn.__State list
    val var : operator -> int
    val menu : operator -> string
    val index : operator -> int
  end;;




module Splitting(Splitting:sig
                             module Global : GLOBAL
                             module MetaSyn' : METASYN
                             module MetaAbstract : METAABSTRACT
                             module MetaPrint : METAPRINT
                             module ModeTable : MODETABLE
                             module Whnf : WHNF
                             module Index : INDEX
                             module Print : PRINT
                             module Unify :
                             ((UNIFY)(* Splitting *)
                             (* Author: Carsten Schuermann *)(*! sharing ModeSyn.IntSyn = MetaSyn'.IntSyn !*)
                             (*! sharing Whnf.IntSyn = MetaSyn'.IntSyn !*)
                             (*! sharing Index.IntSyn = MetaSyn'.IntSyn !*)
                             (*! sharing Print.IntSyn = MetaSyn'.IntSyn !*))
                           end) : SPLITTING =
  struct
    module MetaSyn =
      ((MetaSyn')(*! sharing Unify.IntSyn = MetaSyn'.IntSyn !*)(*! structure CSManager : CS_MANAGER !*)
      (*! sharing CSManager.IntSyn = MetaSyn'.IntSyn !*))
    exception Error of string 
    type 'a flag =
      | Active of
      (('a)(* Invariant:
     Case analysis generates a list of successor states
     (the cases) from a given state.

     'a flag marks cases where unification of the types
     succeeded as "Active", and cases where there were
     leftover constraints after unification as "Inactive".

     NB: cases where unification fails are not considered

     Consequence: Only those splitting operators can be
     applied which do not generate inactive cases.
  *))
      
      | InActive 
    type nonrec operator =
      ((MetaSyn.__State * int) * MetaSyn.__State flag list)
    module M = MetaSyn
    module I = IntSyn
    let rec constCases =
      function
      | (G, Vs, nil, abstract, ops) -> ops
      | (G, Vs, (Const c)::Sgn, abstract, ops) ->
          let (U, Vs') = M.createAtomConst (G, (I.Const c)) in
          constCases
            (G, Vs, Sgn, abstract,
              (CSManager.trail
                 (function
                  | () ->
                      (try
                         if Unify.unifiable (G, Vs, Vs')
                         then
                           (Active
                              (abstract
                                 (((I.conDecName (I.sgnLookup c)) ^ "/"), U)))
                             :: ops
                         else ops
                       with | Error _ -> InActive :: ops))))
    let rec paramCases =
      function
      | (G, Vs, 0, abstract, ops) -> ops
      | (G, Vs, k, abstract, ops) ->
          let (U, Vs') = M.createAtomBVar (G, k) in
          paramCases
            (G, Vs, (k - 1), abstract,
              (CSManager.trail
                 (function
                  | () ->
                      (try
                         if Unify.unifiable (G, Vs, Vs')
                         then
                           (Active (abstract (((Int.toString k) ^ "/"), U)))
                             :: ops
                         else ops
                       with | Error _ -> InActive :: ops))))
    let rec lowerSplitDest =
      function
      | (G, ((Root (Const c, _) as V), s'), abstract) ->
          constCases
            (G, (V, s'), (Index.lookup c), abstract,
              (paramCases (G, (V, s'), (I.ctxLength G), abstract, nil)))
      | (G, (Pi ((D, P), V), s'), abstract) ->
          let D' = I.decSub (D, s') in
          lowerSplitDest
            ((I.Decl (G, D')), (V, (I.dot1 s')),
              (function | (name, U) -> abstract (name, (I.Lam (D', U)))))
    let rec split (Prefix (G, M, B), ((Dec (_, V) as D), s), abstract) =
      lowerSplitDest
        (I.Null, (V, s),
          (function
           | (name', U') ->
               abstract
                 (name', (M.Prefix (G, M, B)), (I.Dot ((I.Exp U'), s)))))
    let rec occursInExp =
      function
      | (k, Uni _) -> false__
      | (k, Pi (DP, V)) ->
          (occursInDecP (k, DP)) || (occursInExp ((k + 1), V))
      | (k, Root (C, S)) -> (occursInCon (k, C)) || (occursInSpine (k, S))
      | (k, Lam (D, V)) -> (occursInDec (k, D)) || (occursInExp ((k + 1), V))
      | (k, FgnExp csfe) ->
          I.FgnExpStd.fold csfe
            (function
             | (U, B) -> B || (occursInExp (k, (Whnf.normalize (U, I.id)))))
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
      | (k, App (U, S)) -> (occursInExp (k, U)) || (occursInSpine (k, S))
    let rec occursInDec (k, Dec (_, V)) = occursInExp (k, V)
    let rec occursInDecP (k, (D, _)) = occursInDec (k, D)
    let rec isIndexInit k = false__
    let rec isIndexSucc (D, isIndex) k =
      (occursInDec (k, D)) || (isIndex (k + 1))
    let rec isIndexFail (D, isIndex) k = isIndex (k + 1)
    let rec checkVar =
      function
      | (Decl (M, M.Top), 1) -> true__
      | (Decl (M, M.Bot), 1) -> false__
      | (Decl (M, _), k) -> checkVar (M, (k - 1))
    let rec checkExp =
      function
      | (M, Uni _) -> true__
      | (M, Pi ((D, P), V)) ->
          (checkDec (M, D)) && (checkExp ((I.Decl (M, M.Top)), V))
      | (M, Lam (D, V)) ->
          (checkDec (M, D)) && (checkExp ((I.Decl (M, M.Top)), V))
      | (M, Root (BVar k, S)) -> (checkVar (M, k)) && (checkSpine (M, S))
      | (M, Root (_, S)) -> checkSpine (M, S)
    let rec checkSpine =
      function
      | (M, I.Nil) -> true__
      | (M, App (U, S)) -> (checkExp (M, U)) && (checkSpine (M, S))
    let rec checkDec (M, Dec (_, V)) = checkExp (M, V)
    let rec modeEq =
      function
      | (Marg (ModeSyn.Plus, _), M.Top) -> true__
      | (Marg (ModeSyn.Minus, _), M.Bot) -> true__
      | _ -> false__
    let rec inheritBelow =
      function
      | (b', k', Lam (D', U'), Bdd') ->
          inheritBelow
            (b', (k' + 1), U', (inheritBelowDec (b', k', D', Bdd')))
      | (b', k', Pi ((D', _), V'), Bdd') ->
          inheritBelow
            (b', (k' + 1), V', (inheritBelowDec (b', k', D', Bdd')))
      | (b', k', Root (BVar n', S'), (B', d, d')) ->
          if ((n' = k') + d') && (n' > k')
          then
            inheritBelowSpine (b', k', S', ((I.Decl (B', b')), d, (d' - 1)))
          else inheritBelowSpine (b', k', S', (B', d, d'))
      | (b', k', Root (C, S'), Bdd') -> inheritBelowSpine (b', k', S', Bdd')
    let rec inheritBelowSpine =
      function
      | (b', k', I.Nil, Bdd') -> Bdd'
      | (b', k', App (U', S'), Bdd') ->
          inheritBelowSpine (b', k', S', (inheritBelow (b', k', U', Bdd')))
    let rec inheritBelowDec (b', k', Dec (x, V'), Bdd') =
      inheritBelow (b', k', V', Bdd')
    let rec skip =
      function
      | (k, Lam (D, U), Bdd') -> skip ((k + 1), U, (skipDec (k, D, Bdd')))
      | (k, Pi ((D, _), V), Bdd') ->
          skip ((k + 1), V, (skipDec (k, D, Bdd')))
      | (k, Root (BVar n, S), (B', d, d')) ->
          if ((n = k) + d) && (n > k)
          then skipSpine (k, S, (B', (d - 1), d'))
          else skipSpine (k, S, (B', d, d'))
      | (k, Root (C, S), Bdd') -> skipSpine (k, S, Bdd')
    let rec skipSpine =
      function
      | (k, I.Nil, Bdd') -> Bdd'
      | (k, App (U, S), Bdd') -> skipSpine (k, S, (skip (k, U, Bdd')))
    let rec skipDec (k, Dec (x, V), Bdd') = skip (k, V, Bdd')
    let rec inheritExp =
      function
      | (B, k, Lam (D, U), k', Lam (D', U'), Bdd') ->
          inheritExp
            (B, (k + 1), U, (k' + 1), U',
              (inheritDec (B, k, D, k', D', Bdd')))
      | (B, k, Pi ((D, _), V), k', Pi ((D', _), V'), Bdd') ->
          inheritExp
            (B, (k + 1), V, (k' + 1), V',
              (inheritDec (B, k, D, k', D', Bdd')))
      | (B, k, (Root (BVar n, S) as V), k', V', (B', d, d')) ->
          if ((n = k) + d) && (n > k)
          then
            skipSpine
              (k, S,
                (inheritNewRoot
                   (B, (I.ctxLookup (B, (n - k))), k, V, k', V', (B', d, d'))))
          else
            if (n > k) + d
            then
              skipSpine
                (k, S,
                  (inheritBelow
                     (((I.ctxLookup (B, (n - k))) - 1), k', V', (B', d, d'))))
            else
              (let Root (C', S') = V' in
               inheritSpine (B, k, S, k', S', (B', d, d')))
      | (B, k, Root (C, S), k', Root (C', S'), Bdd') ->
          inheritSpine (B, k, S, k', S', Bdd')
    let rec inheritNewRoot =
      function
      | (B, b, k, Root (BVar n, S), k', (Root (BVar n', S') as V'),
         (B', d, d')) ->
          if ((n' = k') + d') && (n' > k')
          then inheritBelow (b, k', V', (B', (d - 1), d'))
          else inheritBelow ((b - 1), k', V', (B', (d - 1), d'))
      | (B, b, k, V, k', V', (B', d, d')) ->
          inheritBelow ((b - 1), k', V', (B', (d - 1), d'))
    let rec inheritSpine =
      function
      | (B, k, I.Nil, k', I.Nil, Bdd') -> Bdd'
      | (B, k, App (U, S), k', App (U', S'), Bdd') ->
          inheritSpine
            (B, k, S, k', S', (inheritExp (B, k, U, k', U', Bdd')))
    let rec inheritDec (B, k, Dec (_, V), k', Dec (_, V'), Bdd') =
      inheritExp (B, k, V, k', V', Bdd')
    let rec inheritDTop =
      function
      | (B, k, Pi ((Dec (_, V1), I.No), V2), k', Pi
         ((Dec (_, V1'), I.No), V2'), Bdd') ->
          inheritG
            (B, k, V1, k', V1',
              (inheritDTop (B, (k + 1), V2, (k' + 1), V2', Bdd')))
      | (B, k, (Root (Const cid, S) as V), k', (Root (Const cid', S') as V'),
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
      (B, k, Root (Const cid, S), k', (Root (Const cid', S') as V'), Bdd') =
      let mS = valOf (ModeTable.modeLookup cid) in
      inheritSpineMode
        (M.Bot, mS, B, k, S, k', S',
          (inheritSpineMode (M.Top, mS, B, k, S, k', S', Bdd')))
    let rec inheritSpineMode =
      function
      | (mode, ModeSyn.Mnil, B, k, I.Nil, k', I.Nil, Bdd') -> Bdd'
      | (mode, Mapp (m, mS), B, k, App (U, S), k', App (U', S'), Bdd') ->
          if modeEq (m, mode)
          then
            inheritSpineMode
              (mode, mS, B, k, S, k', S',
                (inheritExp (B, k, U, k', U', Bdd')))
          else inheritSpineMode (mode, mS, B, k, S, k', S', Bdd')
    let rec inheritSplitDepth
      ((State (_, Prefix (G, M, B), V) as S),
       (State (name', Prefix (G', M', B'), V') as S'))
      =
      let d = I.ctxLength G in
      let d' = I.ctxLength G' in
      let V = Whnf.normalize (V, I.id) in
      let V' = Whnf.normalize (V', I.id) in
      let (B'', 0, 0) =
        inheritDBot
          (B, 0, V, 0, V', (inheritDTop (B, 0, V, 0, V', (I.Null, d, d')))) in
      M.State (name', (M.Prefix (G', M', B'')), V')
    let rec abstractInit (State (name, GM, V))
      (name', Prefix (G', M', B'), s') =
      inheritSplitDepth
        ((M.State (name, GM, V)),
          (MetaAbstract.abstract
             (M.State
                ((name ^ name'), (M.Prefix (G', M', B')), (I.EClo (V, s'))))))
    let rec abstractCont ((D, mode, b), abstract)
      (name', Prefix (G', M', B'), s') =
      abstract
        (name',
          (M.Prefix
             ((I.Decl (G', (I.decSub (D, s')))), (I.Decl (M', mode)),
               (I.Decl (B', b)))), (I.dot1 s'))
    let rec makeAddressInit (S) k = (S, k)
    let rec makeAddressCont makeAddress k = makeAddress (k + 1)
    let rec expand' =
      function
      | (Prefix (I.Null, I.Null, I.Null), isIndex, abstract, makeAddress) ->
          ((M.Prefix (I.Null, I.Null, I.Null)), I.id, nil)
      | (Prefix (Decl (G, D), Decl (M, (M.Top as mode)), Decl (B, b)),
         isIndex, abstract, makeAddress) ->
          let (Prefix (G', M', B'), s', ops) =
            expand'
              ((M.Prefix (G, M, B)), (isIndexSucc (D, isIndex)),
                (abstractCont ((D, mode, b), abstract)),
                (makeAddressCont makeAddress)) in
          let Dec (xOpt, V) = D in
          let X = I.newEVar (G', (I.EClo (V, s'))) in
          let ops' =
            if (b > 0) && ((not (isIndex 1)) && (checkDec (M, D)))
            then
              ((makeAddress 1),
                (split ((M.Prefix (G', M', B')), (D, s'), abstract))) :: ops
            else ops in
          ((M.Prefix (G', M', B')), (I.Dot ((I.Exp X), s')), ops')
      | (Prefix (Decl (G, D), Decl (M, (M.Bot as mode)), Decl (B, b)),
         isIndex, abstract, makeAddress) ->
          let (Prefix (G', M', B'), s', ops) =
            expand'
              ((M.Prefix (G, M, B)), (isIndexSucc (D, isIndex)),
                (abstractCont ((D, mode, b), abstract)),
                (makeAddressCont makeAddress)) in
          ((M.Prefix
              ((I.Decl (G', (I.decSub (D, s')))), (I.Decl (M', M.Bot)),
                (I.Decl (B', b)))), (I.dot1 s'), ops)
    let rec expand (State (name, Prefix (G, M, B), V) as S) =
      let (_, _, ops) =
        expand'
          ((M.Prefix (G, M, B)), isIndexInit, (abstractInit S),
            (makeAddressInit S)) in
      ops
    let rec index (_, Sl) = List.length Sl
    let rec apply (_, Sl) =
      map
        (function
         | Active (S) -> S
         | InActive -> raise (Error "Not applicable: leftover constraints"))
        Sl
    let rec menu (((State (name, Prefix (G, M, B), V), i), Sl) as Op) =
      let active =
        function
        | (nil, n) -> n
        | ((InActive)::L, n) -> active (L, n)
        | ((Active _)::L, n) -> active (L, (n + 1)) in
      let inactive =
        function
        | (nil, n) -> n
        | ((InActive)::L, n) -> inactive (L, (n + 1))
        | ((Active _)::L, n) -> inactive (L, n) in
      let indexToString =
        function
        | 0 -> "zero cases"
        | 1 -> "1 case"
        | n -> (Int.toString n) ^ " cases" in
      let flagToString =
        function
        | (_, 0) -> ""
        | (n, m) ->
            (((" [active: " ^ (Int.toString n)) ^ " inactive: ") ^
               (Int.toString m))
              ^ "]" in
      (((((^) "Splitting : " Print.decToString (G, (I.ctxDec (G, i)))) ^ " (")
          ^ (indexToString (index Op)))
         ^ (flagToString ((active (Sl, 0)), (inactive (Sl, 0)))))
        ^ ")"
    let rec var ((_, i), _) = i
    let ((expand)(* constCases (G, (V, s), I, abstract, C) = C'

       Invariant:
       If   G |- s : G'  G' |- V : type
       and  I a list of of constant declarations
       and  abstract an abstraction function
       and  C a list of possible cases
       then C' is a list extending C, containing all possible
         cases from I
    *)
      (* paramCases (G, (V, s), k, abstract, C) = C'

       Invariant:
       If   G |- s : G'  G' |- V : type
       and  k a variable
       and  abstract an abstraction function
       and  C a list of possible cases
       then C' is a list extending C, containing all possible
         cases introduced by parameters <= k in G
    *)
      (* lowerSplitDest (G, (V, s'), abstract) = C'

       Invariant:
       If   G0, G |- s' : G1  G1 |- V: type
       and  G is the context of local parameters
       and  abstract abstraction function
       then C' is a list of all cases unifying with V[s']
            (it contains constant and parameter cases)
    *)
      (* split ((G, M), (x:D, s), abstract) = C'

       Invariant :
       If   |- G ctx
       and  G |- M mtx
       and  G |- s : G1   and  G1 |- D : L
       and  abstract abstraction function
       then C' = (C1, ... Cn) are resulting cases from splitting D[s]
    *)
      (* rename to add N prefix? *)(* occursIn (k, U) = B,

       Invariant:
       If    U in nf
       then  B iff k occurs in U
    *)
      (* no case for Redex, EVar, EClo *)(* no case for FVar *)
      (* no case for SClo *)(* checkExp (M, U) = B

       Invariant:
       If   G |- M
       and  G |- U : V
       and  U in nf
       then B holds iff U does not contain any Bot variables
    *)
      (* copied from meta-abstract *)(* modeEq (marg, st) = B'

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
       (G,M,B) |- V type
       G = G0, G1, G2
       |G2| = k       (length of local context)
       d = |G1, G2|   (last BVar seen)
       let n < |G|
       if   n>d then n is an index of a variable already seen in mdo
       if   n=d then n is an index of a variable now seen for the first
                     time
       if   n<=k then n is a local parameter
       it is impossible for     k < n < d
    *)
      (* invariants on inheritXXX functions? -fp *)(* necessary for d' = 0 *)
      (* skip *)(* necessary for d = 0 *)
      (* Uni impossible *)(* new original variable *)
      (* inheritBelow (I.ctxLookup (B, n-k) - 1, k', V', (B', d-1, d')) *)
      (* already seen original variable *)(* then (B', d, d') *)
      (* previous line avoids redundancy,
                  but may violate invariant outside pattern fragment *)
      (* must correspond *)(* C' = BVar (n) *)(* C ~ C' *)
      (* n = k+d *)(* n' also new --- same variable: do not decrease *)
      (* n' not new --- decrease the splitting depth of all variables in V' *)
      (* cid = cid' *)(* cid = cid' *)
      (* mode dependency in Goal: first M.Top, then M.Bot *)
      (* S' *)(* current first occurrence depth in V *)
      (* current first occurrence depth in V' *)(* mode dependency in Clause: first M.Top then M.Bot *)
      (* check proper traversal *)(* abstractInit (M.State (name, M.Prefix (G, M, B), V)) = F'

       State is the state before splitting, to inherit splitting depths.
       Invariant:
       If   G |- V : L
       then forall |- G' ctx
            and    G' |- M' ctx
            and    G' |- s' : G
            and    names name'
            then   following holds: S' = F' (name', G', M', s')
                                    S' is a new state
    *)
      (* abstractInit (x:D, mode, F) = F'

       Invariant:
       If   G |- D : L
       and  forall |- G' ctx
            and    G' |- M' ctx
            and    G' |- s' : G
            and    names name'
            then   S' = F (name', G', M', s')
       then forall |- G' ctx
            and    G' |- M' ctx
            and    G' |- s' : G
            then   following holds: S' = F (name', (G', D[s]) , (M', mode) , 1 . s' o ^)
                                    is a new state
    *)
      (* expand' (M.Prefix (G, M), isIndex, abstract, makeAddress) = (M.Prefix (G', M'), s', ops')

       Invariant:
       If   |- G ctx
       and  G |- M mtx
       and  isIndex (k) = B function s.t. B holds iff k index
       and  abstract, dynamic abstraction function
       and  makeAddress, a function which calculates the index of the variable
            to be split
       then |- G' ctx
       and  G' |- M' mtx
       and  G' is a subcontext of G where all Top variables have been replaced
            by EVars'
       and  G' |- s' : G
       and  ops' is a list of all possiblie splitting operators
    *)
      (* check if splitting bound > 0 *)(* -###- *)
      (* b = 0 *)(* expand ((G, M), V) = ops'

       Invariant:
       If   |- G ctx
       and  G |- M mtx
       and  G |- V : L
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
       If   Op = ((G, D), Sl)
       and  G |- D : L
       then s' = string describing the operator
    *))
      = expand
    let apply = apply
    let var = var
    let index = index
    let menu = menu
  end ;;
