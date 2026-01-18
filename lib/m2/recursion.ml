
(* Recursion *)
(* Author: Carsten Schuermann *)
module type RECURSION  =
  sig
    module MetaSyn : METASYN
    exception Error of string 
    type nonrec operator
    val expandLazy : MetaSyn.__State -> operator list
    val expandEager : MetaSyn.__State -> operator list
    val apply : operator -> MetaSyn.__State
    val menu : operator -> string
  end;;




(* Recursion *)
(* Author: Carsten Schuermann *)
(* See [Rohwedder,Pfenning ESOP'96] *)
module Recursion(Recursion:sig
                             module Global : GLOBAL
                             module MetaSyn' : METASYN
                             module Whnf : WHNF
                             module Unify : UNIFY
                             module Conv : CONV
                             module Names : NAMES
                             module Subordinate : SUBORDINATE
                             module Print : PRINT
                             module Order : ORDER
                             module ModeTable : MODETABLE
                             module Lemma : LEMMA
                             module Filling : FILLING
                             module MetaPrint : METAPRINT
                             module MetaAbstract : METAABSTRACT
                             (*! sharing Whnf.IntSyn = MetaSyn'.IntSyn !*)
                             (*! sharing Unify.IntSyn = MetaSyn'.IntSyn !*)
                             (*! sharing Conv.IntSyn = MetaSyn'.IntSyn !*)
                             (*! sharing Names.IntSyn = MetaSyn'.IntSyn !*)
                             (*! sharing Subordinate.IntSyn = MetaSyn'.IntSyn !*)
                             (*! sharing Print.IntSyn = MetaSyn'.IntSyn !*)
                             (*! sharing Order.IntSyn = MetaSyn'.IntSyn !*)
                             (*! sharing ModeSyn.IntSyn = MetaSyn'.IntSyn !*)
                             module Formatter : FORMATTER
                           end) : RECURSION =
  struct
    (*! structure CSManager : CS_MANAGER !*)
    (*! sharing CSManager.IntSyn = MetaSyn'.IntSyn !*)
    module MetaSyn = MetaSyn'
    exception Error of string 
    type nonrec operator = MetaSyn.__State
    module M = MetaSyn
    module I = IntSyn
    module O = Order
    module N = Names
    module F = Formatter
    type __Quantifier =
      | Universal 
      | Existential 
    let rec vectorToString (G, O) =
      let rec fmtOrder =
        function
        | Arg (Us, Vs) ->
            [F.String (Print.expToString (G, (I.EClo Us)));
            F.String ":";
            F.String (Print.expToString (G, (I.EClo Vs)))]
        | Lex (L) -> [F.String "{"; F.HVbox (fmtOrders L); F.String "}"]
        | Simul (L) -> [F.String "["; F.HVbox (fmtOrders L); F.String "]"]
      and fmtOrders =
        function
        | nil -> nil
        | (O)::nil -> fmtOrder O
        | (O)::L -> (fmtOrder O) @ ((::) (F.String " ") fmtOrders L) in
      F.makestring_fmt (F.HVbox (fmtOrder O))
    let rec vector (c, (S, s)) =
      let Vid = ((I.constType c), I.id) in
      let rec select' (n, (Ss', Vs'')) =
        select'W (n, (Ss', (Whnf.whnf Vs'')))
      and select'W =
        function
        | (1, ((App (U', S'), s'), (Pi ((Dec (_, V''), _), _), s''))) ->
            ((U', s'), (V'', s''))
        | (n, ((SClo (S', s1'), s2'), Vs'')) ->
            select'W (n, ((S', (I.comp (s1', s2'))), Vs''))
        | (n, ((App (U', S'), s'), (Pi ((Dec (_, V1''), _), V2''), s''))) ->
            select'
              ((n - 1),
                ((S', s'), (V2'', (I.Dot ((I.Exp (I.EClo (U', s'))), s''))))) in
      let rec select =
        function
        | Arg n -> O.Arg (select' (n, ((S, s), Vid)))
        | Lex (L) -> O.Lex (map select L)
        | Simul (L) -> O.Simul (map select L) in
      select (O.selLookup c)
    let rec set_parameter (G, (EVar (r, _, V, _) as X), k, sc, ops) =
      let rec set_parameter' =
        function
        | (0, ops') -> ops'
        | (k', ops') ->
            let Dec (_, V') as D' = I.ctxDec (G, k') in
            let ops'' =
              CSManager.trail
                (function
                 | () ->
                     if
                       (Unify.unifiable (G, (V, I.id), (V', I.id))) &&
                         (Unify.unifiable
                            (G, (X, I.id),
                              ((I.Root ((I.BVar k'), I.Nil)), I.id)))
                     then sc ops'
                     else ops') in
            set_parameter' ((k' - 1), ops'') in
      set_parameter' (k, ops)
    let rec ltinit (G, k, (Us, Vs), UsVs', sc, ops) =
      ltinitW (G, k, (Whnf.whnfEta (Us, Vs)), UsVs', sc, ops)
    let rec ltinitW =
      function
      | (G, k, (Us, ((Root _, _) as Vs)), UsVs', sc, ops) ->
          lt (G, k, (Us, Vs), UsVs', sc, ops)
      | (G, k, ((Lam (D1, U), s1), (Pi (D2, V), s2)), ((U', s1'), (V', s2')),
         sc, ops) ->
          ltinit
            ((I.Decl (G, (I.decSub (D1, s1)))), (k + 1),
              ((U, (I.dot1 s1)), (V, (I.dot1 s2))),
              ((U', (I.comp (s1', I.shift))), (V', (I.comp (s2', I.shift)))),
              sc, ops)
    let rec lt (G, k, (Us, Vs), (Us', Vs'), sc, ops) =
      ltW (G, k, (Us, Vs), (Whnf.whnfEta (Us', Vs')), sc, ops)
    let rec ltW =
      function
      | (G, k, (Us, Vs), ((Root (Const c, S'), s'), Vs'), sc, ops) ->
          ltSpine
            (G, k, (Us, Vs), ((S', s'), ((I.constType c), I.id)), sc, ops)
      | (G, k, (Us, Vs), ((Root (BVar n, S'), s'), Vs'), sc, ops) ->
          if n <= k
          then
            let Dec (_, V') = I.ctxDec (G, n) in
            ltSpine (G, k, (Us, Vs), ((S', s'), (V', I.id)), sc, ops)
          else ops
      | (G, _, _, ((EVar _, _), _), _, ops) -> ops
      | (G, k, ((U, s1), (V, s2)),
         ((Lam ((Dec (_, V1') as D), U'), s1'),
          (Pi ((Dec (_, V2'), _), V'), s2')),
         sc, ops) ->
          if Subordinate.equiv ((I.targetFam V), (I.targetFam V1'))
          then
            let X = I.newEVar (G, (I.EClo (V1', s1'))) in
            let sc' = function | ops' -> set_parameter (G, X, k, sc, ops') in
            lt
              (G, k, ((U, s1), (V, s2)),
                ((U', (I.Dot ((I.Exp X), s1'))),
                  (V', (I.Dot ((I.Exp X), s2')))), sc', ops)
          else
            if Subordinate.below ((I.targetFam V1'), (I.targetFam V))
            then
              (let X = I.newEVar (G, (I.EClo (V1', s1'))) in
               lt
                 (G, k, ((U, s1), (V, s2)),
                   ((U', (I.Dot ((I.Exp X), s1'))),
                     (V', (I.Dot ((I.Exp X), s2')))), sc, ops))
            else ops
    let rec ltSpine (G, k, (Us, Vs), (Ss', Vs'), sc, ops) =
      ltSpineW (G, k, (Us, Vs), (Ss', (Whnf.whnf Vs')), sc, ops)
    let rec ltSpineW =
      function
      | (G, k, (Us, Vs), ((I.Nil, _), _), _, ops) -> ops
      | (G, k, (Us, Vs), ((SClo (S, s'), s''), Vs'), sc, ops) ->
          ltSpineW (G, k, (Us, Vs), ((S, (I.comp (s', s''))), Vs'), sc, ops)
      | (G, k, (Us, Vs),
         ((App (U', S'), s1'), (Pi ((Dec (_, V1'), _), V2'), s2')), sc, ops)
          ->
          let ops' = le (G, k, (Us, Vs), ((U', s1'), (V1', s2')), sc, ops) in
          ltSpine
            (G, k, (Us, Vs),
              ((S', s1'), (V2', (I.Dot ((I.Exp (I.EClo (U', s1'))), s2')))),
              sc, ops')
    let rec eq (G, (Us, Vs), (Us', Vs'), sc, ops) =
      CSManager.trail
        (function
         | () ->
             if
               (Unify.unifiable (G, Vs, Vs')) &&
                 (Unify.unifiable (G, Us, Us'))
             then sc ops
             else ops)
    let rec le (G, k, (Us, Vs), (Us', Vs'), sc, ops) =
      let ops' = eq (G, (Us, Vs), (Us', Vs'), sc, ops) in
      leW (G, k, (Us, Vs), (Whnf.whnfEta (Us', Vs')), sc, ops')
    let rec leW =
      function
      | (G, k, ((U, s1), (V, s2)),
         ((Lam ((Dec (_, V1') as D), U'), s1'),
          (Pi ((Dec (_, V2'), _), V'), s2')),
         sc, ops) ->
          if Subordinate.equiv ((I.targetFam V), (I.targetFam V1'))
          then
            let X = I.newEVar (G, (I.EClo (V1', s1'))) in
            let sc' = function | ops' -> set_parameter (G, X, k, sc, ops') in
            le
              (G, k, ((U, s1), (V, s2)),
                ((U', (I.Dot ((I.Exp X), s1'))),
                  (V', (I.Dot ((I.Exp X), s2')))), sc', ops)
          else
            if Subordinate.below ((I.targetFam V1'), (I.targetFam V))
            then
              (let X = I.newEVar (G, (I.EClo (V1', s1'))) in
               le
                 (G, k, ((U, s1), (V, s2)),
                   ((U', (I.Dot ((I.Exp X), s1'))),
                     (V', (I.Dot ((I.Exp X), s2')))), sc, ops))
            else ops
      | (G, k, (Us, Vs), (Us', Vs'), sc, ops) ->
          lt (G, k, (Us, Vs), (Us', Vs'), sc, ops)
    let rec ordlt =
      function
      | (G, Arg (UsVs), Arg (UsVs'), sc, ops) ->
          ltinit (G, 0, UsVs, UsVs', sc, ops)
      | (G, Lex (L), Lex (L'), sc, ops) -> ordltLex (G, L, L', sc, ops)
      | (G, Simul (L), Simul (L'), sc, ops) -> ordltSimul (G, L, L', sc, ops)
    let rec ordltLex =
      function
      | (G, nil, nil, sc, ops) -> ops
      | (G, (O)::L, (O')::L', sc, ops) ->
          let ops' =
            CSManager.trail (function | () -> ordlt (G, O, O', sc, ops)) in
          ordeq
            (G, O, O', (function | ops'' -> ordltLex (G, L, L', sc, ops'')),
              ops')
    let rec ordltSimul =
      function
      | (G, nil, nil, sc, ops) -> ops
      | (G, (O)::L, (O')::L', sc, ops) ->
          let ops'' =
            CSManager.trail
              (function
               | () ->
                   ordlt
                     (G, O, O',
                       (function | ops' -> ordleSimul (G, L, L', sc, ops')),
                       ops)) in
          ordeq
            (G, O, O', (function | ops' -> ordltSimul (G, L, L', sc, ops')),
              ops'')
    let rec ordleSimul =
      function
      | (G, nil, nil, sc, ops) -> sc ops
      | (G, (O)::L, (O')::L', sc, ops) ->
          ordle
            (G, O, O', (function | ops' -> ordleSimul (G, L, L', sc, ops')),
              ops)
    let rec ordeq =
      function
      | (G, Arg (Us, Vs), Arg (Us', Vs'), sc, ops) ->
          if (Unify.unifiable (G, Vs, Vs')) && (Unify.unifiable (G, Us, Us'))
          then sc ops
          else ops
      | (G, Lex (L), Lex (L'), sc, ops) -> ordeqs (G, L, L', sc, ops)
      | (G, Simul (L), Simul (L'), sc, ops) -> ordeqs (G, L, L', sc, ops)
    let rec ordeqs =
      function
      | (G, nil, nil, sc, ops) -> sc ops
      | (G, (O)::L, (O')::L', sc, ops) ->
          ordeq
            (G, O, O', (function | ops' -> ordeqs (G, L, L', sc, ops')), ops)
    let rec ordle (G, O, O', sc, ops) =
      let ops' = CSManager.trail (function | () -> ordeq (G, O, O', sc, ops)) in
      ordlt (G, O, O', sc, ops')
    let rec createEVars =
      function
      | Prefix (I.Null, I.Null, I.Null) ->
          ((M.Prefix (I.Null, I.Null, I.Null)), I.id)
      | Prefix (Decl (G, D), Decl (M, M.Top), Decl (B, b)) ->
          let (Prefix (G', M', B'), s') = createEVars (M.Prefix (G, M, B)) in
          ((M.Prefix
              ((I.Decl (G', (I.decSub (D, s')))), (I.Decl (M', M.Top)),
                (I.Decl (B', b)))), (I.dot1 s'))
      | Prefix (Decl (G, Dec (_, V)), Decl (M, M.Bot), Decl (B, _)) ->
          let (Prefix (G', M', B'), s') = createEVars (M.Prefix (G, M, B)) in
          let X = I.newEVar (G', (I.EClo (V, s'))) in
          ((M.Prefix (G', M', B')), (I.Dot ((I.Exp X), s')))
    let rec select (G, Vs) = selectW (G, (Whnf.whnf Vs))
    let rec selectW (G, (Pi (((Dec (_, V1) as D), _), V2), s)) =
      let rec select' (G, (Vs1, Vs2)) = selectW' (G, (Vs1, (Whnf.whnf Vs2)))
      and selectW' =
        function
        | (G, (Vs1, ((Root _, _) as Vs2))) -> (G, (Vs1, Vs2))
        | (G, ((V1, s1), (Pi ((D, P), V2'), s2))) ->
            select'
              ((I.Decl (G, (I.decSub (D, s2)))),
                ((V1, (I.comp (s1, I.shift))), (V2', (I.dot1 s2)))) in
      select'
        ((I.Decl (G, (I.decSub (D, s)))),
          ((V1, (I.comp (s, I.shift))), (V2, (I.dot1 s))))
    let rec lemma (S, t, ops) =
      let State (name, GM, V) = Lemma.apply (S, t) in
      let (Prefix (G', M', B'), s') = createEVars GM in
      let (G'', ((Root (Const a1, S1), s1), (Root (Const a2, S2), s2))) =
        select (G', (V, s')) in
      (G'', (vector (a1, (S1, s1))), (vector (a2, (S2, s2))),
        (function
         | ops' ->
             (MetaAbstract.abstract
                (M.State (name, (M.Prefix (G', M', B')), (I.EClo (V, s')))))
               :: ops'), ops)
    let rec expandLazy' =
      function
      | (S, O.Empty, ops) -> ops
      | (S, LE (t, L), ops) ->
          expandLazy' (S, L, (ordle (lemma (S, t, ops))))
      | (S, LT (t, L), ops) ->
          expandLazy' (S, L, (ordlt (lemma (S, t, ops))))
    let rec recursionDepth (V) =
      let rec recursionDepth' =
        function
        | (Root _, n) -> n
        | (Pi (_, V), n) -> recursionDepth' (V, (n + 1)) in
      recursionDepth' (V, 0)
    let rec expandLazy (State (_, _, V) as S) =
      if (recursionDepth V) > (!MetaGlobal.maxRecurse)
      then nil
      else expandLazy' (S, (O.mutLookup (I.targetFam V)), nil)
    let rec inputConv (Vs1, Vs2) =
      inputConvW ((Whnf.whnf Vs1), (Whnf.whnf Vs2))
    let rec inputConvW ((Root (Const c1, S1), s1), (Root (Const c2, S2), s2))
      =
      if c1 = c2
      then
        inputConvSpine
          ((valOf (ModeTable.modeLookup c1)),
            ((S1, s1), ((I.constType c1), I.id)),
            ((S2, s2), ((I.constType c2), I.id)))
      else false__
    let rec inputConvSpine =
      function
      | (ModeSyn.Mnil, ((S1, _), _), ((S2, _), _)) -> true__
      | (mS, ((SClo (S1, s1'), s1), Vs1), (Ss2, Vs2)) ->
          inputConvSpine (mS, ((S1, (I.comp (s1', s1))), Vs1), (Ss2, Vs2))
      | (mS, (Ss1, Vs1), ((SClo (S2, s2'), s2), Vs2)) ->
          inputConvSpine (mS, (Ss1, Vs1), ((S2, (I.comp (s2', s2))), Vs2))
      | (Mapp (Marg (ModeSyn.Minus, _), mS),
         ((App (U1, S1), s1), (Pi ((Dec (_, V1), _), W1), t1)),
         ((App (U2, S2), s2), (Pi ((Dec (_, V2), _), W2), t2))) ->
          (Conv.conv ((V1, t1), (V2, t2))) &&
            (inputConvSpine
               (mS,
                 ((S1, s1), (W1, (I.Dot ((I.Exp (I.EClo (U1, s1))), t1)))),
                 ((S2, s2), (W2, (I.Dot ((I.Exp (I.EClo (U1, s1))), t2))))))
      | (Mapp (Marg (ModeSyn.Plus, _), mS),
         ((App (U1, S1), s1), (Pi ((Dec (_, V1), _), W1), t1)),
         ((App (U2, S2), s2), (Pi ((Dec (_, V2), _), W2), t2))) ->
          inputConvSpine
            (mS, ((S1, s1), (W1, (I.Dot ((I.Exp (I.EClo (U1, s1))), t1)))),
              ((S2, s2), (W2, (I.Dot ((I.Exp (I.EClo (U2, s2))), t2)))))
    let rec removeDuplicates =
      function
      | nil -> nil
      | (S')::ops ->
          let rec compExp (Vs1, Vs2) =
            compExpW ((Whnf.whnf Vs1), (Whnf.whnf Vs2))
          and compExpW =
            function
            | (Vs1, (Root _, _)) -> false__
            | (((V1, s1) as Vs1), (Pi ((D2, _), V2), s2)) ->
                (compDec (Vs1, (D2, s2))) ||
                  (compExp ((V1, (I.comp (s1, I.shift))), (V2, (I.dot1 s2))))
          and compDec (Vs1, (Dec (_, V2), s2)) = inputConv (Vs1, (V2, s2)) in
          let rec check (State (name, GM, V)) = checkW (Whnf.whnf (V, I.id))
          and checkW (Pi ((D, _), V), s) =
            checkDec ((D, (I.comp (s, I.shift))), (V, (I.dot1 s)))
          and checkDec ((Dec (_, V1), s1), Vs2) = compExp ((V1, s1), Vs2) in
          if check S'
          then removeDuplicates ops
          else S' :: (removeDuplicates ops)
    let rec fillOps =
      function
      | nil -> nil
      | (S')::ops ->
          let rec fillOps' =
            function | nil -> nil | (O)::_ -> Filling.apply O in
          let (fillop, _) = Filling.expand S' in
          (fillOps' fillop) @ (fillOps ops)
    let rec expandEager (S) = removeDuplicates (fillOps (expandLazy S))
    let rec apply (S) = S
    let rec menu
      (State (name, Prefix (G', M', B'), Pi ((Dec (_, V), _), _)) as S) =
      "Recursion : " ^ (Print.expToString (G', V))
    let rec handleExceptions f (P) =
      try f P with | Error s -> raise (Error s)
    (* Quantifier to mark parameters *)
    (* Q ::= Uni                     *)
    (*     | Ex                      *)
    (* If Q marks all parameters in a context G we write   G : Q               *)
    (* duplicate code? -fp *)
    (* vector (c, (S, s)) = P'

       Invariant:
       If   . |- c : V   G |- s : G'    G' |- S : V > type
       and  V = {x1:V1} ... {xn:Vn} type
       and  G |- S[s] = U1 .. Un : V[s] > type
       and  sel (c) = i1 .. im
       then P' = (U1'[s1']: V1'[t1'], .., U1'[sm']: V1'[tm'])
       and  G |- sj' : Gj'    Gj' |- Uj' : V1j'
       and  G |- tj' : Gj'    Gj' |- Vj' : L
       and  G |- Vj' [tj'] = V1j' [sj'] : L
       and  G |- Uik = Uk'[sk']
    *)
    (* select'W (1, _, (I.Root _, _)) cannot occur by invariant ! *)
    (* set_parameter (G, X, k, sc, ops) = ops'

       Invariant:
       appends a list of recursion operators to ops after
       instantiating X with all possible local parameters (between 1 and k)
    *)
    (* ltinit (G, k, ((U1, s1), (V2, s2)), ((U3, s3), (V4, s4)), sc, ops) = ops'

       Invariant:
       If   G = G0, Gp    (G0, global context, Gp, parameter context)
       and  |Gp| = k
       and  G |- s1 : G1   G1 |- U1 : V1
       and  G |- s2 : G2   G2 |- V2 : L
            G |- s3 : G1   G1 |- U3 : V3
       and  G |- s4 : G2   G2 |- V4 : L
       and  G |- V1[s1] == V2 [s2]
       and  G |- V3[s3] == V4 [s5]
       and  ops is a set of all all possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators
    *)
    (* = I.decSub (D2, s2) *)
    (* lt (G, k, ((U, s1), (V, s2)), (U', s'), sc, ops) = ops'

       Invariant:
       If   G = G0, Gp    (G0, global context, Gp, parameter context)
       and  |Gp| = k
       and  G |- s1 : G1   G1 |- U1 : V1   (U1 [s1] in  whnf)
       and  G |- s2 : G2   G2 |- V2 : L    (V2 [s2] in  whnf)
            G |- s3 : G1   G1 |- U3 : V3
       and  G |- s4 : G2   G2 |- V4 : L
       and  k is the length of the local context
       and  G |- V1[s1] == V2 [s2]
       and  G |- V3[s3] == V4 [s5]
       and  ops is a set of already calculuate possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators
    *)
    (* Vs is Root!!! *)
    (* (Us',Vs') may not be eta-expanded!!! *)
    (* n must be a local variable *)
    (* == I.targetFam V2' *)
    (* enforce that X gets only bound to parameters *)
    (* = I.newEVar (I.EClo (V2', s2')) *)
    (* = I.newEVar (I.EClo (V2', s2')) *)
    (* eq (G, ((U, s1), (V, s2)), (U', s'), sc, ops) = ops'

       Invariant:
       If   G |- s1 : G1   G1 |- U1 : V1   (U1 [s1] in  whnf)
       and  G |- s2 : G2   G2 |- V2 : L    (V2 [s2] in  whnf)
            G |- s3 : G1   G1 |- U3 : V3
       and  G |- s4 : G2   G2 |- V4 : L
       and  G |- V1[s1] == V2 [s2]
       and  G |- V3[s3] == V4 [s5]
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators resulting from U[s1] = U'[s']
    *)
    (* le (G, k, ((U, s1), (V, s2)), (U', s'), sc, ops) = ops'

       Invariant:
       If   G = G0, Gp    (G0, global context, Gp, parameter context)
       and  |Gp| = k
       and  G |- s1 : G1   G1 |- U1 : V1   (U1 [s1] in  whnf)
       and  G |- s2 : G2   G2 |- V2 : L    (V2 [s2] in  whnf)
            G |- s3 : G1   G1 |- U3 : V3
       and  G |- s4 : G2   G2 |- V4 : L
       and  k is the length of the local context
       and  G |- V1[s1] == V2 [s2]
       and  G |- V3[s3] == V4 [s5]
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators resulting from U[s1] <= U'[s']
    *)
    (* == I.targetFam V2' *)
    (* = I.newEVar (I.EClo (V2', s2')) *)
    (* enforces that X can only bound to parameter *)
    (* = I.newEVar (I.EClo (V2', s2')) *)
    (* ordlt (G, O1, O2, sc, ops) = ops'

       Invariant:
       If   G |- O1 augmented subterms
       and  G |- O2 augmented subterms
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators of all instantiations of EVars s.t. O1 is
            lexicographically smaller than O2
    *)
    (* ordltLex (G, L1, L2, sc, ops) = ops'

       Invariant:
       If   G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators of all instantiations of EVars s.t. L1 is
            lexicographically less then L2
    *)
    (* ordltSimul (G, L1, L2, sc, ops) = ops'

       Invariant:
       If   G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators of all instantiations of EVars s.t. L1 is
            simultaneously smaller than L2
    *)
    (* ordleSimul (G, L1, L2, sc, ops) = ops'

       Invariant:
       If   G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators of all instantiations of EVars s.t. L1 is
            simultaneously smaller than or equal to L2
    *)
    (* ordeq (G, O1, O2, sc, ops) = ops'

       Invariant:
       If   G |- O1 augmented subterms
       and  G |- O2 augmented subterms
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators of all instantiations of EVars s.t. O1 is
            convertible to O2
    *)
    (* ordlteqs (G, L1, L2, sc, ops) = ops'

       Invariant:
       If   G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators of all instantiations of EVars s.t. L1 is
            convertible to L2
    *)
    (* ordeq (G, O1, O2, sc, ops) = ops'

       Invariant:
       If   G |- O1 augmented subterms
       and  G |- O2 augmented subterms
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
1           recursion operators of all instantiations of EVars s.t. O1 is
            convertible to O2 or smaller than O2
    *)
    (* createEVars (G, M) = ((G', M'), s')

       Invariant:
       If   |- G ctx
       and  G |- M mtx
       then |- G' ctx
       and  G' |- M' mtx
       and  G' |- s' : G
    *)
    (* select (G, (V, s)) = (G', (V1', s1'), (V2', s2'))

     Invariant:
     If   G |- s : G1   G1 |- V : type
     and  G |- V [s] = {V1} ... {Vn} a S
     then G' = G, V1 .. Vn
     and  G' |- s1' : G1'   G1' |- V1' : type
     and  G' |- s2' : G2'   G2' |- V2' : type
     and  G' |- V1' [s1'] = V1 [^n]
     and  G' |- V2' [s2'] = a S
    *)
    (* lemma (S, t, ops) = (G', P', P'', abstract', ops')

       Invariant:
       If   S state  (S = ((G, M), V)
                     |- G ctx
                     G |- M mtx
                     G |- V = {V1} ... {Vn} a S)
       and  S' state derived from S by an inductive call to t
       and  ops a list of operators
       then G is context, where all - variables are replaced by EVars in S'
       and  P' is induction variable vector of EVars in the inductive call
       and  P'' is induction variable vector of the theorem S.
       and  G' |- P' : (V1' .. Vn')
              (where  t : {W1} ..{Wm} b S, and Vi' are among W1 .. Wm)
       and  G'' |- P'' : (V1'' .. Vn'')
              (where  a : {W1} ..{Wm} b S, and Vi'' are among W1 .. Wm)

    *)
    (* expandLazy' (S, L, ops) = ops'

       Invariant:
       If   S state
       and  L list of mutual recursive type families
       and  ops a list of operators
       then ops' extends ops by all operators
         representing inductive calls to theorems in L
    *)
    (* expandLazy S = ops'

       Invariant:
       If   S State
       then ops' a list of operations which cause a recursive call
         (only induction variables are instantiated)
    *)
    (* inputConv ((V1, s1), (V2, s2)) = B

       Invariant:
       If  G |- s1 : G1   G1 |- V1 : L
       and G |- s2 : G2   G2 |- V2 : L
       and G |- V1[s1] = c1 ; S1
       and G |- V2[s2] = c2 ; S2
       then B' holds iff c1 =  c2 and V1[s1] ==+ V2[s2]   (convertible on + arguments of c1)
    *)
    (* s1 = s2 = id *)
    (* S1 = S2 = Nil *)
    (* BUG: use the same variable (U1, s1) to continue comparing! --cs
                  in ((S2, s2), (W2, I.Dot (I.Exp (I.EClo (U2, s2), V2), t2))))
             FIXED: --cs Mon Nov  9 19:38:55 EST 1998 *)
    (* removeDuplicates ops = ops'

       Invariant:
       If   ops is a list of recursion operators,
       then ops' is a sublist of ops, s.t.
         forall S = ((G, M), V) in ops'
               |- G ctx
               G |- M mtx
               G |- V = {V0} .. {Vn} a ; S : type
               and Vi = ci ; S'
               and forall 1 <= i <= n:
                 either ci =/= c0 orelse
                 G, V0 .. Vi |- V0 [^ i] =/=+ Vi (not convertible on + arguments on c0)
    *)
    (* fillOps ops = ops'

       Invariant:
       If   ops is a list of lazy recursion operators
       then ops' is a list of recursion operators combined with a filling
         operator to fill non-index variables.
    *)
    (* expandEager S = ops'

       Invariant:
       If   S State
       then ops' a list of operations which cause a recursive call
         (all variables of recursive call are instantiated)
    *)
    let expandLazy = handleExceptions expandLazy
    let expandEager = handleExceptions expandEager
    let apply = apply
    let menu = menu
  end ;;
