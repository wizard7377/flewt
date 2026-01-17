
module type RECURSION  =
  sig
    module MetaSyn :
    ((METASYN)(* Recursion *)(* Author: Carsten Schuermann *))
    exception Error of string 
    type nonrec operator
    val expandLazy : MetaSyn.__State -> operator list
    val expandEager : MetaSyn.__State -> operator list
    val apply : operator -> MetaSyn.__State
    val menu : operator -> string
  end;;




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
                             module Formatter :
                             ((FORMATTER)(* Recursion *)
                             (* Author: Carsten Schuermann *)(* See [Rohwedder,Pfenning ESOP'96] *)
                             (*! sharing Whnf.IntSyn = MetaSyn'.IntSyn !*)
                             (*! sharing Unify.IntSyn = MetaSyn'.IntSyn !*)
                             (*! sharing Conv.IntSyn = MetaSyn'.IntSyn !*)
                             (*! sharing Names.IntSyn = MetaSyn'.IntSyn !*)
                             (*! sharing Subordinate.IntSyn = MetaSyn'.IntSyn !*)
                             (*! sharing Print.IntSyn = MetaSyn'.IntSyn !*)
                             (*! sharing Order.IntSyn = MetaSyn'.IntSyn !*)
                             (*! sharing ModeSyn.IntSyn = MetaSyn'.IntSyn !*))
                           end) : RECURSION =
  struct
    module MetaSyn =
      ((MetaSyn')(*! structure CSManager : CS_MANAGER !*)
      (*! sharing CSManager.IntSyn = MetaSyn'.IntSyn !*))
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
    let rec vectorToString (g, O) =
      let fmtOrder =
        function
        | Arg (Us, Vs) ->
            [F.String (Print.expToString (g, (I.EClo Us)));
            F.String ":";
            F.String (Print.expToString (g, (I.EClo Vs)))]
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
      let select' (n, (Ss', Vs'')) = select'W (n, (Ss', (Whnf.whnf Vs'')))
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
      let select =
        function
        | Arg n -> O.Arg (select' (n, ((S, s), Vid)))
        | Lex (L) -> O.Lex (map select L)
        | Simul (L) -> O.Simul (map select L) in
      select (O.selLookup c)
    let rec set_parameter (g, (EVar (r, _, V, _) as X), k, sc, ops) =
      let set_parameter' =
        function
        | (0, ops') -> ops'
        | (k', ops') ->
            let Dec (_, V') as D' = I.ctxDec (g, k') in
            let ops'' =
              CSManager.trail
                (function
                 | () ->
                     if
                       (Unify.unifiable (g, (V, I.id), (V', I.id))) &&
                         (Unify.unifiable
                            (g, (X, I.id),
                              ((I.Root ((I.BVar k'), I.Nil)), I.id)))
                     then sc ops'
                     else ops') in
            set_parameter' ((k' - 1), ops'') in
      set_parameter' (k, ops)
    let rec ltinit (g, k, (Us, Vs), UsVs', sc, ops) =
      ltinitW (g, k, (Whnf.whnfEta (Us, Vs)), UsVs', sc, ops)
    let rec ltinitW =
      function
      | (g, k, (Us, ((Root _, _) as Vs)), UsVs', sc, ops) ->
          lt (g, k, (Us, Vs), UsVs', sc, ops)
      | (g, k, ((Lam (D1, U), s1), (Pi (D2, V), s2)), ((U', s1'), (V', s2')),
         sc, ops) ->
          ltinit
            ((I.Decl (g, (I.decSub (D1, s1)))), (k + 1),
              ((U, (I.dot1 s1)), (V, (I.dot1 s2))),
              ((U', (I.comp (s1', I.shift))), (V', (I.comp (s2', I.shift)))),
              sc, ops)
    let rec lt (g, k, (Us, Vs), (Us', Vs'), sc, ops) =
      ltW (g, k, (Us, Vs), (Whnf.whnfEta (Us', Vs')), sc, ops)
    let rec ltW =
      function
      | (g, k, (Us, Vs), ((Root (Const c, S'), s'), Vs'), sc, ops) ->
          ltSpine
            (g, k, (Us, Vs), ((S', s'), ((I.constType c), I.id)), sc, ops)
      | (g, k, (Us, Vs), ((Root (BVar n, S'), s'), Vs'), sc, ops) ->
          if n <= k
          then
            let Dec (_, V') = I.ctxDec (g, n) in
            ltSpine (g, k, (Us, Vs), ((S', s'), (V', I.id)), sc, ops)
          else ops
      | (g, _, _, ((EVar _, _), _), _, ops) -> ops
      | (g, k, ((U, s1), (V, s2)),
         ((Lam ((Dec (_, V1') as D), U'), s1'),
          (Pi ((Dec (_, V2'), _), V'), s2')),
         sc, ops) ->
          if Subordinate.equiv ((I.targetFam V), (I.targetFam V1'))
          then
            let X = I.newEVar (g, (I.EClo (V1', s1'))) in
            let sc' = function | ops' -> set_parameter (g, X, k, sc, ops') in
            lt
              (g, k, ((U, s1), (V, s2)),
                ((U', (I.Dot ((I.Exp X), s1'))),
                  (V', (I.Dot ((I.Exp X), s2')))), sc', ops)
          else
            if Subordinate.below ((I.targetFam V1'), (I.targetFam V))
            then
              (let X = I.newEVar (g, (I.EClo (V1', s1'))) in
               lt
                 (g, k, ((U, s1), (V, s2)),
                   ((U', (I.Dot ((I.Exp X), s1'))),
                     (V', (I.Dot ((I.Exp X), s2')))), sc, ops))
            else ops
    let rec ltSpine (g, k, (Us, Vs), (Ss', Vs'), sc, ops) =
      ltSpineW (g, k, (Us, Vs), (Ss', (Whnf.whnf Vs')), sc, ops)
    let rec ltSpineW =
      function
      | (g, k, (Us, Vs), ((I.Nil, _), _), _, ops) -> ops
      | (g, k, (Us, Vs), ((SClo (S, s'), s''), Vs'), sc, ops) ->
          ltSpineW (g, k, (Us, Vs), ((S, (I.comp (s', s''))), Vs'), sc, ops)
      | (g, k, (Us, Vs),
         ((App (U', S'), s1'), (Pi ((Dec (_, V1'), _), V2'), s2')), sc, ops)
          ->
          let ops' = le (g, k, (Us, Vs), ((U', s1'), (V1', s2')), sc, ops) in
          ltSpine
            (g, k, (Us, Vs),
              ((S', s1'), (V2', (I.Dot ((I.Exp (I.EClo (U', s1'))), s2')))),
              sc, ops')
    let rec eq (g, (Us, Vs), (Us', Vs'), sc, ops) =
      CSManager.trail
        (function
         | () ->
             if
               (Unify.unifiable (g, Vs, Vs')) &&
                 (Unify.unifiable (g, Us, Us'))
             then sc ops
             else ops)
    let rec le (g, k, (Us, Vs), (Us', Vs'), sc, ops) =
      let ops' = eq (g, (Us, Vs), (Us', Vs'), sc, ops) in
      leW (g, k, (Us, Vs), (Whnf.whnfEta (Us', Vs')), sc, ops')
    let rec leW =
      function
      | (g, k, ((U, s1), (V, s2)),
         ((Lam ((Dec (_, V1') as D), U'), s1'),
          (Pi ((Dec (_, V2'), _), V'), s2')),
         sc, ops) ->
          if Subordinate.equiv ((I.targetFam V), (I.targetFam V1'))
          then
            let X = I.newEVar (g, (I.EClo (V1', s1'))) in
            let sc' = function | ops' -> set_parameter (g, X, k, sc, ops') in
            le
              (g, k, ((U, s1), (V, s2)),
                ((U', (I.Dot ((I.Exp X), s1'))),
                  (V', (I.Dot ((I.Exp X), s2')))), sc', ops)
          else
            if Subordinate.below ((I.targetFam V1'), (I.targetFam V))
            then
              (let X = I.newEVar (g, (I.EClo (V1', s1'))) in
               le
                 (g, k, ((U, s1), (V, s2)),
                   ((U', (I.Dot ((I.Exp X), s1'))),
                     (V', (I.Dot ((I.Exp X), s2')))), sc, ops))
            else ops
      | (g, k, (Us, Vs), (Us', Vs'), sc, ops) ->
          lt (g, k, (Us, Vs), (Us', Vs'), sc, ops)
    let rec ordlt =
      function
      | (g, Arg (UsVs), Arg (UsVs'), sc, ops) ->
          ltinit (g, 0, UsVs, UsVs', sc, ops)
      | (g, Lex (L), Lex (L'), sc, ops) -> ordltLex (g, L, L', sc, ops)
      | (g, Simul (L), Simul (L'), sc, ops) -> ordltSimul (g, L, L', sc, ops)
    let rec ordltLex =
      function
      | (g, nil, nil, sc, ops) -> ops
      | (g, (O)::L, (O')::L', sc, ops) ->
          let ops' =
            CSManager.trail (function | () -> ordlt (g, O, O', sc, ops)) in
          ordeq
            (g, O, O', (function | ops'' -> ordltLex (g, L, L', sc, ops'')),
              ops')
    let rec ordltSimul =
      function
      | (g, nil, nil, sc, ops) -> ops
      | (g, (O)::L, (O')::L', sc, ops) ->
          let ops'' =
            CSManager.trail
              (function
               | () ->
                   ordlt
                     (g, O, O',
                       (function | ops' -> ordleSimul (g, L, L', sc, ops')),
                       ops)) in
          ordeq
            (g, O, O', (function | ops' -> ordltSimul (g, L, L', sc, ops')),
              ops'')
    let rec ordleSimul =
      function
      | (g, nil, nil, sc, ops) -> sc ops
      | (g, (O)::L, (O')::L', sc, ops) ->
          ordle
            (g, O, O', (function | ops' -> ordleSimul (g, L, L', sc, ops')),
              ops)
    let rec ordeq =
      function
      | (g, Arg (Us, Vs), Arg (Us', Vs'), sc, ops) ->
          if (Unify.unifiable (g, Vs, Vs')) && (Unify.unifiable (g, Us, Us'))
          then sc ops
          else ops
      | (g, Lex (L), Lex (L'), sc, ops) -> ordeqs (g, L, L', sc, ops)
      | (g, Simul (L), Simul (L'), sc, ops) -> ordeqs (g, L, L', sc, ops)
    let rec ordeqs =
      function
      | (g, nil, nil, sc, ops) -> sc ops
      | (g, (O)::L, (O')::L', sc, ops) ->
          ordeq
            (g, O, O', (function | ops' -> ordeqs (g, L, L', sc, ops')), ops)
    let rec ordle (g, O, O', sc, ops) =
      let ops' = CSManager.trail (function | () -> ordeq (g, O, O', sc, ops)) in
      ordlt (g, O, O', sc, ops')
    let rec createEVars =
      function
      | Prefix (I.Null, I.Null, I.Null) ->
          ((M.Prefix (I.Null, I.Null, I.Null)), I.id)
      | Prefix (Decl (g, D), Decl (M, M.Top), Decl (B, b)) ->
          let (Prefix (g', M', B'), s') = createEVars (M.Prefix (g, M, B)) in
          ((M.Prefix
              ((I.Decl (g', (I.decSub (D, s')))), (I.Decl (M', M.Top)),
                (I.Decl (B', b)))), (I.dot1 s'))
      | Prefix (Decl (g, Dec (_, V)), Decl (M, M.Bot), Decl (B, _)) ->
          let (Prefix (g', M', B'), s') = createEVars (M.Prefix (g, M, B)) in
          let X = I.newEVar (g', (I.EClo (V, s'))) in
          ((M.Prefix (g', M', B')), (I.Dot ((I.Exp X), s')))
    let rec select (g, Vs) = selectW (g, (Whnf.whnf Vs))
    let rec selectW (g, (Pi (((Dec (_, V1) as D), _), V2), s)) =
      let select' (g, (Vs1, Vs2)) = selectW' (g, (Vs1, (Whnf.whnf Vs2)))
      and selectW' =
        function
        | (g, (Vs1, ((Root _, _) as Vs2))) -> (g, (Vs1, Vs2))
        | (g, ((V1, s1), (Pi ((D, P), V2'), s2))) ->
            select'
              ((I.Decl (g, (I.decSub (D, s2)))),
                ((V1, (I.comp (s1, I.shift))), (V2', (I.dot1 s2)))) in
      select'
        ((I.Decl (g, (I.decSub (D, s)))),
          ((V1, (I.comp (s, I.shift))), (V2, (I.dot1 s))))
    let rec lemma (S, t, ops) =
      let State (name, GM, V) = Lemma.apply (S, t) in
      let (Prefix (g', M', B'), s') = createEVars GM in
      let (g'', ((Root (Const a1, s1), s1), (Root (Const a2, s2), s2))) =
        select (g', (V, s')) in
      (g'', (vector (a1, (s1, s1))), (vector (a2, (s2, s2))),
        (function
         | ops' ->
             (MetaAbstract.abstract
                (M.State (name, (M.Prefix (g', M', B')), (I.EClo (V, s')))))
               :: ops'), ops)
    let rec expandLazy' =
      function
      | (S, O.Empty, ops) -> ops
      | (S, LE (t, L), ops) ->
          expandLazy' (S, L, (ordle (lemma (S, t, ops))))
      | (S, LT (t, L), ops) ->
          expandLazy' (S, L, (ordlt (lemma (S, t, ops))))
    let rec recursionDepth (V) =
      let recursionDepth' =
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
    let rec inputConvW ((Root (Const c1, s1), s1), (Root (Const c2, s2), s2))
      =
      if c1 = c2
      then
        inputConvSpine
          ((valOf (ModeTable.modeLookup c1)),
            ((s1, s1), ((I.constType c1), I.id)),
            ((s2, s2), ((I.constType c2), I.id)))
      else false__
    let rec inputConvSpine =
      function
      | (ModeSyn.Mnil, ((s1, _), _), ((s2, _), _)) -> true__
      | (mS, ((SClo (s1, s1'), s1), Vs1), (Ss2, Vs2)) ->
          inputConvSpine (mS, ((s1, (I.comp (s1', s1))), Vs1), (Ss2, Vs2))
      | (mS, (Ss1, Vs1), ((SClo (s2, s2'), s2), Vs2)) ->
          inputConvSpine (mS, (Ss1, Vs1), ((s2, (I.comp (s2', s2))), Vs2))
      | (Mapp (Marg (ModeSyn.Minus, _), mS),
         ((App (u1, s1), s1), (Pi ((Dec (_, V1), _), W1), t1)),
         ((App (u2, s2), s2), (Pi ((Dec (_, V2), _), W2), t2))) ->
          (Conv.conv ((V1, t1), (V2, t2))) &&
            (inputConvSpine
               (mS,
                 ((s1, s1), (W1, (I.Dot ((I.Exp (I.EClo (u1, s1))), t1)))),
                 ((s2, s2), (W2, (I.Dot ((I.Exp (I.EClo (u1, s1))), t2))))))
      | (Mapp (Marg (ModeSyn.Plus, _), mS),
         ((App (u1, s1), s1), (Pi ((Dec (_, V1), _), W1), t1)),
         ((App (u2, s2), s2), (Pi ((Dec (_, V2), _), W2), t2))) ->
          inputConvSpine
            (mS, ((s1, s1), (W1, (I.Dot ((I.Exp (I.EClo (u1, s1))), t1)))),
              ((s2, s2), (W2, (I.Dot ((I.Exp (I.EClo (u2, s2))), t2)))))
    let rec removeDuplicates =
      function
      | nil -> nil
      | (S')::ops ->
          let compExp (Vs1, Vs2) =
            compExpW ((Whnf.whnf Vs1), (Whnf.whnf Vs2))
          and compExpW =
            function
            | (Vs1, (Root _, _)) -> false__
            | (((V1, s1) as Vs1), (Pi ((D2, _), V2), s2)) ->
                (compDec (Vs1, (D2, s2))) ||
                  (compExp ((V1, (I.comp (s1, I.shift))), (V2, (I.dot1 s2))))
          and compDec (Vs1, (Dec (_, V2), s2)) = inputConv (Vs1, (V2, s2)) in
          let check (State (name, GM, V)) = checkW (Whnf.whnf (V, I.id))
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
          let fillOps' = function | nil -> nil | (O)::_ -> Filling.apply O in
          let (fillop, _) = Filling.expand S' in
          (fillOps' fillop) @ (fillOps ops)
    let rec expandEager (S) = removeDuplicates (fillOps (expandLazy S))
    let rec apply (S) = S
    let rec menu
      (State (name, Prefix (g', M', B'), Pi ((Dec (_, V), _), _)) as S) =
      "Recursion : " ^ (Print.expToString (g', V))
    let rec handleExceptions f (P) =
      try f P with | Error s -> raise (Error s)
    let ((expandLazy)(* Quantifier to mark parameters *)
      (* Q ::= Uni                     *)(*     | Ex                      *)
      (* If Q marks all parameters in a context g we write   g : Q               *)
      (* duplicate code? -fp *)(* vector (c, (S, s)) = P'

       Invariant:
       If   . |- c : V   g |- s : g'    g' |- S : V > type
       and  V = {x1:V1} ... {xn:Vn} type
       and  g |- S[s] = u1 .. Un : V[s] > type
       and  sel (c) = i1 .. im
       then P' = (u1'[s1']: V1'[t1'], .., u1'[sm']: V1'[tm'])
       and  g |- sj' : Gj'    Gj' |- Uj' : V1j'
       and  g |- tj' : Gj'    Gj' |- Vj' : L
       and  g |- Vj' [tj'] = V1j' [sj'] : L
       and  g |- Uik = Uk'[sk']
    *)
      (* select'W (1, _, (I.Root _, _)) cannot occur by invariant ! *)
      (* set_parameter (g, X, k, sc, ops) = ops'

       Invariant:
       appends a list of recursion operators to ops after
       instantiating X with all possible local parameters (between 1 and k)
    *)
      (* ltinit (g, k, ((u1, s1), (V2, s2)), ((u3, s3), (V4, s4)), sc, ops) = ops'

       Invariant:
       If   g = G0, Gp    (G0, global context, Gp, parameter context)
       and  |Gp| = k
       and  g |- s1 : G1   G1 |- u1 : V1
       and  g |- s2 : G2   G2 |- V2 : L
            g |- s3 : G1   G1 |- u3 : V3
       and  g |- s4 : G2   G2 |- V4 : L
       and  g |- V1[s1] == V2 [s2]
       and  g |- V3[s3] == V4 [s5]
       and  ops is a set of all all possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators
    *)
      (* = I.decSub (D2, s2) *)(* lt (g, k, ((U, s1), (V, s2)), (U', s'), sc, ops) = ops'

       Invariant:
       If   g = G0, Gp    (G0, global context, Gp, parameter context)
       and  |Gp| = k
       and  g |- s1 : G1   G1 |- u1 : V1   (u1 [s1] in  whnf)
       and  g |- s2 : G2   G2 |- V2 : L    (V2 [s2] in  whnf)
            g |- s3 : G1   G1 |- u3 : V3
       and  g |- s4 : G2   G2 |- V4 : L
       and  k is the length of the local context
       and  g |- V1[s1] == V2 [s2]
       and  g |- V3[s3] == V4 [s5]
       and  ops is a set of already calculuate possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators
    *)
      (* Vs is Root!!! *)(* (Us',Vs') may not be eta-expanded!!! *)
      (* n must be a local variable *)(* == I.targetFam V2' *)
      (* enforce that X gets only bound to parameters *)
      (* = I.newEVar (I.EClo (V2', s2')) *)(* = I.newEVar (I.EClo (V2', s2')) *)
      (* eq (g, ((U, s1), (V, s2)), (U', s'), sc, ops) = ops'

       Invariant:
       If   g |- s1 : G1   G1 |- u1 : V1   (u1 [s1] in  whnf)
       and  g |- s2 : G2   G2 |- V2 : L    (V2 [s2] in  whnf)
            g |- s3 : G1   G1 |- u3 : V3
       and  g |- s4 : G2   G2 |- V4 : L
       and  g |- V1[s1] == V2 [s2]
       and  g |- V3[s3] == V4 [s5]
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators resulting from U[s1] = U'[s']
    *)
      (* le (g, k, ((U, s1), (V, s2)), (U', s'), sc, ops) = ops'

       Invariant:
       If   g = G0, Gp    (G0, global context, Gp, parameter context)
       and  |Gp| = k
       and  g |- s1 : G1   G1 |- u1 : V1   (u1 [s1] in  whnf)
       and  g |- s2 : G2   G2 |- V2 : L    (V2 [s2] in  whnf)
            g |- s3 : G1   G1 |- u3 : V3
       and  g |- s4 : G2   G2 |- V4 : L
       and  k is the length of the local context
       and  g |- V1[s1] == V2 [s2]
       and  g |- V3[s3] == V4 [s5]
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators resulting from U[s1] <= U'[s']
    *)
      (* == I.targetFam V2' *)(* = I.newEVar (I.EClo (V2', s2')) *)
      (* enforces that X can only bound to parameter *)
      (* = I.newEVar (I.EClo (V2', s2')) *)(* ordlt (g, O1, O2, sc, ops) = ops'

       Invariant:
       If   g |- O1 augmented subterms
       and  g |- O2 augmented subterms
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators of all instantiations of EVars s.t. O1 is
            lexicographically smaller than O2
    *)
      (* ordltLex (g, L1, L2, sc, ops) = ops'

       Invariant:
       If   g |- L1 list of augmented subterms
       and  g |- L2 list of augmented subterms
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators of all instantiations of EVars s.t. L1 is
            lexicographically less then L2
    *)
      (* ordltSimul (g, L1, L2, sc, ops) = ops'

       Invariant:
       If   g |- L1 list of augmented subterms
       and  g |- L2 list of augmented subterms
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators of all instantiations of EVars s.t. L1 is
            simultaneously smaller than L2
    *)
      (* ordleSimul (g, L1, L2, sc, ops) = ops'

       Invariant:
       If   g |- L1 list of augmented subterms
       and  g |- L2 list of augmented subterms
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators of all instantiations of EVars s.t. L1 is
            simultaneously smaller than or equal to L2
    *)
      (* ordeq (g, O1, O2, sc, ops) = ops'

       Invariant:
       If   g |- O1 augmented subterms
       and  g |- O2 augmented subterms
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators of all instantiations of EVars s.t. O1 is
            convertible to O2
    *)
      (* ordlteqs (g, L1, L2, sc, ops) = ops'

       Invariant:
       If   g |- L1 list of augmented subterms
       and  g |- L2 list of augmented subterms
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators of all instantiations of EVars s.t. L1 is
            convertible to L2
    *)
      (* ordeq (g, O1, O2, sc, ops) = ops'

       Invariant:
       If   g |- O1 augmented subterms
       and  g |- O2 augmented subterms
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
1           recursion operators of all instantiations of EVars s.t. O1 is
            convertible to O2 or smaller than O2
    *)
      (* createEVars (g, M) = ((g', M'), s')

       Invariant:
       If   |- g ctx
       and  g |- M mtx
       then |- g' ctx
       and  g' |- M' mtx
       and  g' |- s' : g
    *)
      (* select (g, (V, s)) = (g', (V1', s1'), (V2', s2'))

     Invariant:
     If   g |- s : G1   G1 |- V : type
     and  g |- V [s] = {V1} ... {Vn} a S
     then g' = g, V1 .. Vn
     and  g' |- s1' : G1'   G1' |- V1' : type
     and  g' |- s2' : G2'   G2' |- V2' : type
     and  g' |- V1' [s1'] = V1 [^n]
     and  g' |- V2' [s2'] = a S
    *)
      (* lemma (S, t, ops) = (g', P', P'', abstract', ops')

       Invariant:
       If   S state  (S = ((g, M), V)
                     |- g ctx
                     g |- M mtx
                     g |- V = {V1} ... {Vn} a S)
       and  S' state derived from S by an inductive call to t
       and  ops a list of operators
       then g is context, where all - variables are replaced by EVars in S'
       and  P' is induction variable vector of EVars in the inductive call
       and  P'' is induction variable vector of the theorem S.
       and  g' |- P' : (V1' .. Vn')
              (where  t : {W1} ..{Wm} b S, and Vi' are among W1 .. Wm)
       and  g'' |- P'' : (V1'' .. Vn'')
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
       If  g |- s1 : G1   G1 |- V1 : L
       and g |- s2 : G2   G2 |- V2 : L
       and g |- V1[s1] = c1 ; s1
       and g |- V2[s2] = c2 ; s2
       then B' holds iff c1 =  c2 and V1[s1] ==+ V2[s2]   (convertible on + arguments of c1)
    *)
      (* s1 = s2 = id *)(* s1 = s2 = Nil *)
      (* BUG: use the same variable (u1, s1) to continue comparing! --cs
                  in ((s2, s2), (W2, I.Dot (I.Exp (I.EClo (u2, s2), V2), t2))))
             FIXED: --cs Mon Nov  9 19:38:55 EST 1998 *)
      (* removeDuplicates ops = ops'

       Invariant:
       If   ops is a list of recursion operators,
       then ops' is a sublist of ops, s.t.
         forall S = ((g, M), V) in ops'
               |- g ctx
               g |- M mtx
               g |- V = {V0} .. {Vn} a ; S : type
               and Vi = ci ; S'
               and forall 1 <= i <= n:
                 either ci =/= c0 orelse
                 g, V0 .. Vi |- V0 [^ i] =/=+ Vi (not convertible on + arguments on c0)
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
    *))
      = handleExceptions expandLazy
    let expandEager = handleExceptions expandEager
    let apply = apply
    let menu = menu
  end ;;
