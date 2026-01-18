
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
    let rec vectorToString (__g, O) =
      let rec fmtOrder =
        function
        | Arg (__Us, __Vs) ->
            [F.String (Print.expToString (__g, (I.EClo __Us)));
            F.String ":";
            F.String (Print.expToString (__g, (I.EClo __Vs)))]
        | Lex (__l) -> [F.String "{"; F.hVbox (fmtOrders __l); F.String "}"]
        | Simul (__l) -> [F.String "["; F.hVbox (fmtOrders __l); F.String "]"]
      and fmtOrders =
        function
        | nil -> nil
        | (O)::nil -> fmtOrder O
        | (O)::__l -> (fmtOrder O) @ ((::) (F.String " ") fmtOrders __l) in
      F.makestring_fmt (F.hVbox (fmtOrder O))
    let rec vector (c, (S, s)) =
      let Vid = ((I.constType c), I.id) in
      let rec select' (n, (__Ss', __Vs'')) =
        select'W (n, (__Ss', (Whnf.whnf __Vs'')))
      and select'W =
        function
        | (1, ((App (__u', S'), s'), (Pi ((Dec (_, __v''), _), _), s''))) ->
            ((__u', s'), (__v'', s''))
        | (n, ((SClo (S', s1'), s2'), __Vs'')) ->
            select'W (n, ((S', (I.comp (s1', s2'))), __Vs''))
        | (n, ((App (__u', S'), s'), (Pi ((Dec (_, V1''), _), V2''), s''))) ->
            select'
              ((n - 1),
                ((S', s'), (V2'', (I.Dot ((I.Exp (I.EClo (__u', s'))), s''))))) in
      let rec select =
        function
        | Arg n -> O.Arg (select' (n, ((S, s), Vid)))
        | Lex (__l) -> O.Lex (map select __l)
        | Simul (__l) -> O.Simul (map select __l) in
      select (O.selLookup c)
    let rec set_parameter (__g, (EVar (r, _, __v, _) as x), k, sc, ops) =
      let rec set_parameter' =
        function
        | (0, ops') -> ops'
        | (k', ops') ->
            let Dec (_, __v') as __d' = I.ctxDec (__g, k') in
            let ops'' =
              CSManager.trail
                (function
                 | () ->
                     if
                       (Unify.unifiable (__g, (__v, I.id), (__v', I.id))) &&
                         (Unify.unifiable
                            (__g, (x, I.id),
                              ((I.Root ((I.BVar k'), I.Nil)), I.id)))
                     then sc ops'
                     else ops') in
            set_parameter' ((k' - 1), ops'') in
      set_parameter' (k, ops)
    let rec ltinit (__g, k, (__Us, __Vs), UsVs', sc, ops) =
      ltinitW (__g, k, (Whnf.whnfEta (__Us, __Vs)), UsVs', sc, ops)
    let rec ltinitW =
      function
      | (__g, k, (__Us, ((Root _, _) as __Vs)), UsVs', sc, ops) ->
          lt (__g, k, (__Us, __Vs), UsVs', sc, ops)
      | (__g, k, ((Lam (D1, __u), s1), (Pi (D2, __v), s2)), ((__u', s1'), (__v', s2')),
         sc, ops) ->
          ltinit
            ((I.Decl (__g, (I.decSub (D1, s1)))), (k + 1),
              ((__u, (I.dot1 s1)), (__v, (I.dot1 s2))),
              ((__u', (I.comp (s1', I.shift))), (__v', (I.comp (s2', I.shift)))),
              sc, ops)
    let rec lt (__g, k, (__Us, __Vs), (__Us', __Vs'), sc, ops) =
      ltW (__g, k, (__Us, __Vs), (Whnf.whnfEta (__Us', __Vs')), sc, ops)
    let rec ltW =
      function
      | (__g, k, (__Us, __Vs), ((Root (Const c, S'), s'), __Vs'), sc, ops) ->
          ltSpine
            (__g, k, (__Us, __Vs), ((S', s'), ((I.constType c), I.id)), sc, ops)
      | (__g, k, (__Us, __Vs), ((Root (BVar n, S'), s'), __Vs'), sc, ops) ->
          if n <= k
          then
            let Dec (_, __v') = I.ctxDec (__g, n) in
            ltSpine (__g, k, (__Us, __Vs), ((S', s'), (__v', I.id)), sc, ops)
          else ops
      | (__g, _, _, ((EVar _, _), _), _, ops) -> ops
      | (__g, k, ((__u, s1), (__v, s2)),
         ((Lam ((Dec (_, V1') as __d), __u'), s1'),
          (Pi ((Dec (_, V2'), _), __v'), s2')),
         sc, ops) ->
          if Subordinate.equiv ((I.targetFam __v), (I.targetFam V1'))
          then
            let x = I.newEVar (__g, (I.EClo (V1', s1'))) in
            let sc' = function | ops' -> set_parameter (__g, x, k, sc, ops') in
            lt
              (__g, k, ((__u, s1), (__v, s2)),
                ((__u', (I.Dot ((I.Exp x), s1'))),
                  (__v', (I.Dot ((I.Exp x), s2')))), sc', ops)
          else
            if Subordinate.below ((I.targetFam V1'), (I.targetFam __v))
            then
              (let x = I.newEVar (__g, (I.EClo (V1', s1'))) in
               lt
                 (__g, k, ((__u, s1), (__v, s2)),
                   ((__u', (I.Dot ((I.Exp x), s1'))),
                     (__v', (I.Dot ((I.Exp x), s2')))), sc, ops))
            else ops
    let rec ltSpine (__g, k, (__Us, __Vs), (__Ss', __Vs'), sc, ops) =
      ltSpineW (__g, k, (__Us, __Vs), (__Ss', (Whnf.whnf __Vs')), sc, ops)
    let rec ltSpineW =
      function
      | (__g, k, (__Us, __Vs), ((I.Nil, _), _), _, ops) -> ops
      | (__g, k, (__Us, __Vs), ((SClo (S, s'), s''), __Vs'), sc, ops) ->
          ltSpineW (__g, k, (__Us, __Vs), ((S, (I.comp (s', s''))), __Vs'), sc, ops)
      | (__g, k, (__Us, __Vs),
         ((App (__u', S'), s1'), (Pi ((Dec (_, V1'), _), V2'), s2')), sc, ops)
          ->
          let ops' = le (__g, k, (__Us, __Vs), ((__u', s1'), (V1', s2')), sc, ops) in
          ltSpine
            (__g, k, (__Us, __Vs),
              ((S', s1'), (V2', (I.Dot ((I.Exp (I.EClo (__u', s1'))), s2')))),
              sc, ops')
    let rec eq (__g, (__Us, __Vs), (__Us', __Vs'), sc, ops) =
      CSManager.trail
        (function
         | () ->
             if
               (Unify.unifiable (__g, __Vs, __Vs')) &&
                 (Unify.unifiable (__g, __Us, __Us'))
             then sc ops
             else ops)
    let rec le (__g, k, (__Us, __Vs), (__Us', __Vs'), sc, ops) =
      let ops' = eq (__g, (__Us, __Vs), (__Us', __Vs'), sc, ops) in
      leW (__g, k, (__Us, __Vs), (Whnf.whnfEta (__Us', __Vs')), sc, ops')
    let rec leW =
      function
      | (__g, k, ((__u, s1), (__v, s2)),
         ((Lam ((Dec (_, V1') as __d), __u'), s1'),
          (Pi ((Dec (_, V2'), _), __v'), s2')),
         sc, ops) ->
          if Subordinate.equiv ((I.targetFam __v), (I.targetFam V1'))
          then
            let x = I.newEVar (__g, (I.EClo (V1', s1'))) in
            let sc' = function | ops' -> set_parameter (__g, x, k, sc, ops') in
            le
              (__g, k, ((__u, s1), (__v, s2)),
                ((__u', (I.Dot ((I.Exp x), s1'))),
                  (__v', (I.Dot ((I.Exp x), s2')))), sc', ops)
          else
            if Subordinate.below ((I.targetFam V1'), (I.targetFam __v))
            then
              (let x = I.newEVar (__g, (I.EClo (V1', s1'))) in
               le
                 (__g, k, ((__u, s1), (__v, s2)),
                   ((__u', (I.Dot ((I.Exp x), s1'))),
                     (__v', (I.Dot ((I.Exp x), s2')))), sc, ops))
            else ops
      | (__g, k, (__Us, __Vs), (__Us', __Vs'), sc, ops) ->
          lt (__g, k, (__Us, __Vs), (__Us', __Vs'), sc, ops)
    let rec ordlt =
      function
      | (__g, Arg (UsVs), Arg (UsVs'), sc, ops) ->
          ltinit (__g, 0, UsVs, UsVs', sc, ops)
      | (__g, Lex (__l), Lex (__l'), sc, ops) -> ordltLex (__g, __l, __l', sc, ops)
      | (__g, Simul (__l), Simul (__l'), sc, ops) -> ordltSimul (__g, __l, __l', sc, ops)
    let rec ordltLex =
      function
      | (__g, nil, nil, sc, ops) -> ops
      | (__g, (O)::__l, (O')::__l', sc, ops) ->
          let ops' =
            CSManager.trail (function | () -> ordlt (__g, O, O', sc, ops)) in
          ordeq
            (__g, O, O', (function | ops'' -> ordltLex (__g, __l, __l', sc, ops'')),
              ops')
    let rec ordltSimul =
      function
      | (__g, nil, nil, sc, ops) -> ops
      | (__g, (O)::__l, (O')::__l', sc, ops) ->
          let ops'' =
            CSManager.trail
              (function
               | () ->
                   ordlt
                     (__g, O, O',
                       (function | ops' -> ordleSimul (__g, __l, __l', sc, ops')),
                       ops)) in
          ordeq
            (__g, O, O', (function | ops' -> ordltSimul (__g, __l, __l', sc, ops')),
              ops'')
    let rec ordleSimul =
      function
      | (__g, nil, nil, sc, ops) -> sc ops
      | (__g, (O)::__l, (O')::__l', sc, ops) ->
          ordle
            (__g, O, O', (function | ops' -> ordleSimul (__g, __l, __l', sc, ops')),
              ops)
    let rec ordeq =
      function
      | (__g, Arg (__Us, __Vs), Arg (__Us', __Vs'), sc, ops) ->
          if (Unify.unifiable (__g, __Vs, __Vs')) && (Unify.unifiable (__g, __Us, __Us'))
          then sc ops
          else ops
      | (__g, Lex (__l), Lex (__l'), sc, ops) -> ordeqs (__g, __l, __l', sc, ops)
      | (__g, Simul (__l), Simul (__l'), sc, ops) -> ordeqs (__g, __l, __l', sc, ops)
    let rec ordeqs =
      function
      | (__g, nil, nil, sc, ops) -> sc ops
      | (__g, (O)::__l, (O')::__l', sc, ops) ->
          ordeq
            (__g, O, O', (function | ops' -> ordeqs (__g, __l, __l', sc, ops')), ops)
    let rec ordle (__g, O, O', sc, ops) =
      let ops' = CSManager.trail (function | () -> ordeq (__g, O, O', sc, ops)) in
      ordlt (__g, O, O', sc, ops')
    let rec createEVars =
      function
      | Prefix (I.Null, I.Null, I.Null) ->
          ((M.Prefix (I.Null, I.Null, I.Null)), I.id)
      | Prefix (Decl (__g, __d), Decl (M, M.Top), Decl (B, b)) ->
          let (Prefix (__g', M', B'), s') = createEVars (M.Prefix (__g, M, B)) in
          ((M.Prefix
              ((I.Decl (__g', (I.decSub (__d, s')))), (I.Decl (M', M.Top)),
                (I.Decl (B', b)))), (I.dot1 s'))
      | Prefix (Decl (__g, Dec (_, __v)), Decl (M, M.Bot), Decl (B, _)) ->
          let (Prefix (__g', M', B'), s') = createEVars (M.Prefix (__g, M, B)) in
          let x = I.newEVar (__g', (I.EClo (__v, s'))) in
          ((M.Prefix (__g', M', B')), (I.Dot ((I.Exp x), s')))
    let rec select (__g, __Vs) = selectW (__g, (Whnf.whnf __Vs))
    let rec selectW (__g, (Pi (((Dec (_, V1) as __d), _), V2), s)) =
      let rec select' (__g, (Vs1, Vs2)) = selectW' (__g, (Vs1, (Whnf.whnf Vs2)))
      and selectW' =
        function
        | (__g, (Vs1, ((Root _, _) as Vs2))) -> (__g, (Vs1, Vs2))
        | (__g, ((V1, s1), (Pi ((__d, P), V2'), s2))) ->
            select'
              ((I.Decl (__g, (I.decSub (__d, s2)))),
                ((V1, (I.comp (s1, I.shift))), (V2', (I.dot1 s2)))) in
      select'
        ((I.Decl (__g, (I.decSub (__d, s)))),
          ((V1, (I.comp (s, I.shift))), (V2, (I.dot1 s))))
    let rec lemma (S, t, ops) =
      let State (name, GM, __v) = Lemma.apply (S, t) in
      let (Prefix (__g', M', B'), s') = createEVars GM in
      let (__g'', ((Root (Const a1, S1), s1), (Root (Const a2, S2), s2))) =
        select (__g', (__v, s')) in
      (__g'', (vector (a1, (S1, s1))), (vector (a2, (S2, s2))),
        (function
         | ops' ->
             (MetaAbstract.abstract
                (M.State (name, (M.Prefix (__g', M', B')), (I.EClo (__v, s')))))
               :: ops'), ops)
    let rec expandLazy' =
      function
      | (S, O.Empty, ops) -> ops
      | (S, LE (t, __l), ops) ->
          expandLazy' (S, __l, (ordle (lemma (S, t, ops))))
      | (S, LT (t, __l), ops) ->
          expandLazy' (S, __l, (ordlt (lemma (S, t, ops))))
    let rec recursionDepth (__v) =
      let rec recursionDepth' =
        function
        | (Root _, n) -> n
        | (Pi (_, __v), n) -> recursionDepth' (__v, (n + 1)) in
      recursionDepth' (__v, 0)
    let rec expandLazy (State (_, _, __v) as S) =
      if (recursionDepth __v) > (!MetaGlobal.maxRecurse)
      then nil
      else expandLazy' (S, (O.mutLookup (I.targetFam __v)), nil)
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
         ((App (__U1, S1), s1), (Pi ((Dec (_, V1), _), W1), t1)),
         ((App (__U2, S2), s2), (Pi ((Dec (_, V2), _), W2), t2))) ->
          (Conv.conv ((V1, t1), (V2, t2))) &&
            (inputConvSpine
               (mS,
                 ((S1, s1), (W1, (I.Dot ((I.Exp (I.EClo (__U1, s1))), t1)))),
                 ((S2, s2), (W2, (I.Dot ((I.Exp (I.EClo (__U1, s1))), t2))))))
      | (Mapp (Marg (ModeSyn.Plus, _), mS),
         ((App (__U1, S1), s1), (Pi ((Dec (_, V1), _), W1), t1)),
         ((App (__U2, S2), s2), (Pi ((Dec (_, V2), _), W2), t2))) ->
          inputConvSpine
            (mS, ((S1, s1), (W1, (I.Dot ((I.Exp (I.EClo (__U1, s1))), t1)))),
              ((S2, s2), (W2, (I.Dot ((I.Exp (I.EClo (__U2, s2))), t2)))))
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
          let rec check (State (name, GM, __v)) = checkW (Whnf.whnf (__v, I.id))
          and checkW (Pi ((__d, _), __v), s) =
            checkDec ((__d, (I.comp (s, I.shift))), (__v, (I.dot1 s)))
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
      (State (name, Prefix (__g', M', B'), Pi ((Dec (_, __v), _), _)) as S) =
      "Recursion : " ^ (Print.expToString (__g', __v))
    let rec handleExceptions f (P) =
      try f P with | Error s -> raise (Error s)
    (* Quantifier to mark parameters *)
    (* Q ::= Uni                     *)
    (*     | Ex                      *)
    (* If Q marks all parameters in a context __g we write   __g : Q               *)
    (* duplicate code? -fp *)
    (* vector (c, (S, s)) = __P'

       Invariant:
       If   . |- c : __v   __g |- s : __g'    __g' |- S : __v > type
       and  __v = {x1:V1} ... {xn:Vn} type
       and  __g |- S[s] = __U1 .. Un : __v[s] > type
       and  sel (c) = i1 .. im
       then __P' = (__U1'[s1']: V1'[t1'], .., __U1'[sm']: V1'[tm'])
       and  __g |- sj' : Gj'    Gj' |- Uj' : V1j'
       and  __g |- tj' : Gj'    Gj' |- Vj' : __l
       and  __g |- Vj' [tj'] = V1j' [sj'] : __l
       and  __g |- Uik = Uk'[sk']
    *)
    (* select'W (1, _, (I.Root _, _)) cannot occur by invariant ! *)
    (* set_parameter (__g, x, k, sc, ops) = ops'

       Invariant:
       appends a list of recursion operators to ops after
       instantiating x with all possible local parameters (between 1 and k)
    *)
    (* ltinit (__g, k, ((__U1, s1), (V2, s2)), ((__U3, s3), (V4, s4)), sc, ops) = ops'

       Invariant:
       If   __g = G0, Gp    (G0, global context, Gp, parameter context)
       and  |Gp| = k
       and  __g |- s1 : G1   G1 |- __U1 : V1
       and  __g |- s2 : G2   G2 |- V2 : __l
            __g |- s3 : G1   G1 |- __U3 : V3
       and  __g |- s4 : G2   G2 |- V4 : __l
       and  __g |- V1[s1] == V2 [s2]
       and  __g |- V3[s3] == V4 [s5]
       and  ops is a set of all all possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators
    *)
    (* = I.decSub (D2, s2) *)
    (* lt (__g, k, ((__u, s1), (__v, s2)), (__u', s'), sc, ops) = ops'

       Invariant:
       If   __g = G0, Gp    (G0, global context, Gp, parameter context)
       and  |Gp| = k
       and  __g |- s1 : G1   G1 |- __U1 : V1   (__U1 [s1] in  whnf)
       and  __g |- s2 : G2   G2 |- V2 : __l    (V2 [s2] in  whnf)
            __g |- s3 : G1   G1 |- __U3 : V3
       and  __g |- s4 : G2   G2 |- V4 : __l
       and  k is the length of the local context
       and  __g |- V1[s1] == V2 [s2]
       and  __g |- V3[s3] == V4 [s5]
       and  ops is a set of already calculuate possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators
    *)
    (* __Vs is Root!!! *)
    (* (__Us',__Vs') may not be eta-expanded!!! *)
    (* n must be a local variable *)
    (* == I.targetFam V2' *)
    (* enforce that x gets only bound to parameters *)
    (* = I.newEVar (I.EClo (V2', s2')) *)
    (* = I.newEVar (I.EClo (V2', s2')) *)
    (* eq (__g, ((__u, s1), (__v, s2)), (__u', s'), sc, ops) = ops'

       Invariant:
       If   __g |- s1 : G1   G1 |- __U1 : V1   (__U1 [s1] in  whnf)
       and  __g |- s2 : G2   G2 |- V2 : __l    (V2 [s2] in  whnf)
            __g |- s3 : G1   G1 |- __U3 : V3
       and  __g |- s4 : G2   G2 |- V4 : __l
       and  __g |- V1[s1] == V2 [s2]
       and  __g |- V3[s3] == V4 [s5]
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators resulting from __u[s1] = __u'[s']
    *)
    (* le (__g, k, ((__u, s1), (__v, s2)), (__u', s'), sc, ops) = ops'

       Invariant:
       If   __g = G0, Gp    (G0, global context, Gp, parameter context)
       and  |Gp| = k
       and  __g |- s1 : G1   G1 |- __U1 : V1   (__U1 [s1] in  whnf)
       and  __g |- s2 : G2   G2 |- V2 : __l    (V2 [s2] in  whnf)
            __g |- s3 : G1   G1 |- __U3 : V3
       and  __g |- s4 : G2   G2 |- V4 : __l
       and  k is the length of the local context
       and  __g |- V1[s1] == V2 [s2]
       and  __g |- V3[s3] == V4 [s5]
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators resulting from __u[s1] <= __u'[s']
    *)
    (* == I.targetFam V2' *)
    (* = I.newEVar (I.EClo (V2', s2')) *)
    (* enforces that x can only bound to parameter *)
    (* = I.newEVar (I.EClo (V2', s2')) *)
    (* ordlt (__g, O1, O2, sc, ops) = ops'

       Invariant:
       If   __g |- O1 augmented subterms
       and  __g |- O2 augmented subterms
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators of all instantiations of EVars s.t. O1 is
            lexicographically smaller than O2
    *)
    (* ordltLex (__g, L1, L2, sc, ops) = ops'

       Invariant:
       If   __g |- L1 list of augmented subterms
       and  __g |- L2 list of augmented subterms
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators of all instantiations of EVars s.t. L1 is
            lexicographically less then L2
    *)
    (* ordltSimul (__g, L1, L2, sc, ops) = ops'

       Invariant:
       If   __g |- L1 list of augmented subterms
       and  __g |- L2 list of augmented subterms
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators of all instantiations of EVars s.t. L1 is
            simultaneously smaller than L2
    *)
    (* ordleSimul (__g, L1, L2, sc, ops) = ops'

       Invariant:
       If   __g |- L1 list of augmented subterms
       and  __g |- L2 list of augmented subterms
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators of all instantiations of EVars s.t. L1 is
            simultaneously smaller than or equal to L2
    *)
    (* ordeq (__g, O1, O2, sc, ops) = ops'

       Invariant:
       If   __g |- O1 augmented subterms
       and  __g |- O2 augmented subterms
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators of all instantiations of EVars s.t. O1 is
            convertible to O2
    *)
    (* ordlteqs (__g, L1, L2, sc, ops) = ops'

       Invariant:
       If   __g |- L1 list of augmented subterms
       and  __g |- L2 list of augmented subterms
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators of all instantiations of EVars s.t. L1 is
            convertible to L2
    *)
    (* ordeq (__g, O1, O2, sc, ops) = ops'

       Invariant:
       If   __g |- O1 augmented subterms
       and  __g |- O2 augmented subterms
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
1           recursion operators of all instantiations of EVars s.t. O1 is
            convertible to O2 or smaller than O2
    *)
    (* createEVars (__g, M) = ((__g', M'), s')

       Invariant:
       If   |- __g ctx
       and  __g |- M mtx
       then |- __g' ctx
       and  __g' |- M' mtx
       and  __g' |- s' : __g
    *)
    (* select (__g, (__v, s)) = (__g', (V1', s1'), (V2', s2'))

     Invariant:
     If   __g |- s : G1   G1 |- __v : type
     and  __g |- __v [s] = {V1} ... {Vn} a S
     then __g' = __g, V1 .. Vn
     and  __g' |- s1' : G1'   G1' |- V1' : type
     and  __g' |- s2' : G2'   G2' |- V2' : type
     and  __g' |- V1' [s1'] = V1 [^n]
     and  __g' |- V2' [s2'] = a S
    *)
    (* lemma (S, t, ops) = (__g', __P', __P'', abstract', ops')

       Invariant:
       If   S state  (S = ((__g, M), __v)
                     |- __g ctx
                     __g |- M mtx
                     __g |- __v = {V1} ... {Vn} a S)
       and  S' state derived from S by an inductive call to t
       and  ops a list of operators
       then __g is context, where all - variables are replaced by EVars in S'
       and  __P' is induction variable vector of EVars in the inductive call
       and  __P'' is induction variable vector of the theorem S.
       and  __g' |- __P' : (V1' .. Vn')
              (where  t : {W1} ..{Wm} b S, and Vi' are among W1 .. Wm)
       and  __g'' |- __P'' : (V1'' .. Vn'')
              (where  a : {W1} ..{Wm} b S, and Vi'' are among W1 .. Wm)

    *)
    (* expandLazy' (S, __l, ops) = ops'

       Invariant:
       If   S state
       and  __l list of mutual recursive type families
       and  ops a list of operators
       then ops' extends ops by all operators
         representing inductive calls to theorems in __l
    *)
    (* expandLazy S = ops'

       Invariant:
       If   S State
       then ops' a list of operations which cause a recursive call
         (only induction variables are instantiated)
    *)
    (* inputConv ((V1, s1), (V2, s2)) = B

       Invariant:
       If  __g |- s1 : G1   G1 |- V1 : __l
       and __g |- s2 : G2   G2 |- V2 : __l
       and __g |- V1[s1] = c1 ; S1
       and __g |- V2[s2] = c2 ; S2
       then B' holds iff c1 =  c2 and V1[s1] ==+ V2[s2]   (convertible on + arguments of c1)
    *)
    (* s1 = s2 = id *)
    (* S1 = S2 = Nil *)
    (* BUG: use the same variable (__U1, s1) to continue comparing! --cs
                  in ((S2, s2), (W2, I.Dot (I.Exp (I.EClo (__U2, s2), V2), t2))))
             FIXED: --cs Mon Nov  9 19:38:55 EST 1998 *)
    (* removeDuplicates ops = ops'

       Invariant:
       If   ops is a list of recursion operators,
       then ops' is a sublist of ops, s.t.
         forall S = ((__g, M), __v) in ops'
               |- __g ctx
               __g |- M mtx
               __g |- __v = {V0} .. {Vn} a ; S : type
               and Vi = ci ; S'
               and forall 1 <= i <= n:
                 either ci =/= c0 orelse
                 __g, V0 .. Vi |- V0 [^ i] =/=+ Vi (not convertible on + arguments on c0)
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
