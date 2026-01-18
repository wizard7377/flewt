
(* Meta Abstraction *)
(* Author: Carsten Schuermann *)
module type METAABSTRACT  =
  sig
    module MetaSyn : METASYN
    exception Error of string 
    val abstract : MetaSyn.__State -> MetaSyn.__State
  end;;




(* Meta Abstraction *)
(* Author: Carsten Schuermann *)
module MetaAbstract(MetaAbstract:sig
                                   module Global : GLOBAL
                                   module MetaSyn' : METASYN
                                   module MetaGlobal : METAGLOBAL
                                   module Abstract : ABSTRACT
                                   module ModeTable : MODETABLE
                                   module Whnf : WHNF
                                   module Print : PRINT
                                   module Constraints : CONSTRAINTS
                                   module Unify : UNIFY
                                   module Names : NAMES
                                   module TypeCheck : TYPECHECK
                                   (*! sharing Abstract.IntSyn = MetaSyn'.IntSyn !*)
                                   (*! sharing ModeSyn.IntSyn = MetaSyn'.IntSyn !*)
                                   (*! sharing Whnf.IntSyn = MetaSyn'.IntSyn !*)
                                   (*! sharing Print.IntSyn = MetaSyn'.IntSyn !*)
                                   (*! sharing Constraints.IntSyn = MetaSyn'.IntSyn !*)
                                   (*! sharing Unify.IntSyn = MetaSyn'.IntSyn !*)
                                   (*! sharing Names.IntSyn = MetaSyn'.IntSyn !*)
                                   (*! sharing TypeCheck.IntSyn = MetaSyn'.IntSyn !*)
                                   module Subordinate : SUBORDINATE
                                 end) : METAABSTRACT =
  struct
    (*! sharing Subordinate.IntSyn = MetaSyn'.IntSyn  !*)
    module MetaSyn = MetaSyn'
    exception Error of string 
    module I = IntSyn
    module S = Stream
    module M = MetaSyn
    module C = Constraints
    type __Var =
      | EV of (I.__Exp option ref * I.__Exp * MetaSyn.__Mode) 
      | BV 
    let rec checkEmpty =
      function
      | nil -> ()
      | Cnstr ->
          (match C.simplify Cnstr with
           | nil -> ()
           | _ -> raise (Error "Unresolved constraints"))
    let rec typecheck (Prefix (__g, M, B), __v) =
      TypeCheck.typeCheck (__g, (__v, (I.Uni I.Type)))
    let rec modeEq =
      function
      | (Marg (ModeSyn.Plus, _), M.Top) -> true__
      | (Marg (ModeSyn.Minus, _), M.Bot) -> true__
      | _ -> false__
    let rec atxLookup =
      function
      | (I.Null, _) -> None
      | (Decl (M, BV), r) -> atxLookup (M, r)
      | (Decl (M, (EV (r', _, _) as E)), r) ->
          if r = r' then Some E else atxLookup (M, r)
    let rec raiseType =
      function
      | (0, __g, __v) -> __v
      | (depth, Decl (__g, __d), __v) ->
          raiseType ((depth - 1), __g, (I.Pi ((__d, I.Maybe), __v)))
    let rec weaken =
      function
      | (0, __g, a) -> I.id
      | (depth, Decl (__g', (Dec (name, __v) as __d)), a) ->
          let w' = weaken ((depth - 1), __g', a) in
          if Subordinate.belowEq ((I.targetFam __v), a)
          then I.dot1 w'
          else I.comp (w', I.shift)
    let rec countPi (__v) =
      let rec countPi' =
        function
        | (Root _, n) -> n
        | (Pi (_, __v), n) -> countPi' (__v, (n + 1))
        | (EClo (__v, _), n) -> countPi' (__v, n) in
      countPi' (__v, 0)
    let rec collectExp (lG0, __g, __Us, mode, Adepth) =
      collectExpW (lG0, __g, (Whnf.whnf __Us), mode, Adepth)
    let rec collectExpW =
      function
      | (lG0, __g, (Uni _, s), mode, Adepth) -> Adepth
      | (lG0, __g, (Pi ((__d, _), __v), s), mode, Adepth) ->
          collectExp
            (lG0, (I.Decl (__g, (I.decSub (__d, s)))), (__v, (I.dot1 s)), mode,
              (collectDec (lG0, __g, (__d, s), mode, Adepth)))
      | (lG0, __g, (Lam (__d, __u), s), mode, Adepth) ->
          collectExp
            (lG0, (I.Decl (__g, (I.decSub (__d, s)))), (__u, (I.dot1 s)), mode,
              (collectDec (lG0, __g, (__d, s), mode, Adepth)))
      | (lG0, __g, ((Root (BVar k, S), s) as __Us), mode, ((A, depth) as Adepth))
          ->
          let l = I.ctxLength __g in
          if (((k = l) + depth) - lG0) && (depth > 0)
          then
            let Dec (_, __v) = I.ctxDec (__g, k) in
            collectSpine
              (lG0, __g, (S, s), mode, ((I.Decl (A, BV)), (depth - 1)))
          else collectSpine (lG0, __g, (S, s), mode, Adepth)
      | (lG0, __g, (Root (C, S), s), mode, Adepth) ->
          collectSpine (lG0, __g, (S, s), mode, Adepth)
      | (lG0, __g, (EVar (r, GX, __v, cnstrs), s), mode, ((A, depth) as Adepth))
          ->
          (match atxLookup (A, r) with
           | None ->
               let _ = checkEmpty (!cnstrs) in
               let lGp' = ((I.ctxLength GX) - lG0) + depth in
               let w = weaken (lGp', GX, (I.targetFam __v)) in
               let iw = Whnf.invert w in
               let GX' = Whnf.strengthen (iw, GX) in
               let lGp'' = ((I.ctxLength GX') - lG0) + depth in
               let Vraised = raiseType (lGp'', GX', (I.EClo (__v, iw))) in
               let EVar (r', _, _, _) as x' =
                 I.newEVar (GX', (I.EClo (__v, iw))) in
               let _ = Unify.instantiateEVar (r, (I.EClo (x', w)), nil) in
               collectSub
                 (lG0, __g, lGp'', s, mode,
                   ((I.Decl (A, (EV (r', Vraised, mode)))), depth))
           | Some (EV (_, __v, _)) ->
               let lGp' = countPi __v in
               collectSub (lG0, __g, lGp', s, mode, Adepth))
      | (lGO, __g, (FgnExp csfe, s), mode, Adepth) ->
          I.FgnExpStd.fold csfe
            (function
             | (__u, Adepth') -> collectExp (lGO, __g, (__u, s), mode, Adepth'))
            Adepth
    let rec collectSub =
      function
      | (_, _, 0, _, _, Adepth) -> Adepth
      | (lG0, __g, lG', Shift k, mode, Adepth) ->
          collectSub
            (lG0, __g, lG', (I.Dot ((I.Idx (k + 1)), (I.Shift (k + 1)))), mode,
              Adepth)
      | (lG0, __g, lG', Dot (Idx k, s), mode, ((A, depth) as Adepth)) ->
          collectSub (lG0, __g, (lG' - 1), s, mode, Adepth)
      | (lG0, __g, lG', Dot (Exp (__u), s), mode, Adepth) ->
          collectSub
            (lG0, __g, (lG' - 1), s, mode,
              (collectExp (lG0, __g, (__u, I.id), mode, Adepth)))
    let rec collectSpine =
      function
      | (lG0, __g, (I.Nil, _), mode, Adepth) -> Adepth
      | (lG0, __g, (SClo (S, s'), s), mode, Adepth) ->
          collectSpine (lG0, __g, (S, (I.comp (s', s))), mode, Adepth)
      | (lG0, __g, (App (__u, S), s), mode, Adepth) ->
          collectSpine
            (lG0, __g, (S, s), mode,
              (collectExp (lG0, __g, (__u, s), mode, Adepth)))
    let rec collectDec (lG0, __g, (Dec (x, __v), s), mode, Adepth) =
      collectExp (lG0, __g, (__v, s), mode, Adepth)
    let rec collectModeW =
      function
      | (lG0, __g, modeIn, modeRec, (Root (Const cid, S), s), Adepth) ->
          let rec collectModeW' =
            function
            | (((I.Nil, _), ModeSyn.Mnil), Adepth) -> Adepth
            | (((SClo (S, s'), s), M), Adepth) ->
                collectModeW' (((S, (I.comp (s', s))), M), Adepth)
            | (((App (__u, S), s), Mapp (m, mS)), Adepth) ->
                collectModeW'
                  (((S, s), mS),
                    (if modeEq (m, modeIn)
                     then collectExp (lG0, __g, (__u, s), modeRec, Adepth)
                     else Adepth)) in
          let mS = valOf (ModeTable.modeLookup cid) in
          collectModeW' (((S, s), mS), Adepth)
      | (lG0, __g, modeIn, modeRec, (Pi ((__d, P), __v), s), Adepth) ->
          raise
            (Error
               "Implementation restricted to the Horn fragment of the meta logic")
    let rec collectG (lG0, __g, __Vs, Adepth) =
      collectGW (lG0, __g, (Whnf.whnf __Vs), Adepth)
    let rec collectGW (lG0, __g, __Vs, Adepth) =
      collectModeW
        (lG0, __g, M.Bot, M.Top, __Vs,
          (collectModeW (lG0, __g, M.Top, M.Bot, __Vs, Adepth)))
    let rec collectDTop (lG0, __g, __Vs, Adepth) =
      collectDTopW (lG0, __g, (Whnf.whnf __Vs), Adepth)
    let rec collectDTopW =
      function
      | (lG0, __g, (Pi (((Dec (x, V1) as __d), I.No), V2), s), Adepth) ->
          collectG
            (lG0, __g, (V1, s),
              (collectDTop
                 (lG0, (I.Decl (__g, (I.decSub (__d, s)))), (V2, (I.dot1 s)),
                   Adepth)))
      | (lG0, __g, ((Root _, s) as __Vs), Adepth) ->
          collectModeW (lG0, __g, M.Top, M.Top, __Vs, Adepth)
    let rec collectDBot (lG0, __g, __Vs, Adepth) =
      collectDBotW (lG0, __g, (Whnf.whnf __Vs), Adepth)
    let rec collectDBotW =
      function
      | (lG0, __g, (Pi ((__d, _), __v), s), Adepth) ->
          collectDBot
            (lG0, (I.Decl (__g, (I.decSub (__d, s)))), (__v, (I.dot1 s)), Adepth)
      | (lG0, __g, ((Root _, s) as __Vs), Adepth) ->
          collectModeW (lG0, __g, M.Bot, M.Bot, __Vs, Adepth)
    let rec collect (Prefix (__g, M, B), __v) =
      let lG0 = I.ctxLength __g in
      let (A, k) =
        collectDBot
          (lG0, __g, (__v, I.id),
            (collectDTop (lG0, __g, (__v, I.id), (I.Null, lG0)))) in
      A
    let rec lookupEV (A, r) =
      let rec lookupEV' =
        function
        | (Decl (A, EV (r, __v, _)), r', k) ->
            if r = r' then (k, __v) else lookupEV' (A, r', (k + 1))
        | (Decl (A, BV), r', k) -> lookupEV' (A, r', (k + 1)) in
      lookupEV' (A, r, 1)
    let rec lookupBV (A, i) =
      let rec lookupBV' =
        function
        | (Decl (A, EV (r, __v, _)), i, k) -> lookupBV' (A, i, (k + 1))
        | (Decl (A, BV), 1, k) -> k
        | (Decl (A, BV), i, k) -> lookupBV' (A, (i - 1), (k + 1)) in
      lookupBV' (A, i, 1)
    let rec abstractExpW =
      function
      | (A, __g, depth, ((Uni (__l) as __v), s)) -> __v
      | (A, __g, depth, (Pi ((__d, P), __v), s)) ->
          Abstract.piDepend
            (((abstractDec (A, __g, depth, (__d, s))), P),
              (abstractExp
                 (A, (I.Decl (__g, (I.decSub (__d, s)))), (depth + 1),
                   (__v, (I.dot1 s)))))
      | (A, __g, depth, (Lam (__d, __u), s)) ->
          I.Lam
            ((abstractDec (A, __g, depth, (__d, s))),
              (abstractExp
                 (A, (I.Decl (__g, (I.decSub (__d, s)))), (depth + 1),
                   (__u, (I.dot1 s)))))
      | (A, __g, depth, (Root ((BVar k as C), S), s)) ->
          if k > depth
          then
            let k' = lookupBV (A, (k - depth)) in
            I.Root
              ((I.BVar (k' + depth)), (abstractSpine (A, __g, depth, (S, s))))
          else I.Root (C, (abstractSpine (A, __g, depth, (S, s))))
      | (A, __g, depth, (Root (C, S), s)) ->
          I.Root (C, (abstractSpine (A, __g, depth, (S, s))))
      | (A, __g, depth, (EVar (r, _, __v, _), s)) ->
          let (k, Vraised) = lookupEV (A, r) in
          I.Root
            ((I.BVar (k + depth)),
              (abstractSub
                 (A, __g, depth, (Vraised, I.id), s, (I.targetFam __v), I.Nil)))
      | (A, __g, depth, (FgnExp csfe, s)) ->
          I.FgnExpStd.Map.apply csfe
            (function | __u -> abstractExp (A, __g, depth, (__u, s)))
    let rec abstractExp (A, __g, depth, __Us) =
      abstractExpW (A, __g, depth, (Whnf.whnf __Us))
    let rec abstractSpine =
      function
      | (A, __g, depth, (I.Nil, _)) -> I.Nil
      | (A, __g, depth, (App (__u, S), s)) ->
          I.App
            ((abstractExp (A, __g, depth, (__u, s))),
              (abstractSpine (A, __g, depth, (S, s))))
      | (A, __g, depth, (SClo (S, s'), s)) ->
          abstractSpine (A, __g, depth, (S, (I.comp (s', s))))
    let rec abstractSub (A, __g, depth, XVt, s, b, S) =
      abstractSubW (A, __g, depth, (Whnf.whnf XVt), s, b, S)
    let rec abstractSubW =
      function
      | (A, __g, depth, (Root _, _), s, b, S) -> S
      | (A, __g, depth, ((Pi _, _) as XVt), Shift k, b, S) ->
          abstractSub
            (A, __g, depth, XVt, (I.Dot ((I.Idx (k + 1)), (I.Shift (k + 1)))),
              b, S)
      | (A, __g, depth, ((Pi (_, XV'), t) as XVt), Dot (Idx k, s), b, S) ->
          let Dec (x, __v) = I.ctxDec (__g, k) in
          if k > depth
          then
            let k' = lookupBV (A, (k - depth)) in
            abstractSub
              (A, __g, depth, (XV', (I.dot1 t)), s, b,
                (I.App ((I.Root ((I.BVar (k' + depth)), I.Nil)), S)))
          else
            abstractSub
              (A, __g, depth, (XV', (I.dot1 t)), s, b,
                (I.App ((I.Root ((I.BVar k), I.Nil)), S)))
      | (A, __g, depth, ((Pi (_, XV'), t) as XVt), Dot (Exp (__u), s), b, S) ->
          abstractSub
            (A, __g, depth, (XV', (I.dot1 t)), s, b,
              (I.App ((abstractExp (A, __g, depth, (__u, I.id))), S)))
    let rec abstractDec (A, __g, depth, (Dec (xOpt, __v), s)) =
      I.Dec (xOpt, (abstractExp (A, __g, depth, (__v, s))))
    let rec abstractCtx =
      function
      | (I.Null, (Prefix (I.Null, I.Null, I.Null) as GM)) -> (GM, I.Null)
      | (Decl (A, BV), Prefix (Decl (__g, __d), Decl (M, marg), Decl (B, b))) ->
          let (Prefix (__g', M', B'), lG') =
            abstractCtx (A, (M.Prefix (__g, M, B))) in
          let __d' = abstractDec (A, __g, 0, (__d, I.id)) in
          let Dec (_, __v) = __d' in
          let _ =
            if !Global.doubleCheck
            then typecheck ((M.Prefix (__g', M', B')), __v)
            else () in
          ((M.Prefix
              ((I.Decl (__g', (Names.decName (__g', __d')))), (I.Decl (M', marg)),
                (I.Decl (B', b)))), (I.Decl (lG', __d')))
      | (Decl (A, EV (r, __v, m)), GM) ->
          let (Prefix (__g', M', B'), lG') = abstractCtx (A, GM) in
          let __v'' = abstractExp (A, lG', 0, (__v, I.id)) in
          let _ =
            if !Global.doubleCheck
            then typecheck ((M.Prefix (__g', M', B')), __v'')
            else () in
          ((M.Prefix
              ((I.Decl (__g', (Names.decName (__g', (I.Dec (None, __v'')))))),
                (I.Decl (M', m)),
                (I.Decl
                   (B',
                     (match m with
                      | M.Top -> !MetaGlobal.maxSplit
                      | M.Bot -> 0))))), lG')
    let rec abstract (State (name, (Prefix (__g, M, B) as GM), __v) as S) =
      let _ = Names.varReset I.Null in
      let A = collect (GM, __v) in
      let (GM', _) = abstractCtx (A, GM) in
      let __v' = abstractExp (A, __g, 0, (__v, I.id)) in
      let S = M.State (name, GM', __v') in
      let _ = if !Global.doubleCheck then typecheck (GM', __v') else () in S
    (* Invariants? *)
    (* Definition: Mode dependency order

       A pair ((__g, M), __v) is in mode dependency order iff
           __g |- __v : type
           __g |- M modes
       and __g = G0+, G1-, G1+,  ... G0-
       and __v = {xn:Vn} ..{x1:V1}__P0
       where G0+ collects all +variables when traversing __P0 in order
       and Gi+ collects all +variables when traverseing Vi in order  (i > 0)
       and Gi- collects all -variables when traversing Vi in order   (i > 0)
       and G0- collects all -variables when traversing __P0 in order.
    *)
    (* Variable found during collect  *)
    (* Var ::= EVar <r_, __v, St>       *)
    (*       | BV                     *)
    (*--------------------------------------------------------------------*)
    (* First section: Collecting EVars and BVars in mode dependency order *)
    (*--------------------------------------------------------------------*)
    (* checkEmpty Cnstr = ()
       raises Error exception if constraints Cnstr cannot be simplified
       to the empty constraint
    *)
    (* Let __g x A: defined as

       .      x .            = .
       (__g, __v) x (A, BVar)    = (__g x A), __v
       (__g, __v) x (A, EVar __v') = (__g, __v x A), __v'

       Then all A : Atx satisfy the following invariant: |- A Atx

       ? If    A = A', EV (r, __v, m)
       ? then  . |- __v = {__g x A'}.V' : type
       ? where __g x A' |- __v' : type

       We write A ||- __u if all EVars and BVars of __u are collected in A,
       A ||- S if all EVars and BVars of S are collected in A,
       and similiar notation for the other syntactic categories.
    *)
    (* typecheck ((__g, M), __v) = ()

       Invariant:
       If __g |- __v : type
       then typecheck returns ()
       else TypeCheck.Error is raised
    *)
    (* modeEq (marg, st) = B'

       Invariant:
       If   (marg = + and st = top) or (marg = - and st = bot)
       then B' = true
       else B' = false
    *)
    (* atxLookup (atx, r)  = Eopt'

       Invariant:
       If   r exists in atx as EV (__v)
       then Eopt' = Some EV and . |- __v : type
       else Eopt' = None
    *)
    (* raiseType (k, __g, __v) = {{__g'}} __v

       Invariant:
       If __g |- __v : __l
          __g = G0, __g'  (so k <= |__g|)
       then  G0 |- {{__g'}} __v : __l
             |__g'| = k

       All abstractions are potentially dependent.
    *)
    (* weaken (depth,  __g, a) = (w')
    *)
    (* countPi __v = n'

       If   __g |- x : __v
       and  __v = {__g'} __v'
       then |__g'| = n'
    *)
    (* __v in nf or enf? -fp *)
    (* collectExp (lG0, __g, (__u, s), mode, (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of __g, which must still
                   be traversed and collected

       If   __g  |- s : __g'  and   __g' |- __u : __v
       and  __g = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- __u [s]
    *)
    (* impossible? *)
    (* s = id *)
    (* invariant: all variables (EV or BV) in __v already seen! *)
    (* lGp' >= 0 *)
    (* lGp'' >= 0 *)
    (* invariant: all variables (EV) in Vraised already seen *)
    (* hack - should discuss with cs    -rv *)
    (* collectSub (lG0, __g, lG'', s, mode, (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of __g, which must still
                   be traversed and collected

       If   __g  |- s : __g'
       and  __g = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       and  __g' = GO, __g''
       and  |__g''| = lG''
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- s   (for the first |__g'| elements of s)
    *)
    (* eta expansion *)
    (* typing invariant guarantees that (EV, BV) in k : __v already
             collected !! *)
    (* typing invariant guarantees that (EV, BV) in __v already
             collected !! *)
    (* collectSpine (lG0, __g, (S, s), mode, (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of __g, which must still
                   be traversed and collected

       If   __g  |- s : __g'  and   __g' |- S : __v > __v'
       and  __g = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- S
    *)
    (* collectDec (lG0, __g, (x:__d, s), mode, (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of __g, which must still
                   be traversed and collected

       If   __g  |- s : __g'  and   __g' |- __d : __l
       and  __g = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- x:__d[s]
    *)
    (* collectModeW (lG0, __g, modeIn, modeRec, (__v, s) (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of __g, which must still
                   be traversed and collected

       If   __g  |- s : __g'  and   __g' |- __v : __l        __v[s] in whnf
       and  __g = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- __v
       and  A'' consists of all EVars/BVars marked with modeIn in __v and
                recored as modeRec
    *)
    (* s = id *)
    (* collectG (lG0, __g, (__v, s) (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of __g, which must still
                   be traversed and collected

       If   __g  |- s : __g'  and   __g' |- __v : __l
       and  __g = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- __v
       and  A'' consists of all Top EVars/BVars in the head of __v
                    followed by Bot/Top EVars/BVars of recursive calls
                    (A'' is in mode dependecy order)
    *)
    (* collectDTop (lG0, __g, (__v, s) (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of __g, which must still
                   be traversed and collected

       If   __g  |- s : __g'  and   __g' |- __v : __l
       and  __g = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- __v
       and  A'' consists of all Top EVars/BVars in the head of __v
                    followed by Bot/Top EVars/BVars of recursive calls
                    (A'' is in mode dependecy order)
    *)
    (* only arrows *)
    (* s = id *)
    (* collectDBot (lG0, __g, (__v, s), (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of __g, which must still
                   be traversed and collected

       If   __g  |- s : __g'  and   __g' |- __v : __l
       and  __g = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- __v
       and  A'' consists of all Top EVars/BVars in the head of __v
                    followed by Bot/Top EVars/BVars of recursive calls
                    followed by Top EVars/BVars in the head of __v
                    (A'' is in mode dependecy order)
    *)
    (* s = id *)
    (* collect ((__g,_,_), __v) = A'
       collects EVar's and BVar's in __v mode dependency order.

       Invariant:
       If   __g  |- s : __g'  and   __g' |- __v : __l
       then . |- A' Atx
       and  A' = A, A''
       and  A'' ||- __v
       and  A'' consists of all Top EVars/BVars in the head of __v
                    followed by Bot/Top EVars/BVars of recursive calls
                    followed by Top EVars/BVars in the head of __v
                    (A'' is in mode dependecy order)
    *)
    (*------------------------------------------------------------*)
    (* Second section: Abstracting over EVars and BVars that have *)
    (* been collected in mode dependency order                    *)
    (*------------------------------------------------------------*)
    (* lookupEV (A, r) = (k', __v')

       Invariant:

       If   A ||- __v
       and  __g |- x : __v' occuring in __v
       then __g x A |- k : __v'
       and  . |- __v' : type
    *)
    (* lookupEV' I.Null cannot occur by invariant *)
    (* lookupBV (A, i) = k'

       Invariant:

       If   A ||- __v
       and  __g |- __v type
       and  __g [x] A |- i : __v'
       then ex a substititution  __g x A |- s : __g [x] A
       and  __g x A |- k' : __v''
       and  __g x A |- __v' [s] = __v'' : type
    *)
    (* lookupBV' I.Null cannot occur by invariant *)
    (* abstractExpW (A, __g, depth, (__u, s)) = __u'

       Invariant:
       If    G0, __g |- s : G1   G1 |- __u : __v    (__u,s) in whnf
       and   |__g| = depth
       and   A is auxiliary context in mode dependency order
       and   A ||- __u  and  A ||- __v
       then  G0 x A, __g |- __u' : __v'
       and   . ||- __u' and . ||- __v'
       and   __u' is in nf
    *)
    (* s = id *)
    (* s = id *)
    (* IMPROVE: remove the raised variable, replace by __v -cs ?-fp *)
    (* hack - should discuss with cs     -rv *)
    (* abstractExp, same as abstractExpW, but (__v, s) need not be in whnf *)
    (* abstractSpine (A, __g, depth, (S, s)) = __u'

       Invariant:
       If    G0, __g |- s : G1   G1 |- S : V1 > V2
       and   |__g| = depth
       and   A is auxiliary context in mode dependency order
       and   A ||- __u  and  H ||- V1
       then  G0 x A, __g |- S' : V1' > V2'
       and   . ||- S' and . ||- V1'
    *)
    (* abstractSub (A, __g, depth, (XV, t), s, b, S) = S'

       Invariant:
       If    G0, __g |- s : __g'
       and   |__g| = depth
       and   A is auxiliary context in mode dependency order
       and   A ||- s
       then  G0 x A, __g |- S' : {XV [t]}.W > W
       and   . ||- S'
    *)
    (* optimize: whnf not necessary *)
    (* abstractDec (A, __g, depth, (x:__v, s)) = x:__v'

       Invariant:
       If    G0, __g |- s : G1   G1 |- __v : __l
       and   |__g| = __g
       and   |__g| = depth
       and   A is auxiliary context in mode dependency order
       and   A ||- __v
       then  G0 x A, __g |- __v' : __l
       and   . ||- __v'
    *)
    (* abstractCtx (A, (__g, M)) = ((__g', M') , __g'')

       Let E be a list of EVars possibly occuring in __g

       Invariant:
       __g' = __g x A
       M' = M x A    (similar to __g x A, but just represents mode information)
       __g'' = __g [x] A
    *)
    (* abstract ((__g, M), __v) = ((__g', M') , __v')

       Invariant:
       If    __g |- __v : type    (M modes associated with __g)
       then  __g' |- __v' : type  (M' modes associated with __g')
       and   . ||- __v'
    *)
    let abstract = abstract
  end ;;
