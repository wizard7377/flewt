
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
    let rec typecheck (Prefix (G, M, B), V) =
      TypeCheck.typeCheck (G, (V, (I.Uni I.Type)))
    let rec modeEq =
      function
      | (Marg (ModeSyn.Plus, _), M.Top) -> true__
      | (Marg (ModeSyn.Minus, _), M.Bot) -> true__
      | _ -> false__
    let rec atxLookup =
      function
      | (I.Null, _) -> NONE
      | (Decl (M, BV), r) -> atxLookup (M, r)
      | (Decl (M, (EV (r', _, _) as E)), r) ->
          if r = r' then SOME E else atxLookup (M, r)
    let rec raiseType =
      function
      | (0, G, V) -> V
      | (depth, Decl (G, D), V) ->
          raiseType ((depth - 1), G, (I.Pi ((D, I.Maybe), V)))
    let rec weaken =
      function
      | (0, G, a) -> I.id
      | (depth, Decl (G', (Dec (name, V) as D)), a) ->
          let w' = weaken ((depth - 1), G', a) in
          if Subordinate.belowEq ((I.targetFam V), a)
          then I.dot1 w'
          else I.comp (w', I.shift)
    let rec countPi (V) =
      let rec countPi' =
        function
        | (Root _, n) -> n
        | (Pi (_, V), n) -> countPi' (V, (n + 1))
        | (EClo (V, _), n) -> countPi' (V, n) in
      countPi' (V, 0)
    let rec collectExp (lG0, G, Us, mode, Adepth) =
      collectExpW (lG0, G, (Whnf.whnf Us), mode, Adepth)
    let rec collectExpW =
      function
      | (lG0, G, (Uni _, s), mode, Adepth) -> Adepth
      | (lG0, G, (Pi ((D, _), V), s), mode, Adepth) ->
          collectExp
            (lG0, (I.Decl (G, (I.decSub (D, s)))), (V, (I.dot1 s)), mode,
              (collectDec (lG0, G, (D, s), mode, Adepth)))
      | (lG0, G, (Lam (D, U), s), mode, Adepth) ->
          collectExp
            (lG0, (I.Decl (G, (I.decSub (D, s)))), (U, (I.dot1 s)), mode,
              (collectDec (lG0, G, (D, s), mode, Adepth)))
      | (lG0, G, ((Root (BVar k, S), s) as Us), mode, ((A, depth) as Adepth))
          ->
          let l = I.ctxLength G in
          if (((k = l) + depth) - lG0) && (depth > 0)
          then
            let Dec (_, V) = I.ctxDec (G, k) in
            collectSpine
              (lG0, G, (S, s), mode, ((I.Decl (A, BV)), (depth - 1)))
          else collectSpine (lG0, G, (S, s), mode, Adepth)
      | (lG0, G, (Root (C, S), s), mode, Adepth) ->
          collectSpine (lG0, G, (S, s), mode, Adepth)
      | (lG0, G, (EVar (r, GX, V, cnstrs), s), mode, ((A, depth) as Adepth))
          ->
          (match atxLookup (A, r) with
           | NONE ->
               let _ = checkEmpty (!cnstrs) in
               let lGp' = ((I.ctxLength GX) - lG0) + depth in
               let w = weaken (lGp', GX, (I.targetFam V)) in
               let iw = Whnf.invert w in
               let GX' = Whnf.strengthen (iw, GX) in
               let lGp'' = ((I.ctxLength GX') - lG0) + depth in
               let Vraised = raiseType (lGp'', GX', (I.EClo (V, iw))) in
               let EVar (r', _, _, _) as X' =
                 I.newEVar (GX', (I.EClo (V, iw))) in
               let _ = Unify.instantiateEVar (r, (I.EClo (X', w)), nil) in
               collectSub
                 (lG0, G, lGp'', s, mode,
                   ((I.Decl (A, (EV (r', Vraised, mode)))), depth))
           | SOME (EV (_, V, _)) ->
               let lGp' = countPi V in
               collectSub (lG0, G, lGp', s, mode, Adepth))
      | (lGO, G, (FgnExp csfe, s), mode, Adepth) ->
          I.FgnExpStd.fold csfe
            (function
             | (U, Adepth') -> collectExp (lGO, G, (U, s), mode, Adepth'))
            Adepth
    let rec collectSub =
      function
      | (_, _, 0, _, _, Adepth) -> Adepth
      | (lG0, G, lG', Shift k, mode, Adepth) ->
          collectSub
            (lG0, G, lG', (I.Dot ((I.Idx (k + 1)), (I.Shift (k + 1)))), mode,
              Adepth)
      | (lG0, G, lG', Dot (Idx k, s), mode, ((A, depth) as Adepth)) ->
          collectSub (lG0, G, (lG' - 1), s, mode, Adepth)
      | (lG0, G, lG', Dot (Exp (U), s), mode, Adepth) ->
          collectSub
            (lG0, G, (lG' - 1), s, mode,
              (collectExp (lG0, G, (U, I.id), mode, Adepth)))
    let rec collectSpine =
      function
      | (lG0, G, (I.Nil, _), mode, Adepth) -> Adepth
      | (lG0, G, (SClo (S, s'), s), mode, Adepth) ->
          collectSpine (lG0, G, (S, (I.comp (s', s))), mode, Adepth)
      | (lG0, G, (App (U, S), s), mode, Adepth) ->
          collectSpine
            (lG0, G, (S, s), mode,
              (collectExp (lG0, G, (U, s), mode, Adepth)))
    let rec collectDec (lG0, G, (Dec (x, V), s), mode, Adepth) =
      collectExp (lG0, G, (V, s), mode, Adepth)
    let rec collectModeW =
      function
      | (lG0, G, modeIn, modeRec, (Root (Const cid, S), s), Adepth) ->
          let rec collectModeW' =
            function
            | (((I.Nil, _), ModeSyn.Mnil), Adepth) -> Adepth
            | (((SClo (S, s'), s), M), Adepth) ->
                collectModeW' (((S, (I.comp (s', s))), M), Adepth)
            | (((App (U, S), s), Mapp (m, mS)), Adepth) ->
                collectModeW'
                  (((S, s), mS),
                    (if modeEq (m, modeIn)
                     then collectExp (lG0, G, (U, s), modeRec, Adepth)
                     else Adepth)) in
          let mS = valOf (ModeTable.modeLookup cid) in
          collectModeW' (((S, s), mS), Adepth)
      | (lG0, G, modeIn, modeRec, (Pi ((D, P), V), s), Adepth) ->
          raise
            (Error
               "Implementation restricted to the Horn fragment of the meta logic")
    let rec collectG (lG0, G, Vs, Adepth) =
      collectGW (lG0, G, (Whnf.whnf Vs), Adepth)
    let rec collectGW (lG0, G, Vs, Adepth) =
      collectModeW
        (lG0, G, M.Bot, M.Top, Vs,
          (collectModeW (lG0, G, M.Top, M.Bot, Vs, Adepth)))
    let rec collectDTop (lG0, G, Vs, Adepth) =
      collectDTopW (lG0, G, (Whnf.whnf Vs), Adepth)
    let rec collectDTopW =
      function
      | (lG0, G, (Pi (((Dec (x, V1) as D), I.No), V2), s), Adepth) ->
          collectG
            (lG0, G, (V1, s),
              (collectDTop
                 (lG0, (I.Decl (G, (I.decSub (D, s)))), (V2, (I.dot1 s)),
                   Adepth)))
      | (lG0, G, ((Root _, s) as Vs), Adepth) ->
          collectModeW (lG0, G, M.Top, M.Top, Vs, Adepth)
    let rec collectDBot (lG0, G, Vs, Adepth) =
      collectDBotW (lG0, G, (Whnf.whnf Vs), Adepth)
    let rec collectDBotW =
      function
      | (lG0, G, (Pi ((D, _), V), s), Adepth) ->
          collectDBot
            (lG0, (I.Decl (G, (I.decSub (D, s)))), (V, (I.dot1 s)), Adepth)
      | (lG0, G, ((Root _, s) as Vs), Adepth) ->
          collectModeW (lG0, G, M.Bot, M.Bot, Vs, Adepth)
    let rec collect (Prefix (G, M, B), V) =
      let lG0 = I.ctxLength G in
      let (A, k) =
        collectDBot
          (lG0, G, (V, I.id),
            (collectDTop (lG0, G, (V, I.id), (I.Null, lG0)))) in
      A
    let rec lookupEV (A, r) =
      let rec lookupEV' =
        function
        | (Decl (A, EV (r, V, _)), r', k) ->
            if r = r' then (k, V) else lookupEV' (A, r', (k + 1))
        | (Decl (A, BV), r', k) -> lookupEV' (A, r', (k + 1)) in
      lookupEV' (A, r, 1)
    let rec lookupBV (A, i) =
      let rec lookupBV' =
        function
        | (Decl (A, EV (r, V, _)), i, k) -> lookupBV' (A, i, (k + 1))
        | (Decl (A, BV), 1, k) -> k
        | (Decl (A, BV), i, k) -> lookupBV' (A, (i - 1), (k + 1)) in
      lookupBV' (A, i, 1)
    let rec abstractExpW =
      function
      | (A, G, depth, ((Uni (L) as V), s)) -> V
      | (A, G, depth, (Pi ((D, P), V), s)) ->
          Abstract.piDepend
            (((abstractDec (A, G, depth, (D, s))), P),
              (abstractExp
                 (A, (I.Decl (G, (I.decSub (D, s)))), (depth + 1),
                   (V, (I.dot1 s)))))
      | (A, G, depth, (Lam (D, U), s)) ->
          I.Lam
            ((abstractDec (A, G, depth, (D, s))),
              (abstractExp
                 (A, (I.Decl (G, (I.decSub (D, s)))), (depth + 1),
                   (U, (I.dot1 s)))))
      | (A, G, depth, (Root ((BVar k as C), S), s)) ->
          if k > depth
          then
            let k' = lookupBV (A, (k - depth)) in
            I.Root
              ((I.BVar (k' + depth)), (abstractSpine (A, G, depth, (S, s))))
          else I.Root (C, (abstractSpine (A, G, depth, (S, s))))
      | (A, G, depth, (Root (C, S), s)) ->
          I.Root (C, (abstractSpine (A, G, depth, (S, s))))
      | (A, G, depth, (EVar (r, _, V, _), s)) ->
          let (k, Vraised) = lookupEV (A, r) in
          I.Root
            ((I.BVar (k + depth)),
              (abstractSub
                 (A, G, depth, (Vraised, I.id), s, (I.targetFam V), I.Nil)))
      | (A, G, depth, (FgnExp csfe, s)) ->
          I.FgnExpStd.Map.apply csfe
            (function | U -> abstractExp (A, G, depth, (U, s)))
    let rec abstractExp (A, G, depth, Us) =
      abstractExpW (A, G, depth, (Whnf.whnf Us))
    let rec abstractSpine =
      function
      | (A, G, depth, (I.Nil, _)) -> I.Nil
      | (A, G, depth, (App (U, S), s)) ->
          I.App
            ((abstractExp (A, G, depth, (U, s))),
              (abstractSpine (A, G, depth, (S, s))))
      | (A, G, depth, (SClo (S, s'), s)) ->
          abstractSpine (A, G, depth, (S, (I.comp (s', s))))
    let rec abstractSub (A, G, depth, XVt, s, b, S) =
      abstractSubW (A, G, depth, (Whnf.whnf XVt), s, b, S)
    let rec abstractSubW =
      function
      | (A, G, depth, (Root _, _), s, b, S) -> S
      | (A, G, depth, ((Pi _, _) as XVt), Shift k, b, S) ->
          abstractSub
            (A, G, depth, XVt, (I.Dot ((I.Idx (k + 1)), (I.Shift (k + 1)))),
              b, S)
      | (A, G, depth, ((Pi (_, XV'), t) as XVt), Dot (Idx k, s), b, S) ->
          let Dec (x, V) = I.ctxDec (G, k) in
          if k > depth
          then
            let k' = lookupBV (A, (k - depth)) in
            abstractSub
              (A, G, depth, (XV', (I.dot1 t)), s, b,
                (I.App ((I.Root ((I.BVar (k' + depth)), I.Nil)), S)))
          else
            abstractSub
              (A, G, depth, (XV', (I.dot1 t)), s, b,
                (I.App ((I.Root ((I.BVar k), I.Nil)), S)))
      | (A, G, depth, ((Pi (_, XV'), t) as XVt), Dot (Exp (U), s), b, S) ->
          abstractSub
            (A, G, depth, (XV', (I.dot1 t)), s, b,
              (I.App ((abstractExp (A, G, depth, (U, I.id))), S)))
    let rec abstractDec (A, G, depth, (Dec (xOpt, V), s)) =
      I.Dec (xOpt, (abstractExp (A, G, depth, (V, s))))
    let rec abstractCtx =
      function
      | (I.Null, (Prefix (I.Null, I.Null, I.Null) as GM)) -> (GM, I.Null)
      | (Decl (A, BV), Prefix (Decl (G, D), Decl (M, marg), Decl (B, b))) ->
          let (Prefix (G', M', B'), lG') =
            abstractCtx (A, (M.Prefix (G, M, B))) in
          let D' = abstractDec (A, G, 0, (D, I.id)) in
          let Dec (_, V) = D' in
          let _ =
            if !Global.doubleCheck
            then typecheck ((M.Prefix (G', M', B')), V)
            else () in
          ((M.Prefix
              ((I.Decl (G', (Names.decName (G', D')))), (I.Decl (M', marg)),
                (I.Decl (B', b)))), (I.Decl (lG', D')))
      | (Decl (A, EV (r, V, m)), GM) ->
          let (Prefix (G', M', B'), lG') = abstractCtx (A, GM) in
          let V'' = abstractExp (A, lG', 0, (V, I.id)) in
          let _ =
            if !Global.doubleCheck
            then typecheck ((M.Prefix (G', M', B')), V'')
            else () in
          ((M.Prefix
              ((I.Decl (G', (Names.decName (G', (I.Dec (NONE, V'')))))),
                (I.Decl (M', m)),
                (I.Decl
                   (B',
                     (match m with
                      | M.Top -> !MetaGlobal.maxSplit
                      | M.Bot -> 0))))), lG')
    let rec abstract (State (name, (Prefix (G, M, B) as GM), V) as S) =
      let _ = Names.varReset I.Null in
      let A = collect (GM, V) in
      let (GM', _) = abstractCtx (A, GM) in
      let V' = abstractExp (A, G, 0, (V, I.id)) in
      let S = M.State (name, GM', V') in
      let _ = if !Global.doubleCheck then typecheck (GM', V') else () in S
    (* Invariants? *)
    (* Definition: Mode dependency order

       A pair ((G, M), V) is in mode dependency order iff
           G |- V : type
           G |- M modes
       and G = G0+, G1-, G1+,  ... G0-
       and V = {xn:Vn} ..{x1:V1}P0
       where G0+ collects all +variables when traversing P0 in order
       and Gi+ collects all +variables when traverseing Vi in order  (i > 0)
       and Gi- collects all -variables when traversing Vi in order   (i > 0)
       and G0- collects all -variables when traversing P0 in order.
    *)
    (* Variable found during collect  *)
    (* Var ::= EVar <r_, V, St>       *)
    (*       | BV                     *)
    (*--------------------------------------------------------------------*)
    (* First section: Collecting EVars and BVars in mode dependency order *)
    (*--------------------------------------------------------------------*)
    (* checkEmpty Cnstr = ()
       raises Error exception if constraints Cnstr cannot be simplified
       to the empty constraint
    *)
    (* Let G x A: defined as

       .      x .            = .
       (G, V) x (A, BVar)    = (G x A), V
       (G, V) x (A, EVar V') = (G, V x A), V'

       Then all A : Atx satisfy the following invariant: |- A Atx

       ? If    A = A', EV (r, V, m)
       ? then  . |- V = {G x A'}.V' : type
       ? where G x A' |- V' : type

       We write A ||- U if all EVars and BVars of U are collected in A,
       A ||- S if all EVars and BVars of S are collected in A,
       and similiar notation for the other syntactic categories.
    *)
    (* typecheck ((G, M), V) = ()

       Invariant:
       If G |- V : type
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
       If   r exists in atx as EV (V)
       then Eopt' = SOME EV and . |- V : type
       else Eopt' = NONE
    *)
    (* raiseType (k, G, V) = {{G'}} V

       Invariant:
       If G |- V : L
          G = G0, G'  (so k <= |G|)
       then  G0 |- {{G'}} V : L
             |G'| = k

       All abstractions are potentially dependent.
    *)
    (* weaken (depth,  G, a) = (w')
    *)
    (* countPi V = n'

       If   G |- x : V
       and  V = {G'} V'
       then |G'| = n'
    *)
    (* V in nf or enf? -fp *)
    (* collectExp (lG0, G, (U, s), mode, (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of G, which must still
                   be traversed and collected

       If   G  |- s : G'  and   G' |- U : V
       and  G = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- U [s]
    *)
    (* impossible? *)
    (* s = id *)
    (* invariant: all variables (EV or BV) in V already seen! *)
    (* lGp' >= 0 *)
    (* lGp'' >= 0 *)
    (* invariant: all variables (EV) in Vraised already seen *)
    (* hack - should discuss with cs    -rv *)
    (* collectSub (lG0, G, lG'', s, mode, (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of G, which must still
                   be traversed and collected

       If   G  |- s : G'
       and  G = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       and  G' = GO, G''
       and  |G''| = lG''
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- s   (for the first |G'| elements of s)
    *)
    (* eta expansion *)
    (* typing invariant guarantees that (EV, BV) in k : V already
             collected !! *)
    (* typing invariant guarantees that (EV, BV) in V already
             collected !! *)
    (* collectSpine (lG0, G, (S, s), mode, (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of G, which must still
                   be traversed and collected

       If   G  |- s : G'  and   G' |- S : V > V'
       and  G = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- S
    *)
    (* collectDec (lG0, G, (x:D, s), mode, (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of G, which must still
                   be traversed and collected

       If   G  |- s : G'  and   G' |- D : L
       and  G = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- x:D[s]
    *)
    (* collectModeW (lG0, G, modeIn, modeRec, (V, s) (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of G, which must still
                   be traversed and collected

       If   G  |- s : G'  and   G' |- V : L        V[s] in whnf
       and  G = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- V
       and  A'' consists of all EVars/BVars marked with modeIn in V and
                recored as modeRec
    *)
    (* s = id *)
    (* collectG (lG0, G, (V, s) (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of G, which must still
                   be traversed and collected

       If   G  |- s : G'  and   G' |- V : L
       and  G = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- V
       and  A'' consists of all Top EVars/BVars in the head of V
                    followed by Bot/Top EVars/BVars of recursive calls
                    (A'' is in mode dependecy order)
    *)
    (* collectDTop (lG0, G, (V, s) (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of G, which must still
                   be traversed and collected

       If   G  |- s : G'  and   G' |- V : L
       and  G = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- V
       and  A'' consists of all Top EVars/BVars in the head of V
                    followed by Bot/Top EVars/BVars of recursive calls
                    (A'' is in mode dependecy order)
    *)
    (* only arrows *)
    (* s = id *)
    (* collectDBot (lG0, G, (V, s), (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of G, which must still
                   be traversed and collected

       If   G  |- s : G'  and   G' |- V : L
       and  G = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- V
       and  A'' consists of all Top EVars/BVars in the head of V
                    followed by Bot/Top EVars/BVars of recursive calls
                    followed by Top EVars/BVars in the head of V
                    (A'' is in mode dependecy order)
    *)
    (* s = id *)
    (* collect ((G,_,_), V) = A'
       collects EVar's and BVar's in V mode dependency order.

       Invariant:
       If   G  |- s : G'  and   G' |- V : L
       then . |- A' Atx
       and  A' = A, A''
       and  A'' ||- V
       and  A'' consists of all Top EVars/BVars in the head of V
                    followed by Bot/Top EVars/BVars of recursive calls
                    followed by Top EVars/BVars in the head of V
                    (A'' is in mode dependecy order)
    *)
    (*------------------------------------------------------------*)
    (* Second section: Abstracting over EVars and BVars that have *)
    (* been collected in mode dependency order                    *)
    (*------------------------------------------------------------*)
    (* lookupEV (A, r) = (k', V')

       Invariant:

       If   A ||- V
       and  G |- X : V' occuring in V
       then G x A |- k : V'
       and  . |- V' : type
    *)
    (* lookupEV' I.Null cannot occur by invariant *)
    (* lookupBV (A, i) = k'

       Invariant:

       If   A ||- V
       and  G |- V type
       and  G [x] A |- i : V'
       then ex a substititution  G x A |- s : G [x] A
       and  G x A |- k' : V''
       and  G x A |- V' [s] = V'' : type
    *)
    (* lookupBV' I.Null cannot occur by invariant *)
    (* abstractExpW (A, G, depth, (U, s)) = U'

       Invariant:
       If    G0, G |- s : G1   G1 |- U : V    (U,s) in whnf
       and   |G| = depth
       and   A is auxiliary context in mode dependency order
       and   A ||- U  and  A ||- V
       then  G0 x A, G |- U' : V'
       and   . ||- U' and . ||- V'
       and   U' is in nf
    *)
    (* s = id *)
    (* s = id *)
    (* IMPROVE: remove the raised variable, replace by V -cs ?-fp *)
    (* hack - should discuss with cs     -rv *)
    (* abstractExp, same as abstractExpW, but (V, s) need not be in whnf *)
    (* abstractSpine (A, G, depth, (S, s)) = U'

       Invariant:
       If    G0, G |- s : G1   G1 |- S : V1 > V2
       and   |G| = depth
       and   A is auxiliary context in mode dependency order
       and   A ||- U  and  H ||- V1
       then  G0 x A, G |- S' : V1' > V2'
       and   . ||- S' and . ||- V1'
    *)
    (* abstractSub (A, G, depth, (XV, t), s, b, S) = S'

       Invariant:
       If    G0, G |- s : G'
       and   |G| = depth
       and   A is auxiliary context in mode dependency order
       and   A ||- s
       then  G0 x A, G |- S' : {XV [t]}.W > W
       and   . ||- S'
    *)
    (* optimize: whnf not necessary *)
    (* abstractDec (A, G, depth, (x:V, s)) = x:V'

       Invariant:
       If    G0, G |- s : G1   G1 |- V : L
       and   |G| = G
       and   |G| = depth
       and   A is auxiliary context in mode dependency order
       and   A ||- V
       then  G0 x A, G |- V' : L
       and   . ||- V'
    *)
    (* abstractCtx (A, (G, M)) = ((G', M') , G'')

       Let E be a list of EVars possibly occuring in G

       Invariant:
       G' = G x A
       M' = M x A    (similar to G x A, but just represents mode information)
       G'' = G [x] A
    *)
    (* abstract ((G, M), V) = ((G', M') , V')

       Invariant:
       If    G |- V : type    (M modes associated with G)
       then  G' |- V' : type  (M' modes associated with G')
       and   . ||- V'
    *)
    let abstract = abstract
  end ;;
