
module type ABSTRACTTABLED  =
  sig
    exception Error of
      ((string)(*! structure TableParam : TABLEPARAM !*)
      (*! structure IntSyn : INTSYN !*)(* Author: Brigitte Pientka *)
      (* Abstraction *)) 
    val abstractEVarCtx :
      (CompSyn.__DProg * IntSyn.__Exp * IntSyn.__Sub) ->
        (IntSyn.dctx * IntSyn.dctx * IntSyn.dctx * IntSyn.__Exp *
          TableParam.__ResEqn * IntSyn.__Sub)
    val abstractAnswSub : IntSyn.__Sub -> (IntSyn.dctx * IntSyn.__Sub)
    val raiseType : (IntSyn.dctx * IntSyn.__Exp) -> IntSyn.__Exp
  end;;




module AbstractTabled(AbstractTabled:sig
                                       module Whnf : WHNF
                                       module Unify : UNIFY
                                       module Constraints : CONSTRAINTS
                                       module Subordinate : SUBORDINATE
                                       module Print : PRINT
                                       module Conv :
                                       ((CONV)(* Abstraction *)(* Author: Frank Pfenning, Carsten Schuermann *)
                                       (* Modified: Roberto Virga, Brigitte Pientka *)
                                       (*! structure IntSyn' : INTSYN !*)
                                       (*! sharing Whnf.IntSyn = IntSyn' !*)
                                       (*! sharing Unify.IntSyn = IntSyn' !*)
                                       (*! sharing Constraints.IntSyn = IntSyn' !*)
                                       (*! sharing Subordinate.IntSyn = IntSyn' !*)
                                       (*! sharing Print.IntSyn = IntSyn' !*))
                                     end) : ABSTRACTTABLED =
  struct
    exception Error of
      ((string)(*! structure TableParam = TableParam !*)
      (*! structure IntSyn = IntSyn' !*)(*! sharing TableParam.IntSyn = IntSyn' !*)
      (*! structure TableParam : TABLEPARAM !*)(*! sharing Conv.IntSyn = IntSyn' !*))
      
    module I = IntSyn
    module C = CompSyn
    type __Duplicates =
      | AV of (I.__Exp * int) 
      | FGN of int 
    type seenIn =
      | TypeLabel 
      | Body 
    type __ExistVars =
      | EV of I.__Exp 
    let rec lengthSub =
      function | Shift n -> 0 | Dot (E, s) -> (+) 1 lengthSub s
    let rec compose' =
      function
      | (IntSyn.Null, g) -> g
      | (Decl (g', D), g) -> IntSyn.Decl ((compose' (g', g)), D)
    let rec isId =
      function
      | Shift n -> n = 0
      | Dot (Idx n, s') as s -> isId' (s, 0)
      | Dot (I.Undef, s') as s -> isId' (s, 0)
      | Dot (Exp _, s) -> false__
    let rec isId' =
      function
      | (Shift n, k) -> n = k
      | (Dot (Idx i, s), k) -> let k' = k + 1 in (i = k') && (isId' (s, k'))
      | (Dot (I.Undef, s), k) -> isId' (s, (k + 1))
    let rec equalCtx =
      function
      | (I.Null, s, I.Null, s') -> true__
      | (Decl (g, D), s, Decl (g', D'), s') ->
          (Conv.convDec ((D, s), (D', s'))) &&
            (equalCtx (g, (I.dot1 s), g', (I.dot1 s')))
      | (Decl (g, D), s, I.Null, s') -> false__
      | (I.Null, s, Decl (g', D'), s') -> false__
    let rec eqEVarW arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (EVar (r1, _, _, _), EV (EVar (r2, _, _, _))) -> r1 = r2
      | (_, _) -> false__
    let rec eqEVar (X1) (EV (X2)) =
      let (X1', s) = Whnf.whnf (X1, I.id) in
      let (X2', s) = Whnf.whnf (X2, I.id) in eqEVarW X1' (EV X2')
    let rec member' (P) (K) =
      let exists' =
        function
        | I.Null -> NONE
        | Decl (K', (l, EV (Y))) -> if P (EV Y) then SOME l else exists' K' in
      exists' K
    let rec member (P) (K) =
      let exists' =
        function
        | I.Null -> NONE
        | Decl (K', (i, Y)) -> if P Y then SOME i else exists' K' in
      exists' K
    let rec update' (P) (K) =
      let update' =
        function
        | I.Null -> I.Null
        | Decl (K', (label, Y)) ->
            if P Y
            then I.Decl (K', (Body, Y))
            else I.Decl ((update' K'), (label, Y)) in
      update' K
    let rec update (P) (K) =
      let update' =
        function
        | I.Null -> I.Null
        | Decl (K', ((label, i), Y)) ->
            if P Y
            then I.Decl (K', ((Body, i), Y))
            else I.Decl ((update' K'), ((label, i), Y)) in
      update' K
    let rec or__ =
      function
      | (I.Maybe, _) -> I.Maybe
      | (_, I.Maybe) -> I.Maybe
      | (I.Meta, _) -> I.Meta
      | (_, I.Meta) -> I.Meta
      | (I.No, I.No) -> I.No
    let rec occursInExp =
      function
      | (k, Uni _) -> I.No
      | (k, Pi (DP, V)) ->
          or__ ((occursInDecP (k, DP)), (occursInExp ((k + 1), V)))
      | (k, Root (H, S)) -> occursInHead (k, H, (occursInSpine (k, S)))
      | (k, Lam (D, V)) ->
          or__ ((occursInDec (k, D)), (occursInExp ((k + 1), V)))
      | (k, FgnExp csfe) ->
          I.FgnExpStd.fold csfe
            (function
             | (U, DP) ->
                 or__ (DP, (occursInExp (k, (Whnf.normalize (U, I.id))))))
            I.No
    let rec occursInHead =
      function
      | (k, BVar k', DP) -> if k = k' then I.Maybe else DP
      | (k, Const _, DP) -> DP
      | (k, Def _, DP) -> DP
      | (k, FgnConst _, DP) -> DP
      | (k, Skonst _, I.No) -> I.No
      | (k, Skonst _, I.Meta) -> I.Meta
      | (k, Skonst _, I.Maybe) -> I.Meta
    let rec occursInSpine =
      function
      | (_, I.Nil) -> I.No
      | (k, App (U, S)) ->
          or__ ((occursInExp (k, U)), (occursInSpine (k, S)))
    let rec occursInDec (k, Dec (_, V)) = occursInExp (k, V)
    let rec occursInDecP (k, (D, _)) = occursInDec (k, D)
    let rec piDepend =
      function
      | ((D, I.No), V) as DPV -> I.Pi DPV
      | ((D, I.Meta), V) as DPV -> I.Pi DPV
      | ((D, I.Maybe), V) -> I.Pi ((D, (occursInExp (1, V))), V)
    let rec raiseType =
      function
      | (I.Null, V) -> V
      | (Decl (g, D), V) -> raiseType (g, (I.Pi ((D, I.Maybe), V)))
    let rec reverseCtx =
      function
      | (I.Null, g) -> g
      | (Decl (g, D), g') -> reverseCtx (g, (I.Decl (g', D)))
    let rec ctxToEVarSub =
      function
      | (IntSyn.Null, s) -> s
      | (Decl (g, Dec (_, A)), s) ->
          let s' = ctxToEVarSub (g, s) in
          let X = IntSyn.newEVar (IntSyn.Null, (I.EClo (A, s'))) in
          IntSyn.Dot ((IntSyn.Exp X), s')
    let rec collectExpW =
      function
      | (Gss, Gl, (Uni (L), s), K, DupVars, flag, d) -> (K, DupVars)
      | (Gss, Gl, (Pi ((D, _), V), s), K, DupVars, flag, d) ->
          let (K', _) = collectDec (Gss, (D, s), (K, DupVars), d, false__) in
          collectExp
            (Gss, (I.Decl (Gl, (I.decSub (D, s)))), (V, (I.dot1 s)), K',
              DupVars, flag, d)
      | (Gss, Gl, (Root (_, S), s), K, DupVars, flag, d) ->
          collectSpine (Gss, Gl, (S, s), K, DupVars, flag, d)
      | (Gss, Gl, (Lam (D, U), s), K, DupVars, flag, d) ->
          let (K', _) = collectDec (Gss, (D, s), (K, DupVars), d, false__) in
          collectExp
            (Gss, (I.Decl (Gl, (I.decSub (D, s)))), (U, (I.dot1 s)), K',
              DupVars, flag, (d + 1))
      | (Gss, Gl, ((EVar (r, GX, V, cnstrs) as X), s), K, DupVars, flag, d)
          -> collectEVar (Gss, Gl, (X, s), K, DupVars, flag, d)
      | (Gss, Gl, (FgnExp csfe, s), K, DupVars, flag, d) ->
          I.FgnExpStd.fold csfe
            (function
             | (U, KD') ->
                 let (K', Dup) = KD' in
                 collectExp (Gss, Gl, (U, s), K', Dup, false__, d))
            (K, (I.Decl (DupVars, (FGN d))))
    let rec collectExp (Gss, Gl, Us, K, DupVars, flag, d) =
      collectExpW (Gss, Gl, (Whnf.whnf Us), K, DupVars, flag, d)
    let rec collectSpine =
      function
      | (Gss, Gl, (I.Nil, _), K, DupVars, flag, d) -> (K, DupVars)
      | (Gss, Gl, (SClo (S, s'), s), K, DupVars, flag, d) ->
          collectSpine (Gss, Gl, (S, (I.comp (s', s))), K, DupVars, flag, d)
      | (Gss, Gl, (App (U, S), s), K, DupVars, flag, d) ->
          let (K', DupVars') =
            collectExp (Gss, Gl, (U, s), K, DupVars, flag, d) in
          collectSpine (Gss, Gl, (S, s), K', DupVars', flag, d)
    let rec collectEVarFapStr
      (Gss, Gl, ((X', V'), w), ((EVar (r, GX, V, cnstrs) as X), s), K,
       DupVars, flag, d)
      =
      match member' (eqEVar X) K with
      | SOME label ->
          if flag
          then
            collectSub
              (Gss, Gl, s, K, (I.Decl (DupVars, (AV (X, d)))), flag, d)
          else collectSub (Gss, Gl, s, K, DupVars, flag, d)
      | NONE ->
          let label = if flag then Body else TypeLabel in
          let (K', DupVars') =
            collectExp
              ((I.Null, I.id), I.Null, (V', I.id), K, DupVars, false__, d) in
          collectSub
            (Gss, Gl, (I.comp (w, s)), (I.Decl (K', (label, (EV X')))),
              DupVars', flag, d)
    let rec collectEVarNFapStr
      (Gss, Gl, ((X', V'), w), ((EVar (r, GX, V, cnstrs) as X), s), K,
       DupVars, flag, d)
      =
      match member' (eqEVar X) K with
      | SOME label ->
          if flag
          then
            collectSub
              (Gss, Gl, s, K, (I.Decl (DupVars, (AV (X, d)))), flag, d)
          else collectSub (Gss, Gl, s, K, DupVars, flag, d)
      | NONE ->
          let label = if flag then Body else TypeLabel in
          let (K', DupVars') =
            collectExp
              ((I.Null, I.id), I.Null, (V', I.id), K, DupVars, false__, d) in
          if flag
          then
            collectSub
              (Gss, Gl, (I.comp (w, s)), (I.Decl (K', (label, (EV X')))),
                (I.Decl (DupVars', (AV (X', d)))), flag, d)
          else
            collectSub
              (Gss, Gl, (I.comp (w, s)), (I.Decl (K', (label, (EV X')))),
                DupVars', flag, d)
    let rec collectEVarStr
      (((Gs, ss) as Gss), Gl, ((EVar (r, GX, V, cnstrs) as X), s), K,
       DupVars, flag, d)
      =
      let w = Subordinate.weaken (GX, (I.targetFam V)) in
      let iw = Whnf.invert w in
      let GX' = Whnf.strengthen (iw, GX) in
      let EVar (r', _, _, _) as X' = I.newEVar (GX', (I.EClo (V, iw))) in
      let _ = Unify.instantiateEVar (r, (I.EClo (X', w)), nil) in
      let V' = raiseType (GX', (I.EClo (V, iw))) in
      if isId (I.comp (w, (I.comp (ss, s))))
      then
        collectEVarFapStr
          (Gss, Gl, ((X', V'), w), (X, s), K, DupVars, flag, d)
      else
        collectEVarNFapStr
          (Gss, Gl, ((X', V'), w), (X, s), K, DupVars, flag, d)
    let rec collectEVarFap
      (Gss, Gl, ((EVar (r, GX, V, cnstrs) as X), s), K, DupVars, flag, d) =
      match member (eqEVar X) K with
      | SOME label ->
          if flag
          then
            collectSub
              (Gss, Gl, s, K, (I.Decl (DupVars, (AV (X, d)))), flag, d)
          else collectSub (Gss, Gl, s, K, DupVars, flag, d)
      | NONE ->
          let label = if flag then Body else TypeLabel in
          let V' = raiseType (GX, V) in
          let (K', DupVars') =
            collectExp
              ((I.Null, I.id), I.Null, (V', I.id), K, DupVars, false__, d) in
          collectSub
            (Gss, Gl, s, (I.Decl (K', (label, (EV X)))), DupVars', flag, d)
    let rec collectEVarNFap
      (Gss, Gl, ((EVar (r, GX, V, cnstrs) as X), s), K, DupVars, flag, d) =
      match member' (eqEVar X) K with
      | SOME label ->
          if flag
          then
            collectSub
              (Gss, Gl, s, K, (I.Decl (DupVars, (AV (X, d)))), flag, d)
          else collectSub (Gss, Gl, s, K, DupVars, flag, d)
      | NONE ->
          let label = if flag then Body else TypeLabel in
          let V' = raiseType (GX, V) in
          let (K', DupVars') =
            collectExp
              ((I.Null, I.id), I.Null, (V', I.id), K, DupVars, false__, d) in
          if flag
          then
            collectSub
              (Gss, Gl, s, (I.Decl (K', (label, (EV X)))),
                (I.Decl (DupVars, (AV (X, d)))), flag, d)
          else
            collectSub
              (Gss, Gl, s, (I.Decl (K', (label, (EV X)))), DupVars, flag, d)
    let rec collectEVar
      (Gss, Gl, ((EVar (r, GX, V, cnstrs) as X), s), K, DupVars, flag, d) =
      if !TableParam.strengthen
      then collectEVarStr (Gss, Gl, (X, s), K, DupVars, flag, d)
      else
        if isId s
        then collectEVarFap (Gss, Gl, (X, s), K, DupVars, flag, d)
        else collectEVarNFap (Gss, Gl, (X, s), K, DupVars, flag, d)
    let rec collectDec (Gss, (Dec (_, V), s), (K, DupVars), d, flag) =
      let (K', DupVars') =
        collectExp (Gss, I.Null, (V, s), K, DupVars, flag, d) in
      (K', DupVars')
    let rec collectSub =
      function
      | (Gss, Gl, Shift _, K, DupVars, flag, d) -> (K, DupVars)
      | (Gss, Gl, Dot (Idx _, s), K, DupVars, flag, d) ->
          collectSub (Gss, Gl, s, K, DupVars, flag, d)
      | (Gss, Gl, Dot (Exp (EVar (ref (SOME (U)), _, _, _) as X), s), K,
         DupVars, flag, d) ->
          let U' = Whnf.normalize (U, I.id) in
          let (K', DupVars') =
            collectExp (Gss, Gl, (U', I.id), K, DupVars, flag, d) in
          collectSub (Gss, Gl, s, K', DupVars', flag, d)
      | (Gss, Gl, Dot (Exp (AVar (ref (SOME (U'))) as U), s), K, DupVars,
         flag, d) ->
          let (K', DupVars') =
            collectExp (Gss, Gl, (U', I.id), K, DupVars, flag, d) in
          collectSub (Gss, Gl, s, K', DupVars', flag, d)
      | (Gss, Gl, Dot (Exp (EClo (U', s')), s), K, DupVars, flag, d) ->
          let U = Whnf.normalize (U', s') in
          let (K', DupVars') =
            collectExp (Gss, Gl, (U, I.id), K, DupVars, flag, d) in
          collectSub (Gss, Gl, s, K', DupVars', flag, d)
      | (Gss, Gl, Dot (Exp (U), s), K, DupVars, flag, d) ->
          let (K', DupVars') =
            collectExp (Gss, Gl, (U, I.id), K, DupVars, flag, d) in
          collectSub (Gss, Gl, s, K', DupVars', flag, d)
      | (Gss, Gl, Dot (I.Undef, s), K, DupVars, flag, d) ->
          collectSub (Gss, Gl, s, K, DupVars, flag, d)
    let rec collectCtx =
      function
      | (Gss, DProg (I.Null, I.Null), (K, DupVars), d) -> (K, DupVars)
      | (Gss, DProg (Decl (g, D), Decl (dPool, C.Parameter)), (K, DupVars),
         d) ->
          let (K', DupVars') =
            collectCtx (Gss, (C.DProg (g, dPool)), (K, DupVars), (d - 1)) in
          collectDec (Gss, (D, I.id), (K', DupVars'), (d - 1), false__)
      | (Gss, DProg (Decl (g, D), Decl (dPool, Dec (r, s, Ha))),
         (K, DupVars), d) ->
          let (K', DupVars') =
            collectCtx (Gss, (C.DProg (g, dPool)), (K, DupVars), (d - 1)) in
          collectDec (Gss, (D, I.id), (K', DupVars'), (d - 1), false__)
    let rec abstractExpW =
      function
      | (flag, Gs, posEA, Vars, Gl, total, depth, ((Uni (L) as U), s), eqn)
          -> (posEA, Vars, U, eqn)
      | (flag, Gs, posEA, Vars, Gl, total, depth, (Pi ((D, P), V), s), eqn)
          ->
          let (posEA', Vars', D, _) =
            abstractDec (Gs, posEA, Vars, Gl, total, depth, (D, s), NONE) in
          let (posEA'', Vars'', V', eqn2) =
            abstractExp
              (flag, Gs, posEA', Vars', Gl, total, (depth + 1),
                (V, (I.dot1 s)), eqn) in
          (posEA'', Vars'', (piDepend ((D, P), V')), eqn2)
      | (flag, Gs, posEA, Vars, Gl, total, depth, (Root (H, S), s), eqn) ->
          let (posEA', Vars', S, eqn') =
            abstractSpine
              (flag, Gs, posEA, Vars, Gl, total, depth, (S, s), eqn) in
          (posEA', Vars', (I.Root (H, S)), eqn')
      | (flag, Gs, posEA, Vars, Gl, total, depth, (Lam (D, U), s), eqn) ->
          let (posEA', Vars', D', _) =
            abstractDec (Gs, posEA, Vars, Gl, total, depth, (D, s), NONE) in
          let (posEA'', Vars'', U', eqn2) =
            abstractExp
              (flag, Gs, posEA', Vars', (I.Decl (Gl, D')), total,
                (depth + 1), (U, (I.dot1 s)), eqn) in
          (posEA'', Vars'', (I.Lam (D', U')), eqn2)
      | (flag, ((Gss, ss) as Gs), ((epos, apos) as posEA), Vars, Gl, total,
         depth, ((EVar (_, GX, VX, _) as X), s), eqn) ->
          if isId (I.comp (ss, s))
          then
            abstractEVarFap
              (flag, Gs, posEA, Vars, Gl, total, depth, (X, s), eqn)
          else
            abstractEVarNFap
              (flag, Gs, posEA, Vars, Gl, total, depth, (X, s), eqn)
    let rec abstractExp (flag, Gs, posEA, Vars, Gl, total, depth, Us, eqn) =
      abstractExpW
        (flag, Gs, posEA, Vars, Gl, total, depth, (Whnf.whnf Us), eqn)
    let rec abstractEVarFap
      (flag, Gs, ((epos, apos) as posEA), Vars, Gl, total, depth, (X, s),
       eqn)
      =
      match member (eqEVar X) Vars with
      | SOME (label, i) ->
          if flag
          then
            (match label with
             | Body ->
                 let BV = I.BVar (apos + depth) in
                 let BV' = I.BVar (i + depth) in
                 let BV1 = I.BVar (apos + depth) in
                 let (posEA', Vars', S, eqn1) =
                   abstractSub
                     (flag, Gs, (epos, (apos - 1)), Vars, Gl, total, depth,
                       s, I.Nil, eqn) in
                 (posEA', Vars', (I.Root (BV, I.Nil)),
                   (TableParam.Unify
                      (Gl, (I.Root (BV', S)), (I.Root (BV1, I.Nil)), eqn1)))
             | TypeLabel ->
                 let Vars' = update (eqEVar X) Vars in
                 let (posEA', Vars'', S, eqn1) =
                   abstractSub
                     (flag, Gs, (epos, apos), Vars', Gl, total, depth, s,
                       I.Nil, eqn) in
                 (posEA', Vars'', (I.Root ((I.BVar (i + depth)), S)), eqn1))
          else
            (let (posEA', Vars', S, eqn1) =
               abstractSub
                 (flag, Gs, (epos, apos), Vars, Gl, total, depth, s, I.Nil,
                   eqn) in
             (posEA', Vars', (I.Root ((I.BVar (i + depth)), S)), eqn1))
      | NONE ->
          let label = if flag then Body else TypeLabel in
          let BV = I.BVar (epos + depth) in
          let pos = ((epos - 1), apos) in
          let (posEA', Vars', S, eqn1) =
            abstractSub
              (flag, Gs, pos, (I.Decl (Vars, ((label, epos), (EV X)))), Gl,
                total, depth, s, I.Nil, eqn) in
          (posEA', Vars', (I.Root (BV, S)), eqn1)
    let rec abstractEVarNFap
      (flag, Gs, ((epos, apos) as posEA), Vars, Gl, total, depth, (X, s),
       eqn)
      =
      match member (eqEVar X) Vars with
      | SOME (label, i) ->
          if flag
          then
            let BV = I.BVar (apos + depth) in
            let BV' = I.BVar (i + depth) in
            let BV1 = I.BVar (apos + depth) in
            let (posEA', Vars', S, eqn1) =
              abstractSub
                (flag, Gs, (epos, (apos - 1)), Vars, Gl, total, depth, s,
                  I.Nil, eqn) in
            (posEA', Vars', (I.Root (BV, I.Nil)),
              (TableParam.Unify
                 (Gl, (I.Root (BV', S)), (I.Root (BV1, I.Nil)), eqn1)))
          else
            (let (posEA', Vars', S, eqn1) =
               abstractSub
                 (flag, Gs, (epos, apos), Vars, Gl, total, depth, s, I.Nil,
                   eqn) in
             (posEA', Vars', (I.Root ((I.BVar (i + depth)), S)), eqn1))
      | NONE ->
          if flag
          then
            let label = if flag then Body else TypeLabel in
            let BV = I.BVar (apos + depth) in
            let BV' = I.BVar (epos + depth) in
            let BV1 = I.BVar (apos + depth) in
            let (posEA', Vars', S, eqn1) =
              abstractSub
                (flag, Gs, ((epos - 1), (apos - 1)),
                  (I.Decl (Vars, ((label, epos), (EV X)))), Gl, total, depth,
                  s, I.Nil, eqn) in
            (posEA', Vars', (I.Root (BV, I.Nil)),
              (TableParam.Unify
                 (Gl, (I.Root (BV', S)), (I.Root (BV1, I.Nil)), eqn1)))
          else
            (let (posEA', Vars', S, eqn1) =
               abstractSub
                 (flag, Gs, ((epos - 1), apos),
                   (I.Decl (Vars, ((TypeLabel, epos), (EV X)))), Gl, total,
                   depth, s, I.Nil, eqn) in
             (posEA', Vars', (I.Root ((I.BVar (epos + depth)), S)), eqn1))
    let rec abstractSub =
      function
      | (flag, Gs, posEA, Vars, Gl, total, depth, Shift k, S, eqn) ->
          if k < depth
          then
            abstractSub
              (flag, Gs, posEA, Vars, Gl, total, depth,
                (I.Dot ((I.Idx (k + 1)), (I.Shift (k + 1)))), S, eqn)
          else (posEA, Vars, S, eqn)
      | (flag, Gs, posEA, Vars, Gl, total, depth, Dot (Idx k, s), S, eqn) ->
          abstractSub
            (flag, Gs, posEA, Vars, Gl, total, depth, s,
              (I.App ((I.Root ((I.BVar k), I.Nil)), S)), eqn)
      | (flag, Gs, posEA, Vars, Gl, total, depth, Dot (Exp (U), s), S, eqn)
          ->
          let (posEA', Vars', U', eqn') =
            abstractExp
              (flag, Gs, posEA, Vars, Gl, total, depth, (U, I.id), eqn) in
          abstractSub
            (flag, Gs, posEA', Vars', Gl, total, depth, s, (I.App (U', S)),
              eqn')
    let rec abstractSpine =
      function
      | (flag, Gs, posEA, Vars, Gl, total, depth, (I.Nil, _), eqn) ->
          (posEA, Vars, I.Nil, eqn)
      | (flag, Gs, posEA, Vars, Gl, total, depth, (SClo (S, s'), s), eqn) ->
          abstractSpine
            (flag, Gs, posEA, Vars, Gl, total, depth, (S, (I.comp (s', s))),
              eqn)
      | (flag, Gs, posEA, Vars, Gl, total, depth, (App (U, S), s), eqn) ->
          let (posEA', Vars', U', eqn') =
            abstractExp
              (flag, Gs, posEA, Vars, Gl, total, depth, (U, s), eqn) in
          let (posEA'', Vars'', S', eqn'') =
            abstractSpine
              (flag, Gs, posEA', Vars', Gl, total, depth, (S, s), eqn') in
          (posEA'', Vars'', (I.App (U', S')), eqn'')
    let rec abstractSub' =
      function
      | (flag, Gs, epos, Vars, total, Shift k) ->
          if k < 0
          then raise (Error "Substitution out of range\n")
          else (epos, Vars, (I.Shift (k + total)))
      | (flag, Gs, epos, Vars, total, Dot (Idx k, s)) ->
          let (epos', Vars', s') =
            abstractSub' (flag, Gs, epos, Vars, total, s) in
          (epos', Vars', (I.Dot ((I.Idx k), s')))
      | (flag, Gs, epos, Vars, total, Dot (Exp (U), s)) ->
          let ((ep, _), Vars', U', _) =
            abstractExp
              (false__, Gs, (epos, 0), Vars, I.Null, total, 0, (U, I.id),
                TableParam.Trivial) in
          let (epos'', Vars'', s') =
            abstractSub' (flag, Gs, ep, Vars', total, s) in
          (epos'', Vars'', (I.Dot ((I.Exp U'), s')))
    let rec abstractDec =
      function
      | (Gs, posEA, Vars, Gl, total, depth, (Dec (x, V), s), NONE) ->
          let (posEA', Vars', V', eqn) =
            abstractExp
              (false__, Gs, posEA, Vars, Gl, total, depth, (V, s),
                TableParam.Trivial) in
          (posEA', Vars', (I.Dec (x, V')), eqn)
      | (Gs, posEA, Vars, Gl, total, depth, (Dec (x, V), s), SOME eqn) ->
          let (posEA', Vars', V', eqn') =
            abstractExp
              (true__, Gs, posEA, Vars, Gl, total, depth, (V, s), eqn) in
          (posEA', Vars', (I.Dec (x, V')), eqn')
    let rec abstractCtx' =
      function
      | (Gs, epos, Vars, total, depth, DProg (I.Null, I.Null), g', eqn) ->
          (epos, Vars, g', eqn)
      | (Gs, epos, Vars, total, depth, DProg
         (Decl (g, D), Decl (dPool, C.Parameter)), g', eqn) ->
          let d = IntSyn.ctxLength g in
          let ((epos', _), Vars', D', _) =
            abstractDec
              (Gs, (epos, total), Vars, I.Null, total, (depth - 1),
                (D, I.id), NONE) in
          abstractCtx'
            (Gs, epos', Vars', total, (depth - 1), (C.DProg (g, dPool)),
              (I.Decl (g', D')), eqn)
      | (Gs, epos, Vars, total, depth, DProg (Decl (g, D), Decl (dPool, _)),
         g', eqn) ->
          let d = IntSyn.ctxLength g in
          let ((epos', _), Vars', D', _) =
            abstractDec
              (Gs, (epos, total), Vars, I.Null, total, (depth - 1),
                (D, I.id), NONE) in
          abstractCtx'
            (Gs, epos', Vars', total, (depth - 1), (C.DProg (g, dPool)),
              (I.Decl (g', D')), eqn)
    let rec abstractCtx (Gs, epos, Vars, total, depth, dProg) =
      abstractCtx'
        (Gs, epos, Vars, total, depth, dProg, I.Null, TableParam.Trivial)
    let rec makeEVarCtx =
      function
      | (Gs, Vars, DEVars, I.Null, total) -> DEVars
      | (Gs, Vars, DEVars, Decl (K', (_, EV (EVar (_, GX, VX, _) as E))),
         total) ->
          let V' = raiseType (GX, VX) in
          let (_, Vars', V'', _) =
            abstractExp
              (false__, Gs, (0, 0), Vars, I.Null, 0, (total - 1), (V', I.id),
                TableParam.Trivial) in
          let DEVars' = makeEVarCtx (Gs, Vars', DEVars, K', (total - 1)) in
          let DEVars'' = I.Decl (DEVars', (I.Dec (NONE, V''))) in DEVars''
    let rec makeAVarCtx (Vars, DupVars) =
      let avarCtx =
        function
        | (Vars, I.Null, k) -> I.Null
        | (Vars, Decl (K', AV ((EVar (ref (NONE), GX, VX, _) as E), d)), k)
            ->
            I.Decl
              ((avarCtx (Vars, K', (k + 1))),
                (I.ADec
                   ((SOME
                       ((^) (((^) "AVar " Int.toString k) ^ "--")
                          Int.toString d)), d)))
        | (Vars, Decl (K', AV ((EVar (_, GX, VX, _) as E), d)), k) ->
            I.Decl
              ((avarCtx (Vars, K', (k + 1))),
                (I.ADec
                   ((SOME
                       ((^) (((^) "AVar " Int.toString k) ^ "--")
                          Int.toString d)), d))) in
      avarCtx (Vars, DupVars, 0)
    let rec lowerEVar' =
      function
      | (X, g, (Pi ((D', _), V'), s')) ->
          let D'' = I.decSub (D', s') in
          let (X', U) =
            lowerEVar' (X, (I.Decl (g, D'')), (Whnf.whnf (V', (I.dot1 s')))) in
          (X', (I.Lam (D'', U)))
      | (X, g, Vs') -> let X' = X in (X', X')
    let rec lowerEVar1 =
      function
      | (X, EVar (r, g, _, _), ((Pi _ as V), s)) ->
          let (X', U) = lowerEVar' (X, g, (V, s)) in
          I.EVar ((ref (SOME U)), I.Null, V, (ref nil))
      | (_, X, _) -> X
    let rec lowerEVar =
      function
      | (E, (EVar (r, g, V, ref nil) as X)) ->
          lowerEVar1 (E, X, (Whnf.whnf (V, I.id)))
      | (E, EVar _) ->
          raise
            (Error
               "abstraction : LowerEVars: Typing ambiguous -- constraint of functional type cannot be simplified")
    let rec evarsToSub =
      function
      | (I.Null, s) -> s
      | (Decl (K', (_, EV (EVar ((ref (NONE) as I), GX, VX, cnstr) as E))),
         s) ->
          let V' = raiseType (GX, VX) in
          let X =
            lowerEVar1
              (E, (I.EVar (I, I.Null, V', cnstr)), (Whnf.whnf (V', I.id))) in
          let s' = evarsToSub (K', s) in I.Dot ((I.Exp X), s')
    let rec avarsToSub =
      function
      | (I.Null, s) -> s
      | (Decl (Vars', AV ((EVar (I, GX, VX, cnstr) as E), d)), s) ->
          let s' = avarsToSub (Vars', s) in
          let AVar r as X' = I.newAVar () in
          I.Dot ((I.Exp (I.EClo (X', (I.Shift (~ d))))), s')
    let rec abstractEVarCtx ((DProg (g, dPool) as dp), p, s) =
      let (Gs, ss, d) =
        if !TableParam.strengthen
        then
          let w' = Subordinate.weaken (g, (I.targetFam p)) in
          let iw = Whnf.invert w' in
          let g' = Whnf.strengthen (iw, g) in
          let d' = I.ctxLength g' in (g', iw, d')
        else (g, I.id, (I.ctxLength g)) in
      let (K, DupVars) = collectCtx ((Gs, ss), dp, (I.Null, I.Null), d) in
      let (K', DupVars') =
        collectExp ((Gs, ss), I.Null, (p, s), K, DupVars, true__, d) in
      let epos = I.ctxLength K' in
      let apos = I.ctxLength DupVars' in
      let total = epos + apos in
      let (epos', Vars', g', eqn) =
        abstractCtx ((Gs, ss), epos, I.Null, total, d, dp) in
      let (posEA'', Vars'', U', eqn') =
        abstractExp
          (true__, (Gs, ss), (epos', total), Vars', I.Null, total, d, 
            (p, s), eqn) in
      let DAVars = makeAVarCtx (Vars'', DupVars') in
      let DEVars = makeEVarCtx ((Gs, ss), Vars'', I.Null, Vars'', 0) in
      let s' = avarsToSub (DupVars', I.id) in
      let s'' = evarsToSub (Vars'', s') in
      let g'' = reverseCtx (g', I.Null) in
      if !TableParam.strengthen
      then
        let w' = Subordinate.weaken (g'', (I.targetFam U')) in
        let iw = Whnf.invert w' in
        let Gs' = Whnf.strengthen (iw, g'') in
        (Gs', DAVars, DEVars, U', eqn', s'')
      else (g'', DAVars, DEVars, U', eqn', s'')
    let ((abstractEVarCtx)(*
       We write {{K}} for the context of K, where EVars have
       been translated to declarations and their occurrences to BVars.
       For each occurrence of EVar in U, we generate a distinct BVar together with
       a residual constraint. This enforces that the final abstraction of U is
       linear. However, we do not linearize the context G.

       We write {{U}}_K, {{S}}_K for the corresponding translation of an
       expression or spine.

       Just like contexts g, any K is implicitly assumed to be
       well-formed and in dependency order.

       We write  K ||- U  if all EVars in U are collected in K.
       In particular, . ||- U means U contains no EVars.  Similarly,
       for spines K ||- S and other syntactic categories.

       Collection and abstraction raise Error if there are unresolved
       constraints after simplification.
    *)
      (* eqEVar X Y = B
     where B iff X and Y represent same variable
     *)
      (* Sun Dec  1 14:04:17 2002 -bp  may raise exception
       if strengthening is applied,i.e. the substitution is not always id! *)
      (* a few helper functions to manage K *)(* member P K = B option *)
      (* member P K = B option *)(* member P K = B option *)
      (* occursInExp (k, U) = DP,

       Invariant:
       If    U in nf
       then  DP = No      iff k does not occur in U
             DP = Maybe   iff k occurs in U some place not as an argument to a Skonst
             DP = Meta    iff k occurs in U and only as arguments to Skonsts
    *)
      (* no case for Redex, EVar, EClo *)(* no case for FVar *)
      (* no case for SClo *)(* piDepend ((D,P), V) = Pi ((D,P'), V)
       where P' = Maybe if D occurs in V, P' = No otherwise
    *)
      (* optimize to have fewer traversals? -cs *)(* pre-Twelf 1.2 code walk Fri May  8 11:17:10 1998 *)
      (* raiseType (g, V) = {{g}} V

       Invariant:
       If g |- V : L
       then  . |- {{g}} V : L

       All abstractions are potentially dependent.
    *)
      (* collectExpW ((Gs, ss), Gl, (U, s), K, DupVars, flag) = (K', DupVars')

       Invariant:
       If    g, Gl |- s : G1     G1 |- U : V      (U,s) in whnf
                Gs |- ss : g  (Gs is the strengthened context and ss is the strengthening substitution)

       No circularities in U
             (enforced by extended occurs-check for FVars in Unify)
       and   K' = K, K''
             where K' contains all EVars in (U,s)
       and  DupVars' = DupVars, DupVars''
            where DupVars' contains all duplicates in (U,s)

      if flag = true
        then duplicates of EVars are collected in DupVars
        otherwise no duplicates are collected

      note : 1) we only need to collect duplicate occurrences of EVars
                if we need to linearize the term the EVars occur in.

             2) we do not linearize fgnExp
    *)
      (* Possible optimization: Calculate also the normal form of the term *)
      (* should we apply I.dot1(ss) ? Tue Oct 15 21:55:16 2002 -bp *)
      (* No other cases can occur due to whnf invariant *)
      (* collectExp (Gss, g, Gl, (U, s), K) = K'
       same as collectExpW  but  (U,s) need not to be in whnf
    *)
      (* collectSpine (Gss, Gl, (S, s), K, DupVars, flag) = (K', DupVars')

       Invariant:
       If    g, Gl |- s : G1     G1 |- S : V > P
                Gs |- ss : g
       then  K' = K, K'' and DupVars' = DupVars, DupVars''
       where K'' contains all EVars in (S, s)
       and DupVars'' contains all duplicates in (S, s)
     *)
      (* we have seen X before *)(* case label of
                     Body => collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(X,d)), flag, d)
                   | TypeLabel =>
                       let
                         val K' = update' (eqEVar X) K
                       in
                         collectSub(Gss, Gl, s, K', DupVars, flag, d)
                       end *)
      (* since X has occurred before, we do not traverse its type V' *)
      (*          val V' = raiseType (GX, V)  inefficient! *)(* we have seen X before, i.e. it was already strengthened *)
      (* -bp this is a possible optimization for the variant case
                   case label of
                   Body => (print "Collect DupVar\n"; collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(X, d)), flag, d) )
                 | TypeLabel =>
                    let
                      val _ = print "TypeLabel\n"
                      val K' = update' (eqEVar X) K
                    in
                      collectSub(Gss, Gl, s, K', DupVars, flag, d)
                    end*)
      (* val V' = raiseType (GX, V)  inefficient! *)
      (* ? *)(* equalCtx (Gs, I.id, GX', s) *)(* fully applied *)
      (* not fully applied *)(* X is fully applied pattern *)
      (* we have seen X before *)(*
                 case label of
                   Body => collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(X, d)), flag, d)
                 | TypeLabel =>
                     let
                       val K' = update' (eqEVar X) K
                     in
                       collectSub(Gss, Gl, s, K', DupVars, flag, d)
                     end *)
      (* since X has occurred before, we do not traverse its type V' *)
      (* val _ = checkEmpty !cnstrs *)(* inefficient! *)
      (* case label of
                   Body => collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(X, d)), flag, d)
                   | TypeLabel =>
                     let
                       val K' = update' (eqEVar X) K
                     in
                       collectSub(Gss, Gl, s, K', DupVars, flag, d)
                     end             *)
      (* inefficient! *)(* equalCtx (compose'(Gl, g), s, GX, s)  *)
      (* X is fully applied *)(* X is not fully applied *)
      (* collectDec (Gss, g, (x:V, s), K, DupVars, flag) = (K', DupVars')

       Invariant:
       If    g |- s : G1     G1 |- V : L
            Gs |- ss : g
       then  K' = K, K'' and DupVars' = DupVars, DupVars''
       where K'' contains all EVars in (V, s)
       and DupVars'' contains all duplicates in (S, s)
    *)
      (*      val (K',DupVars') =  collectExp (Gss, I.Null, (V, s), K, I.Null, false, d)*)
      (* collectSub (g, s, K, DupVars, flag) = (K', DupVars)

       Invariant:
       If    g |- s : G1

       then  K' = K, K'' and DupVars' = DupVars, DupVars''
       where K'' contains all EVars in s
       and DupVars'' contains all duplicates in s
    *)
      (* inefficient? *)(* inefficient? *)
      (* collectCtx (Gss, G0, g, K) = (K', DupVars)
       Invariant:
       If G0 |- g ctx,
       then G0' = G0,g
       and K' = K, K'' where K'' contains all EVars in g
    *)
      (* abstractExpW (epos, apos, Vars, Gl, total, depth, (U, s), eqn) = (epos', apos', Vars', U', eqn')
      (abstraction and linearization of existential variables in (U,s))

       U' = {{U[s]}}_(K, Dup)

       Invariant:
       If     g, Gl |- U[s] : V and  U[s] is in whnf
       and   |Gl| = depth
             |Dup, K| = total

       and epos = (total(K) + l) - #replaced expressions in U    (generate no additional constraints)
       and apos = (total(Dup) + + total(K) + l) - #replaced expressions in U
                  (generate additional constraints (avars))

       and Vars'  = Vars, Vars''
           where Vars contains pairs ((label, i), EV X) of all EVars (EV X),
           where label refers to where we have seen the existential variable (typeLabel or body) and
           i corresponds to the bvar-index assigned to X in U[s]

       and   K ~ Vars (we can obtain K from Vars by dropping the first component of
             each pair (_, EV X) in Vars' )

       then   {{Dup}}, {{K}}  ||- U
       and {{Dup}} {{K}} , g, Gl |-  U' : V'
       and eqn' = eqn, eqn'' where eqn'' are residual equations relating between elements
           in {{K}} and {{Dup}}

       and . ||- Pi G. U'  and   U' is in nf

       if flag then linearize U else allow duplicates.

    *)
      (* X is possibly strengthened ! *)(* X is fully applied *)
      (* s =/= id, i.e. X is not fully applied *)(*      | abstractExpW (posEA, Vars, Gl, total, depth, (X as I.FgnExp (cs, ops), s), eqn) =  *)
      (*      let
          val (X, _) = #map(ops) (fn U => abstractExp (posEA, Vars, Gl, total, depth, (U, s), eqn))
        in        abstractFgn (posEA, Vars, Gl, total, depth, X, eqn)
        end
*)
      (* abstractExp (posEA, Vars, Gl, total, depth, (U, s)) = U'

       same as abstractExpW, but (U,s) need not to be in whnf
    *)
      (* we have seen X before *)(* enforce linearization *)
      (* do not enforce linearization -- used for type labels *)
      (* we see X for the first time *)(* we have seen X before *)
      (* enforce linearization *)(* (case label of
               Body =>
                 let
                  val _ = print "abstractEVarNFap -- flag true; we have seen X before\n"
                   val BV = I.BVar(apos + depth)
                   val BV' = I.BVar(i + depth)
                   val BV1 = I.BVar(apos + depth)
                   val (posEA', Vars', S, eqn1) = abstractSub (flag, Gs, (epos, apos - 1), Vars, Gl, total, depth, s, I.Nil, eqn)
                 in
                   (posEA', Vars', I.Root(BV, I.Nil), TableParam.Unify(Gl, I.Root(BV', S), I.Root(BV1, I.Nil ), eqn1))
                 end
              | TyeLabel =>
                 let
                   val Vars' = update (eqEVar X) Vars
                   val (posEA', Vars'', S, eqn1) = abstractSub (flag, Gs, (epos, apos), Vars', Gl, total, depth, s, I.Nil, eqn)
                 in
                   (posEA', Vars'', I.Root(I.BVar(i + depth), S), eqn1)
                 end) *)
      (* do not enforce linearization -- used for type labels *)
      (* we have not seen X before *)(* enforce linearization since X is not fully applied *)
      (* do not enforce linearization -- used for type labels *)
      (* abstractSub (flag, Gs, posEA, Vars, Gl, total, depth, s, S, eqn) = (posEA', Vars', S', eqn')

       (implicit raising)
       (for posEA, Vars, eqn explanation see above)

       let K* = K, Dup

       S' = {{s}}_K* @@ S

       Invariant:
       If    g, Gl |- s : G1
       and  |Gl| = depth

       and   {{Dup}} {{K}} ||- s
       then {{Dup}} {{K}}, g, Gl |- S' : {G1}.W > W   (for some W)
       and  . ||- S'
    *)
      (* k = depth *)(* abstractSpine (flag, Gs, posEA, Vars, Gl, total, depth, (S, s), eqn) = (posEA', Vars', S', eqn')
       where S' = {{S[s]}}_K*   and K* = K, Dup

       Invariant:
       If   Gl, g |- s : G1     G1 |- S : V > P
       and  K* ||- S
       and  |g| = depth

       then {{K*}}, g, g |- S' : V' > P'
       and  . ||- S'
    *)
      (* abstractSub' (flag, Gs, epos, K, Gl, total, s) = (epos', K', s')      (implicit raising)

        Invariant:
        If   g |- s : G1
       and  |g| = depth
       and  K ||- s
       and {{K}}, g |- {{s}}_K : G1
       then Gs, g |- s' : G1    where  s' == {{s}}_K

         *)
      (* abstractDec (Gs, posEA, Vars, Gl, total, depth, (x:V, s)) = (posEA', Vars', x:V')
       where V = {{V[s]}}_K*

       Invariant:
       If   g |- s : G1     G1 |- V : L
       and  K* ||- V
       and  |g| = depth

       then {{K*}}, g |- V' : L
       and  . ||- V'
    *)
      (*      val (posEA', Vars', V', _) = abstractExp (false, Gs, posEA, Vars, Gl, total, depth, (V, s), TableParam.Trivial)*)
      (*      val (posEA', Vars', V', _) = abstractExp (false, Gs, posEA, Vars, Gl, total, depth, (V, s), TableParam.Trivial)*)
      (* abstractCtx (Gs, epos, K, total, depth, C.DProg(g,dPool)) = (epos', K', g')
       where g' = {{g}}_K

       Invariants:
       If K ||- g
       and |g| = depth
       then {{K}} |- g' ctx
       and . ||- g'
       and epos = current epos

       note: we will linearize all dynamic assumptions in G.
    *)
      (*        let
          val d = IntSyn.ctxLength (g)
          val ((epos', _), Vars', D', eqn') = abstractDec (Gs, (epos, total), Vars, I.Null, total , depth - 1, (D, I.id), SOME(eqn))
        in
          abstractCtx' (Gs, epos', Vars', total, depth - 1, C.DProg(g, dPool), I.Decl (g', D'), eqn')
        end
*)
      (* makeEVarCtx (Gs, Kall, D, K, eqn) = g'  *)(* add case for foreign expressions ? *)
      (* lowerEVar' (g, V[s]) = (X', U), see lowerEVar *)
      (* lowerEVar1 (X, V[s]), V[s] in whnf, see lowerEVar *)(* lowerEVar1 (X, I.EVar (r, g, _, _), (V as I.Pi _, s)) = *)
      (* lowerEVar (X) = X'

       Invariant:
       If   g |- X : {{g'}} P
            X not subject to any constraints
       then g, g' |- X' : P

       Effect: X is instantiated to [[g']] X' if g' is empty
               otherwise X = X' and no effect occurs.
    *)
      (* It is not clear if this case can happen *)(* pre-Twelf 1.2 code walk, Fri May  8 11:05:08 1998 *)
      (* evarsToSub (K, s') = s
      Invariant:
      if K = EV Xn ... EV X2, EV X1
        then
        s = X1 . X2 . ... s'
     *)
      (* redundant ? *)(* evarsToSub (K, s') = s
      Invariant:
      if K = AV Xn ... AV X2, EV X1
        then
        s = X1 . X2 . ... s'
     *)
      (* abstractEVarCtx (g, p, s) = (g', D', U', s')

     if g |- p[s] and s contains free variables X_n .... X_1
     then
       D' |- Pi  g' . U'
       where D' is the abstraction over the free vars X_n .... X_1

       and s' is a substitution the free variables
            X_n .... X_1, s.t.

       . |- s' : D'

       . |- (Pi g' .U' )[s']  is equivalent to . |- Pi g . p[s]

       Note: g' and U' are possibly strengthened
   *)
      (* K ||- g i.e. K contains all EVars in g *)(* DupVars' , K' ||- p[s]  i.e. K' contains all EVars in (p,s) and g and
                                         DupVars' contains all duplicate EVars p[s] *)
      (* {{g}}_Vars' , i.e. abstract over the existential variables in g*)
      (* = 0 *)(* abstract over existential variables in p[s] and linearize the expression *)
      (* depth *)(* note: depth will become negative during makeEVarCtx *))
      = abstractEVarCtx
    let ((abstractAnswSub)(* abstractAnswSub s = (D', s')

   if  |- s : Delta' and s may contain free variables and
     D |- Pi G. U  and  |- s : D and  |- (Pi g . U)[s]
    then

    D' |- s' : D   where D' contains all the
    free variables from s
   *))
      =
      function
      | s ->
          let (((K)(* no linearization for answer substitution *)),
               _)
            =
            collectSub
              ((I.Null, I.id), I.Null, s, I.Null, I.Null, false__, 0) in
          let epos = I.ctxLength K in
          let (_, ((Vars)(*0 *)), s') =
            abstractSub'
              (false__, (I.Null, I.id), epos, I.Null, epos, ((s)
                (* total *))) in
          let DEVars = makeEVarCtx ((I.Null, I.id), Vars, I.Null, Vars, 0) in
          let s1' = ctxToEVarSub (DEVars, I.id) in (DEVars, s')
    let raiseType = function | (g, U) -> raiseType (g, U)
  end ;;
