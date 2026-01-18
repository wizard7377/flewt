
(* Abstraction *)
(* Author: Brigitte Pientka *)
module type ABSTRACTTABLED  =
  sig
    (*! structure IntSyn : INTSYN !*)
    (*! structure TableParam : TABLEPARAM !*)
    exception Error of string 
    val abstractEVarCtx :
      (CompSyn.__DProg * IntSyn.__Exp * IntSyn.__Sub) ->
        (IntSyn.dctx * IntSyn.dctx * IntSyn.dctx * IntSyn.__Exp *
          TableParam.__ResEqn * IntSyn.__Sub)
    val abstractAnswSub : IntSyn.__Sub -> (IntSyn.dctx * IntSyn.__Sub)
    val raiseType : (IntSyn.dctx * IntSyn.__Exp) -> IntSyn.__Exp
  end;;




(* Abstraction *)
(* Author: Frank Pfenning, Carsten Schuermann *)
(* Modified: Roberto Virga, Brigitte Pientka *)
module AbstractTabled(AbstractTabled:sig
                                       (*! structure IntSyn' : INTSYN !*)
                                       module Whnf : WHNF
                                       module Unify : UNIFY
                                       module Constraints : CONSTRAINTS
                                       module Subordinate : SUBORDINATE
                                       module Print : PRINT
                                       (*! sharing Whnf.IntSyn = IntSyn' !*)
                                       (*! sharing Unify.IntSyn = IntSyn' !*)
                                       (*! sharing Constraints.IntSyn = IntSyn' !*)
                                       (*! sharing Subordinate.IntSyn = IntSyn' !*)
                                       (*! sharing Print.IntSyn = IntSyn' !*)
                                       module Conv : CONV
                                     end) : ABSTRACTTABLED =
  struct
    (*! sharing Conv.IntSyn = IntSyn' !*)
    (*! structure TableParam : TABLEPARAM !*)
    (*! sharing TableParam.IntSyn = IntSyn' !*)
    (*! structure IntSyn = IntSyn' !*)
    (*! structure TableParam = TableParam !*)
    exception Error of string 
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
      | (IntSyn.Null, __g) -> __g
      | (Decl (__g', __d), __g) -> IntSyn.Decl ((compose' (__g', __g)), __d)
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
      | (Decl (__g, __d), s, Decl (__g', __d'), s') ->
          (Conv.convDec ((__d, s), (__d', s'))) &&
            (equalCtx (__g, (I.dot1 s), __g', (I.dot1 s')))
      | (Decl (__g, __d), s, I.Null, s') -> false__
      | (I.Null, s, Decl (__g', __d'), s') -> false__
    let rec eqEVarW arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (EVar (r1, _, _, _), EV (EVar (r2, _, _, _))) -> r1 = r2
      | (_, _) -> false__
    let rec eqEVar (X1) (EV (X2)) =
      let (X1', s) = Whnf.whnf (X1, I.id) in
      let (X2', s) = Whnf.whnf (X2, I.id) in eqEVarW X1' (EV X2')
    let rec member' (P) (K) =
      let rec exists' =
        function
        | I.Null -> None
        | Decl (K', (l, EV (y))) -> if P (EV y) then Some l else exists' K' in
      exists' K
    let rec member (P) (K) =
      let rec exists' =
        function
        | I.Null -> None
        | Decl (K', (i, y)) -> if P y then Some i else exists' K' in
      exists' K
    let rec update' (P) (K) =
      let rec update' =
        function
        | I.Null -> I.Null
        | Decl (K', (label, y)) ->
            if P y
            then I.Decl (K', (Body, y))
            else I.Decl ((update' K'), (label, y)) in
      update' K
    let rec update (P) (K) =
      let rec update' =
        function
        | I.Null -> I.Null
        | Decl (K', ((label, i), y)) ->
            if P y
            then I.Decl (K', ((Body, i), y))
            else I.Decl ((update' K'), ((label, i), y)) in
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
      | (k, Pi (DP, __v)) ->
          or__ ((occursInDecP (k, DP)), (occursInExp ((k + 1), __v)))
      | (k, Root (H, S)) -> occursInHead (k, H, (occursInSpine (k, S)))
      | (k, Lam (__d, __v)) ->
          or__ ((occursInDec (k, __d)), (occursInExp ((k + 1), __v)))
      | (k, FgnExp csfe) ->
          I.FgnExpStd.fold csfe
            (function
             | (__u, DP) ->
                 or__ (DP, (occursInExp (k, (Whnf.normalize (__u, I.id))))))
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
      | (k, App (__u, S)) ->
          or__ ((occursInExp (k, __u)), (occursInSpine (k, S)))
    let rec occursInDec (k, Dec (_, __v)) = occursInExp (k, __v)
    let rec occursInDecP (k, (__d, _)) = occursInDec (k, __d)
    let rec piDepend =
      function
      | ((__d, I.No), __v) as DPV -> I.Pi DPV
      | ((__d, I.Meta), __v) as DPV -> I.Pi DPV
      | ((__d, I.Maybe), __v) -> I.Pi ((__d, (occursInExp (1, __v))), __v)
    let rec raiseType =
      function
      | (I.Null, __v) -> __v
      | (Decl (__g, __d), __v) -> raiseType (__g, (I.Pi ((__d, I.Maybe), __v)))
    let rec reverseCtx =
      function
      | (I.Null, __g) -> __g
      | (Decl (__g, __d), __g') -> reverseCtx (__g, (I.Decl (__g', __d)))
    let rec ctxToEVarSub =
      function
      | (IntSyn.Null, s) -> s
      | (Decl (__g, Dec (_, A)), s) ->
          let s' = ctxToEVarSub (__g, s) in
          let x = IntSyn.newEVar (IntSyn.Null, (I.EClo (A, s'))) in
          IntSyn.Dot ((IntSyn.Exp x), s')
    let rec collectExpW =
      function
      | (Gss, Gl, (Uni (__l), s), K, DupVars, flag, d) -> (K, DupVars)
      | (Gss, Gl, (Pi ((__d, _), __v), s), K, DupVars, flag, d) ->
          let (K', _) = collectDec (Gss, (__d, s), (K, DupVars), d, false__) in
          collectExp
            (Gss, (I.Decl (Gl, (I.decSub (__d, s)))), (__v, (I.dot1 s)), K',
              DupVars, flag, d)
      | (Gss, Gl, (Root (_, S), s), K, DupVars, flag, d) ->
          collectSpine (Gss, Gl, (S, s), K, DupVars, flag, d)
      | (Gss, Gl, (Lam (__d, __u), s), K, DupVars, flag, d) ->
          let (K', _) = collectDec (Gss, (__d, s), (K, DupVars), d, false__) in
          collectExp
            (Gss, (I.Decl (Gl, (I.decSub (__d, s)))), (__u, (I.dot1 s)), K',
              DupVars, flag, (d + 1))
      | (Gss, Gl, ((EVar (r, GX, __v, cnstrs) as x), s), K, DupVars, flag, d)
          -> collectEVar (Gss, Gl, (x, s), K, DupVars, flag, d)
      | (Gss, Gl, (FgnExp csfe, s), K, DupVars, flag, d) ->
          I.FgnExpStd.fold csfe
            (function
             | (__u, KD') ->
                 let (K', Dup) = KD' in
                 collectExp (Gss, Gl, (__u, s), K', Dup, false__, d))
            (K, (I.Decl (DupVars, (FGN d))))
    let rec collectExp (Gss, Gl, __Us, K, DupVars, flag, d) =
      collectExpW (Gss, Gl, (Whnf.whnf __Us), K, DupVars, flag, d)
    let rec collectSpine =
      function
      | (Gss, Gl, (I.Nil, _), K, DupVars, flag, d) -> (K, DupVars)
      | (Gss, Gl, (SClo (S, s'), s), K, DupVars, flag, d) ->
          collectSpine (Gss, Gl, (S, (I.comp (s', s))), K, DupVars, flag, d)
      | (Gss, Gl, (App (__u, S), s), K, DupVars, flag, d) ->
          let (K', DupVars') =
            collectExp (Gss, Gl, (__u, s), K, DupVars, flag, d) in
          collectSpine (Gss, Gl, (S, s), K', DupVars', flag, d)
    let rec collectEVarFapStr
      (Gss, Gl, ((x', __v'), w), ((EVar (r, GX, __v, cnstrs) as x), s), K,
       DupVars, flag, d)
      =
      match member' (eqEVar x) K with
      | Some label ->
          if flag
          then
            collectSub
              (Gss, Gl, s, K, (I.Decl (DupVars, (AV (x, d)))), flag, d)
          else collectSub (Gss, Gl, s, K, DupVars, flag, d)
      | None ->
          let label = if flag then Body else TypeLabel in
          let (K', DupVars') =
            collectExp
              ((I.Null, I.id), I.Null, (__v', I.id), K, DupVars, false__, d) in
          collectSub
            (Gss, Gl, (I.comp (w, s)), (I.Decl (K', (label, (EV x')))),
              DupVars', flag, d)
    let rec collectEVarNFapStr
      (Gss, Gl, ((x', __v'), w), ((EVar (r, GX, __v, cnstrs) as x), s), K,
       DupVars, flag, d)
      =
      match member' (eqEVar x) K with
      | Some label ->
          if flag
          then
            collectSub
              (Gss, Gl, s, K, (I.Decl (DupVars, (AV (x, d)))), flag, d)
          else collectSub (Gss, Gl, s, K, DupVars, flag, d)
      | None ->
          let label = if flag then Body else TypeLabel in
          let (K', DupVars') =
            collectExp
              ((I.Null, I.id), I.Null, (__v', I.id), K, DupVars, false__, d) in
          if flag
          then
            collectSub
              (Gss, Gl, (I.comp (w, s)), (I.Decl (K', (label, (EV x')))),
                (I.Decl (DupVars', (AV (x', d)))), flag, d)
          else
            collectSub
              (Gss, Gl, (I.comp (w, s)), (I.Decl (K', (label, (EV x')))),
                DupVars', flag, d)
    let rec collectEVarStr
      (((__Gs, ss) as Gss), Gl, ((EVar (r, GX, __v, cnstrs) as x), s), K,
       DupVars, flag, d)
      =
      let w = Subordinate.weaken (GX, (I.targetFam __v)) in
      let iw = Whnf.invert w in
      let GX' = Whnf.strengthen (iw, GX) in
      let EVar (r', _, _, _) as x' = I.newEVar (GX', (I.EClo (__v, iw))) in
      let _ = Unify.instantiateEVar (r, (I.EClo (x', w)), nil) in
      let __v' = raiseType (GX', (I.EClo (__v, iw))) in
      if isId (I.comp (w, (I.comp (ss, s))))
      then
        collectEVarFapStr
          (Gss, Gl, ((x', __v'), w), (x, s), K, DupVars, flag, d)
      else
        collectEVarNFapStr
          (Gss, Gl, ((x', __v'), w), (x, s), K, DupVars, flag, d)
    let rec collectEVarFap
      (Gss, Gl, ((EVar (r, GX, __v, cnstrs) as x), s), K, DupVars, flag, d) =
      match member (eqEVar x) K with
      | Some label ->
          if flag
          then
            collectSub
              (Gss, Gl, s, K, (I.Decl (DupVars, (AV (x, d)))), flag, d)
          else collectSub (Gss, Gl, s, K, DupVars, flag, d)
      | None ->
          let label = if flag then Body else TypeLabel in
          let __v' = raiseType (GX, __v) in
          let (K', DupVars') =
            collectExp
              ((I.Null, I.id), I.Null, (__v', I.id), K, DupVars, false__, d) in
          collectSub
            (Gss, Gl, s, (I.Decl (K', (label, (EV x)))), DupVars', flag, d)
    let rec collectEVarNFap
      (Gss, Gl, ((EVar (r, GX, __v, cnstrs) as x), s), K, DupVars, flag, d) =
      match member' (eqEVar x) K with
      | Some label ->
          if flag
          then
            collectSub
              (Gss, Gl, s, K, (I.Decl (DupVars, (AV (x, d)))), flag, d)
          else collectSub (Gss, Gl, s, K, DupVars, flag, d)
      | None ->
          let label = if flag then Body else TypeLabel in
          let __v' = raiseType (GX, __v) in
          let (K', DupVars') =
            collectExp
              ((I.Null, I.id), I.Null, (__v', I.id), K, DupVars, false__, d) in
          if flag
          then
            collectSub
              (Gss, Gl, s, (I.Decl (K', (label, (EV x)))),
                (I.Decl (DupVars, (AV (x, d)))), flag, d)
          else
            collectSub
              (Gss, Gl, s, (I.Decl (K', (label, (EV x)))), DupVars, flag, d)
    let rec collectEVar
      (Gss, Gl, ((EVar (r, GX, __v, cnstrs) as x), s), K, DupVars, flag, d) =
      if !TableParam.strengthen
      then collectEVarStr (Gss, Gl, (x, s), K, DupVars, flag, d)
      else
        if isId s
        then collectEVarFap (Gss, Gl, (x, s), K, DupVars, flag, d)
        else collectEVarNFap (Gss, Gl, (x, s), K, DupVars, flag, d)
    let rec collectDec (Gss, (Dec (_, __v), s), (K, DupVars), d, flag) =
      let (K', DupVars') =
        collectExp (Gss, I.Null, (__v, s), K, DupVars, flag, d) in
      (K', DupVars')
    let rec collectSub =
      function
      | (Gss, Gl, Shift _, K, DupVars, flag, d) -> (K, DupVars)
      | (Gss, Gl, Dot (Idx _, s), K, DupVars, flag, d) ->
          collectSub (Gss, Gl, s, K, DupVars, flag, d)
      | (Gss, Gl, Dot (Exp (EVar (ref (Some (__u)), _, _, _) as x), s), K,
         DupVars, flag, d) ->
          let __u' = Whnf.normalize (__u, I.id) in
          let (K', DupVars') =
            collectExp (Gss, Gl, (__u', I.id), K, DupVars, flag, d) in
          collectSub (Gss, Gl, s, K', DupVars', flag, d)
      | (Gss, Gl, Dot (Exp (AVar (ref (Some (__u'))) as __u), s), K, DupVars,
         flag, d) ->
          let (K', DupVars') =
            collectExp (Gss, Gl, (__u', I.id), K, DupVars, flag, d) in
          collectSub (Gss, Gl, s, K', DupVars', flag, d)
      | (Gss, Gl, Dot (Exp (EClo (__u', s')), s), K, DupVars, flag, d) ->
          let __u = Whnf.normalize (__u', s') in
          let (K', DupVars') =
            collectExp (Gss, Gl, (__u, I.id), K, DupVars, flag, d) in
          collectSub (Gss, Gl, s, K', DupVars', flag, d)
      | (Gss, Gl, Dot (Exp (__u), s), K, DupVars, flag, d) ->
          let (K', DupVars') =
            collectExp (Gss, Gl, (__u, I.id), K, DupVars, flag, d) in
          collectSub (Gss, Gl, s, K', DupVars', flag, d)
      | (Gss, Gl, Dot (I.Undef, s), K, DupVars, flag, d) ->
          collectSub (Gss, Gl, s, K, DupVars, flag, d)
    let rec collectCtx =
      function
      | (Gss, DProg (I.Null, I.Null), (K, DupVars), d) -> (K, DupVars)
      | (Gss, DProg (Decl (__g, __d), Decl (dPool, C.Parameter)), (K, DupVars),
         d) ->
          let (K', DupVars') =
            collectCtx (Gss, (C.DProg (__g, dPool)), (K, DupVars), (d - 1)) in
          collectDec (Gss, (__d, I.id), (K', DupVars'), (d - 1), false__)
      | (Gss, DProg (Decl (__g, __d), Decl (dPool, Dec (r, s, Ha))),
         (K, DupVars), d) ->
          let (K', DupVars') =
            collectCtx (Gss, (C.DProg (__g, dPool)), (K, DupVars), (d - 1)) in
          collectDec (Gss, (__d, I.id), (K', DupVars'), (d - 1), false__)
    let rec abstractExpW =
      function
      | (flag, __Gs, posEA, Vars, Gl, total, depth, ((Uni (__l) as __u), s), eqn)
          -> (posEA, Vars, __u, eqn)
      | (flag, __Gs, posEA, Vars, Gl, total, depth, (Pi ((__d, P), __v), s), eqn)
          ->
          let (posEA', Vars', __d, _) =
            abstractDec (__Gs, posEA, Vars, Gl, total, depth, (__d, s), None) in
          let (posEA'', Vars'', __v', eqn2) =
            abstractExp
              (flag, __Gs, posEA', Vars', Gl, total, (depth + 1),
                (__v, (I.dot1 s)), eqn) in
          (posEA'', Vars'', (piDepend ((__d, P), __v')), eqn2)
      | (flag, __Gs, posEA, Vars, Gl, total, depth, (Root (H, S), s), eqn) ->
          let (posEA', Vars', S, eqn') =
            abstractSpine
              (flag, __Gs, posEA, Vars, Gl, total, depth, (S, s), eqn) in
          (posEA', Vars', (I.Root (H, S)), eqn')
      | (flag, __Gs, posEA, Vars, Gl, total, depth, (Lam (__d, __u), s), eqn) ->
          let (posEA', Vars', __d', _) =
            abstractDec (__Gs, posEA, Vars, Gl, total, depth, (__d, s), None) in
          let (posEA'', Vars'', __u', eqn2) =
            abstractExp
              (flag, __Gs, posEA', Vars', (I.Decl (Gl, __d')), total,
                (depth + 1), (__u, (I.dot1 s)), eqn) in
          (posEA'', Vars'', (I.Lam (__d', __u')), eqn2)
      | (flag, ((Gss, ss) as __Gs), ((epos, apos) as posEA), Vars, Gl, total,
         depth, ((EVar (_, GX, VX, _) as x), s), eqn) ->
          if isId (I.comp (ss, s))
          then
            abstractEVarFap
              (flag, __Gs, posEA, Vars, Gl, total, depth, (x, s), eqn)
          else
            abstractEVarNFap
              (flag, __Gs, posEA, Vars, Gl, total, depth, (x, s), eqn)
    let rec abstractExp (flag, __Gs, posEA, Vars, Gl, total, depth, __Us, eqn) =
      abstractExpW
        (flag, __Gs, posEA, Vars, Gl, total, depth, (Whnf.whnf __Us), eqn)
    let rec abstractEVarFap
      (flag, __Gs, ((epos, apos) as posEA), Vars, Gl, total, depth, (x, s),
       eqn)
      =
      match member (eqEVar x) Vars with
      | Some (label, i) ->
          if flag
          then
            (match label with
             | Body ->
                 let BV = I.BVar (apos + depth) in
                 let BV' = I.BVar (i + depth) in
                 let BV1 = I.BVar (apos + depth) in
                 let (posEA', Vars', S, eqn1) =
                   abstractSub
                     (flag, __Gs, (epos, (apos - 1)), Vars, Gl, total, depth,
                       s, I.Nil, eqn) in
                 (posEA', Vars', (I.Root (BV, I.Nil)),
                   (TableParam.Unify
                      (Gl, (I.Root (BV', S)), (I.Root (BV1, I.Nil)), eqn1)))
             | TypeLabel ->
                 let Vars' = update (eqEVar x) Vars in
                 let (posEA', Vars'', S, eqn1) =
                   abstractSub
                     (flag, __Gs, (epos, apos), Vars', Gl, total, depth, s,
                       I.Nil, eqn) in
                 (posEA', Vars'', (I.Root ((I.BVar (i + depth)), S)), eqn1))
          else
            (let (posEA', Vars', S, eqn1) =
               abstractSub
                 (flag, __Gs, (epos, apos), Vars, Gl, total, depth, s, I.Nil,
                   eqn) in
             (posEA', Vars', (I.Root ((I.BVar (i + depth)), S)), eqn1))
      | None ->
          let label = if flag then Body else TypeLabel in
          let BV = I.BVar (epos + depth) in
          let pos = ((epos - 1), apos) in
          let (posEA', Vars', S, eqn1) =
            abstractSub
              (flag, __Gs, pos, (I.Decl (Vars, ((label, epos), (EV x)))), Gl,
                total, depth, s, I.Nil, eqn) in
          (posEA', Vars', (I.Root (BV, S)), eqn1)
    let rec abstractEVarNFap
      (flag, __Gs, ((epos, apos) as posEA), Vars, Gl, total, depth, (x, s),
       eqn)
      =
      match member (eqEVar x) Vars with
      | Some (label, i) ->
          if flag
          then
            let BV = I.BVar (apos + depth) in
            let BV' = I.BVar (i + depth) in
            let BV1 = I.BVar (apos + depth) in
            let (posEA', Vars', S, eqn1) =
              abstractSub
                (flag, __Gs, (epos, (apos - 1)), Vars, Gl, total, depth, s,
                  I.Nil, eqn) in
            (posEA', Vars', (I.Root (BV, I.Nil)),
              (TableParam.Unify
                 (Gl, (I.Root (BV', S)), (I.Root (BV1, I.Nil)), eqn1)))
          else
            (let (posEA', Vars', S, eqn1) =
               abstractSub
                 (flag, __Gs, (epos, apos), Vars, Gl, total, depth, s, I.Nil,
                   eqn) in
             (posEA', Vars', (I.Root ((I.BVar (i + depth)), S)), eqn1))
      | None ->
          if flag
          then
            let label = if flag then Body else TypeLabel in
            let BV = I.BVar (apos + depth) in
            let BV' = I.BVar (epos + depth) in
            let BV1 = I.BVar (apos + depth) in
            let (posEA', Vars', S, eqn1) =
              abstractSub
                (flag, __Gs, ((epos - 1), (apos - 1)),
                  (I.Decl (Vars, ((label, epos), (EV x)))), Gl, total, depth,
                  s, I.Nil, eqn) in
            (posEA', Vars', (I.Root (BV, I.Nil)),
              (TableParam.Unify
                 (Gl, (I.Root (BV', S)), (I.Root (BV1, I.Nil)), eqn1)))
          else
            (let (posEA', Vars', S, eqn1) =
               abstractSub
                 (flag, __Gs, ((epos - 1), apos),
                   (I.Decl (Vars, ((TypeLabel, epos), (EV x)))), Gl, total,
                   depth, s, I.Nil, eqn) in
             (posEA', Vars', (I.Root ((I.BVar (epos + depth)), S)), eqn1))
    let rec abstractSub =
      function
      | (flag, __Gs, posEA, Vars, Gl, total, depth, Shift k, S, eqn) ->
          if k < depth
          then
            abstractSub
              (flag, __Gs, posEA, Vars, Gl, total, depth,
                (I.Dot ((I.Idx (k + 1)), (I.Shift (k + 1)))), S, eqn)
          else (posEA, Vars, S, eqn)
      | (flag, __Gs, posEA, Vars, Gl, total, depth, Dot (Idx k, s), S, eqn) ->
          abstractSub
            (flag, __Gs, posEA, Vars, Gl, total, depth, s,
              (I.App ((I.Root ((I.BVar k), I.Nil)), S)), eqn)
      | (flag, __Gs, posEA, Vars, Gl, total, depth, Dot (Exp (__u), s), S, eqn)
          ->
          let (posEA', Vars', __u', eqn') =
            abstractExp
              (flag, __Gs, posEA, Vars, Gl, total, depth, (__u, I.id), eqn) in
          abstractSub
            (flag, __Gs, posEA', Vars', Gl, total, depth, s, (I.App (__u', S)),
              eqn')
    let rec abstractSpine =
      function
      | (flag, __Gs, posEA, Vars, Gl, total, depth, (I.Nil, _), eqn) ->
          (posEA, Vars, I.Nil, eqn)
      | (flag, __Gs, posEA, Vars, Gl, total, depth, (SClo (S, s'), s), eqn) ->
          abstractSpine
            (flag, __Gs, posEA, Vars, Gl, total, depth, (S, (I.comp (s', s))),
              eqn)
      | (flag, __Gs, posEA, Vars, Gl, total, depth, (App (__u, S), s), eqn) ->
          let (posEA', Vars', __u', eqn') =
            abstractExp
              (flag, __Gs, posEA, Vars, Gl, total, depth, (__u, s), eqn) in
          let (posEA'', Vars'', S', eqn'') =
            abstractSpine
              (flag, __Gs, posEA', Vars', Gl, total, depth, (S, s), eqn') in
          (posEA'', Vars'', (I.App (__u', S')), eqn'')
    let rec abstractSub' =
      function
      | (flag, __Gs, epos, Vars, total, Shift k) ->
          if k < 0
          then raise (Error "Substitution out of range\n")
          else (epos, Vars, (I.Shift (k + total)))
      | (flag, __Gs, epos, Vars, total, Dot (Idx k, s)) ->
          let (epos', Vars', s') =
            abstractSub' (flag, __Gs, epos, Vars, total, s) in
          (epos', Vars', (I.Dot ((I.Idx k), s')))
      | (flag, __Gs, epos, Vars, total, Dot (Exp (__u), s)) ->
          let ((ep, _), Vars', __u', _) =
            abstractExp
              (false__, __Gs, (epos, 0), Vars, I.Null, total, 0, (__u, I.id),
                TableParam.Trivial) in
          let (epos'', Vars'', s') =
            abstractSub' (flag, __Gs, ep, Vars', total, s) in
          (epos'', Vars'', (I.Dot ((I.Exp __u'), s')))
    let rec abstractDec =
      function
      | (__Gs, posEA, Vars, Gl, total, depth, (Dec (x, __v), s), None) ->
          let (posEA', Vars', __v', eqn) =
            abstractExp
              (false__, __Gs, posEA, Vars, Gl, total, depth, (__v, s),
                TableParam.Trivial) in
          (posEA', Vars', (I.Dec (x, __v')), eqn)
      | (__Gs, posEA, Vars, Gl, total, depth, (Dec (x, __v), s), Some eqn) ->
          let (posEA', Vars', __v', eqn') =
            abstractExp
              (true__, __Gs, posEA, Vars, Gl, total, depth, (__v, s), eqn) in
          (posEA', Vars', (I.Dec (x, __v')), eqn')
    let rec abstractCtx' =
      function
      | (__Gs, epos, Vars, total, depth, DProg (I.Null, I.Null), __g', eqn) ->
          (epos, Vars, __g', eqn)
      | (__Gs, epos, Vars, total, depth, DProg
         (Decl (__g, __d), Decl (dPool, C.Parameter)), __g', eqn) ->
          let d = IntSyn.ctxLength __g in
          let ((epos', _), Vars', __d', _) =
            abstractDec
              (__Gs, (epos, total), Vars, I.Null, total, (depth - 1),
                (__d, I.id), None) in
          abstractCtx'
            (__Gs, epos', Vars', total, (depth - 1), (C.DProg (__g, dPool)),
              (I.Decl (__g', __d')), eqn)
      | (__Gs, epos, Vars, total, depth, DProg (Decl (__g, __d), Decl (dPool, _)),
         __g', eqn) ->
          let d = IntSyn.ctxLength __g in
          let ((epos', _), Vars', __d', _) =
            abstractDec
              (__Gs, (epos, total), Vars, I.Null, total, (depth - 1),
                (__d, I.id), None) in
          abstractCtx'
            (__Gs, epos', Vars', total, (depth - 1), (C.DProg (__g, dPool)),
              (I.Decl (__g', __d')), eqn)
    let rec abstractCtx (__Gs, epos, Vars, total, depth, dProg) =
      abstractCtx'
        (__Gs, epos, Vars, total, depth, dProg, I.Null, TableParam.Trivial)
    let rec makeEVarCtx =
      function
      | (__Gs, Vars, DEVars, I.Null, total) -> DEVars
      | (__Gs, Vars, DEVars, Decl (K', (_, EV (EVar (_, GX, VX, _) as E))),
         total) ->
          let __v' = raiseType (GX, VX) in
          let (_, Vars', __v'', _) =
            abstractExp
              (false__, __Gs, (0, 0), Vars, I.Null, 0, (total - 1), (__v', I.id),
                TableParam.Trivial) in
          let DEVars' = makeEVarCtx (__Gs, Vars', DEVars, K', (total - 1)) in
          let DEVars'' = I.Decl (DEVars', (I.Dec (None, __v''))) in DEVars''
    let rec makeAVarCtx (Vars, DupVars) =
      let rec avarCtx =
        function
        | (Vars, I.Null, k) -> I.Null
        | (Vars, Decl (K', AV ((EVar (ref (None), GX, VX, _) as E), d)), k)
            ->
            I.Decl
              ((avarCtx (Vars, K', (k + 1))),
                (I.ADec
                   ((Some
                       ((^) (((^) "AVar " Int.toString k) ^ "--")
                          Int.toString d)), d)))
        | (Vars, Decl (K', AV ((EVar (_, GX, VX, _) as E), d)), k) ->
            I.Decl
              ((avarCtx (Vars, K', (k + 1))),
                (I.ADec
                   ((Some
                       ((^) (((^) "AVar " Int.toString k) ^ "--")
                          Int.toString d)), d))) in
      avarCtx (Vars, DupVars, 0)
    let rec lowerEVar' =
      function
      | (x, __g, (Pi ((__d', _), __v'), s')) ->
          let __d'' = I.decSub (__d', s') in
          let (x', __u) =
            lowerEVar' (x, (I.Decl (__g, __d'')), (Whnf.whnf (__v', (I.dot1 s')))) in
          (x', (I.Lam (__d'', __u)))
      | (x, __g, __Vs') -> let x' = x in (x', x')
    let rec lowerEVar1 =
      function
      | (x, EVar (r, __g, _, _), ((Pi _ as __v), s)) ->
          let (x', __u) = lowerEVar' (x, __g, (__v, s)) in
          I.EVar ((ref (Some __u)), I.Null, __v, (ref nil))
      | (_, x, _) -> x
    let rec lowerEVar =
      function
      | (E, (EVar (r, __g, __v, ref nil) as x)) ->
          lowerEVar1 (E, x, (Whnf.whnf (__v, I.id)))
      | (E, EVar _) ->
          raise
            (Error
               "abstraction : LowerEVars: Typing ambiguous -- constraint of functional type cannot be simplified")
    let rec evarsToSub =
      function
      | (I.Null, s) -> s
      | (Decl (K', (_, EV (EVar ((ref (None) as I), GX, VX, cnstr) as E))),
         s) ->
          let __v' = raiseType (GX, VX) in
          let x =
            lowerEVar1
              (E, (I.EVar (I, I.Null, __v', cnstr)), (Whnf.whnf (__v', I.id))) in
          let s' = evarsToSub (K', s) in I.Dot ((I.Exp x), s')
    let rec avarsToSub =
      function
      | (I.Null, s) -> s
      | (Decl (Vars', AV ((EVar (I, GX, VX, cnstr) as E), d)), s) ->
          let s' = avarsToSub (Vars', s) in
          let AVar r as x' = I.newAVar () in
          I.Dot ((I.Exp (I.EClo (x', (I.Shift (~- d))))), s')
    let rec abstractEVarCtx ((DProg (__g, dPool) as dp), p, s) =
      let (__Gs, ss, d) =
        if !TableParam.strengthen
        then
          let w' = Subordinate.weaken (__g, (I.targetFam p)) in
          let iw = Whnf.invert w' in
          let __g' = Whnf.strengthen (iw, __g) in
          let d' = I.ctxLength __g' in (__g', iw, d')
        else (__g, I.id, (I.ctxLength __g)) in
      let (K, DupVars) = collectCtx ((__Gs, ss), dp, (I.Null, I.Null), d) in
      let (K', DupVars') =
        collectExp ((__Gs, ss), I.Null, (p, s), K, DupVars, true__, d) in
      let epos = I.ctxLength K' in
      let apos = I.ctxLength DupVars' in
      let total = epos + apos in
      let (epos', Vars', __g', eqn) =
        abstractCtx ((__Gs, ss), epos, I.Null, total, d, dp) in
      let (posEA'', Vars'', __u', eqn') =
        abstractExp
          (true__, (__Gs, ss), (epos', total), Vars', I.Null, total, d, 
            (p, s), eqn) in
      let DAVars = makeAVarCtx (Vars'', DupVars') in
      let DEVars = makeEVarCtx ((__Gs, ss), Vars'', I.Null, Vars'', 0) in
      let s' = avarsToSub (DupVars', I.id) in
      let s'' = evarsToSub (Vars'', s') in
      let __g'' = reverseCtx (__g', I.Null) in
      if !TableParam.strengthen
      then
        let w' = Subordinate.weaken (__g'', (I.targetFam __u')) in
        let iw = Whnf.invert w' in
        let __Gs' = Whnf.strengthen (iw, __g'') in
        (__Gs', DAVars, DEVars, __u', eqn', s'')
      else (__g'', DAVars, DEVars, __u', eqn', s'')
    (*
       We write {{K}} for the context of K, where EVars have
       been translated to declarations and their occurrences to BVars.
       For each occurrence of EVar in __u, we generate a distinct BVar together with
       a residual constraint. This enforces that the final abstraction of __u is
       linear. However, we do not linearize the context G.

       We write {{__u}}_K, {{S}}_K for the corresponding translation of an
       expression or spine.

       Just like contexts __g, any K is implicitly assumed to be
       well-formed and in dependency order.

       We write  K ||- __u  if all EVars in __u are collected in K.
       In particular, . ||- __u means __u contains no EVars.  Similarly,
       for spines K ||- S and other syntactic categories.

       Collection and abstraction raise Error if there are unresolved
       constraints after simplification.
    *)
    (* eqEVar x y = B
     where B iff x and y represent same variable
     *)
    (* Sun Dec  1 14:04:17 2002 -bp  may raise exception
       if strengthening is applied,i.e. the substitution is not always id! *)
    (* a few helper functions to manage K *)
    (* member P K = B option *)
    (* member P K = B option *)
    (* member P K = B option *)
    (* occursInExp (k, __u) = DP,

       Invariant:
       If    __u in nf
       then  DP = No      iff k does not occur in __u
             DP = Maybe   iff k occurs in __u some place not as an argument to a Skonst
             DP = Meta    iff k occurs in __u and only as arguments to Skonsts
    *)
    (* no case for Redex, EVar, EClo *)
    (* no case for FVar *)
    (* no case for SClo *)
    (* piDepend ((__d,P), __v) = Pi ((__d,__P'), __v)
       where __P' = Maybe if __d occurs in __v, __P' = No otherwise
    *)
    (* optimize to have fewer traversals? -cs *)
    (* pre-Twelf 1.2 code walk Fri May  8 11:17:10 1998 *)
    (* raiseType (__g, __v) = {{__g}} __v

       Invariant:
       If __g |- __v : __l
       then  . |- {{__g}} __v : __l

       All abstractions are potentially dependent.
    *)
    (* collectExpW ((__Gs, ss), Gl, (__u, s), K, DupVars, flag) = (K', DupVars')

       Invariant:
       If    __g, Gl |- s : G1     G1 |- __u : __v      (__u,s) in whnf
                __Gs |- ss : __g  (__Gs is the strengthened context and ss is the strengthening substitution)

       No circularities in __u
             (enforced by extended occurs-check for FVars in Unify)
       and   K' = K, K''
             where K' contains all EVars in (__u,s)
       and  DupVars' = DupVars, DupVars''
            where DupVars' contains all duplicates in (__u,s)

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
    (* collectExp (Gss, __g, Gl, (__u, s), K) = K'
       same as collectExpW  but  (__u,s) need not to be in whnf
    *)
    (* collectSpine (Gss, Gl, (S, s), K, DupVars, flag) = (K', DupVars')

       Invariant:
       If    __g, Gl |- s : G1     G1 |- S : __v > P
                __Gs |- ss : __g
       then  K' = K, K'' and DupVars' = DupVars, DupVars''
       where K'' contains all EVars in (S, s)
       and DupVars'' contains all duplicates in (S, s)
     *)
    (* we have seen x before *)
    (* case label of
                     Body => collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(x,d)), flag, d)
                   | TypeLabel =>
                       let
                         val K' = update' (eqEVar x) K
                       in
                         collectSub(Gss, Gl, s, K', DupVars, flag, d)
                       end *)
    (* since x has occurred before, we do not traverse its type __v' *)
    (*          val __v' = raiseType (GX, __v)  inefficient! *)
    (* we have seen x before, i.e. it was already strengthened *)
    (* -bp this is a possible optimization for the variant case
                   case label of
                   Body => (print "Collect DupVar\n"; collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(x, d)), flag, d) )
                 | TypeLabel =>
                    let
                      val _ = print "TypeLabel\n"
                      val K' = update' (eqEVar x) K
                    in
                      collectSub(Gss, Gl, s, K', DupVars, flag, d)
                    end*)
    (* val __v' = raiseType (GX, __v)  inefficient! *)
    (* ? *)
    (* equalCtx (__Gs, I.id, GX', s) *)
    (* fully applied *)
    (* not fully applied *)
    (* x is fully applied pattern *)
    (* we have seen x before *)
    (*
                 case label of
                   Body => collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(x, d)), flag, d)
                 | TypeLabel =>
                     let
                       val K' = update' (eqEVar x) K
                     in
                       collectSub(Gss, Gl, s, K', DupVars, flag, d)
                     end *)
    (* since x has occurred before, we do not traverse its type __v' *)
    (* val _ = checkEmpty !cnstrs *)
    (* inefficient! *)
    (* case label of
                   Body => collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(x, d)), flag, d)
                   | TypeLabel =>
                     let
                       val K' = update' (eqEVar x) K
                     in
                       collectSub(Gss, Gl, s, K', DupVars, flag, d)
                     end             *)
    (* inefficient! *)
    (* equalCtx (compose'(Gl, __g), s, GX, s)  *)
    (* x is fully applied *)
    (* x is not fully applied *)
    (* collectDec (Gss, __g, (x:__v, s), K, DupVars, flag) = (K', DupVars')

       Invariant:
       If    __g |- s : G1     G1 |- __v : __l
            __Gs |- ss : __g
       then  K' = K, K'' and DupVars' = DupVars, DupVars''
       where K'' contains all EVars in (__v, s)
       and DupVars'' contains all duplicates in (S, s)
    *)
    (*      val (K',DupVars') =  collectExp (Gss, I.Null, (__v, s), K, I.Null, false, d)*)
    (* collectSub (__g, s, K, DupVars, flag) = (K', DupVars)

       Invariant:
       If    __g |- s : G1

       then  K' = K, K'' and DupVars' = DupVars, DupVars''
       where K'' contains all EVars in s
       and DupVars'' contains all duplicates in s
    *)
    (* inefficient? *)
    (* inefficient? *)
    (* collectCtx (Gss, G0, __g, K) = (K', DupVars)
       Invariant:
       If G0 |- __g ctx,
       then G0' = G0,__g
       and K' = K, K'' where K'' contains all EVars in __g
    *)
    (* abstractExpW (epos, apos, Vars, Gl, total, depth, (__u, s), eqn) = (epos', apos', Vars', __u', eqn')
      (abstraction and linearization of existential variables in (__u,s))

       __u' = {{__u[s]}}_(K, Dup)

       Invariant:
       If     __g, Gl |- __u[s] : __v and  __u[s] is in whnf
       and   |Gl| = depth
             |Dup, K| = total

       and epos = (total(K) + l) - #replaced expressions in __u    (generate no additional constraints)
       and apos = (total(Dup) + + total(K) + l) - #replaced expressions in __u
                  (generate additional constraints (avars))

       and Vars'  = Vars, Vars''
           where Vars contains pairs ((label, i), EV x) of all EVars (EV x),
           where label refers to where we have seen the existential variable (typeLabel or body) and
           i corresponds to the bvar-index assigned to x in __u[s]

       and   K ~ Vars (we can obtain K from Vars by dropping the first component of
             each pair (_, EV x) in Vars' )

       then   {{Dup}}, {{K}}  ||- __u
       and {{Dup}} {{K}} , __g, Gl |-  __u' : __v'
       and eqn' = eqn, eqn'' where eqn'' are residual equations relating between elements
           in {{K}} and {{Dup}}

       and . ||- Pi G. __u'  and   __u' is in nf

       if flag then linearize __u else allow duplicates.

    *)
    (* x is possibly strengthened ! *)
    (* x is fully applied *)
    (* s =/= id, i.e. x is not fully applied *)
    (*      | abstractExpW (posEA, Vars, Gl, total, depth, (x as I.FgnExp (cs, ops), s), eqn) =  *)
    (*      let
          val (x, _) = #map(ops) (fn __u => abstractExp (posEA, Vars, Gl, total, depth, (__u, s), eqn))
        in        abstractFgn (posEA, Vars, Gl, total, depth, x, eqn)
        end
*)
    (* abstractExp (posEA, Vars, Gl, total, depth, (__u, s)) = __u'

       same as abstractExpW, but (__u,s) need not to be in whnf
    *)
    (* we have seen x before *)
    (* enforce linearization *)
    (* do not enforce linearization -- used for type labels *)
    (* we see x for the first time *)
    (* we have seen x before *)
    (* enforce linearization *)
    (* (case label of
               Body =>
                 let
                  val _ = print "abstractEVarNFap -- flag true; we have seen x before\n"
                   val BV = I.BVar(apos + depth)
                   val BV' = I.BVar(i + depth)
                   val BV1 = I.BVar(apos + depth)
                   val (posEA', Vars', S, eqn1) = abstractSub (flag, __Gs, (epos, apos - 1), Vars, Gl, total, depth, s, I.Nil, eqn)
                 in
                   (posEA', Vars', I.Root(BV, I.Nil), TableParam.Unify(Gl, I.Root(BV', S), I.Root(BV1, I.Nil ), eqn1))
                 end
              | TyeLabel =>
                 let
                   val Vars' = update (eqEVar x) Vars
                   val (posEA', Vars'', S, eqn1) = abstractSub (flag, __Gs, (epos, apos), Vars', Gl, total, depth, s, I.Nil, eqn)
                 in
                   (posEA', Vars'', I.Root(I.BVar(i + depth), S), eqn1)
                 end) *)
    (* do not enforce linearization -- used for type labels *)
    (* we have not seen x before *)
    (* enforce linearization since x is not fully applied *)
    (* do not enforce linearization -- used for type labels *)
    (* abstractSub (flag, __Gs, posEA, Vars, Gl, total, depth, s, S, eqn) = (posEA', Vars', S', eqn')

       (implicit raising)
       (for posEA, Vars, eqn explanation see above)

       let K* = K, Dup

       S' = {{s}}_K* @@ S

       Invariant:
       If    __g, Gl |- s : G1
       and  |Gl| = depth

       and   {{Dup}} {{K}} ||- s
       then {{Dup}} {{K}}, __g, Gl |- S' : {G1}.W > W   (for some W)
       and  . ||- S'
    *)
    (* k = depth *)
    (* abstractSpine (flag, __Gs, posEA, Vars, Gl, total, depth, (S, s), eqn) = (posEA', Vars', S', eqn')
       where S' = {{S[s]}}_K*   and K* = K, Dup

       Invariant:
       If   Gl, __g |- s : G1     G1 |- S : __v > P
       and  K* ||- S
       and  |__g| = depth

       then {{K*}}, __g, __g |- S' : __v' > __P'
       and  . ||- S'
    *)
    (* abstractSub' (flag, __Gs, epos, K, Gl, total, s) = (epos', K', s')      (implicit raising)

        Invariant:
        If   __g |- s : G1
       and  |__g| = depth
       and  K ||- s
       and {{K}}, __g |- {{s}}_K : G1
       then __Gs, __g |- s' : G1    where  s' == {{s}}_K

         *)
    (* abstractDec (__Gs, posEA, Vars, Gl, total, depth, (x:__v, s)) = (posEA', Vars', x:__v')
       where __v = {{__v[s]}}_K*

       Invariant:
       If   __g |- s : G1     G1 |- __v : __l
       and  K* ||- __v
       and  |__g| = depth

       then {{K*}}, __g |- __v' : __l
       and  . ||- __v'
    *)
    (*      val (posEA', Vars', __v', _) = abstractExp (false, __Gs, posEA, Vars, Gl, total, depth, (__v, s), TableParam.Trivial)*)
    (*      val (posEA', Vars', __v', _) = abstractExp (false, __Gs, posEA, Vars, Gl, total, depth, (__v, s), TableParam.Trivial)*)
    (* abstractCtx (__Gs, epos, K, total, depth, C.DProg(__g,dPool)) = (epos', K', __g')
       where __g' = {{__g}}_K

       Invariants:
       If K ||- __g
       and |__g| = depth
       then {{K}} |- __g' ctx
       and . ||- __g'
       and epos = current epos

       note: we will linearize all dynamic assumptions in G.
    *)
    (*        let
          val d = IntSyn.ctxLength (__g)
          val ((epos', _), Vars', __d', eqn') = abstractDec (__Gs, (epos, total), Vars, I.Null, total , depth - 1, (__d, I.id), Some(eqn))
        in
          abstractCtx' (__Gs, epos', Vars', total, depth - 1, C.DProg(__g, dPool), I.Decl (__g', __d'), eqn')
        end
*)
    (* makeEVarCtx (__Gs, Kall, __d, K, eqn) = __g'  *)
    (* add case for foreign expressions ? *)
    (* lowerEVar' (__g, __v[s]) = (x', __u), see lowerEVar *)
    (* lowerEVar1 (x, __v[s]), __v[s] in whnf, see lowerEVar *)
    (* lowerEVar1 (x, I.EVar (r, __g, _, _), (__v as I.Pi _, s)) = *)
    (* lowerEVar (x) = x'

       Invariant:
       If   __g |- x : {{__g'}} P
            x not subject to any constraints
       then __g, __g' |- x' : P

       Effect: x is instantiated to [[__g']] x' if __g' is empty
               otherwise x = x' and no effect occurs.
    *)
    (* It is not clear if this case can happen *)
    (* pre-Twelf 1.2 code walk, Fri May  8 11:05:08 1998 *)
    (* evarsToSub (K, s') = s
      Invariant:
      if K = EV Xn ... EV X2, EV X1
        then
        s = X1 . X2 . ... s'
     *)
    (* redundant ? *)
    (* evarsToSub (K, s') = s
      Invariant:
      if K = AV Xn ... AV X2, EV X1
        then
        s = X1 . X2 . ... s'
     *)
    (* abstractEVarCtx (__g, p, s) = (__g', __d', __u', s')

     if __g |- p[s] and s contains free variables X_n .... X_1
     then
       __d' |- Pi  __g' . __u'
       where __d' is the abstraction over the free vars X_n .... X_1

       and s' is a substitution the free variables
            X_n .... X_1, s.t.

       . |- s' : __d'

       . |- (Pi __g' .U' )[s']  is equivalent to . |- Pi __g . p[s]

       Note: __g' and __u' are possibly strengthened
   *)
    (* K ||- __g i.e. K contains all EVars in __g *)
    (* DupVars' , K' ||- p[s]  i.e. K' contains all EVars in (p,s) and __g and
                                         DupVars' contains all duplicate EVars p[s] *)
    (* {{__g}}_Vars' , i.e. abstract over the existential variables in __g*)
    (* = 0 *)
    (* abstract over existential variables in p[s] and linearize the expression *)
    (* depth *)
    (* note: depth will become negative during makeEVarCtx *)
    let abstractEVarCtx = abstractEVarCtx
    (* abstractAnswSub s = (__d', s')

   if  |- s : Delta' and s may contain free variables and
     __d |- Pi G. __u  and  |- s : __d and  |- (Pi __g . __u)[s]
    then

    __d' |- s' : __d   where __d' contains all the
    free variables from s
   *)
    let abstractAnswSub =
      function
      | s ->
          let (K, _) =
            collectSub
              ((I.Null, I.id), I.Null, s, I.Null, I.Null, false__, 0) in
          let epos = I.ctxLength K in
          let (((_, Vars, s'))(*0 *)) =
            abstractSub' (((false__, (I.Null, I.id), epos, I.Null, epos, s))
              (* total *)) in
          let DEVars = makeEVarCtx ((I.Null, I.id), Vars, I.Null, Vars, 0) in
          let s1' = ctxToEVarSub (DEVars, I.id) in (((DEVars, s'))
            (* no linearization for answer substitution *))
    let raiseType = function | (__g, __u) -> raiseType (__g, __u)
  end ;;
