
module type COMPILE  =
  sig
    exception Error of string 
    type __Opt = CompSyn.__Opt
    val optimize : __Opt ref
    val install : IntSyn.__ConDecForm -> IntSyn.cid -> unit
    val sProgReset : unit -> unit
    val compileCtx : bool -> IntSyn.__Dec IntSyn.__Ctx -> CompSyn.__DProg
    val compileGoal :
      IntSyn.__Dec IntSyn.__Ctx -> IntSyn.__Exp -> CompSyn.__Goal
    val compilePsi : bool -> Tomega.__Dec IntSyn.__Ctx -> CompSyn.__DProg
  end;;




module Compile(Compile:sig
                         module Whnf : WHNF
                         module TypeCheck : TYPECHECK
                         module SubTree : SUBTREE
                         module CPrint : CPRINT
                         module Print : PRINT
                         module Names : NAMES
                       end) : COMPILE =
  struct
    exception Error of string 
    module I = IntSyn
    module T = Tomega
    module C = CompSyn
    type __Duplicates =
      | BVAR of int 
      | FGN 
      | DEF of int 
    let rec notCS = function | I.FromCS -> false__ | _ -> true__
    type __Opt = CompSyn.__Opt
    let optimize = CompSyn.optimize
    let rec cidFromHead = function | Const c -> c | Def c -> c
    let rec isConstraint =
      function
      | Const c ->
          (match I.constStatus c with | Constraint _ -> true__ | _ -> false__)
      | __H -> false__
    let rec head = function | Root (h, _) -> h | Pi (_, __A) -> head __A
    let rec seen i (Vars) = List.exists (fun d -> fun x -> x = i) Vars
    let rec etaSpine __0__ __1__ =
      match (__0__, __1__) with
      | (I.Nil, n) -> n = 0
      | (App (Root (BVar k, I.Nil), __S), n) ->
          (k = n) && (etaSpine (__S, (n - 1)))
      | (App (__A, __S), n) -> false__
    let rec collectHead __2__ __3__ __4__ __5__ __6__ =
      match (__2__, __3__, __4__, __5__, __6__) with
      | ((BVar k as h), __S, __K, Vars, depth) ->
          ((if k > depth
            then
              (if etaSpine (__S, depth)
               then
                 (if seen ((k - depth), Vars)
                  then (((depth, (BVAR (k - depth))) :: __K), Vars, true__)
                  else (__K, ((depth, (k - depth)) :: Vars), false__))
               else (((depth, (BVAR (k - depth))) :: __K), Vars, true__))
            else (__K, Vars, false__))
          (* check if h is an eta-expanded variable *)
          (* h is a locally bound variable and need not be collected *))
      | (_, _, __K, Vars, depth) -> (__K, Vars, false__)(* check if k is in Vars *)
    let rec collectSpine __7__ __8__ __9__ __10__ =
      match (__7__, __8__, __9__, __10__) with
      | (I.Nil, __K, Vars, depth) -> (__K, Vars)
      | (App (__U, __S), __K, Vars, depth) ->
          let (__K', Vars') = collectExp (__U, __K, Vars, depth) in
          collectSpine (__S, __K', Vars', depth)
    let rec collectExp __11__ __12__ __13__ __14__ =
      match (__11__, __12__, __13__, __14__) with
      | (Root ((BVar k as h), __S), __K, Vars, depth) ->
          let (__K', Vars', replaced) =
            collectHead (h, __S, __K, Vars, depth) in
          if replaced
          then (__K', Vars')
          else collectSpine (__S, __K', Vars', depth)
      | ((Root (Def k, __S) as U), __K, Vars, depth) ->
          (((depth, (DEF k)) :: __K), Vars)
      | (Root (h, __S), __K, Vars, depth) ->
          collectSpine (__S, __K, Vars, depth)
      | (Lam (__D, __U), __K, Vars, depth) ->
          collectExp (__U, __K, Vars, (depth + 1))
      | (FgnExp (cs, fe), __K, Vars, depth) -> (((depth, FGN) :: __K), Vars)
      (* don't collect D, since it is ignored in unification *)(* | collectExp (I.Uni(L), K, Vars, depth) = (K, Vars) *)
      (* should be impossible, Mon Apr 15 14:55:15 2002 -fp *)(* h is either const or skonst of def*)
    let rec shiftHead __15__ __16__ __17__ =
      match (__15__, __16__, __17__) with
      | ((BVar k as h), depth, total) ->
          if k > depth then I.BVar (k + total) else I.BVar k
      | ((Const k as h), depth, total) -> h
      | ((Def k as h), depth, total) -> h
      | ((NSDef k as h), depth, total) -> h
      | ((FgnConst k as h), depth, total) -> h
      | ((Skonst k as h), depth, total) -> h
    let rec shiftExp __18__ __19__ __20__ =
      match (__18__, __19__, __20__) with
      | (Root (h, __S), depth, total) ->
          I.Root
            ((shiftHead (h, depth, total)), (shiftSpine (__S, depth, total)))
      | (Uni (__L), _, _) -> I.Uni __L
      | (Lam (__D, __U), depth, total) ->
          I.Lam
            ((shiftDec (__D, depth, total)),
              (shiftExp (__U, (depth + 1), total)))
      | (Pi ((__D, __P), __U), depth, total) ->
          I.Pi
            (((shiftDec (__D, depth, total)), __P),
              (shiftExp (__U, (depth + 1), total)))
      | (FgnExp csfe, depth, total) ->
          I.FgnExpStd.Map.apply csfe
            (fun (__U) ->
               shiftExp ((Whnf.normalize (__U, I.id)), depth, total))
      (* Tue Apr  2 12:10:24 2002 -fp -bp *)(* this is overkill and could be very expensive for deeply nested foreign exps *)
      (* calling normalize here because U may not be normal *)
    let rec shiftSpine __21__ __22__ __23__ =
      match (__21__, __22__, __23__) with
      | (I.Nil, _, _) -> I.Nil
      | (App (__U, __S), depth, total) ->
          I.App
            ((shiftExp (__U, depth, total)),
              (shiftSpine (__S, depth, total)))
    let rec shiftDec (Dec (x, __V)) depth total =
      I.Dec (x, (shiftExp (__V, depth, total)))
    let rec linearHead __24__ __25__ __26__ __27__ __28__ __29__ __30__ =
      match (__24__, __25__, __26__, __27__, __28__, __29__, __30__) with
      | (__G, (BVar k as h), __S, left, Vars, depth, total) ->
          if k > depth
          then
            (if etaSpine (__S, depth)
             then
               (if seen ((k - depth), Vars)
                then ((left - 1), Vars, (I.BVar (left + depth)), true__)
                else
                  (left, ((depth, (k - depth)) :: Vars),
                    (I.BVar (k + total)), false__))
             else ((left - 1), Vars, (I.BVar (left + depth)), true__))
          else (left, Vars, h, false__)
      | (__G, (Const k as h), __S, left, Vars, depth, total) ->
          (left, Vars, h, false__)
      | (__G, (FgnConst (k, ConDec) as h), __S, left, Vars, depth, total) ->
          (left, Vars, h, false__)
      | (__G, (Skonst k as h), __S, left, Vars, depth, total) ->
          (left, Vars, h, false__)(*
     | linearHead(G, (h as I.NSDef k), s, S, left, Vars, depth, total) =
         (left, Vars, h, false)
     *)
    let rec linearExp __31__ __32__ __33__ __34__ __35__ __36__ __37__ =
      match (__31__, __32__, __33__, __34__, __35__, __36__, __37__) with
      | (Gl, (Root ((Def k as h), __S) as U), left, Vars, depth, total, eqns)
          ->
          let __N = I.Root ((I.BVar (left + depth)), I.Nil) in
          let __U' = shiftExp (__U, depth, total) in
          ((left - 1), Vars, __N, (C.UnifyEq (Gl, __U', __N, eqns)))
      | (Gl, (Root (h, __S) as U), left, Vars, depth, total, eqns) ->
          let (left', Vars', h', replaced) =
            linearHead (Gl, h, __S, left, Vars, depth, total) in
          ((if replaced
            then
              let __N = I.Root (h', I.Nil) in
              let __U' = shiftExp (__U, depth, total) in
              (left', Vars, __N, (C.UnifyEq (Gl, __U', __N, eqns)))
            else
              (let (left'', Vars'', __S', eqns') =
                 linearSpine (Gl, __S, left', Vars', depth, total, eqns) in
               (left'', Vars'', (I.Root (h', __S')), eqns')))
            (* h = h' not replaced *))
      | (Gl, Lam (__D, __U), left, Vars, depth, total, eqns) ->
          let __D' = shiftDec (__D, depth, total) in
          let (left', Vars', __U', eqns') =
            linearExp
              ((I.Decl (Gl, __D')), __U, left, Vars, (depth + 1), total,
                eqns) in
          (left', Vars', (I.Lam (__D', __U')), eqns')
      | (Gl, (FgnExp (cs, ops) as U), left, Vars, depth, total, eqns) ->
          let __N = I.Root ((I.BVar (left + depth)), I.Nil) in
          let __U' = shiftExp (__U, depth, total) in
          ((left - 1), Vars, __N, (C.UnifyEq (Gl, __U', __N, eqns)))(*
     | linearExp (Gl, U as I.Uni(L), left, Vars, depth, total, eqns) =
         (left, Vars, I.Uni(L), eqns)
     *)
      (* should be impossible  Mon Apr 15 14:54:42 2002 -fp *)
    let rec linearSpine __38__ __39__ __40__ __41__ __42__ __43__ __44__ =
      match (__38__, __39__, __40__, __41__, __42__, __43__, __44__) with
      | (Gl, I.Nil, left, Vars, depth, total, eqns) ->
          (left, Vars, I.Nil, eqns)
      | (Gl, App (__U, __S), left, Vars, depth, total, eqns) ->
          let (left', Vars', __U', eqns') =
            linearExp (Gl, __U, left, Vars, depth, total, eqns) in
          let (left'', Vars'', __S', eqns'') =
            linearSpine (Gl, __S, left', Vars', depth, total, eqns') in
          (left'', Vars'', (I.App (__U', __S')), eqns'')
    let rec compileLinearHead (__G) (Root (h, __S) as R) =
      let (__K, _) = collectExp (__R, nil, nil, 0) in
      let left = List.length __K in
      let (left', _, __R', Eqs) =
        linearExp (I.Null, __R, left, nil, 0, left, C.Trivial) in
      let rec convertKRes __45__ __46__ __47__ =
        match (__45__, __46__, __47__) with
        | (ResG, nil, 0) -> ResG
        | (ResG, (d, k)::__K, i) ->
            C.Axists
              ((I.ADec ((Some ((^) "A" Int.toString i)), d)),
                (convertKRes (ResG, __K, (i - 1)))) in
      let r = convertKRes ((C.Assign (__R', Eqs)), (List.rev __K), left) in
      if (!Global.chatter) >= 6
      then
        (print "\nClause LH Eqn"; print (CPrint.clauseToString "\t" (__G, r)))
      else ();
      r
    let rec compileSbtHead (__G) (Root (h, __S) as H) =
      let (__K, _) = collectExp (__H, nil, nil, 0) in
      let left = List.length __K in
      let (left', _, __H', Eqs) =
        linearExp (I.Null, __H, left, nil, 0, left, C.Trivial) in
      let rec convertKRes __48__ __49__ __50__ =
        match (__48__, __49__, __50__) with
        | (__G, nil, 0) -> __G
        | (__G, (d, k)::__K, i) ->
            convertKRes
              ((I.Decl
                  (__G, (I.ADec ((Some ((^) "AVar " Int.toString i)), d)))),
                __K, (i - 1)) in
      let __G' = convertKRes (__G, (List.rev __K), left) in
      ((if (!Global.chatter) >= 6
        then
          (print "\nClause Sbt Eqn";
           print (CPrint.clauseToString "\t" (__G', (C.Assign (__H', Eqs)))))
        else ();
        (__G', (Some (__H', Eqs))))
        (* insert R' together with Eqs and G and sc C.True *))
    let rec compileGoalN __51__ __52__ __53__ =
      match (__51__, __52__, __53__) with
      | (fromCS, __G, (Root _ as R)) -> C.Atom __R
      | (fromCS, __G, Pi ((Dec (_, __A1), I.No), __A2)) ->
          let Ha1 = I.targetHead __A1 in
          let __R = compileDClauseN fromCS false__ (__G, __A1) in
          let goal =
            compileGoalN fromCS ((I.Decl (__G, (I.Dec (NONE, __A1)))), __A2) in
          ((C.Impl (__R, __A1, Ha1, goal))
            (* A1 is used to build the proof term, Ha1 for indexing *)
            (* never optimize when compiling local assumptions *))
      | (fromCS, __G, Pi (((Dec (_, __A1) as D), I.Maybe), __A2)) ->
          if (notCS fromCS) && (isConstraint (head __A1))
          then raise (Error "Constraint appears in dynamic clause position")
          else C.All (__D, (compileGoalN fromCS ((I.Decl (__G, __D)), __A2)))
      (* A = {x:A1} A2 *)(* A = A1 -> A2 *)(* A = H @ S *)
    let rec compileGoal fromCS (__G) (__A, s) =
      compileGoalN fromCS (__G, (Whnf.normalize (__A, s)))
    let rec compileDClauseN __54__ __55__ __56__ __57__ =
      match (__54__, __55__, __56__, __57__) with
      | (fromCS, opt, __G, (Root (h, __S) as R)) ->
          if opt && ((!optimize) = C.LinearHeads)
          then compileLinearHead (__G, __R)
          else
            if (notCS fromCS) && (isConstraint h)
            then
              raise (Error "Constraint appears in dynamic clause position")
            else C.Eq __R
      | (fromCS, opt, __G, Pi (((Dec (_, __A1) as D), I.No), __A2)) ->
          C.And
            ((compileDClauseN fromCS opt ((I.Decl (__G, __D)), __A2)), __A1,
              (compileGoalN fromCS (__G, __A1)))
      | (fromCS, opt, __G, Pi (((Dec (_, __A1) as D), I.Meta), __A2)) ->
          C.In
            ((compileDClauseN fromCS opt ((I.Decl (__G, __D)), __A2)), __A1,
              (compileGoalN fromCS (__G, __A1)))
      | (fromCS, opt, __G, Pi ((__D, I.Maybe), __A2)) ->
          C.Exists
            (__D, (compileDClauseN fromCS opt ((I.Decl (__G, __D)), __A2)))
      (* A = {x:A1} A2 *)(* A = {x: A1} A2, x  meta variable occuring in A2 *)
      (* A = A1 -> A2 *)
    let rec compileSubgoals __58__ __59__ __60__ __61__ __62__ =
      match (__58__, __59__, __60__, __61__, __62__) with
      | (fromCS, __G', n, Decl (Stack, I.No), Decl (__G, Dec (_, __A))) ->
          let sg = compileSubgoals fromCS __G' ((n + 1), Stack, __G) in
          ((C.Conjunct
              ((compileGoal fromCS (__G', (__A, (I.Shift (n + 1))))),
                (I.EClo (__A, (I.Shift (n + 1)))), sg))
            (* G |- A and G' |- A[^(n+1)] *))
      | (fromCS, __G', n, Decl (Stack, I.Maybe), Decl (__G, Dec (_, __A1)))
          -> compileSubgoals fromCS __G' ((n + 1), Stack, __G)
      | (fromCS, __G', n, I.Null, I.Null) -> C.True
    let rec compileSClauseN __63__ __64__ __65__ __66__ =
      match (__63__, __64__, __65__, __66__) with
      | (fromCS, Stack, __G, (Root (h, __S) as R)) ->
          let (__G', Head) = compileSbtHead (__G, __R) in
          let d = (-) (I.ctxLength __G') I.ctxLength __G in
          let Sgoals = compileSubgoals fromCS __G' (d, Stack, __G) in
          ((((__G', Head), Sgoals))
            (* G' |- Sgoals  and G' |- ^d : G *))
      | (fromCS, Stack, __G, Pi (((Dec (_, __A1) as D), I.No), __A2)) ->
          compileSClauseN fromCS
            ((I.Decl (Stack, I.No)), (I.Decl (__G, __D)), __A2)
      | (fromCS, Stack, __G, Pi (((Dec (_, __A1) as D), I.Meta), __A2)) ->
          compileSClauseN fromCS
            ((I.Decl (Stack, I.Meta)), (I.Decl (__G, __D)), __A2)
      | (fromCS, Stack, __G, Pi (((Dec (_, __A1) as D), I.Maybe), __A2)) ->
          compileSClauseN fromCS
            ((I.Decl (Stack, I.Maybe)), (I.Decl (__G, __D)), __A2)
    let rec compileDClause opt (__G) (__A) =
      compileDClauseN I.Ordinary opt (__G, (Whnf.normalize (__A, I.id)))
    let rec compileGoal (__G) (__A) =
      compileGoalN I.Ordinary (__G, (Whnf.normalize (__A, I.id)))
    let rec compileCtx opt (__G) =
      let rec compileBlock __67__ __68__ __69__ =
        match (__67__, __68__, __69__) with
        | (nil, s, (n, i)) -> nil
        | ((Dec (_, __V))::__Vs, t, (n, i)) ->
            let Vt = I.EClo (__V, t) in
            (::) ((compileDClause opt (__G, Vt)), I.id, (I.targetHead Vt))
              compileBlock
              (__Vs,
                (I.Dot
                   ((I.Exp (I.Root ((I.Proj ((I.Bidx n), i)), I.Nil))), t)),
                (n, (i + 1))) in
      let rec compileCtx' =
        function
        | I.Null -> I.Null
        | Decl (__G, Dec (_, __A)) ->
            let Ha = I.targetHead __A in
            I.Decl
              ((compileCtx' __G),
                (CompSyn.Dec ((compileDClause opt (__G, __A)), I.id, Ha)))
        | Decl (__G, BDec (_, (c, s))) ->
            let (__G, __L) = I.constBlock c in
            let dpool = compileCtx' __G in
            let n = I.ctxLength dpool in
            ((I.Decl (dpool, (CompSyn.BDec (compileBlock (__L, s, (n, 1))))))
              (* this is inefficient! -cs *)) in
      C.DProg (__G, (compileCtx' __G))
    let rec compilePsi opt (Psi) =
      let rec compileBlock __70__ __71__ __72__ =
        match (__70__, __71__, __72__) with
        | (nil, s, (n, i)) -> nil
        | ((Dec (_, __V))::__Vs, t, (n, i)) ->
            let Vt = I.EClo (__V, t) in
            (::) ((compileDClause opt ((T.coerceCtx Psi), Vt)), I.id,
                   (I.targetHead Vt))
              compileBlock
              (__Vs,
                (I.Dot
                   ((I.Exp (I.Root ((I.Proj ((I.Bidx n), i)), I.Nil))), t)),
                (n, (i + 1))) in
      let rec compileCtx' =
        function
        | I.Null -> I.Null
        | Decl (__G, Dec (_, __A)) ->
            let Ha = I.targetHead __A in
            I.Decl
              ((compileCtx' __G),
                (CompSyn.Dec ((compileDClause opt (__G, __A)), I.id, Ha)))
        | Decl (__G, BDec (_, (c, s))) ->
            let (__G, __L) = I.constBlock c in
            let dpool = compileCtx' __G in
            let n = I.ctxLength dpool in
            ((I.Decl (dpool, (CompSyn.BDec (compileBlock (__L, s, (n, 1))))))
              (* this is inefficient! -cs *)) in
      let rec compilePsi' =
        function
        | I.Null -> I.Null
        | Decl (Psi, UDec (Dec (_, __A))) ->
            let Ha = I.targetHead __A in
            I.Decl
              ((compilePsi' Psi),
                (CompSyn.Dec
                   ((compileDClause opt ((T.coerceCtx Psi), __A)), I.id, Ha)))
        | Decl (Psi, UDec (BDec (_, (c, s)))) ->
            let (__G, __L) = I.constBlock c in
            let dpool = compileCtx' __G in
            let n = I.ctxLength dpool in
            ((I.Decl (dpool, (CompSyn.BDec (compileBlock (__L, s, (n, 1))))))
              (* this is inefficient! -cs *))
        | Decl (Psi, PDec _) -> I.Decl ((compilePsi' Psi), CompSyn.PDec) in
      C.DProg ((T.coerceCtx Psi), (compilePsi' Psi))
    let rec installClause fromCS a (__A) =
      match !C.optimize with
      | C.No ->
          C.sProgInstall
            (a, (C.SClause (compileDClauseN fromCS true__ (I.Null, __A))))
      | C.LinearHeads ->
          C.sProgInstall
            (a, (C.SClause (compileDClauseN fromCS true__ (I.Null, __A))))
      | C.Indexing ->
          let ((__G, Head), __R) =
            compileSClauseN fromCS
              (I.Null, I.Null, (Whnf.normalize (__A, I.id))) in
          let _ =
            C.sProgInstall
              (a, (C.SClause (compileDClauseN fromCS true__ (I.Null, __A)))) in
          (match Head with
           | NONE -> raise (Error "Install via normal index")
           | Some (__H, Eqs) ->
               SubTree.sProgInstall
                 ((cidFromHead (I.targetHead __A)),
                   (C.Head (__H, __G, Eqs, a)), __R))
    let rec compileConDec __73__ __74__ __75__ =
      match (__73__, __74__, __75__) with
      | (fromCS, a, ConDec (_, _, _, _, __A, I.Type)) ->
          installClause fromCS (a, __A)
      | (fromCS, a, SkoDec (_, _, _, __A, I.Type)) ->
          (match !C.optimize with
           | C.No ->
               C.sProgInstall
                 (a,
                   (C.SClause (compileDClauseN fromCS true__ (I.Null, __A))))
           | _ ->
               C.sProgInstall
                 (a,
                   (C.SClause (compileDClauseN fromCS true__ (I.Null, __A)))))
      | (I.Clause, a, ConDef (_, _, _, _, __A, I.Type, _)) ->
          C.sProgInstall
            (a,
              (C.SClause
                 (compileDClauseN I.Clause true__
                    (I.Null, (Whnf.normalize (__A, I.id))))))
      | (_, _) -> ()(* we don't use substitution tree indexing for skolem constants yet -bp*)
    let rec install fromCS cid =
      compileConDec fromCS (cid, (I.sgnLookup cid))
    let rec sProgReset () = SubTree.sProgReset (); C.sProgReset ()
  end ;;




module CPrint =
  (Make_CPrint)(struct
                  module Print = Print
                  module Formatter = Formatter
                  module Names = Names
                end)
module SubTree =
  (Make_SubTree)(struct
                   module IntSyn' = IntSyn
                   module Whnf = Whnf
                   module Unify = UnifyTrail
                   module CompSyn' = CompSyn
                   module Print = Print
                   module CPrint = CPrint
                   module Names = Names
                   module Formatter = Formatter
                   module CSManager = CSManager
                   module Table = IntRedBlackTree
                   module RBSet = RBSet
                 end)
module Compile =
  (Make_Compile)(struct
                   module Whnf = Whnf
                   module TypeCheck = TypeCheck
                   module SubTree = SubTree
                   module CPrint = CPrint
                   module Print = Print
                   module Names = Names
                 end)
module Assign =
  (Make_Assign)(struct
                  module Whnf = Whnf
                  module Unify = UnifyTrail
                  module Print = Print
                end);;
