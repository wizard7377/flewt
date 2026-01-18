
(* Translator from Delphin external syntax to Delphin internal syntax *)
(* Author: Richard Fontana, Carsten Schuermann *)
module type TRANS  =
  sig
    module DextSyn : DEXTSYN
    exception Error of string 
    val internalizeSig : unit -> unit
    val transFor : DextSyn.__Form -> Tomega.__For
    val transDecs : DextSyn.__Decs -> Tomega.__Prg
    val externalizePrg : Tomega.__Prg -> Tomega.__Prg
  end;;




(* Translator from Delphin external syntax to Delphin internal syntax *)
(* Author:  Carsten Schuermann *)
module Trans(Trans:sig module DextSyn' : DEXTSYN end) =
  struct
    (* : TRANS *)
    module DextSyn = DextSyn'
    module __d = DextSyn'
    module __l = Lexer
    module I = IntSyn
    module LS = Stream
    module T = Tomega
    module TA = TomegaAbstract
    exception Error of string 
    type __Internal =
      | Empty 
      | Const of (int * int) 
      | Type of int 
    let maxCid = Global.maxCid
    let internal =
      (Array.array ((maxCid + 1), Empty) : __Internal Array.array)
    let rec checkEOF =
      function
      | Cons ((L.EOF, r), s') -> r
      | Cons ((t, r), _) ->
          Parsing.error (r, ((^) "Expected `}', found " L.toString t))
    let rec stringTodec s =
      let f = LS.expose (L.lexStream (TextIO.openString s)) in
      let ((x, yOpt), f') = ParseTerm.parseDec' f in
      let r2 = checkEOF f' in
      let dec =
        match yOpt with
        | None -> ReconTerm.dec0 (x, r2)
        | Some y -> ReconTerm.dec (x, y, r2) in
      dec
    let rec stringToblocks s =
      let f = LS.expose (L.lexStream (TextIO.openString s)) in
      let (dl, f') = ParseTerm.parseCtx' f in dl
    let rec stringToWorlds s =
      let f = LS.expose (L.lexStream (TextIO.openString s)) in
      let (t, f') = ParseTerm.parseQualIds' f in let r2 = checkEOF f' in t
    let rec closure =
      function
      | (I.Null, __v) -> __v
      | (Decl (__g, __d), __v) -> closure (__g, (I.Pi ((__d, I.Maybe), __v)))
    let rec internalizeBlock arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (_, (nil, _)) -> ()
      | ((n, __g, Vb, S), ((Dec (Some name, __v))::L2, s)) ->
          let name' = "o_" ^ name in
          let V1 = I.EClo (__v, s) in
          let V2 = I.Pi (((I.Dec (None, Vb)), I.Maybe), V1) in
          let V3 = closure (__g, V2) in
          let m = I.ctxLength __g in
          let condec = I.ConDec (name', None, m, I.Normal, V3, I.Type) in
          let _ = TypeCheck.check (V3, (I.Uni I.Type)) in
          let _ =
            if (!Global.chatter) >= 4
            then print ((Print.conDecToString condec) ^ "\n")
            else () in
          let cid = I.sgnAdd condec in
          let _ = Names.installConstName cid in
          let _ = Array.update (internal, cid, (Const (m, n))) in
          internalizeBlock ((n + 1), __g, Vb, S)
            (L2, (I.Dot ((I.Exp (I.Root ((I.Const cid), S))), s)))
    let rec makeSpine =
      function
      | (_, I.Null, S) -> S
      | (n, Decl (__g, __d), S) ->
          makeSpine
            ((n + 1), __g, (I.App ((I.Root ((I.BVar (n + 1)), I.Nil)), S)))
    let rec internalizeCondec =
      function
      | (cid, ConDec _) -> ()
      | (cid, ConDef _) -> ()
      | (cid, AbbrevDef _) -> ()
      | (cid, BlockDec (name, _, Gsome, Lpi)) ->
          let __v' = closure (Gsome, (I.Uni I.Type)) in
          let C = I.ConDec ((name ^ "'"), None, 0, I.Normal, __v', I.Kind) in
          let a = I.sgnAdd C in
          let _ = Array.update (internal, a, (Type cid)) in
          let _ = Names.installConstName a in
          let S = makeSpine (0, Gsome, I.Nil) in
          let Vb = I.Root ((I.Const a), S) in
          let S' = makeSpine (0, (I.Decl (Gsome, (I.Dec (None, Vb)))), I.Nil) in
          internalizeBlock (1, Gsome, Vb, S') (Lpi, I.shift)
      | (cid, SkoDec _) -> ()
    let rec internalizeSig () =
      let (max, _) = I.sgnSize () in
      let rec internalizeSig' n =
        if n >= max
        then ()
        else
          (internalizeCondec (n, (I.sgnLookup n)); internalizeSig' (n + 1)) in
      internalizeSig' 0
    let rec dropSpine =
      function | (0, S) -> S | (n, App (_, S)) -> dropSpine ((n - 1), S)
    let rec makeSub =
      function
      | (I.Nil, s) -> s
      | (App (__u, S), s) -> makeSub (S, (I.Dot ((I.Exp __u), s)))
    let rec externalizeExp' =
      function
      | (Uni _ as __u) -> __u
      | Pi ((__d, DP), __u) ->
          I.Pi (((externalizeDec __d), DP), (externalizeExp __u))
      | Root ((BVar _ as H), S) -> I.Root (H, (externalizeSpine S))
      | Root ((Const c as H), S) ->
          (match I.constUni c with
           | I.Kind -> I.Root (H, (externalizeSpine S))
           | I.Type ->
               let Const (n, i) = Array.sub (internal, c) in
               let App (Root (BVar b, I.Nil), S') = dropSpine (n, S) in
               I.Root ((I.Proj ((I.Bidx b), i)), (externalizeSpine S')))
      | Root (Proj _, _) -> raise Domain
      | Root (Skonst _, _) -> raise Domain
      | Root (Def _, _) -> raise Domain
      | Root (NSDef _, _) -> raise Domain
      | Root (FVar _, _) -> raise Domain
      | Root (FgnConst _, _) -> raise Domain
      | Redex (__u, S) -> I.Redex ((externalizeExp __u), (externalizeSpine S))
      | Lam (__d, __u) -> I.Lam ((externalizeDec __d), (externalizeExp __u))
    let rec externalizeExp (__u) = externalizeExp' (Whnf.normalize (__u, I.id))
    let rec externalizeBlock (Bidx _ as B) = B
    let rec externalizeDec (Dec (name, __v)) = I.Dec (name, (externalizeExp __v))
    let rec externalizeSpine =
      function
      | I.Nil -> I.Nil
      | App (__u, S) -> I.App ((externalizeExp __u), (externalizeSpine S))
    let rec externalizeSub =
      function
      | Shift n as s -> s
      | Dot (F, s) -> I.Dot ((externalizeFront F), (externalizeSub s))
    let rec externalizeFront =
      function
      | Idx _ as F -> F
      | Exp (__u) -> I.Exp (externalizeExp __u)
      | Block (B) -> I.Block (externalizeBlock B)
      | I.Undef as F -> F
    let rec externalizePrg =
      function
      | (n, Lam (__d, P)) ->
          T.Lam ((externalizeMDec (n, __d)), (externalizePrg ((n + 1), P)))
      | (n, New (P)) -> T.New (externalizePrg (n, P))
      | (n, Box (W, P)) -> T.Box (W, (externalizePrg (n, P)))
      | (n, Choose (P)) -> T.Choose (externalizePrg (n, P))
      | (n, PairExp (__u, P)) ->
          T.PairExp ((externalizeExp __u), (externalizePrg (n, P)))
      | (n, PairPrg (__P1, __P2)) ->
          T.PairPrg ((externalizePrg (n, __P1)), (externalizePrg (n, __P2)))
      | (n, PairBlock (B, P)) ->
          T.PairBlock ((externalizeBlock B), (externalizePrg (n, P)))
      | (n, T.Unit) -> T.Unit
      | (n, Var k) -> T.Var k
      | (n, Const c) -> T.Const c
      | (n, Redex (P, S)) ->
          T.Redex ((externalizePrg (n, P)), (externalizeMSpine (n, S)))
      | (n, Rec (__d, P)) ->
          T.Rec ((externalizeMDec (n, __d)), (externalizePrg ((n + 1), P)))
      | (n, Case (Cases (O))) -> T.Case (T.Cases (externalizeCases O))
      | (n, Let (__d, __P1, __P2)) ->
          T.Let
            ((externalizeMDec (n, __d)), (externalizePrg (n, __P1)),
              (externalizePrg ((n + 1), __P2)))
    let rec externalizeMDec =
      function
      | (n, UDec (Dec (name, (Root (Const a, S) as __v)) as __d)) ->
          (match Array.sub (internal, a) with
           | Type a' ->
               T.UDec
                 (I.BDec
                    (name,
                      (a', (makeSub ((externalizeSpine S), (I.Shift n))))))
           | _ -> T.UDec (externalizeDec __d))
      | (n, UDec (__d)) -> T.UDec (externalizeDec __d)
      | (n, PDec (s, F)) -> T.PDec (s, (externalizeFor (n, F)))
    let rec externalizeFor =
      function
      | (n, World (W, F)) -> T.World (W, (externalizeFor (n, F)))
      | (n, All ((__d, Q), F)) ->
          T.All
            (((externalizeMDec (n, __d)), Q), (externalizeFor ((n + 1), F)))
      | (n, Ex ((__d, Q), F)) ->
          T.Ex (((externalizeDec __d), Q), (externalizeFor ((n + 1), F)))
      | (n, T.True) -> T.True
      | (n, And (__F1, __F2)) ->
          T.And ((externalizeFor (n, __F1)), (externalizeFor (n, __F2)))
    let rec externalizeMSpine =
      function
      | (n, T.Nil) -> T.Nil
      | (n, AppExp (__u, S)) ->
          T.AppExp ((externalizeExp __u), (externalizeMSpine (n, S)))
      | (n, AppBlock (B, S)) ->
          T.AppBlock ((externalizeBlock B), (externalizeMSpine (n, S)))
      | (n, AppPrg (P, S)) ->
          T.AppPrg ((externalizePrg (n, P)), (externalizeMSpine (n, S)))
    let rec externalizeCases =
      function
      | nil -> nil
      | (Psi, t, P)::O ->
          let n = I.ctxLength Psi in
          (::) ((externalizeMCtx Psi), (externalizeMSub (n, t)),
                 (externalizePrg (n, P)))
            externalizeCases O
    let rec externalizeMSub =
      function
      | (n, (Shift _ as t)) -> t
      | (n, Dot (F, t)) ->
          T.Dot ((externalizeMFront (n, F)), (externalizeMSub (n, t)))
    let rec externalizeMFront =
      function
      | (n, (Idx _ as F)) -> F
      | (n, Prg (P)) -> T.Prg (externalizePrg (n, P))
      | (n, Exp (__u)) -> T.Exp (externalizeExp __u)
      | (n, Block (B)) -> T.Block (externalizeBlock B)
      | (n, (T.Undef as F)) -> F
    let rec externalizeMCtx =
      function
      | I.Null -> I.Null
      | Decl (Psi, __d) ->
          I.Decl
            ((externalizeMCtx Psi), (externalizeMDec ((I.ctxLength Psi), __d)))
    let rec transTerm =
      function
      | Rtarrow (t1, t2) ->
          let (s1, c1) = transTerm t1 in
          let (s2, c2) = transTerm t2 in (((s1 ^ " -> ") ^ s2), (c1 @ c2))
      | Ltarrow (t1, t2) ->
          let (s1, c1) = transTerm t1 in
          let (s2, c2) = transTerm t2 in (((s1 ^ " <- ") ^ s2), (c1 @ c2))
      | D.Type -> ("type", nil)
      | Id s ->
          let qid = Names.Qid (nil, s) in
          (match Names.constLookup qid with
           | None -> (s, nil)
           | Some cid ->
               (match I.sgnLookup cid with
                | BlockDec _ -> ((s ^ "'"), nil)
                | _ -> (s, nil)))
      | Pi (__d, t) ->
          let (s1, c1) = transDec __d in
          let (s2, c2) = transTerm t in
          (((("{" ^ s1) ^ "}") ^ s2), (c1 @ c2))
      | Fn (__d, t) ->
          let (s1, c1) = transDec __d in
          let (s2, c2) = transTerm t in
          (((("[" ^ s1) ^ "]") ^ s2), (c1 @ c2))
      | App (t1, t2) ->
          let (s1, c1) = transTerm t1 in
          let (s2, c2) = transTerm t2 in (((s1 ^ " ") ^ s2), (c1 @ c2))
      | D.Omit -> ("_", nil)
      | Paren t -> let (s, c) = transTerm t in ((("(" ^ s) ^ ")"), c)
      | Of (t1, t2) ->
          let (s1, c1) = transTerm t1 in
          let (s2, c2) = transTerm t2 in (((s1 ^ ":") ^ s2), (c1 @ c2))
      | Dot (t, s2) ->
          let (s1, c1) = transTerm t in (((("o_" ^ s2) ^ " ") ^ s1), c1)
    let rec transDec (Dec (s, t)) =
      let (s', c) = transTerm t in (((s ^ ":") ^ s'), c)
    let rec transWorld =
      function
      | WorldIdent s ->
          let qid = Names.Qid (nil, s) in
          let cid =
            match Names.constLookup qid with
            | None ->
                raise
                  (Names.Error
                     (((^) "Undeclared label " Names.qidToString
                         (valOf (Names.constUndef qid)))
                        ^ "."))
            | Some cid -> cid in
          [cid]
      | Plus (W1, W2) -> (@) (transWorld W1) transWorld W2
      | Concat (W1, W2) -> (@) (transWorld W1) transWorld W2
      | Times (W) -> transWorld W
    let rec transFor' (Psi, __d) =
      let __g = I.Decl (I.Null, __d) in
      let JWithCtx (Decl (I.Null, __d'), ReconTerm.JNothing) =
        ReconTerm.reconWithCtx
          (Psi, (ReconTerm.jwithctx (__g, ReconTerm.jnothing))) in
      __d'
    let rec transFor =
      function
      | (Psi, D.True) -> T.True
      | (Psi, And (EF1, EF2)) ->
          T.And ((transFor (Psi, EF1)), (transFor (Psi, EF2)))
      | (Psi, Forall (__d, F)) ->
          let (__d'', nil) = transDec __d in
          let __d' = transFor' (Psi, (stringTodec __d'')) in
          T.All
            (((T.UDec __d'), T.Explicit), (transFor ((I.Decl (Psi, __d')), F)))
      | (Psi, Exists (__d, F)) ->
          let (__d'', nil) = transDec __d in
          let __d' = transFor' (Psi, (stringTodec __d'')) in
          T.Ex ((__d', T.Explicit), (transFor ((I.Decl (Psi, __d')), F)))
      | (Psi, ForallOmitted (__d, F)) ->
          let (__d'', nil) = transDec __d in
          let __d' = transFor' (Psi, (stringTodec __d'')) in
          T.All
            (((T.UDec __d'), T.Implicit), (transFor ((I.Decl (Psi, __d')), F)))
      | (Psi, ExistsOmitted (__d, F)) ->
          let (__d'', nil) = transDec __d in
          let __d' = transFor' (Psi, (stringTodec __d'')) in
          T.Ex ((__d', T.Implicit), (transFor ((I.Decl (Psi, __d')), F)))
      | (Psi, World (W, EF)) ->
          T.World ((T.Worlds (transWorld W)), (transFor (Psi, EF)))
    let rec stringToterm s =
      let f = LS.expose (L.lexStream (TextIO.openString s)) in
      let (t, f') = ParseTerm.parseTerm' f in let r2 = checkEOF f' in t
    let rec head =
      function
      | Head s -> s
      | AppLF (H, _) -> head H
      | AppMeta (H, _) -> head H
    let rec lamClosure =
      function
      | (All ((__d, _), F), P) -> T.Lam (__d, (lamClosure (F, P)))
      | (World (_, F), P) -> lamClosure (F, P)
      | (Ex _, P) -> P
    let rec exists =
      function
      | (c, []) -> raise (Error "Current world is not subsumed")
      | (c, c'::cids) -> if c = c' then () else exists (c, cids)
    let rec subsumed =
      function
      | ([], cids') -> ()
      | (c::cids, cids') -> (exists (c, cids'); subsumed (cids, cids'))
    let rec checkForWorld =
      function
      | (World ((Worlds cids as W), F), t', Worlds cids') ->
          let _ = subsumed (cids', cids) in (F, t', W)
      | FtW -> FtW
    let rec dotn =
      function | (t, 0) -> t | (t, n) -> I.dot1 (dotn (t, (n - 1)))
    let rec append =
      function
      | (Psi, I.Null) -> Psi
      | (Psi, Decl (Psi', __d)) -> I.Decl ((append (Psi, Psi')), __d)
    let rec parseTerm (Psi, (s, __v)) =
      let (term', c) = transTerm s in
      let term = stringToterm term' in
      let JOf ((__u, occ), (_, _), __l) =
        ReconTerm.reconWithCtx
          ((T.coerceCtx Psi), (ReconTerm.jof' (term, __v))) in
      __u
    let rec parseDec (Psi, s) =
      let (dec', c) = transDec s in
      let dec = stringTodec dec' in
      let JWithCtx (Decl (I.Null, __d), ReconTerm.JNothing) =
        ReconTerm.reconWithCtx
          ((T.coerceCtx Psi),
            (ReconTerm.jwithctx ((I.Decl (I.Null, dec)), ReconTerm.jnothing))) in
      let Dec (Some n, _) = __d in __d
    let rec transDecs =
      function
      | (Psi, D.Empty, sc, W) -> sc (Psi, W)
      | (Psi, FormDecl (FormD, __Ds), sc, W) ->
          transForDec (Psi, FormD, __Ds, sc, W)
      | (Psi, ValDecl (ValD, __Ds), sc, W) ->
          transValDec (Psi, ValD, __Ds, sc, W)
      | (Psi, NewDecl (__d, __Ds), sc, W) ->
          let __d' = T.UDec (parseDec (Psi, __d)) in
          T.Let
            ((T.PDec (None, T.True)),
              (T.Lam (__d', (transDecs ((I.Decl (Psi, __d')), __Ds, sc, W)))),
              (T.Var 1))
      | _ ->
          raise
            (Error
               "Constant declaration must be followed by a constant definition")
    let rec lookup =
      function
      | (I.Null, n, s) -> raise (Error ("Undeclared constant " ^ s))
      | (Decl (__g, PDec (None, _)), n, s) -> lookup (__g, (n + 1), s)
      | (Decl (__g, UDec _), n, s) -> lookup (__g, (n + 1), s)
      | (Decl (__g, PDec (Some s', F)), n, s) ->
          if s = s'
          then (n, (T.forSub (F, (T.Shift n))))
          else lookup (__g, (n + 1), s)
    let rec transHead =
      function
      | (Psi, Head s, args) ->
          let (n, F) = lookup (Psi, 1, s) in
          transHead' ((F, T.id), I.Nil, args)
      | (Psi, AppLF (h, t), args) -> transHead (Psi, h, (t :: args))
    let rec transHead' =
      function
      | ((World (_, F), s), S, args) -> transHead' ((F, s), S, args)
      | ((All ((UDec (Dec (_, __v)), T.Implicit), __F'), s), S, args) ->
          let x =
            I.newEVar
              ((I.Decl (I.Null, I.NDec)), (I.EClo (__v, (T.coerceSub s)))) in
          transHead' ((__F', (T.Dot ((T.Exp x), s))), (I.App (x, S)), args)
      | ((All ((UDec (Dec (_, __v)), T.Explicit), __F'), s), S, t::args) ->
          let (term', c) = transTerm t in
          let term = stringToterm term' in
          let JOf ((__u, occ), (_, _), __l) =
            ReconTerm.reconWithCtx
              (I.Null,
                (ReconTerm.jof' (term, (I.EClo (__v, (T.coerceSub s)))))) in
          transHead' ((__F', (T.Dot ((T.Exp __u), s))), (I.App (__u, S)), args)
      | ((F, s), S, nil) -> ((F, s), S)
    let rec spineToSub =
      function
      | ((I.Nil, _), s') -> s'
      | ((App (__u, S), t), s') ->
          T.Dot ((T.Exp (I.EClo (__u, t))), (spineToSub ((S, t), s')))
    let rec transPattern =
      function
      | (p, (Ex ((Dec (_, __v), T.Implicit), __F'), s)) ->
          transPattern
            (p,
              (__F',
                (T.Dot
                   ((T.Exp
                       (I.EVar
                          ((ref None), I.Null, (I.EClo (__v, (T.coerceSub s))),
                            (ref nil)))), s))))
      | (PatInx (t, p), (Ex ((Dec (_, __v), T.Explicit), __F'), s)) ->
          let (term', c) = transTerm t in
          let term = stringToterm term' in
          let JOf ((__u, occ), (_, _), __l) =
            ReconTerm.reconWithCtx
              (I.Null,
                (ReconTerm.jof' (term, (I.EClo (__v, (T.coerceSub s)))))) in
          T.PairExp (__u, (transPattern (p, (__F', (T.Dot ((T.Exp __u), s))))))
      | (D.PatUnit, (F, s)) -> T.Unit
    let rec transFun1 =
      function
      | (Psi, (s', F), FunDecl (Fun (eH, eP), __Ds), sc, W) ->
          let s = head eH in
          let _ =
            if s = s'
            then ()
            else
              raise
                (Error
                   "Function defined is different from function declared.") in
          transFun2
            (Psi, (s, F), (D.FunDecl ((D.Bar (eH, eP)), __Ds)), sc,
              (function | __Cs -> T.Case (T.Cases __Cs)), W)
      | (Psi, (s', F), FunDecl (FunAnd (eH, eP), __Ds), sc, W) ->
          raise (Error "Mutual recursive functions not yet implemented")
      | _ -> raise (Error "Function declaration expected")
    let rec transFun2 =
      function
      | (Psi, (s, F), FunDecl (Bar (eH, eP), __Ds), sc, k, W) ->
          transFun3 (Psi, (s, F), eH, eP, __Ds, sc, k, W)
      | (Psi, (s, F), __Ds, sc, k, W) ->
          let __d = T.PDec ((Some s), F) in
          let __P' = T.Rec (__d, (lamClosure (F, (k nil)))) in (__P', __Ds)
    let rec transFun3 (Psi, (s, F), eH, eP, __Ds, sc, k, W) =
      let _ =
        if (head eH) <> s
        then raise (Error "Functions don't all have the same name")
        else () in
      let _ = Names.varReset I.Null in
      let Psi0 = I.Decl (Psi, (T.PDec ((Some s), F))) in
      let ((__F', t'), S) = transHead (Psi0, eH, nil) in
      let (Psi', S') = Abstract.abstractSpine (S, I.id) in
      let Psi'' = append (Psi0, (T.embedCtx Psi')) in
      let m0 = I.ctxLength Psi0 in
      let m' = I.ctxLength Psi' in
      let t0 = dotn ((I.Shift m0), m') in
      let t'' = spineToSub ((S', t0), (T.Shift m')) in
      let P = transProgI (Psi'', eP, (__F', t'), W) in
      transFun2
        (Psi, (s, F), __Ds, sc, (function | __Cs -> k ((Psi'', t'', P) :: __Cs)),
          W)
    let rec transForDec (Psi, Form (s, eF), __Ds, sc, W) =
      let __g = Names.ctxName (T.coerceCtx Psi) in
      let F = transFor (__g, eF) in
      let World (W, __F') as __F'' = T.forSub (F, T.id) in
      let _ = TomegaTypeCheck.checkFor (Psi, __F'') in
      let (P, __Ds') = transFun1 (Psi, (s, __F'), __Ds, sc, W) in
      let __d = T.PDec ((Some s), __F'') in
      T.Let
        (__d, (T.Box (W, P)),
          (transDecs ((I.Decl (Psi, __d)), __Ds', (function | __P' -> sc __P'), W)))
    let rec transValDec (Psi, Val (EPat, eP, eFopt), __Ds, sc, W) =
      let (P, (__F', t')) =
        match eFopt with
        | None -> transProgS (Psi, eP, W, nil)
        | Some eF ->
            let __F' = transFor ((T.coerceCtx Psi), eF) in
            let __P' = transProgIN (Psi, eP, __F', W) in (__P', (__F', T.id)) in
      let __F'' = T.forSub (__F', t') in
      let Pat = transPattern (EPat, (__F', t')) in
      let __d = T.PDec (None, __F'') in
      let (Psi', Pat') = Abstract.abstractTomegaPrg Pat in
      let m = I.ctxLength Psi' in
      let t = T.Dot ((T.Prg Pat'), (T.Shift m)) in
      let Psi'' = append (Psi, Psi') in
      let __P'' = transDecs (Psi'', __Ds, sc, W) in
      T.Let (__d, P, (T.Case (T.Cases [(Psi'', t, __P'')])))
    let rec transProgI (Psi, eP, Ft, W) =
      transProgIN (Psi, eP, (T.forSub Ft), W)
    let rec transProgIN =
      function
      | (Psi, D.Unit, T.True, W) -> T.Unit
      | (Psi, (Inx (s, EP) as P), Ex ((Dec (_, __v), T.Explicit), __F'), W) ->
          let __u = parseTerm (Psi, (s, __v)) in
          let __P' = transProgI (Psi, EP, (__F', (T.Dot ((T.Exp __u), T.id))), W) in
          T.PairExp (__u, __P')
      | (Psi, Let (eDs, eP), F, W) ->
          transDecs
            (Psi, eDs,
              (function
               | (Psi', W') ->
                   transProgI
                     (Psi', eP,
                       (F,
                         (T.Shift ((-) (I.ctxLength Psi') I.ctxLength Psi))),
                       W')), W)
      | (Psi, Choose (eD, eP), F, W) ->
          let __d' = parseDec (Psi, eD) in
          let Psi'' = I.Decl (Psi, (T.UDec __d')) in
          T.Choose
            (T.Lam
               ((T.UDec __d'), (transProgI (Psi'', eP, (F, (T.Shift 1)), W))))
      | (Psi, New (nil, eP), F, W) -> transProgIN (Psi, eP, F, W)
      | (Psi, New (eD::eDs, eP), F, W) ->
          let __d' = parseDec (Psi, eD) in
          let Psi'' = I.Decl (Psi, (T.UDec __d')) in
          T.New
            (T.Lam
               ((T.UDec __d'),
                 (transProgI
                    (Psi'', (D.New ((eD :: eDs), eP)), (F, (T.Shift 1)), W))))
      | (Psi, (AppTerm (EP, s) as P), F, W) ->
          let (__P', (__F', _)) = transProgS (Psi, P, W, nil) in
          let () = () in __P'
    let rec transProgS =
      function
      | (Psi, D.Unit, W, args) -> (T.Unit, (T.True, T.id))
      | (Psi, AppTerm (EP, s), W, args) ->
          transProgS (Psi, EP, W, (s :: args))
      | (Psi, Const name, W, args) ->
          let (n, F) = lookup (Psi, 1, name) in
          let (S, __Fs') = transProgS' (Psi, (F, T.id), W, args) in
          ((T.Redex ((T.Var n), S)), __Fs')
      | (Psi, Choose (eD, eP), W, args) ->
          let __d' = parseDec (Psi, eD) in
          let (P, (F, t)) =
            transProgS ((I.Decl (Psi, (T.UDec __d'))), eP, W, args) in
          ((T.Choose (T.Lam ((T.UDec __d'), P))), (F, t))
      | (Psi, New (nil, eP), W, args) -> transProgS (Psi, eP, W, args)
      | (Psi, New (eD::eDs, eP), W, args) ->
          let __d' = parseDec (Psi, eD) in
          let (P, (F, t)) =
            transProgS
              ((I.Decl (Psi, (T.UDec __d'))), (D.New (eDs, eP)), W, args) in
          let UDec (__d'') = externalizeMDec ((I.ctxLength Psi), (T.UDec __d')) in
          let (B, _) = T.deblockify (I.Decl (I.Null, __d'')) in
          let __F' = TA.raiseFor (B, (F, (T.coerceSub t))) in
          ((T.New (T.Lam ((T.UDec __d'), P))), (__F', T.id))
    let rec transProgS' =
      function
      | (Psi, (World (_, F), s), W, args) ->
          transProgS' (Psi, (F, s), W, args)
      | (Psi, (All ((UDec (Dec (_, __v)), T.Implicit), __F'), s), W, args) ->
          let __g = T.coerceCtx Psi in
          let x = I.newEVar (__g, (I.EClo (__v, (T.coerceSub s)))) in
          let (S, __Fs') =
            transProgS' (Psi, (__F', (T.Dot ((T.Exp x), s))), W, args) in
          ((T.AppExp ((Whnf.normalize (x, I.id)), S)), __Fs')
      | (Psi, (All ((UDec (Dec (_, __v)), T.Explicit), __F'), s), W, t::args) ->
          let __u = parseTerm (Psi, (t, (I.EClo (__v, (T.coerceSub s))))) in
          let (S, __Fs') =
            transProgS' (Psi, (__F', (T.Dot ((T.Exp __u), s))), W, args) in
          ((T.AppExp (__u, S)), __Fs')
      | (Psi, (F, s), _, nil) -> (T.Nil, (F, s))
    let rec transProgram (__Ds) =
      transDecs (I.Null, __Ds, (function | (Psi, W) -> T.Unit), (T.Worlds []))
    (* Invariant   for each cid which has been internalize out of a block,
       internal(cid) = Const(n, i), where n is the number of some variables and
       i is the projection index
       for each type family
       internal(cid) = Type (cid'), where cid' is the orginial type family.
    *)
    (* checkEOF f = r

      Invariant:
      If   f is the end of stream
      then r is a region

      Side effect: May raise Parsing.Error
    *)
    (* region information useless
                                                   since it only refers to string --cs *)
    (* Note that this message is inapplicable when we use
            checkEOF in stringToterm --rf *)
    (* stringToDec s = dec

       Invariant:
       If   s is a string representing a declaration,
       then dec is the result of parsing it
       otherwise Parsing.error is raised.
    *)
    (* below use region arithmetic --cs !!!  *)
    (* stringToWorlds s = W

       Invariant:
       If   s is a string representing an expression,
       then W is the result of parsing it
       otherwise Parsing.error is raised.
    *)
    (* closure (__g, __v) = __v'

       Invariant:
       {__g}__v = __v'
    *)
    (* internalizeBlock  (n, __g, Vb, S) (L2, s) = ()

       Invariant:
       If   |- __g ctx                the context of some variables
       and  __g |- Vb :  type         the type of the block
       and  __g |- L1, L2 decs
       and  G1, L1 |- L2 decs       block declarations still to be traversed
       and  __g, b:Vb |- s : G1, L1
       and  n is the current projection
       then internalizeBlock adds new declarations into the signature that
              correspond to the block declarations.
    *)
    (* __g, B |- __v' : type *)
    (* __g |- {B} __v' : type *)
    (* makeSpine (n, __g, S) = S'

       Invariant:
       If  G0 = __g, __g'
       and |__g'| = n
       and G0 |- S : __v >> __v'   for some __v, __v'
       then S' extends S
       and G0 |- S' : __v >> type.
    *)
    (* interalizeCondec condec = ()

       Invariant:
       If   condec is a condec,
       then all pi declarations are internalized if condec was a blockdec
    *)
    (* sigToCtx () = ()

       Invariant:
       __g is the internal representation of the global signature
       It converts every block declaration to a type family (stored in the global
       signature) and a list of declarations.
    *)
    (* we might want to save max, here to restore the original
                 signature after parsing is over  --cs Thu Apr 17 09:46:29 2003 *)
    (* Externalization *)
    (* Check : the translators hould only generate normal forms. Fix during the next pass --cs Thu Apr 17 17:06:24 2003 *)
    (* PClo should not be possible, since by invariant, parser
         always generates a program in normal form  --cs Thu Apr 17 16:56:07 2003
      *)
    (* Translation starts here *)
    (*      | transTerm (D.Dot (D.Id s1, s2)) =
        ("PROJ#" ^ s1 ^ "#" ^ s2, nil)
      | transTerm (D.Dot (D.Paren (D.Of (D.Id s1, t)), s2)) =
        ("PROJ#" ^ s1 ^ "#" ^ s2, [(s1, t)])
*)
    (* We should use the worlds we have defined in Tomega, but this
              is not good enough, because worlds are not defined
              by a regualar expression.  Therefore this is a patch *)
    (* transFor (ExtDctx, ExtF) = (Psi, F)

       Invariant:
       If   |- ExtDPsi extdecctx
       and  |- ExtF extfor
       then |- Psi <= ExtDPsi
       and  Psi |- F <= ExtF
    *)
    (* stringToTerm s = __u

       Invariant:
       If   s is a string representing an expression,
       then __u is the result of parsing it
       otherwise Parsing.error is raised.
    *)
    (* head (dH) = n

       Invariant:
       n is the name of the function head dH
    *)
    (* lamClosure (F, P) = __P'

       Invariant:
       If   . |- F formula
       and  . |- F = all D1. ... all Dn. __F' formula
         for  . |- __F' formula that does not commence with a universal quantifier
       and . |- P :: __F'
       then __P' = lam D1 ... lam Dn P
    *)
    (* check that W is at least as large as W' *)
    (* dotn (t, n) = t'

       Invariant:
       If   Psi0 |- t : Psi
       and  |__g| = n   for any __g
       then Psi0, __g[t] |- t : Psi, __g
    *)
    (* append (Psi1, Psi2) = Psi3

       Invariant:
       If   |- Psi1 ctx
       and  |- Psi2 ctx
       then |- Psi3 = Psi1, Psi2 ctx
    *)
    (* transDecs ((Psi, t), dDs, sc, W) = x

       Invariant:
       If   . |- t :: Psi
       and  Psi |- dDs decs
       and  W is the valid world
       and  sc is the success continuation that expects
            as input: (Psi', env')
                      where Psi' is the context after translating dDs
                      and   Psi' |- env' environment
                            are all variables introduced until this point
            as output: anything.
       then eventually x = ().     --cs
    *)
    (*          T.Let (T.PDec (None, T.True), T.Lam (__d', transDecs (I.Decl (Psi, __d'), __Ds, sc, W)), T.Unit) *)
    (* T.True is not right! -- cs Sat Jun 28 11:43:30 2003  *)
    (* transHead (__g, T, S) = (__F', t')

       Invariant:
       If   __g |- T : F
       and  __g |- S : world{W}all{__g'}__F' >> __F'
       then __g |- t' : __g'
    *)
    (* spineToSub ((S, t), s) = s'

       Invariant:
       If  Psi' |- S spine
       and Psi'' |- t: Psi'
       and Psi'' |- s : Psi'''
       then  Psi'' |- s' : Psi''', Psi''''
    *)
    (* other cases should be impossible by invariant
                                         F should be F.True
                                         --cs Sun Mar 23 10:38:57 2003 *)
    (* transFun1 ((Psi, env), dDs, sc, W) = x

       Invariant:
       If   Psi |- dDs :: Psi'
       and  Psi |- env environment
       and  the top declaration is a function declaration
       and  W is the valid world
       and  sc is the success continuation that expects
            as input: (Psi', env')
                      where Psi' is the context after translating dDs
                      and   Psi' |- env' environment
                            are all variables introduced until this point
            as output: anything.
       then eventually x = ().     --cs
    *)
    (* transFun2 ((Psi, env), s, dDs, sc, k, W) = x

       Invariant:
       If   Psi |- dDs :: Psi'
       and  Psi |- env environment
       and  s is the name of the function currently being translated
       and  the top declaration is a function declaration
       and  the top declaration is a function declaration
       and  W is the valid world
       and  sc is the success continuation that expects
            as input: (Psi', env')
                      where Psi' is the context after translating dDs
                      and   Psi' |- env' environment
                            are all variables introduced until this point
            as output: anything.
       and  k is the continuation that expects
            as input: __Cs a list of cases
            as ouput: A program P that corresponds to the case list __Cs
       then eventually x = ().     --cs
    *)
    (* transFun3 ((Psi, env), s, eH, eP, __Ds, sc, k, W) = x

       Invariant:
       If   Psi |- dDs :: Psi'
       and  Psi |- env environment
       and  s is the name of the function currently being translated
       and  eH is the head of the function
       and  eP its body
       and  W is the valid world
       and  __Ds are the remaining declarations
       and  sc is the success continuation that expects
            as input: (Psi', env')
                      where Psi' is the context after translating dDs
                      and   Psi' |- env' environment
                            are all variables introduced until this point
            as output: anything.
       and  k is the continuation that expects
            as input: __Cs a list of cases
            as ouput: A program P that corresponds to the case list __Cs
       then eventually x = ().     --cs
    *)
    (*                val __F' = T.forSub (F, t) *)
    (* |Psi''| = m0 + m' *)
    (* Psi0, Psi'[^m0] |- t0 : Psi' *)
    (*        val t1 = T.Dot (T.Prg (T.Root (T.Var (m'+1), T.Nil)), T.Shift (m'))    BUG !!!! Wed Jun 25 11:23:13 2003 *)
    (* Psi0, Psi'[^m0] |- t1 : F[^m0]  *)
    (*        val _ = print (TomegaPrint.forToString (Names.ctxName (T.coerceCtx Psi''), myF) ^ "\n") *)
    (* transForDec ((Psi, env), eDf, dDs, sc, W) = x

       Invariant:
       If   Psi |- dDs :: Psi'
       and  Psi |- env environment
       and  Psi |- eDf is a theorem declaration.
       and  W is the valid world
       and  dDs are the remaining declarations
       and  sc is the success continuation that expects
            as input: (Psi', env')
                      where Psi' is the context after translating dDs
                      and   Psi' |- env' environment
                            are all variables introduced until this point
            as output: anything.
       then eventually x = ().     --cs
    *)
    (*        val _ = print s
          val _ = print " :: "
          val _ = print (TomegaPrint.forToString (T.embedCtx __g, __F'') ^ "\n") *)
    (* transValDec ((Psi, env), dDv, dDs, sc, W) = x

       Invariant:
       If   Psi |- dDs :: Psi'
       and  Psi |- env environment
       and  Psi |- dDv value declaration
       and  W is the valid world
       and  dDs are the remaining declarations
       and  sc is the success continuation that expects
            as input: (Psi', env')
                      where Psi' is the context after translating dDs
                      and   Psi' |- env' environment
                            are all variables introduced until this point
            as output: anything.
       then eventually x = ().     --cs
    *)
    (*        val t = T.Dot (T.Prg Pat', T.id)  was --cs Tue Jun 24 13:04:55 2003 *)
    (* transProgS ((Psi, env), ExtP, F, W) = P
       transProgI ((Psi, env), ExtP, W) = (P, F)
       Invariant:
       If   ExtP contains free variables among (Psi, env)
       and  ExtP is a program defined in (Psi, env)
       and  W is a world
       and  Exists Psi |- F : formula
       then Psi |- P :: F
    *)
    (* check that F == __F' *)
    (*      | transProgIN ((Psi, env), D.Pair (EP1, EP2), T.And (__F1, __F2), W) =
        let
          val __P1 = transProgIN ((Psi, env), EP1, __F1, W)
          val __P2 = transProgIN ((Psi, env), EP2, __F2, W)
        in
          T.PairPrg (__P1, __P2)
        end
      | transProgIN ((Psi, env), P as D.AppProg (EP1, EP2), F, W) =
        let
          val (__P', (__F', _)) = transProgS ((Psi, env), P, W)
          val ()  = ()    check that F == __F' *)
    (* check that F == __F' *)
    (* check that F == __F' *)
    (*      | transProgIN (Psi, D.Lam (s, EP)) =
        let
          val dec = stringTodec s
          val (I.Decl (Psi, (__d, _, _)), P, __F') = transProgI (I.Decl (ePsi, dec), EP)
        in
          (Psi, T.Lam (T.UDec __d, P), T.All (__d, __F'))
        end
*)
    (* is this the right starting point --cs *)
    (*         val lemma = T.lemmaName name
           val F = T.lemmaFor lemma *)
    (* bug: forgot to raise F[t] to __F' --cs Tue Jul  1 10:49:52 2003 *)
    (*        val x = I.EVar (ref None, I.Null, I.EClo (__v, T.coerceSub s), ref nil) *)
    (*        val (__F'', s'', _) = checkForWorld (__F', T.Dot (T.Exp __u, s), W) *)
    (*
     | transProgS ((Psi, env), D.Pair (EP1, EP2), W) =
        let
          val (__P1, (__F1, t1)) = transProgS ((Psi, env), EP1, W)
          val (__P2, (__F2, t2)) = transProgS ((Psi, env), EP2, W)
        in
          (T.PairPrg (__P1, __P2), (T.And (__F1, __F2), T.comp (t1, t2)))
        end

     | transProgS ((Psi, env), D.AppProg (EP1, EP2), W) =
        let
          val (__P1, (T.And (__F1, __F2), t)) = transProgS ((Psi, env), EP1, W)
          val __P2 = transProgIN ((Psi, env), EP2, T.FClo (__F1, t), W)
          val (__F'', t'', W) = checkForWorld (__F2, t, W)
        in
          (T.Redex (__P1, T.AppPrg (__P2, T.Nil)), (__F'', t''))
        end


      | transProgS ((Psi, env), P as D.Inx (s, EP), W) =  raise Error "Cannot infer existential types"

      | transProgS ((Psi, env), D.Lam (s, EP), W) =
        let
          val dec = stringTodec s
          val (I.Decl (Psi', (__d, _, _)), P, F) = transProgI (I.Decl (Psi, dec), EP)
          val (__F', t', _) = checkForWorld (F, T.id, W)
        in
          (T.Lam (T.UDec __d, P), (T.All (__d, __F'), t'))
        end
*)
    (*        val _ = print (Print.expToString (__g, __u) ^ "\n") *)
    (* is this the right starting point --cs *)
    (* transProgram __Ds = P

       Invariant:
       If __Ds is a list of declarations then P is
       the translated program, that does not do anything
    *)
    let transFor = function | F -> let __F' = transFor (I.Null, F) in __F'
    (*    val makePattern = makePattern *)
    (*    val transPro = fn P => let val (__P', _) = transProgS ((I.Null, []), P, T.Worlds []) in __P' end *)
    let transDecs = transProgram
    let internalizeSig = internalizeSig
    let externalizePrg = function | P -> externalizePrg (0, P)
  end;;
