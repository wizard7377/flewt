
module type TRANS  =
  sig
    module DextSyn :
    ((DEXTSYN)(* Translator from Delphin external syntax to Delphin internal syntax *)
    (* Author: Richard Fontana, Carsten Schuermann *))
    exception Error of string 
    val internalizeSig : unit -> unit
    val transFor :
      DextSyn.__Form -> ((Tomega.__For)(* IntSyn.dctx * *))
    val transDecs : DextSyn.__Decs -> Tomega.__Prg
    val externalizePrg : Tomega.__Prg -> Tomega.__Prg
  end;;




module Trans(Trans:sig
                     module DextSyn' :
                     ((DEXTSYN)(* Translator from Delphin external syntax to Delphin internal syntax *)
                     (* Author:  Carsten Schuermann *))
                   end) =
  struct
    module DextSyn = ((DextSyn')(* : TRANS *))
    module D = DextSyn'
    module L = Lexer
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
        | NONE -> ReconTerm.dec0 (x, r2)
        | SOME y -> ReconTerm.dec (x, y, r2) in
      dec
    let rec stringToblocks s =
      let f = LS.expose (L.lexStream (TextIO.openString s)) in
      let (dl, f') = ParseTerm.parseCtx' f in dl
    let rec stringToWorlds s =
      let f = LS.expose (L.lexStream (TextIO.openString s)) in
      let (t, f') = ParseTerm.parseQualIds' f in let r2 = checkEOF f' in t
    let rec closure =
      function
      | (I.Null, V) -> V
      | (Decl (g, D), V) -> closure (g, (I.Pi ((D, I.Maybe), V)))
    let rec internalizeBlock arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (_, (nil, _)) -> ()
      | ((n, g, Vb, S), ((Dec (SOME name, V))::L2, s)) ->
          let name' = "o_" ^ name in
          let V1 = I.EClo (V, s) in
          let V2 = I.Pi (((I.Dec (NONE, Vb)), I.Maybe), V1) in
          let V3 = closure (g, V2) in
          let m = I.ctxLength g in
          let condec = I.ConDec (name', NONE, m, I.Normal, V3, I.Type) in
          let _ = TypeCheck.check (V3, (I.Uni I.Type)) in
          let _ =
            if (!Global.chatter) >= 4
            then print ((Print.conDecToString condec) ^ "\n")
            else () in
          let cid = I.sgnAdd condec in
          let _ = Names.installConstName cid in
          let _ = Array.update (internal, cid, (Const (m, n))) in
          internalizeBlock ((n + 1), g, Vb, S)
            (L2, (I.Dot ((I.Exp (I.Root ((I.Const cid), S))), s)))
    let rec makeSpine =
      function
      | (_, I.Null, S) -> S
      | (n, Decl (g, D), S) ->
          makeSpine
            ((n + 1), g, (I.App ((I.Root ((I.BVar (n + 1)), I.Nil)), S)))
    let rec internalizeCondec =
      function
      | (cid, ConDec _) -> ()
      | (cid, ConDef _) -> ()
      | (cid, AbbrevDef _) -> ()
      | (cid, BlockDec (name, _, Gsome, Lpi)) ->
          let V' = closure (Gsome, (I.Uni I.Type)) in
          let C = I.ConDec ((name ^ "'"), NONE, 0, I.Normal, V', I.Kind) in
          let a = I.sgnAdd C in
          let _ = Array.update (internal, a, (Type cid)) in
          let _ = Names.installConstName a in
          let S = makeSpine (0, Gsome, I.Nil) in
          let Vb = I.Root ((I.Const a), S) in
          let S' = makeSpine (0, (I.Decl (Gsome, (I.Dec (NONE, Vb)))), I.Nil) in
          internalizeBlock (1, Gsome, Vb, S') (Lpi, I.shift)
      | (cid, SkoDec _) -> ()
    let rec internalizeSig () =
      let (max, _) = I.sgnSize () in
      let internalizeSig' n =
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
      | (App (U, S), s) -> makeSub (S, (I.Dot ((I.Exp U), s)))
    let rec externalizeExp' =
      function
      | Uni _ as U -> U
      | Pi ((D, DP), U) ->
          I.Pi (((externalizeDec D), DP), (externalizeExp U))
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
      | Redex (U, S) -> I.Redex ((externalizeExp U), (externalizeSpine S))
      | Lam (D, U) -> I.Lam ((externalizeDec D), (externalizeExp U))
    let rec externalizeExp (U) = externalizeExp' (Whnf.normalize (U, I.id))
    let rec externalizeBlock (Bidx _ as B) = B
    let rec externalizeDec (Dec (name, V)) = I.Dec (name, (externalizeExp V))
    let rec externalizeSpine =
      function
      | I.Nil -> I.Nil
      | App (U, S) -> I.App ((externalizeExp U), (externalizeSpine S))
    let rec externalizeSub =
      function
      | Shift n as s -> s
      | Dot (F, s) -> I.Dot ((externalizeFront F), (externalizeSub s))
    let rec externalizeFront =
      function
      | Idx _ as F -> F
      | Exp (U) -> I.Exp (externalizeExp U)
      | Block (B) -> I.Block (externalizeBlock B)
      | I.Undef as F -> F
    let rec externalizePrg =
      function
      | (n, Lam (D, P)) ->
          T.Lam ((externalizeMDec (n, D)), (externalizePrg ((n + 1), P)))
      | (n, New (P)) -> T.New (externalizePrg (n, P))
      | (n, Box (W, P)) -> T.Box (W, (externalizePrg (n, P)))
      | (n, Choose (P)) -> T.Choose (externalizePrg (n, P))
      | (n, PairExp (U, P)) ->
          T.PairExp ((externalizeExp U), (externalizePrg (n, P)))
      | (n, PairPrg (P1, P2)) ->
          T.PairPrg ((externalizePrg (n, P1)), (externalizePrg (n, P2)))
      | (n, PairBlock (B, P)) ->
          T.PairBlock ((externalizeBlock B), (externalizePrg (n, P)))
      | (n, T.Unit) -> T.Unit
      | (n, Var k) -> T.Var k
      | (n, Const c) -> T.Const c
      | (n, Redex (P, S)) ->
          T.Redex ((externalizePrg (n, P)), (externalizeMSpine (n, S)))
      | (n, Rec (D, P)) ->
          T.Rec ((externalizeMDec (n, D)), (externalizePrg ((n + 1), P)))
      | (n, Case (Cases (O))) -> T.Case (T.Cases (externalizeCases O))
      | (n, Let (D, P1, P2)) ->
          T.Let
            ((externalizeMDec (n, D)), (externalizePrg (n, P1)),
              (externalizePrg ((n + 1), P2)))
    let rec externalizeMDec =
      function
      | (n, UDec (Dec (name, (Root (Const a, S) as V)) as D)) ->
          (match Array.sub (internal, a) with
           | Type a' ->
               T.UDec
                 (I.BDec
                    (name,
                      (a', (makeSub ((externalizeSpine S), (I.Shift n))))))
           | _ -> T.UDec (externalizeDec D))
      | (n, UDec (D)) -> T.UDec (externalizeDec D)
      | (n, PDec (s, F)) -> T.PDec (s, (externalizeFor (n, F)))
    let rec externalizeFor =
      function
      | (n, World (W, F)) -> T.World (W, (externalizeFor (n, F)))
      | (n, All ((D, Q), F)) ->
          T.All
            (((externalizeMDec (n, D)), Q), (externalizeFor ((n + 1), F)))
      | (n, Ex ((D, Q), F)) ->
          T.Ex (((externalizeDec D), Q), (externalizeFor ((n + 1), F)))
      | (n, T.True) -> T.True
      | (n, And (F1, F2)) ->
          T.And ((externalizeFor (n, F1)), (externalizeFor (n, F2)))
    let rec externalizeMSpine =
      function
      | (n, T.Nil) -> T.Nil
      | (n, AppExp (U, S)) ->
          T.AppExp ((externalizeExp U), (externalizeMSpine (n, S)))
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
      | (n, Exp (U)) -> T.Exp (externalizeExp U)
      | (n, Block (B)) -> T.Block (externalizeBlock B)
      | (n, (T.Undef as F)) -> F
    let rec externalizeMCtx =
      function
      | I.Null -> I.Null
      | Decl (Psi, D) ->
          I.Decl
            ((externalizeMCtx Psi), (externalizeMDec ((I.ctxLength Psi), D)))
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
           | NONE -> (s, nil)
           | SOME cid ->
               (match I.sgnLookup cid with
                | BlockDec _ -> ((s ^ "'"), nil)
                | _ -> (s, nil)))
      | Pi (D, t) ->
          let (s1, c1) = transDec D in
          let (s2, c2) = transTerm t in
          (((("{" ^ s1) ^ "}") ^ s2), (c1 @ c2))
      | Fn (D, t) ->
          let (s1, c1) = transDec D in
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
            | NONE ->
                raise
                  (Names.Error
                     (((^) "Undeclared label " Names.qidToString
                         (valOf (Names.constUndef qid)))
                        ^ "."))
            | SOME cid -> cid in
          [cid]
      | Plus (W1, W2) -> (@) (transWorld W1) transWorld W2
      | Concat (W1, W2) -> (@) (transWorld W1) transWorld W2
      | Times (W) -> transWorld W
    let rec transFor' (Psi, D) =
      let g = I.Decl (I.Null, D) in
      let JWithCtx (Decl (I.Null, D'), ReconTerm.JNothing) =
        ReconTerm.reconWithCtx
          (Psi, (ReconTerm.jwithctx (g, ReconTerm.jnothing))) in
      D'
    let rec transFor =
      function
      | (Psi, D.True) -> T.True
      | (Psi, And (EF1, EF2)) ->
          T.And ((transFor (Psi, EF1)), (transFor (Psi, EF2)))
      | (Psi, Forall (D, F)) ->
          let (D'', nil) = transDec D in
          let D' = transFor' (Psi, (stringTodec D'')) in
          T.All
            (((T.UDec D'), T.Explicit), (transFor ((I.Decl (Psi, D')), F)))
      | (Psi, Exists (D, F)) ->
          let (D'', nil) = transDec D in
          let D' = transFor' (Psi, (stringTodec D'')) in
          T.Ex ((D', T.Explicit), (transFor ((I.Decl (Psi, D')), F)))
      | (Psi, ForallOmitted (D, F)) ->
          let (D'', nil) = transDec D in
          let D' = transFor' (Psi, (stringTodec D'')) in
          T.All
            (((T.UDec D'), T.Implicit), (transFor ((I.Decl (Psi, D')), F)))
      | (Psi, ExistsOmitted (D, F)) ->
          let (D'', nil) = transDec D in
          let D' = transFor' (Psi, (stringTodec D'')) in
          T.Ex ((D', T.Implicit), (transFor ((I.Decl (Psi, D')), F)))
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
      | (All ((D, _), F), P) -> T.Lam (D, (lamClosure (F, P)))
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
      | (Psi, Decl (Psi', D)) -> I.Decl ((append (Psi, Psi')), D)
    let rec parseTerm (Psi, (s, V)) =
      let (term', c) = transTerm s in
      let term = stringToterm term' in
      let JOf ((U, occ), (_, _), L) =
        ReconTerm.reconWithCtx
          ((T.coerceCtx Psi), (ReconTerm.jof' (term, V))) in
      U
    let rec parseDec (Psi, s) =
      let (dec', c) = transDec s in
      let dec = stringTodec dec' in
      let JWithCtx (Decl (I.Null, D), ReconTerm.JNothing) =
        ReconTerm.reconWithCtx
          ((T.coerceCtx Psi),
            (ReconTerm.jwithctx ((I.Decl (I.Null, dec)), ReconTerm.jnothing))) in
      let Dec (SOME n, _) = D in D
    let rec transDecs =
      function
      | (Psi, D.Empty, sc, W) -> sc (Psi, W)
      | (Psi, FormDecl (FormD, Ds), sc, W) ->
          transForDec (Psi, FormD, Ds, sc, W)
      | (Psi, ValDecl (ValD, Ds), sc, W) ->
          transValDec (Psi, ValD, Ds, sc, W)
      | (Psi, NewDecl (D, Ds), sc, W) ->
          let D' = T.UDec (parseDec (Psi, D)) in
          T.Let
            ((T.PDec (NONE, T.True)),
              (T.Lam (D', (transDecs ((I.Decl (Psi, D')), Ds, sc, W)))),
              (T.Var 1))
      | _ ->
          raise
            (Error
               "Constant declaration must be followed by a constant definition")
    let rec lookup =
      function
      | (I.Null, n, s) -> raise (Error ("Undeclared constant " ^ s))
      | (Decl (g, PDec (NONE, _)), n, s) -> lookup (g, (n + 1), s)
      | (Decl (g, UDec _), n, s) -> lookup (g, (n + 1), s)
      | (Decl (g, PDec (SOME s', F)), n, s) ->
          if s = s'
          then (n, (T.forSub (F, (T.Shift n))))
          else lookup (g, (n + 1), s)
    let rec transHead =
      function
      | (Psi, Head s, args) ->
          let (n, F) = lookup (Psi, 1, s) in
          transHead' ((F, T.id), I.Nil, args)
      | (Psi, AppLF (h, t), args) -> transHead (Psi, h, (t :: args))
    let rec transHead' =
      function
      | ((World (_, F), s), S, args) -> transHead' ((F, s), S, args)
      | ((All ((UDec (Dec (_, V)), T.Implicit), F'), s), S, args) ->
          let X =
            I.newEVar
              ((I.Decl (I.Null, I.NDec)), (I.EClo (V, (T.coerceSub s)))) in
          transHead' ((F', (T.Dot ((T.Exp X), s))), (I.App (X, S)), args)
      | ((All ((UDec (Dec (_, V)), T.Explicit), F'), s), S, t::args) ->
          let (term', c) = transTerm t in
          let term = stringToterm term' in
          let JOf ((U, occ), (_, _), L) =
            ReconTerm.reconWithCtx
              (I.Null,
                (ReconTerm.jof' (term, (I.EClo (V, (T.coerceSub s)))))) in
          transHead' ((F', (T.Dot ((T.Exp U), s))), (I.App (U, S)), args)
      | ((F, s), S, nil) -> ((F, s), S)
    let rec spineToSub =
      function
      | ((I.Nil, _), s') -> s'
      | ((App (U, S), t), s') ->
          T.Dot ((T.Exp (I.EClo (U, t))), (spineToSub ((S, t), s')))
    let rec transPattern =
      function
      | (p, (Ex ((Dec (_, V), T.Implicit), F'), s)) ->
          transPattern
            (p,
              (F',
                (T.Dot
                   ((T.Exp
                       (I.EVar
                          ((ref NONE), I.Null, (I.EClo (V, (T.coerceSub s))),
                            (ref nil)))), s))))
      | (PatInx (t, p), (Ex ((Dec (_, V), T.Explicit), F'), s)) ->
          let (term', c) = transTerm t in
          let term = stringToterm term' in
          let JOf ((U, occ), (_, _), L) =
            ReconTerm.reconWithCtx
              (I.Null,
                (ReconTerm.jof' (term, (I.EClo (V, (T.coerceSub s)))))) in
          T.PairExp (U, (transPattern (p, (F', (T.Dot ((T.Exp U), s))))))
      | (D.PatUnit, (F, s)) -> T.Unit
    let rec transFun1 =
      function
      | (Psi, (s', F), FunDecl (Fun (eH, eP), Ds), sc, W) ->
          let s = head eH in
          let _ =
            if s = s'
            then ()
            else
              raise
                (Error
                   "Function defined is different from function declared.") in
          transFun2
            (Psi, (s, F), (D.FunDecl ((D.Bar (eH, eP)), Ds)), sc,
              (function | Cs -> T.Case (T.Cases Cs)), W)
      | (Psi, (s', F), FunDecl (FunAnd (eH, eP), Ds), sc, W) ->
          raise (Error "Mutual recursive functions not yet implemented")
      | _ -> raise (Error "Function declaration expected")
    let rec transFun2 =
      function
      | (Psi, (s, F), FunDecl (Bar (eH, eP), Ds), sc, k, W) ->
          transFun3 (Psi, (s, F), eH, eP, Ds, sc, k, W)
      | (Psi, (s, F), Ds, sc, k, W) ->
          let D = T.PDec ((SOME s), F) in
          let P' = T.Rec (D, (lamClosure (F, (k nil)))) in (P', Ds)
    let rec transFun3 (Psi, (s, F), eH, eP, Ds, sc, k, W) =
      let _ =
        if (head eH) <> s
        then raise (Error "Functions don't all have the same name")
        else () in
      let _ = Names.varReset I.Null in
      let Psi0 = I.Decl (Psi, (T.PDec ((SOME s), F))) in
      let ((F', t'), S) = transHead (Psi0, eH, nil) in
      let (Psi', S') = Abstract.abstractSpine (S, I.id) in
      let Psi'' = append (Psi0, (T.embedCtx Psi')) in
      let m0 = I.ctxLength Psi0 in
      let m' = I.ctxLength Psi' in
      let t0 = dotn ((I.Shift m0), m') in
      let t'' = spineToSub ((S', t0), (T.Shift m')) in
      let P = transProgI (Psi'', eP, (F', t'), W) in
      transFun2
        (Psi, (s, F), Ds, sc, (function | Cs -> k ((Psi'', t'', P) :: Cs)),
          W)
    let rec transForDec (Psi, Form (s, eF), Ds, sc, W) =
      let g = Names.ctxName (T.coerceCtx Psi) in
      let F = transFor (g, eF) in
      let World (W, F') as F'' = T.forSub (F, T.id) in
      let _ = TomegaTypeCheck.checkFor (Psi, F'') in
      let (P, Ds') = transFun1 (Psi, (s, F'), Ds, sc, W) in
      let D = T.PDec ((SOME s), F'') in
      T.Let
        (D, (T.Box (W, P)),
          (transDecs ((I.Decl (Psi, D)), Ds', (function | P' -> sc P'), W)))
    let rec transValDec (Psi, Val (EPat, eP, eFopt), Ds, sc, W) =
      let (P, (F', t')) =
        match eFopt with
        | NONE -> transProgS (Psi, eP, W, nil)
        | SOME eF ->
            let F' = transFor ((T.coerceCtx Psi), eF) in
            let P' = transProgIN (Psi, eP, F', W) in (P', (F', T.id)) in
      let F'' = T.forSub (F', t') in
      let Pat = transPattern (EPat, (F', t')) in
      let D = T.PDec (NONE, F'') in
      let (Psi', Pat') = Abstract.abstractTomegaPrg Pat in
      let m = I.ctxLength Psi' in
      let t = T.Dot ((T.Prg Pat'), (T.Shift m)) in
      let Psi'' = append (Psi, Psi') in
      let P'' = transDecs (Psi'', Ds, sc, W) in
      T.Let (D, P, (T.Case (T.Cases [(Psi'', t, P'')])))
    let rec transProgI (Psi, eP, Ft, W) =
      transProgIN (Psi, eP, (T.forSub Ft), W)
    let rec transProgIN =
      function
      | (Psi, D.Unit, T.True, W) -> T.Unit
      | (Psi, (Inx (s, EP) as P), Ex ((Dec (_, V), T.Explicit), F'), W) ->
          let U = parseTerm (Psi, (s, V)) in
          let P' = transProgI (Psi, EP, (F', (T.Dot ((T.Exp U), T.id))), W) in
          T.PairExp (U, P')
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
          let D' = parseDec (Psi, eD) in
          let Psi'' = I.Decl (Psi, (T.UDec D')) in
          T.Choose
            (T.Lam
               ((T.UDec D'), (transProgI (Psi'', eP, (F, (T.Shift 1)), W))))
      | (Psi, New (nil, eP), F, W) -> transProgIN (Psi, eP, F, W)
      | (Psi, New (eD::eDs, eP), F, W) ->
          let D' = parseDec (Psi, eD) in
          let Psi'' = I.Decl (Psi, (T.UDec D')) in
          T.New
            (T.Lam
               ((T.UDec D'),
                 (transProgI
                    (Psi'', (D.New ((eD :: eDs), eP)), (F, (T.Shift 1)), W))))
      | (Psi, (AppTerm (EP, s) as P), F, W) ->
          let (P', (F', _)) = transProgS (Psi, P, W, nil) in
          let () = () in P'
    let rec transProgS =
      function
      | (Psi, D.Unit, W, args) -> (T.Unit, (T.True, T.id))
      | (Psi, AppTerm (EP, s), W, args) ->
          transProgS (Psi, EP, W, (s :: args))
      | (Psi, Const name, W, args) ->
          let (n, F) = lookup (Psi, 1, name) in
          let (S, Fs') = transProgS' (Psi, (F, T.id), W, args) in
          ((T.Redex ((T.Var n), S)), Fs')
      | (Psi, Choose (eD, eP), W, args) ->
          let D' = parseDec (Psi, eD) in
          let (P, (F, t)) =
            transProgS ((I.Decl (Psi, (T.UDec D'))), eP, W, args) in
          ((T.Choose (T.Lam ((T.UDec D'), P))), (F, t))
      | (Psi, New (nil, eP), W, args) -> transProgS (Psi, eP, W, args)
      | (Psi, New (eD::eDs, eP), W, args) ->
          let D' = parseDec (Psi, eD) in
          let (P, (F, t)) =
            transProgS
              ((I.Decl (Psi, (T.UDec D'))), (D.New (eDs, eP)), W, args) in
          let UDec (D'') = externalizeMDec ((I.ctxLength Psi), (T.UDec D')) in
          let (B, _) = T.deblockify (I.Decl (I.Null, D'')) in
          let F' = TA.raiseFor (B, (F, (T.coerceSub t))) in
          ((T.New (T.Lam ((T.UDec D'), P))), (F', T.id))
    let rec transProgS' =
      function
      | (Psi, (World (_, F), s), W, args) ->
          transProgS' (Psi, (F, s), W, args)
      | (Psi, (All ((UDec (Dec (_, V)), T.Implicit), F'), s), W, args) ->
          let g = T.coerceCtx Psi in
          let X = I.newEVar (g, (I.EClo (V, (T.coerceSub s)))) in
          let (S, Fs') =
            transProgS' (Psi, (F', (T.Dot ((T.Exp X), s))), W, args) in
          ((T.AppExp ((Whnf.normalize (X, I.id)), S)), Fs')
      | (Psi, (All ((UDec (Dec (_, V)), T.Explicit), F'), s), W, t::args) ->
          let U = parseTerm (Psi, (t, (I.EClo (V, (T.coerceSub s))))) in
          let (S, Fs') =
            transProgS' (Psi, (F', (T.Dot ((T.Exp U), s))), W, args) in
          ((T.AppExp (U, S)), Fs')
      | (Psi, (F, s), _, nil) -> (T.Nil, (F, s))
    let rec transProgram (Ds) =
      transDecs (I.Null, Ds, (function | (Psi, W) -> T.Unit), (T.Worlds []))
    let ((transFor)(* Invariant   for each cid which has been internalize out of a block,
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
      (* below use region arithmetic --cs !!!  *)(* stringToWorlds s = W

       Invariant:
       If   s is a string representing an expression,
       then W is the result of parsing it
       otherwise Parsing.error is raised.
    *)
      (* closure (g, V) = V'

       Invariant:
       {g}V = V'
    *)
      (* internalizeBlock  (n, g, Vb, S) (L2, s) = ()

       Invariant:
       If   |- g ctx                the context of some variables
       and  g |- Vb :  type         the type of the block
       and  g |- L1, L2 decs
       and  G1, L1 |- L2 decs       block declarations still to be traversed
       and  g, b:Vb |- s : G1, L1
       and  n is the current projection
       then internalizeBlock adds new declarations into the signature that
              correspond to the block declarations.
    *)
      (* g, B |- V' : type *)(* g |- {B} V' : type *)
      (* makeSpine (n, g, S) = S'

       Invariant:
       If  G0 = g, g'
       and |g'| = n
       and G0 |- S : V >> V'   for some V, V'
       then S' extends S
       and G0 |- S' : V >> type.
    *)
      (* interalizeCondec condec = ()

       Invariant:
       If   condec is a condec,
       then all pi declarations are internalized if condec was a blockdec
    *)
      (* sigToCtx () = ()

       Invariant:
       g is the internal representation of the global signature
       It converts every block declaration to a type family (stored in the global
       signature) and a list of declarations.
    *)
      (* we might want to save max, here to restore the original
                 signature after parsing is over  --cs Thu Apr 17 09:46:29 2003 *)
      (* Externalization *)(* Check : the translators hould only generate normal forms. Fix during the next pass --cs Thu Apr 17 17:06:24 2003 *)
      (* PClo should not be possible, since by invariant, parser
         always generates a program in normal form  --cs Thu Apr 17 16:56:07 2003
      *)
      (* Translation starts here *)(*      | transTerm (D.Dot (D.Id s1, s2)) =
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
      (* stringToTerm s = U

       Invariant:
       If   s is a string representing an expression,
       then U is the result of parsing it
       otherwise Parsing.error is raised.
    *)
      (* head (dH) = n

       Invariant:
       n is the name of the function head dH
    *)
      (* lamClosure (F, P) = P'

       Invariant:
       If   . |- F formula
       and  . |- F = all D1. ... all Dn. F' formula
         for  . |- F' formula that does not commence with a universal quantifier
       and . |- P :: F'
       then P' = lam D1 ... lam Dn P
    *)
      (* check that W is at least as large as W' *)(* dotn (t, n) = t'

       Invariant:
       If   Psi0 |- t : Psi
       and  |g| = n   for any g
       then Psi0, g[t] |- t : Psi, g
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
      (*          T.Let (T.PDec (NONE, T.True), T.Lam (D', transDecs (I.Decl (Psi, D'), Ds, sc, W)), T.Unit) *)
      (* T.True is not right! -- cs Sat Jun 28 11:43:30 2003  *)
      (* transHead (g, T, S) = (F', t')

       Invariant:
       If   g |- T : F
       and  g |- S : world{W}all{g'}F' >> F'
       then g |- t' : g'
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
            as input: Cs a list of cases
            as ouput: A program P that corresponds to the case list Cs
       then eventually x = ().     --cs
    *)
      (* transFun3 ((Psi, env), s, eH, eP, Ds, sc, k, W) = x

       Invariant:
       If   Psi |- dDs :: Psi'
       and  Psi |- env environment
       and  s is the name of the function currently being translated
       and  eH is the head of the function
       and  eP its body
       and  W is the valid world
       and  Ds are the remaining declarations
       and  sc is the success continuation that expects
            as input: (Psi', env')
                      where Psi' is the context after translating dDs
                      and   Psi' |- env' environment
                            are all variables introduced until this point
            as output: anything.
       and  k is the continuation that expects
            as input: Cs a list of cases
            as ouput: A program P that corresponds to the case list Cs
       then eventually x = ().     --cs
    *)
      (*                val F' = T.forSub (F, t) *)(* |Psi''| = m0 + m' *)
      (* Psi0, Psi'[^m0] |- t0 : Psi' *)(*        val t1 = T.Dot (T.Prg (T.Root (T.Var (m'+1), T.Nil)), T.Shift (m'))    BUG !!!! Wed Jun 25 11:23:13 2003 *)
      (* Psi0, Psi'[^m0] |- t1 : F[^m0]  *)(*        val _ = print (TomegaPrint.forToString (Names.ctxName (T.coerceCtx Psi''), myF) ^ "\n") *)
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
          val _ = print (TomegaPrint.forToString (T.embedCtx g, F'') ^ "\n") *)
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
      (* check that F == F' *)(*      | transProgIN ((Psi, env), D.Pair (EP1, EP2), T.And (F1, F2), W) =
        let
          val P1 = transProgIN ((Psi, env), EP1, F1, W)
          val P2 = transProgIN ((Psi, env), EP2, F2, W)
        in
          T.PairPrg (P1, P2)
        end
      | transProgIN ((Psi, env), P as D.AppProg (EP1, EP2), F, W) =
        let
          val (P', (F', _)) = transProgS ((Psi, env), P, W)
          val ()  = ()    check that F == F' *)
      (* check that F == F' *)(* check that F == F' *)
      (*      | transProgIN (Psi, D.Lam (s, EP)) =
        let
          val dec = stringTodec s
          val (I.Decl (Psi, (D, _, _)), P, F') = transProgI (I.Decl (ePsi, dec), EP)
        in
          (Psi, T.Lam (T.UDec D, P), T.All (D, F'))
        end
*)
      (* is this the right starting point --cs *)(*         val lemma = T.lemmaName name
           val F = T.lemmaFor lemma *)
      (* bug: forgot to raise F[t] to F' --cs Tue Jul  1 10:49:52 2003 *)
      (*        val X = I.EVar (ref NONE, I.Null, I.EClo (V, T.coerceSub s), ref nil) *)
      (*        val (F'', s'', _) = checkForWorld (F', T.Dot (T.Exp U, s), W) *)
      (*
     | transProgS ((Psi, env), D.Pair (EP1, EP2), W) =
        let
          val (P1, (F1, t1)) = transProgS ((Psi, env), EP1, W)
          val (P2, (F2, t2)) = transProgS ((Psi, env), EP2, W)
        in
          (T.PairPrg (P1, P2), (T.And (F1, F2), T.comp (t1, t2)))
        end

     | transProgS ((Psi, env), D.AppProg (EP1, EP2), W) =
        let
          val (P1, (T.And (F1, F2), t)) = transProgS ((Psi, env), EP1, W)
          val P2 = transProgIN ((Psi, env), EP2, T.FClo (F1, t), W)
          val (F'', t'', W) = checkForWorld (F2, t, W)
        in
          (T.Redex (P1, T.AppPrg (P2, T.Nil)), (F'', t''))
        end


      | transProgS ((Psi, env), P as D.Inx (s, EP), W) =  raise Error "Cannot infer existential types"

      | transProgS ((Psi, env), D.Lam (s, EP), W) =
        let
          val dec = stringTodec s
          val (I.Decl (Psi', (D, _, _)), P, F) = transProgI (I.Decl (Psi, dec), EP)
          val (F', t', _) = checkForWorld (F, T.id, W)
        in
          (T.Lam (T.UDec D, P), (T.All (D, F'), t'))
        end
*)
      (*        val _ = print (Print.expToString (g, U) ^ "\n") *)
      (* is this the right starting point --cs *)(* transProgram Ds = P

       Invariant:
       If Ds is a list of declarations then P is
       the translated program, that does not do anything
    *))
      = function | F -> let F' = transFor (I.Null, F) in F'
    let ((transDecs)(*    val makePattern = makePattern *)
      (*    val transPro = fn P => let val (P', _) = transProgS ((I.Null, []), P, T.Worlds []) in P' end *))
      = transProgram
    let internalizeSig = internalizeSig
    let externalizePrg = function | P -> externalizePrg (0, P)
  end;;
