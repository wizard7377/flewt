
module type TRANS  =
  sig
    module DextSyn : DEXTSYN
    exception Error of string 
    val internalizeSig : unit -> unit
    val transFor : DextSyn.__Form -> Tomega.__For
    val transDecs : DextSyn.__Decs -> Tomega.__Prg
    val externalizePrg : Tomega.__Prg -> Tomega.__Prg
  end;;




module Trans(Trans:sig module DextSyn' : DEXTSYN end) =
  struct
    module DextSyn = DextSyn'
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
      (* region information useless
                                                   since it only refers to string --cs *)
    let rec stringTodec s =
      let f = LS.expose (L.lexStream (TextIO.openString s)) in
      let ((x, yOpt), f') = ParseTerm.parseDec' f in
      let r2 = checkEOF f' in
      let dec =
        ((match yOpt with
          | NONE -> ReconTerm.dec0 (x, r2)
          | Some y -> ReconTerm.dec (x, y, r2))
        (* below use region arithmetic --cs !!!  *)) in
      dec
    let rec stringToblocks s =
      let f = LS.expose (L.lexStream (TextIO.openString s)) in
      let (dl, f') = ParseTerm.parseCtx' f in dl
    let rec stringToWorlds s =
      let f = LS.expose (L.lexStream (TextIO.openString s)) in
      let (t, f') = ParseTerm.parseQualIds' f in let r2 = checkEOF f' in t
    let rec closure __0__ __1__ =
      match (__0__, __1__) with
      | (I.Null, __V) -> __V
      | (Decl (__G, __D), __V) -> closure (__G, (I.Pi ((__D, I.Maybe), __V)))
    let rec internalizeBlock __2__ __3__ __4__ =
      match (__2__, __3__, __4__) with
      | (_, nil, _) -> ()
      | (n, __G, Vb, __S, (Dec (Some name, __V))::__L2, s) ->
          let name' = "o_" ^ name in
          let __V1 = I.EClo (__V, s) in
          let __V2 = I.Pi (((I.Dec (NONE, Vb)), I.Maybe), __V1) in
          let __V3 = closure (__G, __V2) in
          let m = I.ctxLength __G in
          let condec = I.ConDec (name', NONE, m, I.Normal, __V3, I.Type) in
          let _ = TypeCheck.check (__V3, (I.Uni I.Type)) in
          let _ =
            if (!Global.chatter) >= 4
            then print ((Print.conDecToString condec) ^ "\n")
            else () in
          let cid = I.sgnAdd condec in
          let _ = Names.installConstName cid in
          let _ = Array.update (internal, cid, (Const (m, n))) in
          ((internalizeBlock ((n + 1), __G, Vb, __S)
              (__L2, (I.Dot ((I.Exp (I.Root ((I.Const cid), __S))), s))))
            (* G, B |- V' : type *)(* G |- {B} V' : type *))
    let rec makeSpine __5__ __6__ __7__ =
      match (__5__, __6__, __7__) with
      | (_, I.Null, __S) -> __S
      | (n, Decl (__G, __D), __S) ->
          makeSpine
            ((n + 1), __G, (I.App ((I.Root ((I.BVar (n + 1)), I.Nil)), __S)))
    let rec internalizeCondec __8__ __9__ =
      match (__8__, __9__) with
      | (cid, ConDec _) -> ()
      | (cid, ConDef _) -> ()
      | (cid, AbbrevDef _) -> ()
      | (cid, BlockDec (name, _, Gsome, Lpi)) ->
          let __V' = closure (Gsome, (I.Uni I.Type)) in
          let __C = I.ConDec ((name ^ "'"), NONE, 0, I.Normal, __V', I.Kind) in
          let a = I.sgnAdd __C in
          let _ = Array.update (internal, a, (Type cid)) in
          let _ = Names.installConstName a in
          let __S = makeSpine (0, Gsome, I.Nil) in
          let Vb = I.Root ((I.Const a), __S) in
          let __S' =
            makeSpine (0, (I.Decl (Gsome, (I.Dec (NONE, Vb)))), I.Nil) in
          internalizeBlock (1, Gsome, Vb, __S') (Lpi, I.shift)
      | (cid, SkoDec _) -> ()
    let rec internalizeSig () =
      let (max, _) = I.sgnSize () in
      let rec internalizeSig' n =
        if n >= max
        then ()
        else
          (internalizeCondec (n, (I.sgnLookup n)); internalizeSig' (n + 1)) in
      ((internalizeSig' 0)
        (* we might want to save max, here to restore the original
                 signature after parsing is over  --cs Thu Apr 17 09:46:29 2003 *))
    let rec dropSpine __10__ __11__ =
      match (__10__, __11__) with
      | (0, __S) -> __S
      | (n, App (_, __S)) -> dropSpine ((n - 1), __S)
    let rec makeSub __12__ __13__ =
      match (__12__, __13__) with
      | (I.Nil, s) -> s
      | (App (__U, __S), s) -> makeSub (__S, (I.Dot ((I.Exp __U), s)))
    let rec externalizeExp' =
      function
      | Uni _ as U -> __U
      | Pi ((__D, DP), __U) ->
          I.Pi (((externalizeDec __D), DP), (externalizeExp __U))
      | Root ((BVar _ as H), __S) -> I.Root (__H, (externalizeSpine __S))
      | Root ((Const c as H), __S) ->
          (match I.constUni c with
           | I.Kind -> I.Root (__H, (externalizeSpine __S))
           | I.Type ->
               let Const (n, i) = Array.sub (internal, c) in
               let App (Root (BVar b, I.Nil), __S') = dropSpine (n, __S) in
               I.Root ((I.Proj ((I.Bidx b), i)), (externalizeSpine __S')))
      | Root (Proj _, _) -> raise Domain
      | Root (Skonst _, _) -> raise Domain
      | Root (Def _, _) -> raise Domain
      | Root (NSDef _, _) -> raise Domain
      | Root (FVar _, _) -> raise Domain
      | Root (FgnConst _, _) -> raise Domain
      | Redex (__U, __S) ->
          I.Redex ((externalizeExp __U), (externalizeSpine __S))
      | Lam (__D, __U) -> I.Lam ((externalizeDec __D), (externalizeExp __U))
    let rec externalizeExp (__U) =
      externalizeExp' (Whnf.normalize (__U, I.id))
    let rec externalizeBlock (Bidx _ as B) = __B
    let rec externalizeDec (Dec (name, __V)) =
      I.Dec (name, (externalizeExp __V))
    let rec externalizeSpine =
      function
      | I.Nil -> I.Nil
      | App (__U, __S) ->
          I.App ((externalizeExp __U), (externalizeSpine __S))
    let rec externalizeSub =
      function
      | Shift n as s -> s
      | Dot (__F, s) -> I.Dot ((externalizeFront __F), (externalizeSub s))
    let rec externalizeFront =
      function
      | Idx _ as F -> __F
      | Exp (__U) -> I.Exp (externalizeExp __U)
      | Block (__B) -> I.Block (externalizeBlock __B)
      | I.Undef as F -> __F
    let rec externalizePrg __14__ __15__ =
      match (__14__, __15__) with
      | (n, Lam (__D, __P)) ->
          T.Lam ((externalizeMDec (n, __D)), (externalizePrg ((n + 1), __P)))
      | (n, New (__P)) -> T.New (externalizePrg (n, __P))
      | (n, Box (__W, __P)) -> T.Box (__W, (externalizePrg (n, __P)))
      | (n, Choose (__P)) -> T.Choose (externalizePrg (n, __P))
      | (n, PairExp (__U, __P)) ->
          T.PairExp ((externalizeExp __U), (externalizePrg (n, __P)))
      | (n, PairPrg (__P1, __P2)) ->
          T.PairPrg ((externalizePrg (n, __P1)), (externalizePrg (n, __P2)))
      | (n, PairBlock (__B, __P)) ->
          T.PairBlock ((externalizeBlock __B), (externalizePrg (n, __P)))
      | (n, T.Unit) -> T.Unit
      | (n, Var k) -> T.Var k
      | (n, Const c) -> T.Const c
      | (n, Redex (__P, __S)) ->
          T.Redex ((externalizePrg (n, __P)), (externalizeMSpine (n, __S)))
      | (n, Rec (__D, __P)) ->
          T.Rec ((externalizeMDec (n, __D)), (externalizePrg ((n + 1), __P)))
      | (n, Case (Cases (__O))) -> T.Case (T.Cases (externalizeCases __O))
      | (n, Let (__D, __P1, __P2)) ->
          T.Let
            ((externalizeMDec (n, __D)), (externalizePrg (n, __P1)),
              (externalizePrg ((n + 1), __P2)))
    let rec externalizeMDec __16__ __17__ =
      match (__16__, __17__) with
      | (n, UDec (Dec (name, (Root (Const a, __S) as V)) as D)) ->
          (match Array.sub (internal, a) with
           | Type a' ->
               T.UDec
                 (I.BDec
                    (name,
                      (a', (makeSub ((externalizeSpine __S), (I.Shift n))))))
           | _ -> T.UDec (externalizeDec __D))
      | (n, UDec (__D)) -> T.UDec (externalizeDec __D)
      | (n, PDec (s, __F)) -> T.PDec (s, (externalizeFor (n, __F)))
    let rec externalizeFor __18__ __19__ =
      match (__18__, __19__) with
      | (n, World (__W, __F)) -> T.World (__W, (externalizeFor (n, __F)))
      | (n, All ((__D, __Q), __F)) ->
          T.All
            (((externalizeMDec (n, __D)), __Q),
              (externalizeFor ((n + 1), __F)))
      | (n, Ex ((__D, __Q), __F)) ->
          T.Ex (((externalizeDec __D), __Q), (externalizeFor ((n + 1), __F)))
      | (n, T.True) -> T.True
      | (n, And (__F1, __F2)) ->
          T.And ((externalizeFor (n, __F1)), (externalizeFor (n, __F2)))
    let rec externalizeMSpine __20__ __21__ =
      match (__20__, __21__) with
      | (n, T.Nil) -> T.Nil
      | (n, AppExp (__U, __S)) ->
          T.AppExp ((externalizeExp __U), (externalizeMSpine (n, __S)))
      | (n, AppBlock (__B, __S)) ->
          T.AppBlock ((externalizeBlock __B), (externalizeMSpine (n, __S)))
      | (n, AppPrg (__P, __S)) ->
          T.AppPrg ((externalizePrg (n, __P)), (externalizeMSpine (n, __S)))
    let rec externalizeCases =
      function
      | nil -> nil
      | (Psi, t, __P)::__O ->
          let n = I.ctxLength Psi in
          (::) ((externalizeMCtx Psi), (externalizeMSub (n, t)),
                 (externalizePrg (n, __P)))
            externalizeCases __O
    let rec externalizeMSub __22__ __23__ =
      match (__22__, __23__) with
      | (n, (Shift _ as t)) -> t
      | (n, Dot (__F, t)) ->
          T.Dot ((externalizeMFront (n, __F)), (externalizeMSub (n, t)))
    let rec externalizeMFront __24__ __25__ =
      match (__24__, __25__) with
      | (n, (Idx _ as F)) -> __F
      | (n, Prg (__P)) -> T.Prg (externalizePrg (n, __P))
      | (n, Exp (__U)) -> T.Exp (externalizeExp __U)
      | (n, Block (__B)) -> T.Block (externalizeBlock __B)
      | (n, (T.Undef as F)) -> __F
    let rec externalizeMCtx =
      function
      | I.Null -> I.Null
      | Decl (Psi, __D) ->
          I.Decl
            ((externalizeMCtx Psi),
              (externalizeMDec ((I.ctxLength Psi), __D)))
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
           | Some cid ->
               (match I.sgnLookup cid with
                | BlockDec _ -> ((s ^ "'"), nil)
                | _ -> (s, nil)))
      | Pi (__D, t) ->
          let (s1, c1) = transDec __D in
          let (s2, c2) = transTerm t in
          (((("{" ^ s1) ^ "}") ^ s2), (c1 @ c2))
      | Fn (__D, t) ->
          let (s1, c1) = transDec __D in
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
            | Some cid -> cid in
          [cid]
      | Plus (__W1, __W2) -> (@) (transWorld __W1) transWorld __W2
      | Concat (__W1, __W2) -> (@) (transWorld __W1) transWorld __W2
      | Times (__W) -> transWorld __W(* We should use the worlds we have defined in Tomega, but this
              is not good enough, because worlds are not defined
              by a regualar expression.  Therefore this is a patch *)
    let rec transFor' (Psi) (__D) =
      let __G = I.Decl (I.Null, __D) in
      let JWithCtx (Decl (I.Null, __D'), ReconTerm.JNothing) =
        ReconTerm.reconWithCtx
          (Psi, (ReconTerm.jwithctx (__G, ReconTerm.jnothing))) in
      __D'
    let rec transFor __26__ __27__ =
      match (__26__, __27__) with
      | (Psi, D.True) -> T.True
      | (Psi, And (EF1, EF2)) ->
          T.And ((transFor (Psi, EF1)), (transFor (Psi, EF2)))
      | (Psi, Forall (__D, __F)) ->
          let (D'', nil) = transDec __D in
          let __D' = transFor' (Psi, (stringTodec D'')) in
          T.All
            (((T.UDec __D'), T.Explicit),
              (transFor ((I.Decl (Psi, __D')), __F)))
      | (Psi, Exists (__D, __F)) ->
          let (D'', nil) = transDec __D in
          let __D' = transFor' (Psi, (stringTodec D'')) in
          T.Ex ((__D', T.Explicit), (transFor ((I.Decl (Psi, __D')), __F)))
      | (Psi, ForallOmitted (__D, __F)) ->
          let (D'', nil) = transDec __D in
          let __D' = transFor' (Psi, (stringTodec D'')) in
          T.All
            (((T.UDec __D'), T.Implicit),
              (transFor ((I.Decl (Psi, __D')), __F)))
      | (Psi, ExistsOmitted (__D, __F)) ->
          let (D'', nil) = transDec __D in
          let __D' = transFor' (Psi, (stringTodec D'')) in
          T.Ex ((__D', T.Implicit), (transFor ((I.Decl (Psi, __D')), __F)))
      | (Psi, World (__W, EF)) ->
          T.World ((T.Worlds (transWorld __W)), (transFor (Psi, EF)))
    let rec stringToterm s =
      let f = LS.expose (L.lexStream (TextIO.openString s)) in
      let (t, f') = ParseTerm.parseTerm' f in let r2 = checkEOF f' in t
    let rec head =
      function
      | Head s -> s
      | AppLF (__H, _) -> head __H
      | AppMeta (__H, _) -> head __H
    let rec lamClosure __28__ __29__ =
      match (__28__, __29__) with
      | (All ((__D, _), __F), __P) -> T.Lam (__D, (lamClosure (__F, __P)))
      | (World (_, __F), __P) -> lamClosure (__F, __P)
      | (Ex _, __P) -> __P
    let rec exists __30__ __31__ =
      match (__30__, __31__) with
      | (c, []) -> raise (Error "Current world is not subsumed")
      | (c, c'::cids) -> if c = c' then () else exists (c, cids)
    let rec subsumed __32__ __33__ =
      match (__32__, __33__) with
      | ([], cids') -> ()
      | (c::cids, cids') -> (exists (c, cids'); subsumed (cids, cids'))
    let rec checkForWorld __34__ __35__ __36__ =
      match (__34__, __35__, __36__) with
      | (World ((Worlds cids as W), __F), t', Worlds cids') ->
          let _ = subsumed (cids', cids) in (((__F, t', __W))
            (* check that W is at least as large as W' *))
      | FtW -> FtW
    let rec dotn __37__ __38__ =
      match (__37__, __38__) with
      | (t, 0) -> t
      | (t, n) -> I.dot1 (dotn (t, (n - 1)))
    let rec append __39__ __40__ =
      match (__39__, __40__) with
      | (Psi, I.Null) -> Psi
      | (Psi, Decl (Psi', __D)) -> I.Decl ((append (Psi, Psi')), __D)
    let rec parseTerm (Psi) (s, __V) =
      let (term', c) = transTerm s in
      let term = stringToterm term' in
      let JOf ((__U, occ), (_, _), __L) =
        ReconTerm.reconWithCtx
          ((T.coerceCtx Psi), (ReconTerm.jof' (term, __V))) in
      __U
    let rec parseDec (Psi) s =
      let (dec', c) = transDec s in
      let dec = stringTodec dec' in
      let JWithCtx (Decl (I.Null, __D), ReconTerm.JNothing) =
        ReconTerm.reconWithCtx
          ((T.coerceCtx Psi),
            (ReconTerm.jwithctx ((I.Decl (I.Null, dec)), ReconTerm.jnothing))) in
      let Dec (Some n, _) = __D in __D
    let rec transDecs __41__ __42__ __43__ __44__ =
      match (__41__, __42__, __43__, __44__) with
      | (Psi, D.Empty, sc, __W) -> sc (Psi, __W)
      | (Psi, FormDecl (FormD, __Ds), sc, __W) ->
          transForDec (Psi, FormD, __Ds, sc, __W)
      | (Psi, ValDecl (ValD, __Ds), sc, __W) ->
          transValDec (Psi, ValD, __Ds, sc, __W)
      | (Psi, NewDecl (__D, __Ds), sc, __W) ->
          let __D' = T.UDec (parseDec (Psi, __D)) in
          ((T.Let
              ((T.PDec (NONE, T.True)),
                (T.Lam
                   (__D', (transDecs ((I.Decl (Psi, __D')), __Ds, sc, __W)))),
                (T.Var 1)))
            (*          T.Let (T.PDec (NONE, T.True), T.Lam (D', transDecs (I.Decl (Psi, D'), Ds, sc, W)), T.Unit) *)
            (* T.True is not right! -- cs Sat Jun 28 11:43:30 2003  *))
      | _ ->
          raise
            (Error
               "Constant declaration must be followed by a constant definition")
    let rec lookup __45__ __46__ __47__ =
      match (__45__, __46__, __47__) with
      | (I.Null, n, s) -> raise (Error ("Undeclared constant " ^ s))
      | (Decl (__G, PDec (NONE, _)), n, s) -> lookup (__G, (n + 1), s)
      | (Decl (__G, UDec _), n, s) -> lookup (__G, (n + 1), s)
      | (Decl (__G, PDec (Some s', __F)), n, s) ->
          if s = s'
          then (n, (T.forSub (__F, (T.Shift n))))
          else lookup (__G, (n + 1), s)
    let rec transHead __48__ __49__ __50__ =
      match (__48__, __49__, __50__) with
      | (Psi, Head s, args) ->
          let (n, __F) = lookup (Psi, 1, s) in
          transHead' ((__F, T.id), I.Nil, args)
      | (Psi, AppLF (h, t), args) -> transHead (Psi, h, (t :: args))
    let rec transHead' __51__ __52__ __53__ =
      match (__51__, __52__, __53__) with
      | ((World (_, __F), s), __S, args) -> transHead' ((__F, s), __S, args)
      | ((All ((UDec (Dec (_, __V)), T.Implicit), __F'), s), __S, args) ->
          let __X =
            I.newEVar
              ((I.Decl (I.Null, I.NDec)), (I.EClo (__V, (T.coerceSub s)))) in
          transHead'
            ((__F', (T.Dot ((T.Exp __X), s))), (I.App (__X, __S)), args)
      | ((All ((UDec (Dec (_, __V)), T.Explicit), __F'), s), __S, t::args) ->
          let (term', c) = transTerm t in
          let term = stringToterm term' in
          let JOf ((__U, occ), (_, _), __L) =
            ReconTerm.reconWithCtx
              (I.Null,
                (ReconTerm.jof' (term, (I.EClo (__V, (T.coerceSub s)))))) in
          transHead'
            ((__F', (T.Dot ((T.Exp __U), s))), (I.App (__U, __S)), args)
      | ((__F, s), __S, nil) -> ((__F, s), __S)
    let rec spineToSub __54__ __55__ =
      match (__54__, __55__) with
      | ((I.Nil, _), s') -> s'
      | ((App (__U, __S), t), s') ->
          T.Dot ((T.Exp (I.EClo (__U, t))), (spineToSub ((__S, t), s')))
    let rec transPattern __56__ __57__ =
      match (__56__, __57__) with
      | (p, (Ex ((Dec (_, __V), T.Implicit), __F'), s)) ->
          transPattern
            (p,
              (__F',
                (T.Dot
                   ((T.Exp
                       (I.EVar
                          ((ref NONE), I.Null,
                            (I.EClo (__V, (T.coerceSub s))), (ref nil)))), s))))
      | (PatInx (t, p), (Ex ((Dec (_, __V), T.Explicit), __F'), s)) ->
          let (term', c) = transTerm t in
          let term = stringToterm term' in
          let JOf ((__U, occ), (_, _), __L) =
            ReconTerm.reconWithCtx
              (I.Null,
                (ReconTerm.jof' (term, (I.EClo (__V, (T.coerceSub s)))))) in
          T.PairExp
            (__U, (transPattern (p, (__F', (T.Dot ((T.Exp __U), s))))))
      | (D.PatUnit, (__F, s)) -> T.Unit
    let rec transFun1 __58__ __59__ __60__ __61__ __62__ =
      match (__58__, __59__, __60__, __61__, __62__) with
      | (Psi, (s', __F), FunDecl (Fun (eH, eP), __Ds), sc, __W) ->
          let s = head eH in
          let _ =
            if s = s'
            then ()
            else
              raise
                (Error
                   "Function defined is different from function declared.") in
          transFun2
            (Psi, (s, __F), (D.FunDecl ((D.Bar (eH, eP)), __Ds)), sc,
              (fun (__Cs) -> T.Case (T.Cases __Cs)), __W)
      | (Psi, (s', __F), FunDecl (FunAnd (eH, eP), __Ds), sc, __W) ->
          raise (Error "Mutual recursive functions not yet implemented")
      | _ -> raise (Error "Function declaration expected")
    let rec transFun2 __63__ __64__ __65__ __66__ __67__ __68__ =
      match (__63__, __64__, __65__, __66__, __67__, __68__) with
      | (Psi, (s, __F), FunDecl (Bar (eH, eP), __Ds), sc, k, __W) ->
          transFun3 (Psi, (s, __F), eH, eP, __Ds, sc, k, __W)
      | (Psi, (s, __F), __Ds, sc, k, __W) ->
          let __D = T.PDec ((Some s), __F) in
          let __P' = T.Rec (__D, (lamClosure (__F, (k nil)))) in (__P', __Ds)
    let rec transFun3 (Psi) (s, __F) eH eP (__Ds) sc k (__W) =
      let _ =
        if (head eH) <> s
        then raise (Error "Functions don't all have the same name")
        else () in
      let _ = Names.varReset I.Null in
      let Psi0 = I.Decl (Psi, (T.PDec ((Some s), __F))) in
      let ((__F', t'), __S) = transHead (Psi0, eH, nil) in
      let (Psi', __S') = Abstract.abstractSpine (__S, I.id) in
      let Psi'' = append (Psi0, (T.embedCtx Psi')) in
      let m0 = I.ctxLength Psi0 in
      let m' = I.ctxLength Psi' in
      let t0 = dotn ((I.Shift m0), m') in
      let t'' = spineToSub ((__S', t0), (T.Shift m')) in
      let __P = transProgI (Psi'', eP, (__F', t'), __W) in
      ((transFun2
          (Psi, (s, __F), __Ds, sc,
            (fun (__Cs) -> k ((Psi'', t'', __P) :: __Cs)), __W))
        (*                val F' = T.forSub (F, t) *)
        (* |Psi''| = m0 + m' *)(* Psi0, Psi'[^m0] |- t0 : Psi' *)
        (*        val t1 = T.Dot (T.Prg (T.Root (T.Var (m'+1), T.Nil)), T.Shift (m'))    BUG !!!! Wed Jun 25 11:23:13 2003 *)
        (* Psi0, Psi'[^m0] |- t1 : F[^m0]  *)(*        val _ = print (TomegaPrint.forToString (Names.ctxName (T.coerceCtx Psi''), myF) ^ "\n") *))
    let rec transForDec (Psi) (Form (s, eF)) (__Ds) sc (__W) =
      let __G = Names.ctxName (T.coerceCtx Psi) in
      let __F = transFor (__G, eF) in
      let World (__W, __F') as F'' = T.forSub (__F, T.id) in
      let _ = TomegaTypeCheck.checkFor (Psi, F'') in
      let (__P, __Ds') = transFun1 (Psi, (s, __F'), __Ds, sc, __W) in
      let __D = T.PDec ((Some s), F'') in
      ((T.Let
          (__D, (T.Box (__W, __P)),
            (transDecs
               ((I.Decl (Psi, __D)), __Ds', (fun (__P') -> sc __P'), __W))))
        (*        val _ = print s
          val _ = print " :: "
          val _ = print (TomegaPrint.forToString (T.embedCtx G, F'') ^ "\n") *))
    let rec transValDec (Psi) (Val (EPat, eP, eFopt)) (__Ds) sc (__W) =
      let (__P, (__F', t')) =
        match eFopt with
        | NONE -> transProgS (Psi, eP, __W, nil)
        | Some eF ->
            let __F' = transFor ((T.coerceCtx Psi), eF) in
            let __P' = transProgIN (Psi, eP, __F', __W) in
            (__P', (__F', T.id)) in
      let F'' = T.forSub (__F', t') in
      let Pat = transPattern (EPat, (__F', t')) in
      let __D = T.PDec (NONE, F'') in
      let (Psi', Pat') = Abstract.abstractTomegaPrg Pat in
      let m = I.ctxLength Psi' in
      let t = T.Dot ((T.Prg Pat'), (T.Shift m)) in
      let Psi'' = append (Psi, Psi') in
      let P'' = transDecs (Psi'', __Ds, sc, __W) in
      ((T.Let (__D, __P, (T.Case (T.Cases [(Psi'', t, P'')]))))
        (*        val t = T.Dot (T.Prg Pat', T.id)  was --cs Tue Jun 24 13:04:55 2003 *))
    let rec transProgI (Psi) eP (Ft) (__W) =
      transProgIN (Psi, eP, (T.forSub Ft), __W)
    let rec transProgIN __69__ __70__ __71__ __72__ =
      match (__69__, __70__, __71__, __72__) with
      | (Psi, D.Unit, T.True, __W) -> T.Unit
      | (Psi, (Inx (s, EP) as P), Ex ((Dec (_, __V), T.Explicit), __F'), __W)
          ->
          let __U = parseTerm (Psi, (s, __V)) in
          let __P' =
            transProgI (Psi, EP, (__F', (T.Dot ((T.Exp __U), T.id))), __W) in
          T.PairExp (__U, __P')
      | (Psi, Let (eDs, eP), __F, __W) ->
          transDecs
            (Psi, eDs,
              (fun (Psi') ->
                 fun (__W') ->
                   transProgI
                     (Psi', eP,
                       (__F,
                         (T.Shift ((-) (I.ctxLength Psi') I.ctxLength Psi))),
                       __W')), __W)
      | (Psi, Choose (eD, eP), __F, __W) ->
          let __D' = parseDec (Psi, eD) in
          let Psi'' = I.Decl (Psi, (T.UDec __D')) in
          T.Choose
            (T.Lam
               ((T.UDec __D'),
                 (transProgI (Psi'', eP, (__F, (T.Shift 1)), __W))))
      | (Psi, New (nil, eP), __F, __W) -> transProgIN (Psi, eP, __F, __W)
      | (Psi, New (eD::eDs, eP), __F, __W) ->
          let __D' = parseDec (Psi, eD) in
          let Psi'' = I.Decl (Psi, (T.UDec __D')) in
          T.New
            (T.Lam
               ((T.UDec __D'),
                 (transProgI
                    (Psi'', (D.New ((eD :: eDs), eP)), (__F, (T.Shift 1)),
                      __W))))
      | (Psi, (AppTerm (EP, s) as P), __F, __W) ->
          let (__P', (__F', _)) = transProgS (Psi, __P, __W, nil) in
          let () = () in ((__P')(* check that F == F' *))
    let rec transProgS __73__ __74__ __75__ __76__ =
      match (__73__, __74__, __75__, __76__) with
      | (Psi, D.Unit, __W, args) -> (T.Unit, (T.True, T.id))
      | (Psi, AppTerm (EP, s), __W, args) ->
          transProgS (Psi, EP, __W, (s :: args))
      | (Psi, Const name, __W, args) ->
          let (n, __F) = lookup (Psi, 1, name) in
          let (__S, __Fs') = transProgS' (Psi, (__F, T.id), __W, args) in
          ((((T.Redex ((T.Var n), __S)), __Fs'))
            (*         val lemma = T.lemmaName name
           val F = T.lemmaFor lemma *))
      | (Psi, Choose (eD, eP), __W, args) ->
          let __D' = parseDec (Psi, eD) in
          let (__P, (__F, t)) =
            transProgS ((I.Decl (Psi, (T.UDec __D'))), eP, __W, args) in
          ((T.Choose (T.Lam ((T.UDec __D'), __P))), (__F, t))
      | (Psi, New (nil, eP), __W, args) -> transProgS (Psi, eP, __W, args)
      | (Psi, New (eD::eDs, eP), __W, args) ->
          let __D' = parseDec (Psi, eD) in
          let (__P, (__F, t)) =
            transProgS
              ((I.Decl (Psi, (T.UDec __D'))), (D.New (eDs, eP)), __W, args) in
          let UDec (D'') = externalizeMDec ((I.ctxLength Psi), (T.UDec __D')) in
          let (__B, _) = T.deblockify (I.Decl (I.Null, D'')) in
          let __F' = TA.raiseFor (__B, (__F, (T.coerceSub t))) in
          ((((T.New (T.Lam ((T.UDec __D'), __P))), (__F', T.id)))
            (* bug: forgot to raise F[t] to F' --cs Tue Jul  1 10:49:52 2003 *))
    let rec transProgS' __77__ __78__ __79__ __80__ =
      match (__77__, __78__, __79__, __80__) with
      | (Psi, (World (_, __F), s), __W, args) ->
          transProgS' (Psi, (__F, s), __W, args)
      | (Psi, (All ((UDec (Dec (_, __V)), T.Implicit), __F'), s), __W, args)
          ->
          let __G = T.coerceCtx Psi in
          let __X = I.newEVar (__G, (I.EClo (__V, (T.coerceSub s)))) in
          let (__S, __Fs') =
            transProgS' (Psi, (__F', (T.Dot ((T.Exp __X), s))), __W, args) in
          ((((T.AppExp ((Whnf.normalize (__X, I.id)), __S)), __Fs'))
            (*        val X = I.EVar (ref NONE, I.Null, I.EClo (V, T.coerceSub s), ref nil) *))
      | (Psi, (All ((UDec (Dec (_, __V)), T.Explicit), __F'), s), __W,
         t::args) ->
          let __U = parseTerm (Psi, (t, (I.EClo (__V, (T.coerceSub s))))) in
          let (__S, __Fs') =
            transProgS' (Psi, (__F', (T.Dot ((T.Exp __U), s))), __W, args) in
          ((((T.AppExp (__U, __S)), __Fs'))
            (*        val (F'', s'', _) = checkForWorld (F', T.Dot (T.Exp U, s), W) *))
      | (Psi, (__F, s), _, nil) -> (T.Nil, (__F, s))
    let rec transProgram (__Ds) =
      transDecs
        (I.Null, __Ds, (fun (Psi) -> fun (__W) -> T.Unit), (T.Worlds []))
    let transFor (__F) = let __F' = transFor (I.Null, __F) in __F'
    let transDecs = transProgram
    let internalizeSig = internalizeSig
    let externalizePrg (__P) = externalizePrg (0, __P)
  end;;
