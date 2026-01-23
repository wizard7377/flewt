module type TRANS  =
  sig
    module DextSyn : DEXTSYN
    exception Error of string 
    val internalizeSig : unit -> unit
    val transFor : DextSyn.form_ -> Tomega.for_
    val transDecs : DextSyn.decs_ -> Tomega.prg_
    val externalizePrg : Tomega.prg_ -> Tomega.prg_
  end


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
    type internal_ =
      | Empty 
      | Const of (int * int) 
      | Type of int 
    let maxCid = Global.maxCid
    let internal =
      (Array.array ((maxCid + 1), Empty) : internal_ Array.array)
    let rec checkEOF =
      begin function
      | Cons ((L.EOF, r), s') -> r
      | Cons ((t, r), _) ->
          Parsing.error (r, ((^) "Expected `}', found " L.toString t)) end
    (* region information useless
                                                   since it only refers to string --cs *)
    let rec stringTodec s =
      let f = LS.expose (L.lexStream (TextIO.openString s)) in
      let ((x, yOpt), f') = ParseTerm.parseDec' f in
      let r2 = checkEOF f' in
      let dec =
        ((begin match yOpt with
          | None -> ReconTerm.dec0 (x, r2)
          | Some y -> ReconTerm.dec (x, y, r2) end)
        (* below use region arithmetic --cs !!!  *)) in
      dec
  let rec stringToblocks s =
    let f = LS.expose (L.lexStream (TextIO.openString s)) in
    let (dl, f') = ParseTerm.parseCtx' f in dl
  let rec stringToWorlds s =
    let f = LS.expose (L.lexStream (TextIO.openString s)) in
    let (t, f') = ParseTerm.parseQualIds' f in let r2 = checkEOF f' in t
  let rec closure =
    begin function
    | (I.Null, v_) -> v_
    | (Decl (g_, d_), v_) -> closure (g_, (I.Pi ((d_, I.Maybe), v_))) end
let rec internalizeBlock arg__0 arg__1 =
  begin match (arg__0, arg__1) with
  | (_, ([], _)) -> ()
  | ((n, g_, Vb, s_), ((Dec (Some name, v_))::l2_, s)) ->
      let name' = "o_" ^ name in
      let v1_ = I.EClo (v_, s) in
      let v2_ = I.Pi (((I.Dec (None, Vb)), I.Maybe), v1_) in
      let v3_ = closure (g_, v2_) in
      let m = I.ctxLength g_ in
      let condec = I.ConDec (name', None, m, I.Normal, v3_, I.Type) in
      let _ = TypeCheck.check (v3_, (I.Uni I.Type)) in
      let _ =
        if !Global.chatter >= 4
        then begin print ((Print.conDecToString condec) ^ "\n") end
        else begin () end in
      let cid = I.sgnAdd condec in
      let _ = Names.installConstName cid in
      let _ = Array.update (internal, cid, (Const (m, n))) in
      ((internalizeBlock ((n + 1), g_, Vb, s_)
          (l2_, (I.Dot ((I.Exp (I.Root ((I.Const cid), s_))), s))))
        (* G, B |- V' : type *)(* G |- {B} V' : type *)) end
let rec makeSpine =
  begin function
  | (_, I.Null, s_) -> s_
  | (n, Decl (g_, d_), s_) ->
      makeSpine
        ((n + 1), g_, (I.App ((I.Root ((I.BVar (n + 1)), I.Nil)), s_))) end
let rec internalizeCondec =
  begin function
  | (cid, ConDec _) -> ()
  | (cid, ConDef _) -> ()
  | (cid, AbbrevDef _) -> ()
  | (cid, BlockDec (name, _, Gsome, Lpi)) ->
      let v'_ = closure (Gsome, (I.Uni I.Type)) in
      let c_ = I.ConDec ((name ^ "'"), None, 0, I.Normal, v'_, I.Kind) in
      let a = I.sgnAdd c_ in
      let _ = Array.update (internal, a, (Type cid)) in
      let _ = Names.installConstName a in
      let s_ = makeSpine (0, Gsome, I.Nil) in
      let Vb = I.Root ((I.Const a), s_) in
      let s'_ = makeSpine (0, (I.Decl (Gsome, (I.Dec (None, Vb)))), I.Nil) in
      internalizeBlock (1, Gsome, Vb, s'_) (Lpi, I.shift)
  | (cid, SkoDec _) -> () end
let rec internalizeSig () =
  let (max, _) = I.sgnSize () in
  let rec internalizeSig' n = if n >= max then begin () end
    else begin
      (begin internalizeCondec (n, (I.sgnLookup n)); internalizeSig' (n + 1) end) end in
((internalizeSig' 0)
  (* we might want to save max, here to restore the original
                 signature after parsing is over  --cs Thu Apr 17 09:46:29 2003 *))
let rec dropSpine =
  begin function
  | (0, s_) -> s_
  | (n, App (_, s_)) -> dropSpine ((n - 1), s_) end
let rec makeSub =
  begin function
  | (I.Nil, s) -> s
  | (App (u_, s_), s) -> makeSub (s_, (I.Dot ((I.Exp u_), s))) end
let rec externalizeExp' =
  begin function
  | Uni _ as u_ -> u_
  | Pi ((d_, DP), u_) ->
      I.Pi (((externalizeDec d_), DP), (externalizeExp u_))
  | Root ((BVar _ as h_), s_) -> I.Root (h_, (externalizeSpine s_))
  | Root ((Const c as h_), s_) ->
      (begin match I.constUni c with
       | I.Kind -> I.Root (h_, (externalizeSpine s_))
       | I.Type ->
           let Const (n, i) = Array.sub (internal, c) in
           let App (Root (BVar b, I.Nil), s'_) = dropSpine (n, s_) in
           I.Root ((I.Proj ((I.Bidx b), i)), (externalizeSpine s'_)) end)
  | Root (Proj _, _) -> raise Domain | Root (Skonst _, _) -> raise Domain
  | Root (Def _, _) -> raise Domain | Root (NSDef _, _) -> raise Domain
  | Root (FVar _, _) -> raise Domain | Root (FgnConst _, _) -> raise Domain
  | Redex (u_, s_) -> I.Redex ((externalizeExp u_), (externalizeSpine s_))
  | Lam (d_, u_) -> I.Lam ((externalizeDec d_), (externalizeExp u_)) end
let rec externalizeExp (u_) = externalizeExp' (Whnf.normalize (u_, I.id))
let rec externalizeBlock (Bidx _ as b_) = b_
let rec externalizeDec (Dec (name, v_)) = I.Dec (name, (externalizeExp v_))
let rec externalizeSpine =
  begin function
  | I.Nil -> I.Nil
  | App (u_, s_) -> I.App ((externalizeExp u_), (externalizeSpine s_)) end
let rec externalizeSub =
  begin function
  | Shift n as s -> s
  | Dot (f_, s) -> I.Dot ((externalizeFront f_), (externalizeSub s)) end
let rec externalizeFront =
  begin function
  | Idx _ as f_ -> f_
  | Exp (u_) -> I.Exp (externalizeExp u_)
  | Block (b_) -> I.Block (externalizeBlock b_)
  | I.Undef as f_ -> f_ end
let rec externalizePrg =
  begin function
  | (n, Lam (d_, p_)) ->
      T.Lam ((externalizeMDec (n, d_)), (externalizePrg ((n + 1), p_)))
  | (n, New (p_)) -> T.New (externalizePrg (n, p_))
  | (n, Box (w_, p_)) -> T.Box (w_, (externalizePrg (n, p_)))
  | (n, Choose (p_)) -> T.Choose (externalizePrg (n, p_))
  | (n, PairExp (u_, p_)) ->
      T.PairExp ((externalizeExp u_), (externalizePrg (n, p_)))
  | (n, PairPrg (p1_, p2_)) ->
      T.PairPrg ((externalizePrg (n, p1_)), (externalizePrg (n, p2_)))
  | (n, PairBlock (b_, p_)) ->
      T.PairBlock ((externalizeBlock b_), (externalizePrg (n, p_)))
  | (n, T.Unit) -> T.Unit
  | (n, Var k) -> T.Var k
  | (n, Const c) -> T.Const c
  | (n, Redex (p_, s_)) ->
      T.Redex ((externalizePrg (n, p_)), (externalizeMSpine (n, s_)))
  | (n, Rec (d_, p_)) ->
      T.Rec ((externalizeMDec (n, d_)), (externalizePrg ((n + 1), p_)))
  | (n, Case (Cases (o_))) -> T.Case (T.Cases (externalizeCases o_))
  | (n, Let (d_, p1_, p2_)) ->
      T.Let
        ((externalizeMDec (n, d_)), (externalizePrg (n, p1_)),
          (externalizePrg ((n + 1), p2_))) end
let rec externalizeMDec =
  begin function
  | (n, UDec (Dec (name, (Root (Const a, s_) as v_)) as d_)) ->
      (begin match Array.sub (internal, a) with
       | Type a' ->
           T.UDec
             (I.BDec
                (name, (a', (makeSub ((externalizeSpine s_), (I.Shift n))))))
       | _ -> T.UDec (externalizeDec d_) end)
  | (n, UDec (d_)) -> T.UDec (externalizeDec d_)
  | (n, PDec (s, f_)) -> T.PDec (s, (externalizeFor (n, f_))) end
let rec externalizeFor =
  begin function
  | (n, World (w_, f_)) -> T.World (w_, (externalizeFor (n, f_)))
  | (n, All ((d_, q_), f_)) ->
      T.All (((externalizeMDec (n, d_)), q_), (externalizeFor ((n + 1), f_)))
  | (n, Ex ((d_, q_), f_)) ->
      T.Ex (((externalizeDec d_), q_), (externalizeFor ((n + 1), f_)))
  | (n, T.True) -> T.True
  | (n, And (f1_, f2_)) ->
      T.And ((externalizeFor (n, f1_)), (externalizeFor (n, f2_))) end
let rec externalizeMSpine =
  begin function
  | (n, T.Nil) -> T.Nil
  | (n, AppExp (u_, s_)) ->
      T.AppExp ((externalizeExp u_), (externalizeMSpine (n, s_)))
  | (n, AppBlock (b_, s_)) ->
      T.AppBlock ((externalizeBlock b_), (externalizeMSpine (n, s_)))
  | (n, AppPrg (p_, s_)) ->
      T.AppPrg ((externalizePrg (n, p_)), (externalizeMSpine (n, s_))) end
let rec externalizeCases =
  begin function
  | [] -> []
  | (Psi, t, p_)::o_ ->
      let n = I.ctxLength Psi in
      (::) ((externalizeMCtx Psi), (externalizeMSub (n, t)),
             (externalizePrg (n, p_)))
        externalizeCases o_ end
let rec externalizeMSub =
  begin function
  | (n, (Shift _ as t)) -> t
  | (n, Dot (f_, t)) ->
      T.Dot ((externalizeMFront (n, f_)), (externalizeMSub (n, t))) end
let rec externalizeMFront =
  begin function
  | (n, (Idx _ as f_)) -> f_
  | (n, Prg (p_)) -> T.Prg (externalizePrg (n, p_))
  | (n, Exp (u_)) -> T.Exp (externalizeExp u_)
  | (n, Block (b_)) -> T.Block (externalizeBlock b_)
  | (n, (T.Undef as f_)) -> f_ end
let rec externalizeMCtx =
  begin function
  | I.Null -> I.Null
  | Decl (Psi, d_) ->
      I.Decl
        ((externalizeMCtx Psi), (externalizeMDec ((I.ctxLength Psi), d_))) end
let rec transTerm =
  begin function
  | Rtarrow (t1, t2) ->
      let (s1, c1) = transTerm t1 in
      let (s2, c2) = transTerm t2 in (((s1 ^ " -> ") ^ s2), (c1 @ c2))
  | Ltarrow (t1, t2) ->
      let (s1, c1) = transTerm t1 in
      let (s2, c2) = transTerm t2 in (((s1 ^ " <- ") ^ s2), (c1 @ c2))
  | D.Type -> ("type", [])
  | Id s ->
      let qid = Names.Qid ([], s) in
      (begin match Names.constLookup qid with
       | None -> (s, [])
       | Some cid ->
           (begin match I.sgnLookup cid with
            | BlockDec _ -> ((s ^ "'"), [])
            | _ -> (s, []) end) end)
  | Pi (d_, t) ->
      let (s1, c1) = transDec d_ in
      let (s2, c2) = transTerm t in (((("{" ^ s1) ^ "}") ^ s2), (c1 @ c2))
  | Fn (d_, t) ->
      let (s1, c1) = transDec d_ in
      let (s2, c2) = transTerm t in (((("[" ^ s1) ^ "]") ^ s2), (c1 @ c2))
  | App (t1, t2) ->
      let (s1, c1) = transTerm t1 in
      let (s2, c2) = transTerm t2 in (((s1 ^ " ") ^ s2), (c1 @ c2))
  | D.Omit -> ("_", [])
  | Paren t -> let (s, c) = transTerm t in ((("(" ^ s) ^ ")"), c)
  | Of (t1, t2) ->
      let (s1, c1) = transTerm t1 in
      let (s2, c2) = transTerm t2 in (((s1 ^ ":") ^ s2), (c1 @ c2))
  | Dot (t, s2) ->
      let (s1, c1) = transTerm t in (((("o_" ^ s2) ^ " ") ^ s1), c1) end
let rec transDec (Dec (s, t)) =
  let (s', c) = transTerm t in (((s ^ ":") ^ s'), c)
let rec transWorld =
  begin function
  | WorldIdent s ->
      let qid = Names.Qid ([], s) in
      let cid =
        begin match Names.constLookup qid with
        | None ->
            raise
              (Names.Error
                 (((^) "Undeclared label " Names.qidToString
                     (valOf (Names.constUndef qid)))
                    ^ "."))
        | Some cid -> cid end in
      [cid]
  | Plus (w1_, w2_) -> (@) (transWorld w1_) transWorld w2_
  | Concat (w1_, w2_) -> (@) (transWorld w1_) transWorld w2_
  | Times (w_) -> transWorld w_ end(* We should use the worlds we have defined in Tomega, but this
              is not good enough, because worlds are not defined
              by a regualar expression.  Therefore this is a patch *)
let rec transFor' (Psi, d_) =
  let g_ = I.Decl (I.Null, d_) in
  let JWithCtx (Decl (I.Null, d'_), ReconTerm.JNothing) =
    ReconTerm.reconWithCtx
      (Psi, (ReconTerm.jwithctx (g_, ReconTerm.jnothing))) in
  d'_
let rec transFor =
  begin function
  | (Psi, D.True) -> T.True
  | (Psi, And (EF1, EF2)) ->
      T.And ((transFor (Psi, EF1)), (transFor (Psi, EF2)))
  | (Psi, Forall (d_, f_)) ->
      let (D'', []) = transDec d_ in
      let d'_ = transFor' (Psi, (stringTodec D'')) in
      T.All
        (((T.UDec d'_), T.Explicit), (transFor ((I.Decl (Psi, d'_)), f_)))
  | (Psi, Exists (d_, f_)) ->
      let (D'', []) = transDec d_ in
      let d'_ = transFor' (Psi, (stringTodec D'')) in
      T.Ex ((d'_, T.Explicit), (transFor ((I.Decl (Psi, d'_)), f_)))
  | (Psi, ForallOmitted (d_, f_)) ->
      let (D'', []) = transDec d_ in
      let d'_ = transFor' (Psi, (stringTodec D'')) in
      T.All
        (((T.UDec d'_), T.Implicit), (transFor ((I.Decl (Psi, d'_)), f_)))
  | (Psi, ExistsOmitted (d_, f_)) ->
      let (D'', []) = transDec d_ in
      let d'_ = transFor' (Psi, (stringTodec D'')) in
      T.Ex ((d'_, T.Implicit), (transFor ((I.Decl (Psi, d'_)), f_)))
  | (Psi, World (w_, EF)) ->
      T.World ((T.Worlds (transWorld w_)), (transFor (Psi, EF))) end
let rec stringToterm s =
  let f = LS.expose (L.lexStream (TextIO.openString s)) in
  let (t, f') = ParseTerm.parseTerm' f in let r2 = checkEOF f' in t
let rec head =
  begin function
  | Head s -> s
  | AppLF (h_, _) -> head h_
  | AppMeta (h_, _) -> head h_ end
let rec lamClosure =
  begin function
  | (All ((d_, _), f_), p_) -> T.Lam (d_, (lamClosure (f_, p_)))
  | (World (_, f_), p_) -> lamClosure (f_, p_)
  | (Ex _, p_) -> p_ end
let rec exists =
  begin function
  | (c, []) -> raise (Error "Current world is not subsumed")
  | (c, c'::cids) -> if c = c' then begin () end
      else begin exists (c, cids) end end
let rec subsumed =
  begin function
  | ([], cids') -> ()
  | (c::cids, cids') -> (begin exists (c, cids'); subsumed (cids, cids') end) end
let rec checkForWorld =
  begin function
  | (World ((Worlds cids as w_), f_), t', Worlds cids') ->
      let _ = subsumed (cids', cids) in (((f_, t', w_))
        (* check that W is at least as large as W' *))
  | FtW -> FtW end
let rec dotn =
  begin function | (t, 0) -> t | (t, n) -> I.dot1 (dotn (t, (n - 1))) end
let rec append =
  begin function
  | (Psi, I.Null) -> Psi
  | (Psi, Decl (Psi', d_)) -> I.Decl ((append (Psi, Psi')), d_) end
let rec parseTerm (Psi, (s, v_)) =
  let (term', c) = transTerm s in
  let term = stringToterm term' in
  let JOf ((u_, occ), (_, _), l_) =
    ReconTerm.reconWithCtx ((T.coerceCtx Psi), (ReconTerm.jof' (term, v_))) in
  u_
let rec parseDec (Psi, s) =
  let (dec', c) = transDec s in
  let dec = stringTodec dec' in
  let JWithCtx (Decl (I.Null, d_), ReconTerm.JNothing) =
    ReconTerm.reconWithCtx
      ((T.coerceCtx Psi),
        (ReconTerm.jwithctx ((I.Decl (I.Null, dec)), ReconTerm.jnothing))) in
  let Dec (Some n, _) = d_ in d_
let rec transDecs =
  begin function
  | (Psi, D.Empty, sc, w_) -> sc (Psi, w_)
  | (Psi, FormDecl (FormD, ds_), sc, w_) ->
      transForDec (Psi, FormD, ds_, sc, w_)
  | (Psi, ValDecl (ValD, ds_), sc, w_) ->
      transValDec (Psi, ValD, ds_, sc, w_)
  | (Psi, NewDecl (d_, ds_), sc, w_) ->
      let d'_ = T.UDec (parseDec (Psi, d_)) in
      ((T.Let
          ((T.PDec (None, T.True)),
            (T.Lam (d'_, (transDecs ((I.Decl (Psi, d'_)), ds_, sc, w_)))),
            (T.Var 1)))
        (*          T.Let (T.PDec (NONE, T.True), T.Lam (D', transDecs (I.Decl (Psi, D'), Ds, sc, W)), T.Unit) *)
        (* T.True is not right! -- cs Sat Jun 28 11:43:30 2003  *))
  | _ ->
      raise
        (Error
           "Constant declaration must be followed by a constant definition") end
let rec lookup =
  begin function
  | (I.Null, n, s) -> raise (Error ("Undeclared constant " ^ s))
  | (Decl (g_, PDec (None, _)), n, s) -> lookup (g_, (n + 1), s)
  | (Decl (g_, UDec _), n, s) -> lookup (g_, (n + 1), s)
  | (Decl (g_, PDec (Some s', f_)), n, s) ->
      if s = s' then begin (n, (T.forSub (f_, (T.Shift n)))) end
      else begin lookup (g_, (n + 1), s) end end
let rec transHead =
  begin function
  | (Psi, Head s, args) ->
      let (n, f_) = lookup (Psi, 1, s) in
      transHead' ((f_, T.id), I.Nil, args)
  | (Psi, AppLF (h, t), args) -> transHead (Psi, h, (t :: args)) end
let rec transHead' =
  begin function
  | ((World (_, f_), s), s_, args) -> transHead' ((f_, s), s_, args)
  | ((All ((UDec (Dec (_, v_)), T.Implicit), f'_), s), s_, args) ->
      let x_ =
        I.newEVar ((I.Decl (I.Null, I.NDec)), (I.EClo (v_, (T.coerceSub s)))) in
      transHead' ((f'_, (T.Dot ((T.Exp x_), s))), (I.App (x_, s_)), args)
  | ((All ((UDec (Dec (_, v_)), T.Explicit), f'_), s), s_, t::args) ->
      let (term', c) = transTerm t in
      let term = stringToterm term' in
      let JOf ((u_, occ), (_, _), l_) =
        ReconTerm.reconWithCtx
          (I.Null, (ReconTerm.jof' (term, (I.EClo (v_, (T.coerceSub s)))))) in
      transHead' ((f'_, (T.Dot ((T.Exp u_), s))), (I.App (u_, s_)), args)
  | ((f_, s), s_, []) -> ((f_, s), s_) end
let rec spineToSub =
  begin function
  | ((I.Nil, _), s') -> s'
  | ((App (u_, s_), t), s') ->
      T.Dot ((T.Exp (I.EClo (u_, t))), (spineToSub ((s_, t), s'))) end
let rec transPattern =
  begin function
  | (p, (Ex ((Dec (_, v_), T.Implicit), f'_), s)) ->
      transPattern
        (p,
          (f'_,
            (T.Dot
               ((T.Exp
                   (I.EVar
                      ((ref None), I.Null, (I.EClo (v_, (T.coerceSub s))),
                        (ref [])))), s))))
  | (PatInx (t, p), (Ex ((Dec (_, v_), T.Explicit), f'_), s)) ->
      let (term', c) = transTerm t in
      let term = stringToterm term' in
      let JOf ((u_, occ), (_, _), l_) =
        ReconTerm.reconWithCtx
          (I.Null, (ReconTerm.jof' (term, (I.EClo (v_, (T.coerceSub s)))))) in
      T.PairExp (u_, (transPattern (p, (f'_, (T.Dot ((T.Exp u_), s))))))
  | (D.PatUnit, (f_, s)) -> T.Unit end
let rec transFun1 =
  begin function
  | (Psi, (s', f_), FunDecl (Fun (eH, eP), ds_), sc, w_) ->
      let s = head eH in
      let _ = if s = s' then begin () end
        else begin
          raise
            (Error "Function defined is different from function declared.") end in
    transFun2
      (Psi, (s, f_), (D.FunDecl ((D.Bar (eH, eP)), ds_)), sc,
        (begin function | cs_ -> T.Case (T.Cases cs_) end), w_)
| (Psi, (s', f_), FunDecl (FunAnd (eH, eP), ds_), sc, w_) ->
    raise (Error "Mutual recursive functions not yet implemented")
| _ -> raise (Error "Function declaration expected") end
let rec transFun2 =
  begin function
  | (Psi, (s, f_), FunDecl (Bar (eH, eP), ds_), sc, k, w_) ->
      transFun3 (Psi, (s, f_), eH, eP, ds_, sc, k, w_)
  | (Psi, (s, f_), ds_, sc, k, w_) ->
      let d_ = T.PDec ((Some s), f_) in
      let p'_ = T.Rec (d_, (lamClosure (f_, (k [])))) in (p'_, ds_) end
let rec transFun3 (Psi, (s, f_), eH, eP, ds_, sc, k, w_) =
  let _ =
    if (head eH) <> s
    then begin raise (Error "Functions don't all have the same name") end
    else begin () end in
let _ = Names.varReset I.Null in
let Psi0 = I.Decl (Psi, (T.PDec ((Some s), f_))) in
let ((f'_, t'), s_) = transHead (Psi0, eH, []) in
let (Psi', s'_) = Abstract.abstractSpine (s_, I.id) in
let Psi'' = append (Psi0, (T.embedCtx Psi')) in
let m0 = I.ctxLength Psi0 in
let m' = I.ctxLength Psi' in
let t0 = dotn ((I.Shift m0), m') in
let t'' = spineToSub ((s'_, t0), (T.Shift m')) in
let p_ = transProgI (Psi'', eP, (f'_, t'), w_) in
((transFun2
    (Psi, (s, f_), ds_, sc,
      (begin function | cs_ -> k ((Psi'', t'', p_) :: cs_) end), w_))
  (*                val F' = T.forSub (F, t) *)(* |Psi''| = m0 + m' *)
  (* Psi0, Psi'[^m0] |- t0 : Psi' *)(*        val t1 = T.Dot (T.Prg (T.Root (T.Var (m'+1), T.Nil)), T.Shift (m'))    BUG !!!! Wed Jun 25 11:23:13 2003 *)
  (* Psi0, Psi'[^m0] |- t1 : F[^m0]  *)(*        val _ = print (TomegaPrint.forToString (Names.ctxName (T.coerceCtx Psi''), myF) ^ "\n") *))
let rec transForDec (Psi, Form (s, eF), ds_, sc, w_) =
  let g_ = Names.ctxName (T.coerceCtx Psi) in
  let f_ = transFor (g_, eF) in
  let World (w_, f'_) as F'' = T.forSub (f_, T.id) in
  let _ = TomegaTypeCheck.checkFor (Psi, F'') in
  let (p_, ds'_) = transFun1 (Psi, (s, f'_), ds_, sc, w_) in
  let d_ = T.PDec ((Some s), F'') in
  ((T.Let
      (d_, (T.Box (w_, p_)),
        (transDecs
           ((I.Decl (Psi, d_)), ds'_, (begin function | p'_ -> sc p'_ end),
           w_))))
    (*        val _ = print s
          val _ = print " :: "
          val _ = print (TomegaPrint.forToString (T.embedCtx G, F'') ^ "\n") *))
let rec transValDec (Psi, Val (EPat, eP, eFopt), ds_, sc, w_) =
  let (p_, (f'_, t')) =
    begin match eFopt with
    | None -> transProgS (Psi, eP, w_, [])
    | Some eF ->
        let f'_ = transFor ((T.coerceCtx Psi), eF) in
        let p'_ = transProgIN (Psi, eP, f'_, w_) in (p'_, (f'_, T.id)) end in
let F'' = T.forSub (f'_, t') in
let Pat = transPattern (EPat, (f'_, t')) in
let d_ = T.PDec (None, F'') in
let (Psi', Pat') = Abstract.abstractTomegaPrg Pat in
let m = I.ctxLength Psi' in
let t = T.Dot ((T.Prg Pat'), (T.Shift m)) in
let Psi'' = append (Psi, Psi') in
let P'' = transDecs (Psi'', ds_, sc, w_) in
((T.Let (d_, p_, (T.Case (T.Cases [(Psi'', t, P'')]))))
  (*        val t = T.Dot (T.Prg Pat', T.id)  was --cs Tue Jun 24 13:04:55 2003 *))
let rec transProgI (Psi, eP, Ft, w_) =
  transProgIN (Psi, eP, (T.forSub Ft), w_)
let rec transProgIN =
  begin function
  | (Psi, D.Unit, T.True, w_) -> T.Unit
  | (Psi, (Inx (s, EP) as p_), Ex ((Dec (_, v_), T.Explicit), f'_), w_) ->
      let u_ = parseTerm (Psi, (s, v_)) in
      let p'_ = transProgI (Psi, EP, (f'_, (T.Dot ((T.Exp u_), T.id))), w_) in
      T.PairExp (u_, p'_)
  | (Psi, Let (eDs, eP), f_, w_) ->
      transDecs
        (Psi, eDs,
          (begin function
           | (Psi', w'_) ->
               transProgI
                 (Psi', eP,
                   (f_, (T.Shift ((-) (I.ctxLength Psi') I.ctxLength Psi))),
                   w'_) end), w_)
  | (Psi, Choose (eD, eP), f_, w_) ->
      let d'_ = parseDec (Psi, eD) in
      let Psi'' = I.Decl (Psi, (T.UDec d'_)) in
      T.Choose
        (T.Lam
           ((T.UDec d'_), (transProgI (Psi'', eP, (f_, (T.Shift 1)), w_))))
  | (Psi, New ([], eP), f_, w_) -> transProgIN (Psi, eP, f_, w_)
  | (Psi, New (eD::eDs, eP), f_, w_) ->
      let d'_ = parseDec (Psi, eD) in
      let Psi'' = I.Decl (Psi, (T.UDec d'_)) in
      T.New
        (T.Lam
           ((T.UDec d'_),
             (transProgI
                (Psi'', (D.New ((eD :: eDs), eP)), (f_, (T.Shift 1)), w_))))
  | (Psi, (AppTerm (EP, s) as p_), f_, w_) ->
      let (p'_, (f'_, _)) = transProgS (Psi, p_, w_, []) in
      let () = () in ((p'_)(* check that F == F' *)) end
let rec transProgS =
  begin function
  | (Psi, D.Unit, w_, args) -> (T.Unit, (T.True, T.id))
  | (Psi, AppTerm (EP, s), w_, args) -> transProgS (Psi, EP, w_, (s :: args))
  | (Psi, Const name, w_, args) ->
      let (n, f_) = lookup (Psi, 1, name) in
      let (s_, fs'_) = transProgS' (Psi, (f_, T.id), w_, args) in
      ((((T.Redex ((T.Var n), s_)), fs'_))
        (*         val lemma = T.lemmaName name
           val F = T.lemmaFor lemma *))
  | (Psi, Choose (eD, eP), w_, args) ->
      let d'_ = parseDec (Psi, eD) in
      let (p_, (f_, t)) =
        transProgS ((I.Decl (Psi, (T.UDec d'_))), eP, w_, args) in
      ((T.Choose (T.Lam ((T.UDec d'_), p_))), (f_, t))
  | (Psi, New ([], eP), w_, args) -> transProgS (Psi, eP, w_, args)
  | (Psi, New (eD::eDs, eP), w_, args) ->
      let d'_ = parseDec (Psi, eD) in
      let (p_, (f_, t)) =
        transProgS
          ((I.Decl (Psi, (T.UDec d'_))), (D.New (eDs, eP)), w_, args) in
      let UDec (D'') = externalizeMDec ((I.ctxLength Psi), (T.UDec d'_)) in
      let (b_, _) = T.deblockify (I.Decl (I.Null, D'')) in
      let f'_ = TA.raiseFor (b_, (f_, (T.coerceSub t))) in
      ((((T.New (T.Lam ((T.UDec d'_), p_))), (f'_, T.id)))
        (* bug: forgot to raise F[t] to F' --cs Tue Jul  1 10:49:52 2003 *)) end
let rec transProgS' =
  begin function
  | (Psi, (World (_, f_), s), w_, args) ->
      transProgS' (Psi, (f_, s), w_, args)
  | (Psi, (All ((UDec (Dec (_, v_)), T.Implicit), f'_), s), w_, args) ->
      let g_ = T.coerceCtx Psi in
      let x_ = I.newEVar (g_, (I.EClo (v_, (T.coerceSub s)))) in
      let (s_, fs'_) =
        transProgS' (Psi, (f'_, (T.Dot ((T.Exp x_), s))), w_, args) in
      ((((T.AppExp ((Whnf.normalize (x_, I.id)), s_)), fs'_))
        (*        val X = I.EVar (ref NONE, I.Null, I.EClo (V, T.coerceSub s), ref nil) *))
  | (Psi, (All ((UDec (Dec (_, v_)), T.Explicit), f'_), s), w_, t::args) ->
      let u_ = parseTerm (Psi, (t, (I.EClo (v_, (T.coerceSub s))))) in
      let (s_, fs'_) =
        transProgS' (Psi, (f'_, (T.Dot ((T.Exp u_), s))), w_, args) in
      ((((T.AppExp (u_, s_)), fs'_))
        (*        val (F'', s'', _) = checkForWorld (F', T.Dot (T.Exp U, s), W) *))
  | (Psi, (f_, s), _, []) -> (T.Nil, (f_, s)) end
let rec transProgram (ds_) =
  transDecs (I.Null, ds_, (begin function | (Psi, w_) -> T.Unit end),
    (T.Worlds []))
let transFor =
  begin function | f_ -> let f'_ = transFor (I.Null, f_) in f'_ end
let transDecs = transProgram
let internalizeSig = internalizeSig
let externalizePrg = begin function | p_ -> externalizePrg (0, p_) end
end