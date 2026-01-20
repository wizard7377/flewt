
module type THMEXTSYN  =
  sig
    module ExtSyn : EXTSYN
    type nonrec order
    val varg : Paths.region -> string list -> order
    val lex : Paths.region -> order list -> order
    val simul : Paths.region -> order list -> order
    type nonrec callpats
    val callpats :
      (string * string option list * Paths.region) list -> callpats
    type nonrec tdecl
    val tdecl : order -> callpats -> tdecl
    type nonrec predicate
    val predicate : string -> Paths.region -> predicate
    type nonrec rdecl
    val rdecl : predicate -> order -> order -> callpats -> rdecl
    type nonrec tableddecl
    val tableddecl : string -> Paths.region -> tableddecl
    type nonrec keepTabledecl
    val keepTabledecl : string -> Paths.region -> keepTabledecl
    type nonrec prove
    val prove : int -> tdecl -> prove
    type nonrec establish
    val establish : int -> tdecl -> establish
    type nonrec assert__
    val assert__ : callpats -> assert__
    type nonrec decs
    type nonrec theorem
    type nonrec theoremdec
    val null : decs
    val decl : decs -> ExtSyn.dec -> decs
    val top : theorem
    val exists : decs -> theorem -> theorem
    val forall : decs -> theorem -> theorem
    val forallStar : decs -> theorem -> theorem
    val forallG : (decs * decs) list -> theorem -> theorem
    val dec : string -> theorem -> theoremdec
    type nonrec wdecl
    val wdecl : (string list * string) list -> callpats -> wdecl
  end
module type RECON_THM  =
  sig
    module ThmSyn : THMSYN
    include THMEXTSYN
    exception Error of string 
    val tdeclTotDecl :
      tdecl -> (ThmSyn.__TDecl * (Paths.region * Paths.region list))
    val rdeclTorDecl :
      rdecl -> (ThmSyn.__RDecl * (Paths.region * Paths.region list))
    val tableddeclTotabledDecl :
      tableddecl -> (ThmSyn.__TabledDecl * Paths.region)
    val keepTabledeclToktDecl :
      keepTabledecl -> (ThmSyn.__KeepTableDecl * Paths.region)
    val theoremToTheorem : theorem -> ThmSyn.__ThDecl
    val theoremDecToTheoremDec : theoremdec -> (string * ThmSyn.__ThDecl)
    val proveToProve :
      prove -> (ThmSyn.__PDecl * (Paths.region * Paths.region list))
    val establishToEstablish :
      establish -> (ThmSyn.__PDecl * (Paths.region * Paths.region list))
    val assertToAssert : assert__ -> (ThmSyn.__Callpats * Paths.region list)
    val wdeclTowDecl : wdecl -> (ThmSyn.__WDecl * Paths.region list)
  end;;




module ReconThm(ReconThm:sig
                           module Global : GLOBAL
                           module Abstract : ABSTRACT
                           module Constraints : CONSTRAINTS
                           module Names : NAMES
                           module ThmSyn' : THMSYN
                           module ReconTerm' : RECON_TERM
                           module Print : PRINT
                         end) : RECON_THM =
  struct
    module ThmSyn = ThmSyn'
    module ExtSyn = ReconTerm'
    exception Error of string 
    module M = ModeSyn
    module I = IntSyn
    module L = ThmSyn
    module P = Paths
    module T = ReconTerm'
    let rec error r msg = raise (Error (P.wrap (r, msg)))
    type nonrec order = (ThmSyn.__Order * Paths.region)
    let rec varg r (__L) = ((ThmSyn.Varg __L), r)
    let rec lex r0 (__L) =
      let rec lex' =
        function
        | nil -> (nil, r0)
        | (__O, r)::__L ->
            let (__Os, r') = lex' __L in
            ((__O :: __Os), (Paths.join (r, r'))) in
      let (__Os, r1) = lex' __L in ((ThmSyn.Lex __Os), r1)
    let rec simul r0 (__L) =
      let rec simul' =
        function
        | nil -> (nil, r0)
        | (__O, r)::__L ->
            let (__Os, r') = simul' __L in
            ((__O :: __Os), (Paths.join (r, r'))) in
      let (__Os, r1) = simul' __L in ((ThmSyn.Simul __Os), r1)
    type nonrec callpats = (ThmSyn.__Callpats * Paths.region list)
    let rec checkArgNumber __0__ __1__ __2__ __3__ =
      match (__0__, __1__, __2__, __3__) with
      | (0, Uni (I.Type), nil, r) -> ()
      | (0, Pi (_, __V2), arg::args, r) -> checkArgNumber (0, __V2, args, r)
      | (0, Pi (_, __V2), nil, r) ->
          error (r, "Missing arguments in call pattern")
      | (0, Uni (I.Type), arg::args, r) ->
          error (r, "Extraneous arguments in call pattern")
      | (i, Pi (_, __V2), args, r) -> checkArgNumber ((i - 1), __V2, args, r)
    let rec checkCallPat __4__ __5__ __6__ =
      match (__4__, __5__, __6__) with
      | (ConDec (_, _, i, I.Normal, __V, I.Kind), __P, r) ->
          checkArgNumber (i, __V, __P, r)
      | (ConDec (a, _, _, Constraint _, _, _), __P, r) ->
          error
            (r, (("Illegal constraint constant " ^ a) ^ " in call pattern"))
      | (ConDec (a, _, _, Foreign _, _, _), __P, r) ->
          error (r, (("Illegal foreign constant " ^ a) ^ " in call pattern"))
      | (ConDec (a, _, _, _, _, I.Type), __P, r) ->
          error
            (r, (("Constant " ^ a) ^ " in call pattern not a type family"))
      | (ConDef (a, _, _, _, _, _, _), __P, r) ->
          error (r, (("Illegal defined constant " ^ a) ^ " in call pattern"))
      | (AbbrevDef (a, _, _, _, _, _), __P, r) ->
          error (r, (("Illegal abbreviation " ^ a) ^ " in call pattern"))
      | (BlockDec (a, _, _, _), __P, r) ->
          error (r, (("Illegal block identifier " ^ a) ^ " in call pattern"))
      | (SkoDec (a, _, _, _, _), __P, r) ->
          error (r, (("Illegal Skolem constant " ^ a) ^ " in call pattern"))
    let rec callpats (__L) =
      let rec callpats' =
        function
        | nil -> (nil, nil)
        | (name, __P, r)::__L ->
            let (cps, rs) = callpats' __L in
            let qid = Names.Qid (nil, name) in
            (((match Names.constLookup qid with
               | NONE ->
                   error
                     (r,
                       (((^) "Undeclared identifier " Names.qidToString
                           (valOf (Names.constUndef qid)))
                          ^ " in call pattern"))
               | Some cid ->
                   (checkCallPat ((I.sgnLookup cid), __P, r);
                    (((cid, __P) :: cps), (r :: rs)))))
              (* check whether they are families here? *)) in
      let (cps, rs) = callpats' __L in ((ThmSyn.Callpats cps), rs)
    type nonrec tdecl = (ThmSyn.__TDecl * (Paths.region * Paths.region list))
    let rec tdecl (__O, r) (__C, rs) = ((ThmSyn.TDecl (__O, __C)), (r, rs))
    let rec tdeclTotDecl (__T) = __T
    type nonrec predicate = (ThmSyn.__Predicate * Paths.region)
    let rec predicate __7__ __8__ =
      match (__7__, __8__) with
      | ("LESS", r) -> (ThmSyn.Less, r)
      | ("LEQ", r) -> (ThmSyn.Leq, r)
      | ("EQUAL", r) -> (ThmSyn.Eq, r)
    type nonrec rdecl = (ThmSyn.__RDecl * (Paths.region * Paths.region list))
    let rec rdecl (__P, r0) (__O1, r1) (__O2, r2) (__C, rs) =
      let r = Paths.join (r1, r2) in
      ((ThmSyn.RDecl ((ThmSyn.RedOrder (__P, __O1, __O2)), __C)),
        ((Paths.join (r0, r)), rs))
    let rec rdeclTorDecl (__T) = __T
    type nonrec tableddecl = (ThmSyn.__TabledDecl * Paths.region)
    let rec tableddecl name r =
      let qid = Names.Qid (nil, name) in
      ((match Names.constLookup qid with
        | NONE ->
            error
              (r,
                (((^) "Undeclared identifier " Names.qidToString
                    (valOf (Names.constUndef qid)))
                   ^ " in call pattern"))
        | Some cid -> ((ThmSyn.TabledDecl cid), r))
        (* check whether they are families here? *))
    let rec tableddeclTotabledDecl (__T) = __T
    type nonrec keepTabledecl = (ThmSyn.__KeepTableDecl * Paths.region)
    let rec keepTabledecl name r =
      let qid = Names.Qid (nil, name) in
      ((match Names.constLookup qid with
        | NONE ->
            error
              (r,
                (((^) "Undeclared identifier " Names.qidToString
                    (valOf (Names.constUndef qid)))
                   ^ " in call pattern"))
        | Some cid -> ((ThmSyn.KeepTableDecl cid), r))
        (* check whether they are families here? *))
    let rec keepTabledeclToktDecl (__T) = __T
    type nonrec prove = (ThmSyn.__PDecl * (Paths.region * Paths.region list))
    let rec prove n (td, rrs) = ((ThmSyn.PDecl (n, td)), rrs)
    let rec proveToProve (__P) = __P
    type nonrec establish =
      (ThmSyn.__PDecl * (Paths.region * Paths.region list))
    let rec establish n (td, rrs) = ((ThmSyn.PDecl (n, td)), rrs)
    let rec establishToEstablish (__P) = __P
    type nonrec assert__ = (ThmSyn.__Callpats * Paths.region list)
    let rec assert__ cp rs = (cp, rs)
    let rec assertToAssert (__P) = __P
    type nonrec decs = ExtSyn.dec I.__Ctx
    let null = I.Null
    let decl = I.Decl
    type nonrec labeldec = (decs * decs)
    type nonrec thm =
      (labeldec list * ExtSyn.dec I.__Ctx * ModeSyn.__Mode I.__Ctx * int)
    type nonrec theorem = thm -> thm
    type nonrec theoremdec = (string * theorem)
    let rec dec name t = (name, t)
    let rec ctxAppend __9__ __10__ =
      match (__9__, __10__) with
      | (__G, I.Null) -> __G
      | (__G, Decl (__G', __D)) -> I.Decl ((ctxAppend (__G, __G')), __D)
    let rec ctxMap __11__ __12__ =
      match (__11__, __12__) with
      | (f, I.Null) -> I.Null
      | (f, Decl (__G, __D)) -> I.Decl ((ctxMap f __G), (f __D))
    let rec ctxBlockToString (__G0) (__G1, __G2) =
      let _ = Names.varReset I.Null in
      let G0' = Names.ctxName __G0 in
      let G1' = Names.ctxLUName __G1 in
      let G2' = Names.ctxLUName __G2 in
      (^) ((((Print.ctxToString (I.Null, G0')) ^ "\n") ^
              (match G1' with
               | I.Null -> ""
               | _ -> ((^) "some " Print.ctxToString (G0', G1')) ^ "\n"))
             ^ "pi ")
        Print.ctxToString ((ctxAppend (G0', G1')), G2')
    let rec checkFreevars __13__ __14__ __15__ =
      match (__13__, __14__, __15__) with
      | (I.Null, (__G1, __G2), r) -> ()
      | (__G0, (__G1, __G2), r) ->
          let _ = Names.varReset I.Null in
          let G0' = Names.ctxName __G0 in
          let G1' = Names.ctxLUName __G1 in
          let G2' = Names.ctxLUName __G2 in
          error
            (r,
              ((^) "Free variables in context block after term reconstruction:\n"
                 ctxBlockToString (G0', (G1', G2'))))
    let rec abstractCtxPair g1 g2 =
      let r =
        match ((T.ctxRegion g1), (T.ctxRegion g2)) with
        | (Some r1, Some r2) -> Paths.join (r1, r2)
        | (_, Some r2) -> r2 in
      let JWithCtx (__G1, JWithCtx (__G2, _)) =
        T.recon (T.jwithctx (g1, (T.jwithctx (g2, T.jnothing)))) in
      let (__G0, (G1')::(G2')::[]) =
        try Abstract.abstractCtxs [__G1; __G2]
        with
        | Error (__C) ->
            error
              (r,
                ((^) (((^) "Constraints remain in context block after term reconstruction:\n"
                         ctxBlockToString (I.Null, (__G1, __G2)))
                        ^ "\n")
                   Print.cnstrsToString __C)) in
      let _ = checkFreevars (__G0, (G1', G2'), r) in (((G1', G2'))
        (* each block reconstructed independent of others *)
        (* closed nf *))
    let rec top (GBs) g (__M) k = (GBs, g, __M, k)
    let rec exists g' t (GBs) g (__M) k =
      t
        (GBs, (ctxAppend (g, g')),
          (ctxAppend (__M, (ctxMap (fun _ -> M.Minus) g'))), k)
    let rec forall g' t (GBs) g (__M) k =
      t
        (GBs, (ctxAppend (g, g')),
          (ctxAppend (__M, (ctxMap (fun _ -> M.Plus) g'))), k)
    let rec forallStar g' t (GBs) g (__M) _ =
      t
        (GBs, (ctxAppend (g, g')),
          (ctxAppend (__M, (ctxMap (fun _ -> M.Plus) g'))), (I.ctxLength g'))
    let rec forallG gbs (t : thm -> thm) _ =
      (t (gbs, I.Null, I.Null, 0) : thm)
    let rec theoremToTheorem t =
      let (gbs, g, __M, k) = t (nil, I.Null, I.Null, 0) in
      let _ = Names.varReset IntSyn.Null in
      let GBs = List.map abstractCtxPair gbs in
      let JWithCtx (__G, _) = T.recon (T.jwithctx (g, T.jnothing)) in
      L.ThDecl (GBs, __G, __M, k)
    let rec theoremDecToTheoremDec name t = (name, (theoremToTheorem t))
    let rec abstractWDecl (__W) = let __W' = List.map Names.Qid __W in __W'
    type nonrec wdecl = (ThmSyn.__WDecl * Paths.region list)
    let rec wdecl (__W) (cp, rs) =
      ((ThmSyn.WDecl ((abstractWDecl __W), cp)), rs)
    let rec wdeclTowDecl (__T) = __T
    type nonrec order = order
    let varg = varg
    let lex = lex
    let simul = simul
    type nonrec callpats = callpats
    let callpats = callpats
    type nonrec tdecl = tdecl
    let tdecl = tdecl
    type nonrec predicate = predicate
    let predicate = predicate
    type nonrec rdecl = rdecl
    let rdecl = rdecl
    type nonrec tableddecl = tableddecl
    let tableddecl = tableddecl
    type nonrec keepTabledecl = keepTabledecl
    let keepTabledecl = keepTabledecl
    type nonrec prove = prove
    let prove = prove
    type nonrec establish = establish
    let establish = establish
    type nonrec assert__ = assert__
    let assert__ = assert__
    let tdeclTotDecl = tdeclTotDecl
    let rdeclTorDecl = rdeclTorDecl
    let tableddeclTotabledDecl = tableddeclTotabledDecl
    let keepTabledeclToktDecl = keepTabledeclToktDecl
    let proveToProve = proveToProve
    let establishToEstablish = establishToEstablish
    let assertToAssert = assertToAssert
    type nonrec decs = decs
    let null = null
    let decl = decl
    type nonrec theorem = theorem
    let top = top
    let forallStar = forallStar
    let forall = forall
    let exists = exists
    let forallG = forallG
    let theoremToTheorem = theoremToTheorem
    type nonrec theoremdec = theoremdec
    let dec = dec
    let theoremDecToTheoremDec = theoremDecToTheoremDec
    type nonrec wdecl = wdecl
    let wdeclTowDecl = wdeclTowDecl
    let wdecl = wdecl
  end ;;
