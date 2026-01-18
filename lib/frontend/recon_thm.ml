
module type THMEXTSYN  =
  sig
    module ExtSyn : EXTSYN
    type nonrec order
    val varg : (Paths.region * string list) -> order
    val lex : (Paths.region * order list) -> order
    val simul : (Paths.region * order list) -> order
    type nonrec callpats
    val callpats :
      (string * string option list * Paths.region) list -> callpats
    type nonrec tdecl
    val tdecl : (order * callpats) -> tdecl
    type nonrec predicate
    val predicate : (string * Paths.region) -> predicate
    type nonrec rdecl
    val rdecl : (predicate * order * order * callpats) -> rdecl
    type nonrec tableddecl
    val tableddecl : (string * Paths.region) -> tableddecl
    type nonrec keepTabledecl
    val keepTabledecl : (string * Paths.region) -> keepTabledecl
    type nonrec prove
    val prove : (int * tdecl) -> prove
    type nonrec establish
    val establish : (int * tdecl) -> establish
    type nonrec assert__
    val assert__ : callpats -> assert__
    type nonrec decs
    type nonrec theorem
    type nonrec theoremdec
    val null : decs
    val decl : (decs * ExtSyn.dec) -> decs
    val top : theorem
    val exists : (decs * theorem) -> theorem
    val forall : (decs * theorem) -> theorem
    val forallStar : (decs * theorem) -> theorem
    val forallG : ((decs * decs) list * theorem) -> theorem
    val dec : (string * theorem) -> theoremdec
    type nonrec wdecl
    val wdecl : ((string list * string) list * callpats) -> wdecl
  end (* External Syntax for meta theorems *)
(* Author: Carsten Schuermann *)
(*! structure Paths : PATHS  !*)
(* -bp *) (* -bp *)
(* world checker *)
(*  val wdecl : (decs * decs) list * callpats -> wdecl *)
(* signature THMEXTSYN *)
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




(* Reconstruct Termination Information *)
(* Author: Carsten Schuermann *)
(* Modified: Brigitte Pientka *)
module ReconThm(ReconThm:sig
                           module Global : GLOBAL
                           module Abstract : ABSTRACT
                           module Constraints : CONSTRAINTS
                           module Names : NAMES
                           module ThmSyn' : THMSYN
                           module ReconTerm' : RECON_TERM
                           (* structure IntSyn : INTSYN *)
                           (*! sharing Abstract.IntSyn = IntSyn !*)
                           (*! sharing Names.IntSyn = IntSyn !*)
                           (*! structure Paths' : PATHS !*)
                           (*! sharing ReconTerm'.IntSyn = IntSyn !*)
                           (*! sharing ReconTerm'.Paths = Paths'  !*)
                           module Print : PRINT
                         end) : RECON_THM =
  struct
    (*! sharing Print.IntSyn = IntSyn !*)
    module ThmSyn = ThmSyn'
    (*! structure Paths = Paths' !*)
    module ExtSyn = ReconTerm'
    exception Error of string 
    module M = ModeSyn
    module I = IntSyn
    module __l = ThmSyn
    module P = Paths
    module T = ReconTerm'
    let rec error (r, msg) = raise (Error (P.wrap (r, msg)))
    type nonrec order = (ThmSyn.__Order * Paths.region)
    let rec varg (r, __l) = ((ThmSyn.Varg __l), r)
    let rec lex (r0, __l) =
      let rec lex' =
        function
        | nil -> (nil, r0)
        | (O, r)::__l ->
            let (__Os, r') = lex' __l in ((O :: __Os), (Paths.join (r, r'))) in
      let (__Os, r1) = lex' __l in ((ThmSyn.Lex __Os), r1)
    let rec simul (r0, __l) =
      let rec simul' =
        function
        | nil -> (nil, r0)
        | (O, r)::__l ->
            let (__Os, r') = simul' __l in ((O :: __Os), (Paths.join (r, r'))) in
      let (__Os, r1) = simul' __l in ((ThmSyn.Simul __Os), r1)
    type nonrec callpats = (ThmSyn.__Callpats * Paths.region list)
    let rec checkArgNumber =
      function
      | (0, Uni (I.Type), nil, r) -> ()
      | (0, Pi (_, V2), arg::args, r) -> checkArgNumber (0, V2, args, r)
      | (0, Pi (_, V2), nil, r) ->
          error (r, "Missing arguments in call pattern")
      | (0, Uni (I.Type), arg::args, r) ->
          error (r, "Extraneous arguments in call pattern")
      | (i, Pi (_, V2), args, r) -> checkArgNumber ((i - 1), V2, args, r)
    let rec checkCallPat =
      function
      | (ConDec (_, _, i, I.Normal, __v, I.Kind), P, r) ->
          checkArgNumber (i, __v, P, r)
      | (ConDec (a, _, _, Constraint _, _, _), P, r) ->
          error
            (r, (("Illegal constraint constant " ^ a) ^ " in call pattern"))
      | (ConDec (a, _, _, Foreign _, _, _), P, r) ->
          error (r, (("Illegal foreign constant " ^ a) ^ " in call pattern"))
      | (ConDec (a, _, _, _, _, I.Type), P, r) ->
          error
            (r, (("Constant " ^ a) ^ " in call pattern not a type family"))
      | (ConDef (a, _, _, _, _, _, _), P, r) ->
          error (r, (("Illegal defined constant " ^ a) ^ " in call pattern"))
      | (AbbrevDef (a, _, _, _, _, _), P, r) ->
          error (r, (("Illegal abbreviation " ^ a) ^ " in call pattern"))
      | (BlockDec (a, _, _, _), P, r) ->
          error (r, (("Illegal block identifier " ^ a) ^ " in call pattern"))
      | (SkoDec (a, _, _, _, _), P, r) ->
          error (r, (("Illegal Skolem constant " ^ a) ^ " in call pattern"))
    let rec callpats (__l) =
      let rec callpats' =
        function
        | nil -> (nil, nil)
        | (name, P, r)::__l ->
            let (cps, rs) = callpats' __l in
            let qid = Names.Qid (nil, name) in
            (match Names.constLookup qid with
             | None ->
                 error
                   (r,
                     (((^) "Undeclared identifier " Names.qidToString
                         (valOf (Names.constUndef qid)))
                        ^ " in call pattern"))
             | Some cid ->
                 (checkCallPat ((I.sgnLookup cid), P, r);
                  (((cid, P) :: cps), (r :: rs)))) in
      let (cps, rs) = callpats' __l in ((ThmSyn.Callpats cps), rs)
    type nonrec tdecl = (ThmSyn.__TDecl * (Paths.region * Paths.region list))
    let rec tdecl ((O, r), (C, rs)) = ((ThmSyn.TDecl (O, C)), (r, rs))
    let rec tdeclTotDecl (T) = T
    type nonrec predicate = (ThmSyn.__Predicate * Paths.region)
    let rec predicate =
      function
      | ("LESS", r) -> (ThmSyn.Less, r)
      | ("LEQ", r) -> (ThmSyn.Leq, r)
      | ("EQUAL", r) -> (ThmSyn.Eq, r)
    type nonrec rdecl = (ThmSyn.__RDecl * (Paths.region * Paths.region list))
    let rec rdecl ((P, r0), (O1, r1), (O2, r2), (C, rs)) =
      let r = Paths.join (r1, r2) in
      ((ThmSyn.RDecl ((ThmSyn.RedOrder (P, O1, O2)), C)),
        ((Paths.join (r0, r)), rs))
    let rec rdeclTorDecl (T) = T
    type nonrec tableddecl = (ThmSyn.__TabledDecl * Paths.region)
    let rec tableddecl (name, r) =
      let qid = Names.Qid (nil, name) in
      match Names.constLookup qid with
      | None ->
          error
            (r,
              (((^) "Undeclared identifier " Names.qidToString
                  (valOf (Names.constUndef qid)))
                 ^ " in call pattern"))
      | Some cid -> ((ThmSyn.TabledDecl cid), r)
    let rec tableddeclTotabledDecl (T) = T
    type nonrec keepTabledecl = (ThmSyn.__KeepTableDecl * Paths.region)
    let rec keepTabledecl (name, r) =
      let qid = Names.Qid (nil, name) in
      match Names.constLookup qid with
      | None ->
          error
            (r,
              (((^) "Undeclared identifier " Names.qidToString
                  (valOf (Names.constUndef qid)))
                 ^ " in call pattern"))
      | Some cid -> ((ThmSyn.KeepTableDecl cid), r)
    let rec keepTabledeclToktDecl (T) = T
    type nonrec prove = (ThmSyn.__PDecl * (Paths.region * Paths.region list))
    let rec prove (n, (td, rrs)) = ((ThmSyn.PDecl (n, td)), rrs)
    let rec proveToProve (P) = P
    type nonrec establish =
      (ThmSyn.__PDecl * (Paths.region * Paths.region list))
    let rec establish (n, (td, rrs)) = ((ThmSyn.PDecl (n, td)), rrs)
    let rec establishToEstablish (P) = P
    type nonrec assert__ = (ThmSyn.__Callpats * Paths.region list)
    let rec assert__ (cp, rs) = (cp, rs)
    let rec assertToAssert (P) = P
    type nonrec decs = ExtSyn.dec I.__Ctx
    let null = I.Null
    let decl = I.Decl
    type nonrec labeldec = (decs * decs)
    type nonrec thm =
      (labeldec list * ExtSyn.dec I.__Ctx * ModeSyn.__Mode I.__Ctx * int)
    type nonrec theorem = thm -> thm
    type nonrec theoremdec = (string * theorem)
    let rec dec (name, t) = (name, t)
    let rec ctxAppend =
      function
      | (__g, I.Null) -> __g
      | (__g, Decl (__g', __d)) -> I.Decl ((ctxAppend (__g, __g')), __d)
    let rec ctxMap arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (f, I.Null) -> I.Null
      | (f, Decl (__g, __d)) -> I.Decl ((ctxMap f __g), (f __d))
    let rec ctxBlockToString (G0, (G1, G2)) =
      let _ = Names.varReset I.Null in
      let G0' = Names.ctxName G0 in
      let G1' = Names.ctxLUName G1 in
      let G2' = Names.ctxLUName G2 in
      (^) ((((Print.ctxToString (I.Null, G0')) ^ "\n") ^
              (match G1' with
               | I.Null -> ""
               | _ -> ((^) "some " Print.ctxToString (G0', G1')) ^ "\n"))
             ^ "pi ")
        Print.ctxToString ((ctxAppend (G0', G1')), G2')
    let rec checkFreevars =
      function
      | (I.Null, (G1, G2), r) -> ()
      | (G0, (G1, G2), r) ->
          let _ = Names.varReset I.Null in
          let G0' = Names.ctxName G0 in
          let G1' = Names.ctxLUName G1 in
          let G2' = Names.ctxLUName G2 in
          error
            (r,
              ((^) "Free variables in context block after term reconstruction:\n"
                 ctxBlockToString (G0', (G1', G2'))))
    let rec abstractCtxPair (g1, g2) =
      let r =
        match ((T.ctxRegion g1), (T.ctxRegion g2)) with
        | (Some r1, Some r2) -> Paths.join (r1, r2)
        | (_, Some r2) -> r2 in
      let JWithCtx (G1, JWithCtx (G2, _)) =
        T.recon (T.jwithctx (g1, (T.jwithctx (g2, T.jnothing)))) in
      let (G0, (G1')::(G2')::[]) =
        try Abstract.abstractCtxs [G1; G2]
        with
        | Error (C) ->
            error
              (r,
                ((^) (((^) "Constraints remain in context block after term reconstruction:\n"
                         ctxBlockToString (I.Null, (G1, G2)))
                        ^ "\n")
                   Print.cnstrsToString C)) in
      let _ = checkFreevars (G0, (G1', G2'), r) in (G1', G2')
    let rec top (GBs, g, M, k) = (GBs, g, M, k)
    let rec exists (g', t) (GBs, g, M, k) =
      t
        (GBs, (ctxAppend (g, g')),
          (ctxAppend (M, (ctxMap (function | _ -> M.Minus) g'))), k)
    let rec forall (g', t) (GBs, g, M, k) =
      t
        (GBs, (ctxAppend (g, g')),
          (ctxAppend (M, (ctxMap (function | _ -> M.Plus) g'))), k)
    let rec forallStar (g', t) (GBs, g, M, _) =
      t
        (GBs, (ctxAppend (g, g')),
          (ctxAppend (M, (ctxMap (function | _ -> M.Plus) g'))),
          (I.ctxLength g'))
    let rec forallG (gbs, (t : thm -> thm)) (_ : thm) =
      (t (gbs, I.Null, I.Null, 0) : thm)
    let rec theoremToTheorem t =
      let (gbs, g, M, k) = t (nil, I.Null, I.Null, 0) in
      let _ = Names.varReset IntSyn.Null in
      let GBs = List.map abstractCtxPair gbs in
      let JWithCtx (__g, _) = T.recon (T.jwithctx (g, T.jnothing)) in
      L.ThDecl (GBs, __g, M, k)
    let rec theoremDecToTheoremDec (name, t) = (name, (theoremToTheorem t))
    let rec abstractWDecl (W) = let W' = List.map Names.Qid W in W'
    type nonrec wdecl = (ThmSyn.__WDecl * Paths.region list)
    let rec wdecl (W, (cp, rs)) =
      ((ThmSyn.WDecl ((abstractWDecl W), cp)), rs)
    let rec wdeclTowDecl (T) = T
    (* everything else should be impossible! *)
    (* check whether they are families here? *)
    (* -bp *)
    (* predicate *)
    (* reduces declaration *)
    (* tabled declaration *)
    (* check whether they are families here? *)
    (* keepTable declaration *)
    (* check whether they are families here? *)
    (* Theorem and prove declarations *)
    (* each block reconstructed independent of others *)
    (* closed nf *)
    (* World checker *)
    (* avoid this re-copying? -fp *)
    type nonrec order = order
    let varg = varg
    let lex = lex
    let simul = simul
    type nonrec callpats = callpats
    let callpats = callpats
    type nonrec tdecl = tdecl
    let tdecl = tdecl
    (* -bp *)
    type nonrec predicate = predicate
    let predicate = predicate
    (* -bp *)
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
