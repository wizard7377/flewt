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
    type nonrec assert_
    val assert_ : callpats -> assert_
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
  end
module type RECON_THM  =
  sig
    module ThmSyn : THMSYN
    include THMEXTSYN
    exception Error of string 
    val tdeclTotDecl :
      tdecl -> (ThmSyn.tDecl_ * (Paths.region * Paths.region list))
    val rdeclTorDecl :
      rdecl -> (ThmSyn.rDecl_ * (Paths.region * Paths.region list))
    val tableddeclTotabledDecl :
      tableddecl -> (ThmSyn.tabledDecl_ * Paths.region)
    val keepTabledeclToktDecl :
      keepTabledecl -> (ThmSyn.keepTableDecl_ * Paths.region)
    val theoremToTheorem : theorem -> ThmSyn.thDecl_
    val theoremDecToTheoremDec : theoremdec -> (string * ThmSyn.thDecl_)
    val proveToProve :
      prove -> (ThmSyn.pDecl_ * (Paths.region * Paths.region list))
    val establishToEstablish :
      establish -> (ThmSyn.pDecl_ * (Paths.region * Paths.region list))
    val assertToAssert : assert_ -> (ThmSyn.callpats_ * Paths.region list)
    val wdeclTowDecl : wdecl -> (ThmSyn.wDecl_ * Paths.region list)
  end


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
    let rec error (r, msg) = raise (Error (P.wrap (r, msg)))
    type nonrec order = (ThmSyn.order_ * Paths.region)
    let rec varg (r, l_) = ((ThmSyn.Varg l_), r)
    let rec lex (r0, l_) =
      let rec lex' =
        begin function
        | [] -> ([], r0)
        | (o_, r)::l_ ->
            let (os_, r') = lex' l_ in ((o_ :: os_), (Paths.join (r, r'))) end in
    let (os_, r1) = lex' l_ in ((ThmSyn.Lex os_), r1)
    let rec simul (r0, l_) =
      let rec simul' =
        begin function
        | [] -> ([], r0)
        | (o_, r)::l_ ->
            let (os_, r') = simul' l_ in ((o_ :: os_), (Paths.join (r, r'))) end in
    let (os_, r1) = simul' l_ in ((ThmSyn.Simul os_), r1)
  type nonrec callpats = (ThmSyn.callpats_ * Paths.region list)
  let rec checkArgNumber =
    begin function
    | (0, Uni (I.Type), [], r) -> ()
    | (0, Pi (_, v2_), arg::args, r) -> checkArgNumber (0, v2_, args, r)
    | (0, Pi (_, v2_), [], r) ->
        error (r, "Missing arguments in call pattern")
    | (0, Uni (I.Type), arg::args, r) ->
        error (r, "Extraneous arguments in call pattern")
    | (i, Pi (_, v2_), args, r) -> checkArgNumber ((i - 1), v2_, args, r) end
let rec checkCallPat =
  begin function
  | (ConDec (_, _, i, I.Normal, v_, I.Kind), p_, r) ->
      checkArgNumber (i, v_, p_, r)
  | (ConDec (a, _, _, Constraint _, _, _), p_, r) ->
      error (r, (("Illegal constraint constant " ^ a) ^ " in call pattern"))
  | (ConDec (a, _, _, Foreign _, _, _), p_, r) ->
      error (r, (("Illegal foreign constant " ^ a) ^ " in call pattern"))
  | (ConDec (a, _, _, _, _, I.Type), p_, r) ->
      error (r, (("Constant " ^ a) ^ " in call pattern not a type family"))
  | (ConDef (a, _, _, _, _, _, _), p_, r) ->
      error (r, (("Illegal defined constant " ^ a) ^ " in call pattern"))
  | (AbbrevDef (a, _, _, _, _, _), p_, r) ->
      error (r, (("Illegal abbreviation " ^ a) ^ " in call pattern"))
  | (BlockDec (a, _, _, _), p_, r) ->
      error (r, (("Illegal block identifier " ^ a) ^ " in call pattern"))
  | (SkoDec (a, _, _, _, _), p_, r) ->
      error (r, (("Illegal Skolem constant " ^ a) ^ " in call pattern")) end
let rec callpats (l_) =
  let rec callpats' =
    begin function
    | [] -> ([], [])
    | (name, p_, r)::l_ ->
        let (cps, rs) = callpats' l_ in
        let qid = Names.Qid ([], name) in
        (((begin match Names.constLookup qid with
           | None ->
               error
                 (r,
                   (((^) "Undeclared identifier " Names.qidToString
                       (valOf (Names.constUndef qid)))
                      ^ " in call pattern"))
           | Some cid ->
               (begin checkCallPat ((I.sgnLookup cid), p_, r);
                (((cid, p_) :: cps), (r :: rs)) end) end))
        (* check whether they are families here? *)) end in
let (cps, rs) = callpats' l_ in ((ThmSyn.Callpats cps), rs)
type nonrec tdecl = (ThmSyn.tDecl_ * (Paths.region * Paths.region list))
let rec tdecl ((o_, r), (c_, rs)) = ((ThmSyn.TDecl (o_, c_)), (r, rs))
let rec tdeclTotDecl (t_) = t_
type nonrec predicate = (ThmSyn.predicate_ * Paths.region)
let rec predicate =
  begin function
  | ("LESS", r) -> (ThmSyn.Less, r)
  | ("LEQ", r) -> (ThmSyn.Leq, r)
  | ("EQUAL", r) -> (ThmSyn.Eq, r) end
type nonrec rdecl = (ThmSyn.rDecl_ * (Paths.region * Paths.region list))
let rec rdecl ((p_, r0), (o1_, r1), (o2_, r2), (c_, rs)) =
  let r = Paths.join (r1, r2) in
  ((ThmSyn.RDecl ((ThmSyn.RedOrder (p_, o1_, o2_)), c_)),
    ((Paths.join (r0, r)), rs))
let rec rdeclTorDecl (t_) = t_
type nonrec tableddecl = (ThmSyn.tabledDecl_ * Paths.region)
let rec tableddecl (name, r) =
  let qid = Names.Qid ([], name) in
  ((begin match Names.constLookup qid with
    | None ->
        error
          (r,
            (((^) "Undeclared identifier " Names.qidToString
                (valOf (Names.constUndef qid)))
               ^ " in call pattern"))
    | Some cid -> ((ThmSyn.TabledDecl cid), r) end)
  (* check whether they are families here? *))
let rec tableddeclTotabledDecl (t_) = t_
type nonrec keepTabledecl = (ThmSyn.keepTableDecl_ * Paths.region)
let rec keepTabledecl (name, r) =
  let qid = Names.Qid ([], name) in
  ((begin match Names.constLookup qid with
    | None ->
        error
          (r,
            (((^) "Undeclared identifier " Names.qidToString
                (valOf (Names.constUndef qid)))
               ^ " in call pattern"))
    | Some cid -> ((ThmSyn.KeepTableDecl cid), r) end)
  (* check whether they are families here? *))
let rec keepTabledeclToktDecl (t_) = t_
type nonrec prove = (ThmSyn.pDecl_ * (Paths.region * Paths.region list))
let rec prove (n, (td, rrs)) = ((ThmSyn.PDecl (n, td)), rrs)
let rec proveToProve (p_) = p_
type nonrec establish = (ThmSyn.pDecl_ * (Paths.region * Paths.region list))
let rec establish (n, (td, rrs)) = ((ThmSyn.PDecl (n, td)), rrs)
let rec establishToEstablish (p_) = p_
type nonrec assert_ = (ThmSyn.callpats_ * Paths.region list)
let rec assert_ (cp, rs) = (cp, rs)
let rec assertToAssert (p_) = p_
type nonrec decs = ExtSyn.dec I.ctx_
let null = I.Null
let decl = I.Decl
type nonrec labeldec = (decs * decs)
type nonrec thm =
  (labeldec list * ExtSyn.dec I.ctx_ * ModeSyn.mode_ I.ctx_ * int)
type nonrec theorem = thm -> thm
type nonrec theoremdec = (string * theorem)
let rec dec (name, t) = (name, t)
let rec ctxAppend =
  begin function
  | (g_, I.Null) -> g_
  | (g_, Decl (g'_, d_)) -> I.Decl ((ctxAppend (g_, g'_)), d_) end
let rec ctxMap arg__0 arg__1 =
  begin match (arg__0, arg__1) with
  | (f, I.Null) -> I.Null
  | (f, Decl (g_, d_)) -> I.Decl ((ctxMap f g_), (f d_)) end
let rec ctxBlockToString (g0_, (g1_, g2_)) =
  let _ = Names.varReset I.Null in
  let G0' = Names.ctxName g0_ in
  let G1' = Names.ctxLUName g1_ in
  let G2' = Names.ctxLUName g2_ in
  (^) ((((Print.ctxToString (I.Null, G0')) ^ "\n") ^
          (begin match G1' with
           | I.Null -> ""
           | _ -> ((^) "some " Print.ctxToString (G0', G1')) ^ "\n" end))
    ^ "pi ") Print.ctxToString ((ctxAppend (G0', G1')), G2')
let rec checkFreevars =
  begin function
  | (I.Null, (g1_, g2_), r) -> ()
  | (g0_, (g1_, g2_), r) ->
      let _ = Names.varReset I.Null in
      let G0' = Names.ctxName g0_ in
      let G1' = Names.ctxLUName g1_ in
      let G2' = Names.ctxLUName g2_ in
      error
        (r,
          ((^) "Free variables in context block after term reconstruction:\n"
             ctxBlockToString (G0', (G1', G2')))) end
let rec abstractCtxPair (g1, g2) =
  let r =
    begin match ((T.ctxRegion g1), (T.ctxRegion g2)) with
    | (Some r1, Some r2) -> Paths.join (r1, r2)
    | (_, Some r2) -> r2 end in
let JWithCtx (g1_, JWithCtx (g2_, _)) =
  T.recon (T.jwithctx (g1, (T.jwithctx (g2, T.jnothing)))) in
let (g0_, (G1')::(G2')::[]) =
  begin try Abstract.abstractCtxs [g1_; g2_]
  with
  | Error (c_) ->
      error
        (r,
          ((^) (((^) "Constraints remain in context block after term reconstruction:\n"
                   ctxBlockToString (I.Null, (g1_, g2_)))
                  ^ "\n")
             Print.cnstrsToString c_)) end in
let _ = checkFreevars (g0_, (G1', G2'), r) in (((G1', G2'))
  (* each block reconstructed independent of others *)
  (* closed nf *))
let rec top (GBs, g, m_, k) = (GBs, g, m_, k)
let rec exists (g', t) (GBs, g, m_, k) =
  t
    (GBs, (ctxAppend (g, g')),
      (ctxAppend (m_, (ctxMap (begin function | _ -> M.Minus end) g'))), k)
let rec forall (g', t) (GBs, g, m_, k) =
  t
    (GBs, (ctxAppend (g, g')),
      (ctxAppend (m_, (ctxMap (begin function | _ -> M.Plus end) g'))), k)
let rec forallStar (g', t) (GBs, g, m_, _) =
  t
    (GBs, (ctxAppend (g, g')),
      (ctxAppend (m_, (ctxMap (begin function | _ -> M.Plus end) g'))),
    (I.ctxLength g'))
let rec forallG (gbs, (t : thm -> thm)) (_ : thm) =
  (t (gbs, I.Null, I.Null, 0) : thm)
let rec theoremToTheorem t =
  let (gbs, g, m_, k) = t ([], I.Null, I.Null, 0) in
  let _ = Names.varReset IntSyn.Null in
  let GBs = List.map abstractCtxPair gbs in
  let JWithCtx (g_, _) = T.recon (T.jwithctx (g, T.jnothing)) in
  L.ThDecl (GBs, g_, m_, k)
let rec theoremDecToTheoremDec (name, t) = (name, (theoremToTheorem t))
let rec abstractWDecl (w_) = let w'_ = List.map Names.Qid w_ in w'_
type nonrec wdecl = (ThmSyn.wDecl_ * Paths.region list)
let rec wdecl (w_, (cp, rs)) = ((ThmSyn.WDecl ((abstractWDecl w_), cp)), rs)
let rec wdeclTowDecl (t_) = t_
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
type nonrec assert_ = assert_
let assert_ = assert_
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
let wdecl = wdecl end
