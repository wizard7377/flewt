module type EXTCONDEC  =
  sig
    module ExtSyn : EXTSYN
    type nonrec condec
    val condec : (string * ExtSyn.term) -> condec
    val blockdec : (string * ExtSyn.dec list * ExtSyn.dec list) -> condec
    val blockdef : (string * (string list * string) list) -> condec
    val condef : (string option * ExtSyn.term * ExtSyn.term option) -> condec
  end
module type RECON_CONDEC  =
  sig
    include EXTCONDEC
    exception Error of string 
    val condecToConDec :
      (condec * Paths.location * bool) ->
        (IntSyn.conDec_ option * Paths.occConDec option)
    val internalInst :
      (IntSyn.conDec_ * IntSyn.conDec_ * Paths.region) -> IntSyn.conDec_
    val externalInst :
      (IntSyn.conDec_ * ExtSyn.term * Paths.region) -> IntSyn.conDec_
  end


module ReconConDec(ReconConDec:sig
                                 module Global : GLOBAL
                                 module Names : NAMES
                                 module Abstract : ABSTRACT
                                 module ReconTerm' : RECON_TERM
                                 module Constraints : CONSTRAINTS
                                 module Strict : STRICT
                                 module TypeCheck : TYPECHECK
                                 module Timers : TIMERS
                                 module Print : PRINT
                                 module Msg : MSG
                               end) : RECON_CONDEC =
  struct
    module ExtSyn = ReconTerm'
    exception Error of string 
    let rec error (r, msg) = raise (Error (Paths.wrap (r, msg)))
    type nonrec name = string
    type condec =
      | condec of (name * ExtSyn.term)
      [@sml.renamed "condec"][@sml.renamed "condec"]
      | condef of (name option * ExtSyn.term * ExtSyn.term option)
      [@sml.renamed "condef"][@sml.renamed "condef"]
      | blockdef of (string * (string list * string) list)
      [@sml.renamed "blockdef"][@sml.renamed "blockdef"]
      | blockdec of (name * ExtSyn.dec list * ExtSyn.dec list)
      [@sml.renamed "blockdec"][@sml.renamed "blockdec"]
    let rec condecToConDec =
      begin function
      | (condec (name, tm), Loc (fileName, r), abbFlag) ->
          let _ = Names.varReset IntSyn.Null in
          let _ = ExtSyn.resetErrors fileName in
          let JClass ((v_, oc), l_) =
            Timers.time Timers.recon ExtSyn.recon (ExtSyn.jclass tm) in
          let _ = ExtSyn.checkErrors r in
          let (i, v'_) =
            begin try Timers.time Timers.abstract Abstract.abstractDecImp v_
            with | Error msg -> raise (Abstract.Error (Paths.wrap (r, msg))) end in
          let cd =
            Names.nameConDec
              (IntSyn.ConDec (name, None, i, IntSyn.Normal, v'_, l_)) in
          let ocd = Paths.dec (i, oc) in
          let _ =
            if !Global.chatter >= 3
            then
              begin Msg.message
                      ((Timers.time Timers.printing Print.conDecToString cd)
                         ^ "\n") end
            else begin () end in
          let _ =
            if !Global.doubleCheck
            then
              begin Timers.time Timers.checking TypeCheck.check
                      (v'_, (IntSyn.Uni l_)) end
            else begin () end in
          ((Some cd), (Some ocd))
  | (condef (optName, tm1, tm2Opt), Loc (fileName, r), abbFlag) ->
      let _ = Names.varReset IntSyn.Null in
      let _ = ExtSyn.resetErrors fileName in
      let f =
        begin match tm2Opt with
        | None -> ExtSyn.jterm tm1
        | Some tm2 -> ExtSyn.jof (tm1, tm2) end in
      let f' = Timers.time Timers.recon ExtSyn.recon f in
      let ((u_, oc1), (v_, oc2Opt), l_) =
        begin match f' with
        | JTerm ((u_, oc1), v_, l_) -> ((u_, oc1), (v_, None), l_)
        | JOf ((u_, oc1), (v_, oc2), l_) -> ((u_, oc1), (v_, (Some oc2)), l_) end in
      let _ = ExtSyn.checkErrors r in
      let (i, (U'', V'')) =
        begin try Timers.time Timers.abstract Abstract.abstractDef (u_, v_)
        with | Error msg -> raise (Abstract.Error (Paths.wrap (r, msg))) end in
      let name =
        begin match optName with | None -> "_" | Some name -> name end in
      let ocd = Paths.def (i, oc1, oc2Opt) in
      let cd =
        if abbFlag
        then
          begin Names.nameConDec
                  (IntSyn.AbbrevDef (name, None, i, U'', V'', l_)) end
        else begin
          (((begin Strict.check ((U'', V''), (Some ocd));
             Names.nameConDec
               (IntSyn.ConDef
                  (name, None, i, U'', V'', l_, (IntSyn.ancestor U''))) end))
        (* stricter checking of types according to Chris Richards Fri Jul  2 16:33:46 2004 -fp *)
        (* (case optName of NONE => () | _ => Strict.checkType ((i, V''), SOME(ocd))); *)) end in
      let _ =
        if !Global.chatter >= 3
        then
          begin Msg.message
                  ((Timers.time Timers.printing Print.conDecToString cd) ^
                     "\n") end
        else begin () end in
      let _ =
        if !Global.doubleCheck
        then
          begin (begin Timers.time Timers.checking TypeCheck.check
                         (V'', (IntSyn.Uni l_));
                 Timers.time Timers.checking TypeCheck.check (U'', V'') end) end
        else begin () end in
    let optConDec =
      begin match optName with | None -> None | Some _ -> Some cd end in
    (optConDec, (Some ocd))
| (blockdec (name, Lsome, Lblock), Loc (fileName, r), abbFlag) ->
    let rec makectx =
      begin function
      | [] -> IntSyn.Null
      | (d_)::l_ -> IntSyn.Decl ((makectx l_), d_) end in
  let rec ctxToList =
    begin function
    | (IntSyn.Null, acc) -> acc
    | (Decl (g_, d_), acc) -> ctxToList (g_, (d_ :: acc)) end in
  let rec ctxAppend =
    begin function
    | (g_, IntSyn.Null) -> g_
    | (g_, Decl (g'_, d_)) -> IntSyn.Decl ((ctxAppend (g_, g'_)), d_) end in
  let rec ctxBlockToString (g0_, (g1_, g2_)) =
    let _ = Names.varReset IntSyn.Null in
    let G0' = Names.ctxName g0_ in
    let G1' = Names.ctxLUName g1_ in
    let G2' = Names.ctxLUName g2_ in
    (^) ((((Print.ctxToString (IntSyn.Null, G0')) ^ "\n") ^
            (begin match G1' with
             | IntSyn.Null -> ""
             | _ -> ((^) "some " Print.ctxToString (G0', G1')) ^ "\n" end))
      ^ "pi ") Print.ctxToString ((ctxAppend (G0', G1')), G2') in
  let rec checkFreevars =
    begin function
    | (IntSyn.Null, (g1_, g2_), r) -> ()
    | (g0_, (g1_, g2_), r) ->
        let _ = Names.varReset IntSyn.Null in
        let G0' = Names.ctxName g0_ in
        let G1' = Names.ctxLUName g1_ in
        let G2' = Names.ctxLUName g2_ in
        error
          (r,
            ((^) "Free variables in context block after term reconstruction:\n"
               ctxBlockToString (G0', (G1', G2')))) end in
  let (gsome, gblock) = ((makectx Lsome), (makectx Lblock)) in
  let r' =
    begin match ((ExtSyn.ctxRegion gsome), (ExtSyn.ctxRegion gblock)) with
    | (Some r1, Some r2) -> Paths.join (r1, r2)
    | (_, Some r2) -> r2 end in
  let _ = Names.varReset IntSyn.Null in
  let _ = ExtSyn.resetErrors fileName in
  let j =
    ExtSyn.jwithctx (gsome, (ExtSyn.jwithctx (gblock, ExtSyn.jnothing))) in
  let JWithCtx (Gsome, JWithCtx (Gblock, _)) =
    Timers.time Timers.recon ExtSyn.recon j in
  let _ = ExtSyn.checkErrors r in
  let (g0_, (Gsome')::(Gblock')::[]) =
    begin try Abstract.abstractCtxs [Gsome; Gblock]
    with
    | Error (c_) ->
        raise
          (error
             (r',
               ((^) (((^) "Constraints remain in context block after term reconstruction:\n"
                        ctxBlockToString (IntSyn.Null, (Gsome, Gblock)))
                       ^ "\n")
                  Print.cnstrsToString c_))) end in
  let _ = checkFreevars (g0_, (Gsome', Gblock'), r') in
  let bd = IntSyn.BlockDec (name, None, Gsome', (ctxToList (Gblock', []))) in
  let _ =
    if !Global.chatter >= 3
    then
      begin Msg.message
              ((Timers.time Timers.printing Print.conDecToString bd) ^ "\n") end
    else begin () end in
  ((((Some bd), None))(* closed nf *))
| (blockdef (name, w_), Loc (fileName, r), abbFlag) ->
    let w'_ = List.map Names.Qid w_ in
    let W'' =
      List.map
        (begin function
         | qid ->
             (begin match Names.constLookup qid with
              | None ->
                  raise
                    (Names.Error
                       (((^) "Undeclared label " Names.qidToString
                           (valOf (Names.constUndef qid)))
                          ^ "."))
              | Some cid -> cid end) end)
      w'_ in
  let bd = IntSyn.BlockDef (name, None, W'') in
  let _ =
    if !Global.chatter >= 3
    then
      begin Msg.message
              ((Timers.time Timers.printing Print.conDecToString bd) ^ "\n") end
    else begin () end in
  ((Some bd), None) end
let rec internalInst _ = raise Match
let rec externalInst _ = raise Match end
