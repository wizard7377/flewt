
module type EXTCONDEC  =
  sig
    module ExtSyn : EXTSYN
    type nonrec condec
    val condec : string -> ExtSyn.term -> condec
    val blockdec : string -> ExtSyn.dec list -> ExtSyn.dec list -> condec
    val blockdef : string -> (string list * string) list -> condec
    val condef : string option -> ExtSyn.term -> ExtSyn.term option -> condec
  end
module type RECON_CONDEC  =
  sig
    include EXTCONDEC
    exception Error of string 
    val condecToConDec :
      condec ->
        Paths.location ->
          bool -> (IntSyn.__ConDec option * Paths.occConDec option)
    val internalInst :
      IntSyn.__ConDec -> IntSyn.__ConDec -> Paths.region -> IntSyn.__ConDec
    val externalInst :
      IntSyn.__ConDec -> ExtSyn.term -> Paths.region -> IntSyn.__ConDec
  end;;




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
    let rec error r msg = raise (Error (Paths.wrap (r, msg)))
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
    let rec condecToConDec __7__ __8__ __9__ =
      match (__7__, __8__, __9__) with
      | (condec (name, tm), Loc (fileName, r), abbFlag) ->
          let _ = Names.varReset IntSyn.Null in
          let _ = ExtSyn.resetErrors fileName in
          let JClass ((__V, oc), __L) =
            Timers.time Timers.recon ExtSyn.recon (ExtSyn.jclass tm) in
          let _ = ExtSyn.checkErrors r in
          let (i, __V') =
            try Timers.time Timers.abstract Abstract.abstractDecImp __V
            with | Error msg -> raise (Abstract.Error (Paths.wrap (r, msg))) in
          let cd =
            Names.nameConDec
              (IntSyn.ConDec (name, NONE, i, IntSyn.Normal, __V', __L)) in
          let ocd = Paths.dec (i, oc) in
          let _ =
            if (!Global.chatter) >= 3
            then
              Msg.message
                ((Timers.time Timers.printing Print.conDecToString cd) ^ "\n")
            else () in
          let _ =
            if !Global.doubleCheck
            then
              Timers.time Timers.checking TypeCheck.check
                (__V', (IntSyn.Uni __L))
            else () in
          ((Some cd), (Some ocd))
      | (condef (optName, tm1, tm2Opt), Loc (fileName, r), abbFlag) ->
          let _ = Names.varReset IntSyn.Null in
          let _ = ExtSyn.resetErrors fileName in
          let f =
            match tm2Opt with
            | NONE -> ExtSyn.jterm tm1
            | Some tm2 -> ExtSyn.jof (tm1, tm2) in
          let f' = Timers.time Timers.recon ExtSyn.recon f in
          let ((__U, oc1), (__V, oc2Opt), __L) =
            match f' with
            | JTerm ((__U, oc1), __V, __L) -> ((__U, oc1), (__V, NONE), __L)
            | JOf ((__U, oc1), (__V, oc2), __L) ->
                ((__U, oc1), (__V, (Some oc2)), __L) in
          let _ = ExtSyn.checkErrors r in
          let (i, (U'', V'')) =
            try Timers.time Timers.abstract Abstract.abstractDef (__U, __V)
            with | Error msg -> raise (Abstract.Error (Paths.wrap (r, msg))) in
          let name = match optName with | NONE -> "_" | Some name -> name in
          let ocd = Paths.def (i, oc1, oc2Opt) in
          let cd =
            if abbFlag
            then
              Names.nameConDec
                (IntSyn.AbbrevDef (name, NONE, i, U'', V'', __L))
            else
              (((Strict.check ((U'', V''), (Some ocd));
                 Names.nameConDec
                   (IntSyn.ConDef
                      (name, NONE, i, U'', V'', __L, (IntSyn.ancestor U'')))))
              (* stricter checking of types according to Chris Richards Fri Jul  2 16:33:46 2004 -fp *)
              (* (case optName of NONE => () | _ => Strict.checkType ((i, V''), Some(ocd))); *)) in
          let _ =
            if (!Global.chatter) >= 3
            then
              Msg.message
                ((Timers.time Timers.printing Print.conDecToString cd) ^ "\n")
            else () in
          let _ =
            if !Global.doubleCheck
            then
              (Timers.time Timers.checking TypeCheck.check
                 (V'', (IntSyn.Uni __L));
               Timers.time Timers.checking TypeCheck.check (U'', V''))
            else () in
          let optConDec =
            match optName with | NONE -> NONE | Some _ -> Some cd in
          (optConDec, (Some ocd))
      | (blockdec (name, Lsome, Lblock), Loc (fileName, r), abbFlag) ->
          let rec makectx =
            function
            | nil -> IntSyn.Null
            | (__D)::__L -> IntSyn.Decl ((makectx __L), __D) in
          let rec ctxToList __0__ __1__ =
            match (__0__, __1__) with
            | (IntSyn.Null, acc) -> acc
            | (Decl (__G, __D), acc) -> ctxToList (__G, (__D :: acc)) in
          let rec ctxAppend __2__ __3__ =
            match (__2__, __3__) with
            | (__G, IntSyn.Null) -> __G
            | (__G, Decl (__G', __D)) ->
                IntSyn.Decl ((ctxAppend (__G, __G')), __D) in
          let rec ctxBlockToString (__G0) (__G1, __G2) =
            let _ = Names.varReset IntSyn.Null in
            let G0' = Names.ctxName __G0 in
            let G1' = Names.ctxLUName __G1 in
            let G2' = Names.ctxLUName __G2 in
            (^) ((((Print.ctxToString (IntSyn.Null, G0')) ^ "\n") ^
                    (match G1' with
                     | IntSyn.Null -> ""
                     | _ -> ((^) "some " Print.ctxToString (G0', G1')) ^ "\n"))
                   ^ "pi ")
              Print.ctxToString ((ctxAppend (G0', G1')), G2') in
          let rec checkFreevars __4__ __5__ __6__ =
            match (__4__, __5__, __6__) with
            | (IntSyn.Null, (__G1, __G2), r) -> ()
            | (__G0, (__G1, __G2), r) ->
                let _ = Names.varReset IntSyn.Null in
                let G0' = Names.ctxName __G0 in
                let G1' = Names.ctxLUName __G1 in
                let G2' = Names.ctxLUName __G2 in
                error
                  (r,
                    ((^) "Free variables in context block after term reconstruction:\n"
                       ctxBlockToString (G0', (G1', G2')))) in
          let (gsome, gblock) = ((makectx Lsome), (makectx Lblock)) in
          let r' =
            match ((ExtSyn.ctxRegion gsome), (ExtSyn.ctxRegion gblock)) with
            | (Some r1, Some r2) -> Paths.join (r1, r2)
            | (_, Some r2) -> r2 in
          let _ = Names.varReset IntSyn.Null in
          let _ = ExtSyn.resetErrors fileName in
          let j =
            ExtSyn.jwithctx
              (gsome, (ExtSyn.jwithctx (gblock, ExtSyn.jnothing))) in
          let JWithCtx (Gsome, JWithCtx (Gblock, _)) =
            Timers.time Timers.recon ExtSyn.recon j in
          let _ = ExtSyn.checkErrors r in
          let (__G0, (Gsome')::(Gblock')::[]) =
            try Abstract.abstractCtxs [Gsome; Gblock]
            with
            | Error (__C) ->
                raise
                  (error
                     (r',
                       ((^) (((^) "Constraints remain in context block after term reconstruction:\n"
                                ctxBlockToString
                                (IntSyn.Null, (Gsome, Gblock)))
                               ^ "\n")
                          Print.cnstrsToString __C))) in
          let _ = checkFreevars (__G0, (Gsome', Gblock'), r') in
          let bd =
            IntSyn.BlockDec (name, NONE, Gsome', (ctxToList (Gblock', nil))) in
          let _ =
            if (!Global.chatter) >= 3
            then
              Msg.message
                ((Timers.time Timers.printing Print.conDecToString bd) ^ "\n")
            else () in
          ((((Some bd), NONE))(* closed nf *))
      | (blockdef (name, __W), Loc (fileName, r), abbFlag) ->
          let __W' = List.map Names.Qid __W in
          let W'' =
            List.map
              (fun qid ->
                 match Names.constLookup qid with
                 | NONE ->
                     raise
                       (Names.Error
                          (((^) "Undeclared label " Names.qidToString
                              (valOf (Names.constUndef qid)))
                             ^ "."))
                 | Some cid -> cid) __W' in
          let bd = IntSyn.BlockDef (name, NONE, W'') in
          let _ =
            if (!Global.chatter) >= 3
            then
              Msg.message
                ((Timers.time Timers.printing Print.conDecToString bd) ^ "\n")
            else () in
          ((Some bd), NONE)
    let rec internalInst _ = raise Match
    let rec externalInst _ = raise Match
  end ;;
