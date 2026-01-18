
module type EXTCONDEC  =
  sig
    module ExtSyn : EXTSYN
    type nonrec condec
    val condec : (string * ExtSyn.term) -> condec
    val blockdec : (string * ExtSyn.dec list * ExtSyn.dec list) -> condec
    val blockdef : (string * (string list * string) list) -> condec
    val condef : (string option * ExtSyn.term * ExtSyn.term option) -> condec
  end (* External Syntax for signature entries *)
(* Author: Frank Pfenning *)
(*! structure Paths : PATHS !*)
(* constant declaration *)
(* id : tm *)
(* id : tm = tm | _ : tm = tm *)
(* signature EXTCONDEC *)
module type RECON_CONDEC  =
  sig
    (*! structure IntSyn : INTSYN !*)
    include EXTCONDEC
    exception Error of string 
    val condecToConDec :
      (condec * Paths.location * bool) ->
        (IntSyn.__ConDec option * Paths.occConDec option)
    (* optional ConDec is absent for anonymous definitions *)
    (* bool = true means that condec is an abbreviation *)
    val internalInst :
      (IntSyn.__ConDec * IntSyn.__ConDec * Paths.region) -> IntSyn.__ConDec
    val externalInst :
      (IntSyn.__ConDec * ExtSyn.term * Paths.region) -> IntSyn.__ConDec
  end;;




(* Reconstruct signature entries *)
(* Author: Frank Pfenning *)
(* Modified: Roberto Virga, Jeff Polakow *)
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
                                 (*! structure IntSyn' : INTSYN !*)
                                 (*! sharing Names.IntSyn = IntSyn' !*)
                                 (*! sharing Abstract.IntSyn = IntSyn' !*)
                                 (*! structure Paths' : PATHS !*)
                                 (*! sharing ReconTerm'.IntSyn = IntSyn' !*)
                                 (*! sharing ReconTerm'.Paths = Paths' !*)
                                 (*! sharing Constraints.IntSyn = IntSyn' !*)
                                 (*! sharing Strict.IntSyn = IntSyn' !*)
                                 (*! sharing Strict.Paths = Paths' !*)
                                 (*! sharing TypeCheck.IntSyn = IntSyn' !*)
                                 (*! sharing Print.IntSyn = IntSyn' !*)
                                 module Msg : MSG
                               end) : RECON_CONDEC =
  struct
    (*! structure IntSyn = IntSyn' !*)
    (*! structure Paths = Paths' !*)
    module ExtSyn = ReconTerm'
    exception Error of string 
    (* error (r, msg) raises a syntax error within region r with text msg *)
    let rec error (r, msg) = raise (Error (Paths.wrap (r, msg)))
    type nonrec name = string
    (* Constant declarations *)
    type condec =
      | condec of (name * ExtSyn.term)
      [@sml.renamed "condec"][@sml.renamed "condec"]
      | condef of (name option * ExtSyn.term * ExtSyn.term option)
      [@sml.renamed "condef"][@sml.renamed "condef"]
      | blockdef of (string * (string list * string) list)
      [@sml.renamed "blockdef"][@sml.renamed "blockdef"]
      | blockdec of (name * ExtSyn.dec list * ExtSyn.dec list)
      [@sml.renamed "blockdec"][@sml.renamed "blockdec"]
    (* condecToConDec (condec, r) = (Some(cd), Some(ocd))
     if condec is a named constant declaration with occurrence tree ocd,
     None if name or occurrence tree is missing

     Free variables in condec are interpreted universally (as FVars)
     then abstracted as implicit parameters.

     Only works properly when the declaration contains no EVars.
  *)
    (* should printing of result be moved to frontend? *)
    (* Wed May 20 08:08:50 1998 -fp *)
    let rec condecToConDec =
      function
      | (condec (name, tm), Loc (fileName, r), abbFlag) ->
          let _ = Names.varReset IntSyn.Null in
          let _ = ExtSyn.resetErrors fileName in
          let JClass ((__v, oc), __l) =
            Timers.time Timers.recon ExtSyn.recon (ExtSyn.jclass tm) in
          let _ = ExtSyn.checkErrors r in
          let (i, __v') =
            try Timers.time Timers.abstract Abstract.abstractDecImp __v
            with | Error msg -> raise (Abstract.Error (Paths.wrap (r, msg))) in
          let cd =
            Names.nameConDec
              (IntSyn.ConDec (name, None, i, IntSyn.Normal, __v', __l)) in
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
                (__v', (IntSyn.Uni __l))
            else () in
          ((Some cd), (Some ocd))
      | (condef (optName, tm1, tm2Opt), Loc (fileName, r), abbFlag) ->
          let _ = Names.varReset IntSyn.Null in
          let _ = ExtSyn.resetErrors fileName in
          let f =
            match tm2Opt with
            | None -> ExtSyn.jterm tm1
            | Some tm2 -> ExtSyn.jof (tm1, tm2) in
          let f' = Timers.time Timers.recon ExtSyn.recon f in
          let ((__u, oc1), (__v, oc2Opt), __l) =
            match f' with
            | JTerm ((__u, oc1), __v, __l) -> ((__u, oc1), (__v, None), __l)
            | JOf ((__u, oc1), (__v, oc2), __l) -> ((__u, oc1), (__v, (Some oc2)), __l) in
          let _ = ExtSyn.checkErrors r in
          let (i, (__u'', __v'')) =
            try Timers.time Timers.abstract Abstract.abstractDef (__u, __v)
            with | Error msg -> raise (Abstract.Error (Paths.wrap (r, msg))) in
          let name = match optName with | None -> "_" | Some name -> name in
          let ocd = Paths.def (i, oc1, oc2Opt) in
          let cd =
            if abbFlag
            then
              Names.nameConDec
                (IntSyn.AbbrevDef (name, None, i, __u'', __v'', __l))
            else
              (((Strict.check ((__u'', __v''), (Some ocd));
                 Names.nameConDec
                   (IntSyn.ConDef
                      (name, None, i, __u'', __v'', __l, (IntSyn.ancestor __u'')))))
              (* stricter checking of types according to Chris Richards Fri Jul  2 16:33:46 2004 -fp *)
              (* (case optName of None => () | _ => Strict.checkType ((i, __v''), Some(ocd))); *)) in
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
                 (__v'', (IntSyn.Uni __l));
               Timers.time Timers.checking TypeCheck.check (__u'', __v''))
            else () in
          let optConDec =
            match optName with | None -> None | Some _ -> Some cd in
          (optConDec, (Some ocd))
      | (blockdec (name, Lsome, Lblock), Loc (fileName, r), abbFlag) ->
          let rec makectx =
            function
            | nil -> IntSyn.Null
            | (__d)::__l -> IntSyn.Decl ((makectx __l), __d) in
          let rec ctxToList =
            function
            | (IntSyn.Null, acc) -> acc
            | (Decl (__g, __d), acc) -> ctxToList (__g, (__d :: acc)) in
          let rec ctxAppend =
            function
            | (__g, IntSyn.Null) -> __g
            | (__g, Decl (__g', __d)) -> IntSyn.Decl ((ctxAppend (__g, __g')), __d) in
          let rec ctxBlockToString (G0, (G1, G2)) =
            let _ = Names.varReset IntSyn.Null in
            let G0' = Names.ctxName G0 in
            let G1' = Names.ctxLUName G1 in
            let G2' = Names.ctxLUName G2 in
            (^) ((((Print.ctxToString (IntSyn.Null, G0')) ^ "\n") ^
                    (match G1' with
                     | IntSyn.Null -> ""
                     | _ -> ((^) "some " Print.ctxToString (G0', G1')) ^ "\n"))
                   ^ "pi ")
              Print.ctxToString ((ctxAppend (G0', G1')), G2') in
          let rec checkFreevars =
            function
            | (IntSyn.Null, (G1, G2), r) -> ()
            | (G0, (G1, G2), r) ->
                let _ = Names.varReset IntSyn.Null in
                let G0' = Names.ctxName G0 in
                let G1' = Names.ctxLUName G1 in
                let G2' = Names.ctxLUName G2 in
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
          let (G0, (Gsome')::(Gblock')::[]) =
            try Abstract.abstractCtxs [Gsome; Gblock]
            with
            | Error (C) ->
                raise
                  (error
                     (r',
                       ((^) (((^) "Constraints remain in context block after term reconstruction:\n"
                                ctxBlockToString
                                (IntSyn.Null, (Gsome, Gblock)))
                               ^ "\n")
                          Print.cnstrsToString C))) in
          let _ = checkFreevars (G0, (Gsome', Gblock'), r') in
          let bd =
            IntSyn.BlockDec (name, None, Gsome', (ctxToList (Gblock', nil))) in
          let _ =
            if (!Global.chatter) >= 3
            then
              Msg.message
                ((Timers.time Timers.printing Print.conDecToString bd) ^ "\n")
            else () in
          ((((Some bd), None))(* closed nf *))
      | (blockdef (name, W), Loc (fileName, r), abbFlag) ->
          let W' = List.map Names.Qid W in
          let W'' =
            List.map
              (function
               | qid ->
                   (match Names.constLookup qid with
                    | None ->
                        raise
                          (Names.Error
                             (((^) "Undeclared label " Names.qidToString
                                 (valOf (Names.constUndef qid)))
                                ^ "."))
                    | Some cid -> cid)) W' in
          let bd = IntSyn.BlockDef (name, None, W'') in
          let _ =
            if (!Global.chatter) >= 3
            then
              Msg.message
                ((Timers.time Timers.printing Print.conDecToString bd) ^ "\n")
            else () in
          ((Some bd), None)
    let rec internalInst _ = raise Match
    let rec externalInst _ = raise Match
  end ;;
