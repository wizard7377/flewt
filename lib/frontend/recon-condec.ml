
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
    include
      ((EXTCONDEC)(* External Syntax for signature entries *)(* Author: Frank Pfenning *)
      (*! structure Paths : PATHS !*)(* constant declaration *)
      (* id : tm *)(* id : tm = tm | _ : tm = tm *)
      (* signature EXTCONDEC *)(*! structure IntSyn : INTSYN !*))
    exception Error of string 
    val condecToConDec :
      (condec * Paths.location * bool) ->
        (IntSyn.__ConDec option * Paths.occConDec option)
    val internalInst :
      (IntSyn.__ConDec * IntSyn.__ConDec * Paths.region) ->
        ((IntSyn.__ConDec)(* bool = true means that condec is an abbreviation *)
        (* optional ConDec is absent for anonymous definitions *))
    val externalInst :
      (IntSyn.__ConDec * ExtSyn.term * Paths.region) -> IntSyn.__ConDec
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
                                 module Msg :
                                 ((MSG)(* Reconstruct signature entries *)
                                 (* Author: Frank Pfenning *)(* Modified: Roberto Virga, Jeff Polakow *)
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
                                 (*! sharing Print.IntSyn = IntSyn' !*))
                               end) : RECON_CONDEC =
  struct
    module ExtSyn =
      ((ReconTerm')(*! structure IntSyn = IntSyn' !*)
      (*! structure Paths = Paths' !*))
    exception Error of string 
    let rec error
      (((r)(* error (r, msg) raises a syntax error within region r with text msg *)),
       msg)
      = raise (Error (Paths.wrap (r, msg)))
    type nonrec name = string
    type condec =
      | condec of (((name)(* Constant declarations *)) *
      ExtSyn.term) [@sml.renamed "condec"][@sml.renamed "condec"]
      | condef of (name option * ExtSyn.term * ExtSyn.term option)
      [@sml.renamed "condef"][@sml.renamed "condef"]
      | blockdef of (string * (string list * string) list)
      [@sml.renamed "blockdef"][@sml.renamed "blockdef"]
      | blockdec of (name * ExtSyn.dec list * ExtSyn.dec list)
      [@sml.renamed "blockdec"][@sml.renamed "blockdec"]
    let rec condecToConDec =
      function
      | (condec
         (((name)(* condecToConDec (condec, r) = (SOME(cd), SOME(ocd))
     if condec is a named constant declaration with occurrence tree ocd,
     NONE if name or occurrence tree is missing

     Free variables in condec are interpreted universally (as FVars)
     then abstracted as implicit parameters.

     Only works properly when the declaration contains no EVars.
  *)
          (* should printing of result be moved to frontend? *)(* Wed May 20 08:08:50 1998 -fp *)),
          tm),
         Loc (fileName, r), abbFlag) ->
          let _ = Names.varReset IntSyn.Null in
          let _ = ExtSyn.resetErrors fileName in
          let JClass ((V, oc), L) =
            Timers.time Timers.recon ExtSyn.recon (ExtSyn.jclass tm) in
          let _ = ExtSyn.checkErrors r in
          let (i, V') =
            try Timers.time Timers.abstract Abstract.abstractDecImp V
            with | Error msg -> raise (Abstract.Error (Paths.wrap (r, msg))) in
          let cd =
            Names.nameConDec
              (IntSyn.ConDec (name, NONE, i, IntSyn.Normal, V', L)) in
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
                (V', (IntSyn.Uni L))
            else () in
          ((SOME cd), (SOME ocd))
      | (condef (optName, tm1, tm2Opt), Loc (fileName, r), abbFlag) ->
          let _ = Names.varReset IntSyn.Null in
          let _ = ExtSyn.resetErrors fileName in
          let f =
            match tm2Opt with
            | NONE -> ExtSyn.jterm tm1
            | SOME tm2 -> ExtSyn.jof (tm1, tm2) in
          let f' = Timers.time Timers.recon ExtSyn.recon f in
          let ((U, oc1), (V, oc2Opt), L) =
            match f' with
            | JTerm ((U, oc1), V, L) -> ((U, oc1), (V, NONE), L)
            | JOf ((U, oc1), (V, oc2), L) -> ((U, oc1), (V, (SOME oc2)), L) in
          let _ = ExtSyn.checkErrors r in
          let (i, (U'', V'')) =
            try Timers.time Timers.abstract Abstract.abstractDef (U, V)
            with | Error msg -> raise (Abstract.Error (Paths.wrap (r, msg))) in
          let name = match optName with | NONE -> "_" | SOME name -> name in
          let ocd = Paths.def (i, oc1, oc2Opt) in
          let cd =
            if abbFlag
            then
              Names.nameConDec
                (IntSyn.AbbrevDef (name, NONE, i, U'', V'', L))
            else
              (Strict.check ((U'', V''), (SOME ocd));
               Names.nameConDec
                 (IntSyn.ConDef
                    (((name)
                      (* stricter checking of types according to Chris Richards Fri Jul  2 16:33:46 2004 -fp *)
                      (* (case optName of NONE => () | _ => Strict.checkType ((i, V''), SOME(ocd))); *)),
                      NONE, i, U'', V'', L, (IntSyn.ancestor U'')))) in
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
                 (V'', (IntSyn.Uni L));
               Timers.time Timers.checking TypeCheck.check (U'', V''))
            else () in
          let optConDec =
            match optName with | NONE -> NONE | SOME _ -> SOME cd in
          (optConDec, (SOME ocd))
      | (blockdec (name, Lsome, Lblock), Loc (fileName, r), abbFlag) ->
          let makectx =
            function
            | nil -> IntSyn.Null
            | (D)::L -> IntSyn.Decl ((makectx L), D) in
          let ctxToList =
            function
            | (IntSyn.Null, acc) -> acc
            | (Decl (G, D), acc) -> ctxToList (G, (D :: acc)) in
          let ctxAppend =
            function
            | (G, IntSyn.Null) -> G
            | (G, Decl (G', D)) -> IntSyn.Decl ((ctxAppend (G, G')), D) in
          let ctxBlockToString (G0, (G1, G2)) =
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
          let checkFreevars =
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
            | (SOME r1, SOME r2) -> Paths.join (r1, r2)
            | (_, SOME r2) -> r2 in
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
                     (((r')(* closed nf *)),
                       ((^) (((^) "Constraints remain in context block after term reconstruction:\n"
                                ctxBlockToString
                                (IntSyn.Null, (Gsome, Gblock)))
                               ^ "\n")
                          Print.cnstrsToString C))) in
          let _ = checkFreevars (G0, (Gsome', Gblock'), r') in
          let bd =
            IntSyn.BlockDec (name, NONE, Gsome', (ctxToList (Gblock', nil))) in
          let _ =
            if (!Global.chatter) >= 3
            then
              Msg.message
                ((Timers.time Timers.printing Print.conDecToString bd) ^ "\n")
            else () in
          ((SOME bd), NONE)
      | (blockdef (name, W), Loc (fileName, r), abbFlag) ->
          let W' = List.map Names.Qid W in
          let W'' =
            List.map
              (function
               | qid ->
                   (match Names.constLookup qid with
                    | NONE ->
                        raise
                          (Names.Error
                             (((^) "Undeclared label " Names.qidToString
                                 (valOf (Names.constUndef qid)))
                                ^ "."))
                    | SOME cid -> cid)) W' in
          let bd = IntSyn.BlockDef (name, NONE, W'') in
          let _ =
            if (!Global.chatter) >= 3
            then
              Msg.message
                ((Timers.time Timers.printing Print.conDecToString bd) ^ "\n")
            else () in
          ((SOME bd), NONE)
    let rec internalInst _ = raise Match
    let rec externalInst _ = raise Match
  end ;;
