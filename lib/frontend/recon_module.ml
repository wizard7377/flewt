
module type MODEXTSYN  =
  sig
    module ExtSyn : EXTSYN
    type nonrec strexp
    val strexp : (string list * string * Paths.region) -> strexp
    type nonrec inst
    val coninst :
      ((string list * string * Paths.region) * ExtSyn.term * Paths.region) ->
        inst
    val strinst :
      ((string list * string * Paths.region) * strexp * Paths.region) -> inst
    type nonrec sigexp
    val thesig : sigexp
    val sigid : (string * Paths.region) -> sigexp
    val wheresig : (sigexp * inst list) -> sigexp
    type nonrec sigdef
    val sigdef : (string option * sigexp) -> sigdef
    type nonrec structdec
    val structdec : (string option * sigexp) -> structdec
    val structdef : (string option * strexp) -> structdec
  end (* External syntax for module expressions *)
(* Author: Kevin Watkins *)
(*! structure Paths : PATHS !*)
module type RECON_MODULE  =
  sig
    include MODEXTSYN
    module ModSyn : MODSYN
    exception Error of string 
    type nonrec whereclause
    type __StructDec =
      | StructDec of (string option * ModSyn.module__ * whereclause list) 
      | StructDef of (string option * IntSyn.mid) 
    val strexpToStrexp : strexp -> IntSyn.mid
    val sigexpToSigexp :
      (sigexp * ModSyn.module__ option) ->
        (ModSyn.module__ * whereclause list)
    val sigdefToSigdef :
      (sigdef * ModSyn.module__ option) ->
        (string option * ModSyn.module__ * whereclause list)
    val structdecToStructDec :
      (structdec * ModSyn.module__ option) -> __StructDec
    val moduleWhere : (ModSyn.module__ * whereclause) -> ModSyn.module__
  end;;




(* Elaboration for module expressions *)
(* Author: Kevin Watkins *)
module ReconModule(ReconModule:sig
                                 module Global : GLOBAL
                                 module Names : NAMES
                                 module ReconTerm' : RECON_TERM
                                 module ModSyn' : MODSYN
                                 (*! structure IntSyn : INTSYN !*)
                                 (*! sharing Names.IntSyn = IntSyn !*)
                                 (*! structure Paths' : PATHS !*)
                                 (*! sharing ReconTerm'.IntSyn = IntSyn !*)
                                 (*! sharing ReconTerm'.Paths = Paths' !*)
                                 (*! sharing ModSyn'.IntSyn = IntSyn !*)
                                 module IntTree : TABLE
                               end) : RECON_MODULE =
  struct
    module ExtSyn = ReconTerm'
    (*! structure Paths = Paths' !*)
    module ModSyn = ModSyn'
    exception Error of string 
    let rec error (r, msg) = raise (Error (Paths.wrap (r, msg)))
    type nonrec strexp = unit -> (IntSyn.mid * Paths.region)
    let rec strexp (ids, id, r) () =
      let qid = Names.Qid (ids, id) in
      match Names.structLookup qid with
      | None ->
          error
            (r,
              ((^) "Undeclared structure " Names.qidToString
                 (valOf (Names.structUndef qid))))
      | Some mid -> (mid, r)
    let rec strexpToStrexp (f : strexp) = (fun (r, _) -> r) (f ())
    type __Inst =
      | External of ExtSyn.term 
      | Internal of IntSyn.cid 
    type nonrec eqn = (IntSyn.cid * __Inst * Paths.region)
    type nonrec inst = (Names.namespace * eqn list) -> eqn list
    let rec coninst ((ids, id, r1), tm, r2) (ns, eqns) =
      let qid = Names.Qid (ids, id) in
      match Names.constLookupIn (ns, qid) with
      | None ->
          error
            (r1,
              ((^) "Undeclared identifier " Names.qidToString
                 (valOf (Names.constUndefIn (ns, qid)))))
      | Some cid -> (((cid, (External tm), r2) :: eqns)
          (* this is wrong because constants in the sig being instantiated might incorrectly appear in tm -kw *))
    let rec addStructEqn (rEqns, r1, r2, ids, mid1, mid2) =
      let ns1 = Names.getComponents mid1 in
      let ns2 = Names.getComponents mid2 in
      let rec push eqn = (rEqns := eqn) :: (!rEqns) in
      let rec doConst (name, cid1) =
        match Names.constLookupIn (ns2, (Names.Qid (nil, name))) with
        | None ->
            error
              (r1,
                ((^) "Instantiating structure lacks component "
                   Names.qidToString (Names.Qid ((rev ids), name))))
        | Some cid2 -> push (cid1, (Internal cid2), r2) in
      let rec doStruct (name, mid1) =
        match Names.structLookupIn (ns2, (Names.Qid (nil, name))) with
        | None ->
            error
              (r1,
                ((^) "Instantiating structure lacks component "
                   Names.qidToString (Names.Qid ((rev ids), name))))
        | Some mid2 ->
            addStructEqn (rEqns, r1, r2, (name :: ids), mid1, mid2) in
      Names.appConsts doConst ns1; Names.appStructs doStruct ns1
    let rec strinst ((ids, id, r1), strexp, r3) (ns, eqns) =
      let qid = Names.Qid (ids, id) in
      let mid1 =
        match Names.structLookupIn (ns, qid) with
        | None ->
            error
              (r1,
                ((^) "Undeclared structure " Names.qidToString
                   (valOf (Names.structUndefIn (ns, qid)))))
        | Some mid1 -> mid1 in
      let (mid2, r2) = strexp () in
      let rEqns = ref eqns in
      addStructEqn (rEqns, r2, r3, nil, mid1, mid2); !rEqns
    type nonrec whereclause = Names.namespace -> eqn list
    type nonrec sigexp =
      ModSyn.module__ option -> (ModSyn.module__ * whereclause list)
    let rec thesig (Some module__) = (module__, nil)
    let rec sigid (id, r) (None) =
      match ModSyn.lookupSigDef id with
      | None -> error (r, ("Undefined signature " ^ id))
      | Some module__ -> (module__, nil)
    let rec wheresig (sigexp, instList) moduleOpt =
      let (module__, wherecls) = sigexp moduleOpt in
      let rec wherecl ns =
        foldr (function | (inst, eqns) -> inst (ns, eqns)) nil instList in
      (module__, (wherecls @ [wherecl]))
    let rec sigexpToSigexp (sigexp, moduleOpt) = sigexp moduleOpt
    type nonrec sigdef =
      ModSyn.module__ option ->
        (string option * ModSyn.module__ * whereclause list)
    let rec sigdef (idOpt, sigexp) moduleOpt =
      let (module__, wherecls) = sigexp moduleOpt in
      (idOpt, module__, wherecls)
    let rec sigdefToSigdef (sigdef, moduleOpt) = sigdef moduleOpt
    type __StructDec =
      | StructDec of (string option * ModSyn.module__ * whereclause list) 
      | StructDef of (string option * IntSyn.mid) 
    type nonrec structdec = ModSyn.module__ option -> __StructDec
    let rec structdec (idOpt, sigexp) moduleOpt =
      let (module__, inst) = sigexp moduleOpt in
      StructDec (idOpt, module__, inst)
    let rec structdef (idOpt, strexp) (None) =
      let mid = strexpToStrexp strexp in StructDef (idOpt, mid)
    let rec structdecToStructDec (structdec, moduleOpt) = structdec moduleOpt
    type nonrec eqnTable = (__Inst * Paths.region) list ref IntTree.__Table
    let rec applyEqns wherecl namespace =
      let eqns = wherecl namespace in
      let (table : eqnTable) = IntTree.new__ 0 in
      let rec add (cid, Inst, r) =
        match IntTree.lookup table cid with
        | None -> IntTree.insert table (cid, (ref [(Inst, r)]))
        | Some rl -> (rl := (Inst, r)) :: (!rl) in
      let _ = List.app add eqns in
      let rec doInst =
        function
        | ((Internal cid, r), condec) ->
            (try
               ModSyn.strictify
                 (ExtSyn.internalInst
                    (condec,
                      (ModSyn.abbrevify (cid, (IntSyn.sgnLookup cid))), r))
             with
             | Error msg ->
                 raise
                   (ExtSyn.Error
                      ((^) (msg ^ "\nin instantiation generated for ")
                         Names.qidToString (Names.constQid cid))))
        | ((External tm, r), condec) ->
            ModSyn.strictify (ExtSyn.externalInst (condec, tm, r)) in
      let rec transformConDec (cid, condec) =
        match IntTree.lookup table cid with
        | None -> condec
        | Some (ref l) -> List.foldr doInst condec l in
      transformConDec
    let rec moduleWhere (module__, wherecl) =
      let (mark, markStruct) = IntSyn.sgnSize () in
      let module' = ModSyn.instantiateModule (module__, (applyEqns wherecl)) in
      let _ = Names.resetFrom (mark, markStruct) in ((module')
        (* val _ = IntSyn.resetFrom (mark, markStruct) *))
  end ;;
