
module type FIXITY  =
  sig
    type associativity =
      | Left 
      | Right 
      | None 
    type precedence =
      | Strength of int 
    val maxPrec : precedence
    val minPrec : precedence
    val less : precedence -> precedence -> bool
    val leq : precedence -> precedence -> bool
    val compare : precedence -> precedence -> order
    val inc : precedence -> precedence
    val dec : precedence -> precedence
    type fixity =
      | Nonfix 
      | Infix of (precedence * associativity) 
      | Prefix of precedence 
      | Postfix of precedence 
    val prec : fixity -> precedence
    val toString : fixity -> string
    val precToIntAsc : fixity -> int
  end
module type NAMES  =
  sig
    exception Error of string 
    exception Unprintable 
    module Fixity : FIXITY
    type __Qid =
      | Qid of (string list * string) 
    val qidToString : __Qid -> string
    val stringToQid : string -> __Qid option
    val unqualified : __Qid -> string option
    type nonrec namespace
    val newNamespace : unit -> namespace
    val insertConst : namespace -> IntSyn.cid -> unit
    val insertStruct : namespace -> IntSyn.mid -> unit
    val appConsts : (string -> IntSyn.cid -> unit) -> namespace -> unit
    val appStructs : (string -> IntSyn.mid -> unit) -> namespace -> unit
    val reset : unit -> unit
    val resetFrom : IntSyn.cid -> IntSyn.mid -> unit
    val installConstName : IntSyn.cid -> unit
    val installStructName : IntSyn.mid -> unit
    val constLookup : __Qid -> IntSyn.cid option
    val structLookup : __Qid -> IntSyn.mid option
    val constUndef : __Qid -> __Qid option
    val structUndef : __Qid -> __Qid option
    val constLookupIn : namespace -> __Qid -> IntSyn.cid option
    val structLookupIn : namespace -> __Qid -> IntSyn.mid option
    val constUndefIn : namespace -> __Qid -> __Qid option
    val structUndefIn : namespace -> __Qid -> __Qid option
    val conDecQid : IntSyn.__ConDec -> __Qid
    val constQid : IntSyn.cid -> __Qid
    val structQid : IntSyn.mid -> __Qid
    val installFixity : IntSyn.cid -> Fixity.fixity -> unit
    val getFixity : IntSyn.cid -> Fixity.fixity
    val fixityLookup : __Qid -> Fixity.fixity
    val installNamePref : IntSyn.cid -> (string list * string list) -> unit
    val getNamePref : IntSyn.cid -> (string list * string list) option
    val installComponents : IntSyn.mid -> namespace -> unit
    val getComponents : IntSyn.mid -> namespace
    val varReset : IntSyn.dctx -> unit
    val addEVar : IntSyn.__Exp -> string -> unit
    val getEVarOpt : string -> IntSyn.__Exp option
    val evarName : IntSyn.dctx -> IntSyn.__Exp -> string
    val bvarName : IntSyn.dctx -> int -> string
    val decName : IntSyn.dctx -> IntSyn.__Dec -> IntSyn.__Dec
    val decEName : IntSyn.dctx -> IntSyn.__Dec -> IntSyn.__Dec
    val decUName : IntSyn.dctx -> IntSyn.__Dec -> IntSyn.__Dec
    val decLUName : IntSyn.dctx -> IntSyn.__Dec -> IntSyn.__Dec
    val ctxName : IntSyn.dctx -> IntSyn.dctx
    val ctxLUName : IntSyn.dctx -> IntSyn.dctx
    val nameConDec : IntSyn.__ConDec -> IntSyn.__ConDec
    val skonstName : string -> string
    val namedEVars : unit -> (IntSyn.__Exp * string) list
    val evarCnstr : unit -> (IntSyn.__Exp * string) list
  end;;




module Names(Names:sig
                     module Global : GLOBAL
                     module Constraints : CONSTRAINTS
                     module HashTable : TABLE
                     module StringTree : TABLE
                   end) : NAMES =
  struct
    exception Error of string 
    exception Unprintable 
    module Fixity : FIXITY =
      struct
        type associativity =
          | Left 
          | Right 
          | None 
        type precedence =
          | Strength of int 
        let maxPrecInt = 9999
        let maxPrec = Strength maxPrecInt
        let minPrecInt = 0
        let minPrec = Strength minPrecInt
        let rec less (Strength p) (Strength q) = p < q
        let rec leq (Strength p) (Strength q) = p <= q
        let rec compare (Strength p) (Strength q) = Int.compare (p, q)
        let rec inc (Strength p) = Strength (p + 1)
        let rec dec (Strength p) = Strength (p - 1)
        type fixity =
          | Nonfix 
          | Infix of (precedence * associativity) 
          | Prefix of precedence 
          | Postfix of precedence 
        let rec precToIntAsc =
          function
          | Infix (Strength n, _) -> (maxPrecInt + 1) - n
          | Prefix (Strength n) -> (maxPrecInt + 1) - n
          | Postfix (Strength n) -> (maxPrecInt + 1) - n
          | Nonfix -> minPrecInt
        let rec prec =
          function
          | Infix (p, _) -> p
          | Prefix p -> p
          | Postfix p -> p
          | Nonfix -> inc maxPrec
        let rec toString =
          function
          | Infix (Strength p, Left) -> (^) "%infix left " Int.toString p
          | Infix (Strength p, Right) -> (^) "%infix right " Int.toString p
          | Infix (Strength p, None) -> (^) "%infix none " Int.toString p
          | Prefix (Strength p) -> (^) "%prefix " Int.toString p
          | Postfix (Strength p) -> (^) "%postfix " Int.toString p
          | Nonfix -> "%nonfix"
      end 
    let rec argNumber =
      function
      | Fixity.Nonfix -> 0
      | Infix _ -> 2
      | Prefix _ -> 1
      | Postfix _ -> 1
    let rec checkAtomic __0__ __1__ __2__ =
      match (__0__, __1__, __2__) with
      | (name, Pi (__D, __V), 0) -> true__
      | (name, Pi (__D, __V), n) -> checkAtomic (name, __V, (n - 1))
      | (_, Uni _, 0) -> true__
      | (_, Root _, 0) -> true__
      | (name, _, _) -> false__(* raise Error ("Constant " ^ name ^ " takes too many explicit arguments for given fixity") *)
      (* allow extraneous arguments, Sat Oct 23 14:18:27 1999 -fp *)
    let rec checkArgNumber __3__ __4__ =
      match (__3__, __4__) with
      | (ConDec (name, _, i, _, __V, __L), n) ->
          checkAtomic (name, __V, (i + n))
      | (SkoDec (name, _, i, __V, __L), n) ->
          checkAtomic (name, __V, (i + n))
      | (ConDef (name, _, i, _, __V, __L, _), n) ->
          checkAtomic (name, __V, (i + n))
      | (AbbrevDef (name, _, i, _, __V, __L), n) ->
          checkAtomic (name, __V, (i + n))
    let rec checkFixity __5__ __6__ __7__ =
      match (__5__, __6__, __7__) with
      | (name, _, 0) -> ()
      | (name, cid, n) ->
          if checkArgNumber ((IntSyn.sgnLookup cid), n)
          then ()
          else
            raise
              (Error
                 (("Constant " ^ name) ^
                    " takes too few explicit arguments for given fixity"))
    type __Qid =
      | Qid of (string list * string) 
    let rec qidToString (Qid (ids, name)) =
      List.foldr (fun id -> fun s -> (id ^ ".") ^ s) name ids
    let rec validateQualName =
      function
      | nil -> NONE
      | id::ids as l ->
          if List.exists (fun s -> s = "") l
          then NONE
          else Some (Qid ((rev ids), id))
    let rec stringToQid name =
      validateQualName (rev (String.fields (fun c -> c = '.') name))
    let rec unqualified = function | Qid (nil, id) -> Some id | _ -> NONE
    type nonrec namespace =
      (IntSyn.mid StringTree.__Table * IntSyn.cid StringTree.__Table)
    let rec newNamespace () =
      (((StringTree.new__ 0), (StringTree.new__ 0)) : namespace)
    let rec insertConst (structTable, constTable) cid =
      let condec = IntSyn.sgnLookup cid in
      let id = IntSyn.conDecName condec in
      match StringTree.insertShadow constTable (id, cid) with
      | NONE -> ()
      | Some _ ->
          raise
            (Error
               (("Shadowing: A constant named " ^ id) ^
                  "\nhas already been declared in this signature"))
    let rec insertStruct (structTable, constTable) mid =
      let strdec = IntSyn.sgnStructLookup mid in
      let id = IntSyn.strDecName strdec in
      match StringTree.insertShadow structTable (id, mid) with
      | NONE -> ()
      | Some _ ->
          raise
            (Error
               (("Shadowing: A structure named " ^ id) ^
                  "\nhas already been declared in this signature"))
    let rec appConsts f structTable constTable = StringTree.app f constTable
    let rec appStructs f structTable constTable =
      StringTree.app f structTable
    let rec fromTo f from to__ =
      if from >= to__ then () else (f from; fromTo f ((from + 1), to__))
    let maxCid = Global.maxCid
    let (shadowArray : IntSyn.cid option Array.array) =
      Array.array ((maxCid + 1), NONE)
    let rec shadowClear () = Array.modify (fun _ -> NONE) shadowArray
    let (fixityArray : Fixity.fixity Array.array) =
      Array.array ((maxCid + 1), Fixity.Nonfix)
    let rec fixityClear () =
      Array.modify (fun _ -> Fixity.Nonfix) fixityArray
    let (namePrefArray : (string list * string list) option Array.array) =
      Array.array ((maxCid + 1), NONE)
    let rec namePrefClear () = Array.modify (fun _ -> NONE) namePrefArray
    let (topNamespace : IntSyn.cid HashTable.__Table) = HashTable.new__ 4096
    let topInsert = HashTable.insertShadow topNamespace
    let topLookup = HashTable.lookup topNamespace
    let topDelete = HashTable.delete topNamespace
    let rec topClear () = HashTable.clear topNamespace
    let dummyNamespace =
      (((StringTree.new__ 0), (StringTree.new__ 0)) : namespace)
    let maxMid = Global.maxMid
    let (structShadowArray : IntSyn.mid option Array.array) =
      Array.array ((maxMid + 1), NONE)
    let rec structShadowClear () =
      Array.modify (fun _ -> NONE) structShadowArray
    let (componentsArray : namespace Array.array) =
      Array.array ((maxMid + 1), dummyNamespace)
    let rec componentsClear () =
      Array.modify (fun _ -> dummyNamespace) componentsArray
    let (topStructNamespace : IntSyn.mid HashTable.__Table) =
      HashTable.new__ 4096
    let topStructInsert = HashTable.insertShadow topStructNamespace
    let topStructLookup = HashTable.lookup topStructNamespace
    let topStructDelete = HashTable.delete topStructNamespace
    let rec topStructClear () = HashTable.clear topStructNamespace
    let rec installConstName cid =
      let condec = IntSyn.sgnLookup cid in
      let id = IntSyn.conDecName condec in
      match topInsert (id, cid) with
      | NONE -> ()
      | Some (_, cid') -> Array.update (shadowArray, cid, (Some cid'))
    let rec uninstallConst cid =
      let condec = IntSyn.sgnLookup cid in
      let id = IntSyn.conDecName condec in
      (match Array.sub (shadowArray, cid) with
       | NONE -> if (=) (topLookup id) Some cid then topDelete id else ()
       | Some cid' ->
           (topInsert (id, cid'); Array.update (shadowArray, cid, NONE)));
      Array.update (fixityArray, cid, Fixity.Nonfix);
      Array.update (namePrefArray, cid, NONE)
    let rec installStructName mid =
      let strdec = IntSyn.sgnStructLookup mid in
      let id = IntSyn.strDecName strdec in
      match topStructInsert (id, mid) with
      | NONE -> ()
      | Some (_, mid') -> Array.update (structShadowArray, mid, (Some mid'))
    let rec uninstallStruct mid =
      let strdec = IntSyn.sgnStructLookup mid in
      let id = IntSyn.strDecName strdec in
      (match Array.sub (structShadowArray, mid) with
       | NONE ->
           if (=) (topStructLookup id) Some mid
           then topStructDelete id
           else ()
       | Some mid' ->
           (topStructInsert (id, mid');
            Array.update (structShadowArray, mid, NONE)));
      Array.update (componentsArray, mid, dummyNamespace)
    let rec resetFrom mark markStruct =
      let (limit, limitStruct) = IntSyn.sgnSize () in
      let rec ct f i j = if j < i then () else (f j; ct f (i, (j - 1))) in
      ct uninstallConst (mark, (limit - 1));
      ct uninstallStruct (markStruct, (limitStruct - 1))
    let rec reset () =
      topClear ();
      topStructClear ();
      shadowClear ();
      structShadowClear ();
      fixityClear ();
      namePrefClear ();
      componentsClear ()
    let rec structComps mid =
      (fun r -> r.1) (Array.sub (componentsArray, mid))
    let rec constComps mid =
      (fun r -> r.2) (Array.sub (componentsArray, mid))
    let rec findStruct __8__ __9__ =
      match (__8__, __9__) with
      | (structTable, id::[]) -> StringTree.lookup structTable id
      | (structTable, id::ids) ->
          (match StringTree.lookup structTable id with
           | NONE -> NONE
           | Some mid -> findStruct ((structComps mid), ids))
    let rec findTopStruct =
      function
      | id::[] -> HashTable.lookup topStructNamespace id
      | id::ids ->
          (match HashTable.lookup topStructNamespace id with
           | NONE -> NONE
           | Some mid -> findStruct ((structComps mid), ids))
    let rec findUndefStruct __10__ __11__ __12__ =
      match (__10__, __11__, __12__) with
      | (structTable, id::[], ids') ->
          (match StringTree.lookup structTable id with
           | NONE -> Some (Qid ((rev ids'), id))
           | Some _ -> NONE)
      | (structTable, id::ids, ids') ->
          (match StringTree.lookup structTable id with
           | NONE -> Some (Qid ((rev ids'), id))
           | Some mid ->
               findUndefStruct ((structComps mid), ids, (id :: ids')))
    let rec findTopUndefStruct =
      function
      | id::[] ->
          (match HashTable.lookup topStructNamespace id with
           | NONE -> Some (Qid (nil, id))
           | Some _ -> NONE)
      | id::ids ->
          (match HashTable.lookup topStructNamespace id with
           | NONE -> Some (Qid (nil, id))
           | Some mid -> findUndefStruct ((structComps mid), ids, [id]))
    let rec constLookupIn __13__ __14__ =
      match (__13__, __14__) with
      | ((structTable, constTable), Qid (nil, id)) ->
          StringTree.lookup constTable id
      | ((structTable, constTable), Qid (ids, id)) ->
          (match findStruct (structTable, ids) with
           | NONE -> NONE
           | Some mid -> StringTree.lookup (constComps mid) id)
    let rec structLookupIn __15__ __16__ =
      match (__15__, __16__) with
      | ((structTable, constTable), Qid (nil, id)) ->
          StringTree.lookup structTable id
      | ((structTable, constTable), Qid (ids, id)) ->
          (match findStruct (structTable, ids) with
           | NONE -> NONE
           | Some mid -> StringTree.lookup (structComps mid) id)
    let rec constUndefIn __17__ __18__ =
      match (__17__, __18__) with
      | ((structTable, constTable), Qid (nil, id)) ->
          (match StringTree.lookup constTable id with
           | NONE -> Some (Qid (nil, id))
           | Some _ -> NONE)
      | ((structTable, constTable), Qid (ids, id)) ->
          (match findUndefStruct (structTable, ids, nil) with
           | Some _ as opt -> opt
           | NONE ->
               (match StringTree.lookup
                        (constComps (valOf (findStruct (structTable, ids))))
                        id
                with
                | NONE -> Some (Qid (ids, id))
                | Some _ -> NONE))
    let rec structUndefIn __19__ __20__ =
      match (__19__, __20__) with
      | ((structTable, constTable), Qid (nil, id)) ->
          (match StringTree.lookup structTable id with
           | NONE -> Some (Qid (nil, id))
           | Some _ -> NONE)
      | ((structTable, constTable), Qid (ids, id)) ->
          (match findUndefStruct (structTable, ids, nil) with
           | Some _ as opt -> opt
           | NONE ->
               (match StringTree.lookup
                        (structComps (valOf (findStruct (structTable, ids))))
                        id
                with
                | NONE -> Some (Qid (ids, id))
                | Some _ -> NONE))
    let rec constLookup =
      function
      | Qid (nil, id) -> HashTable.lookup topNamespace id
      | Qid (ids, id) ->
          (match findTopStruct ids with
           | NONE -> NONE
           | Some mid -> StringTree.lookup (constComps mid) id)
    let rec structLookup =
      function
      | Qid (nil, id) -> HashTable.lookup topStructNamespace id
      | Qid (ids, id) ->
          (match findTopStruct ids with
           | NONE -> NONE
           | Some mid -> StringTree.lookup (structComps mid) id)
    let rec constUndef =
      function
      | Qid (nil, id) ->
          (match HashTable.lookup topNamespace id with
           | NONE -> Some (Qid (nil, id))
           | Some _ -> NONE)
      | Qid (ids, id) ->
          (match findTopUndefStruct ids with
           | Some _ as opt -> opt
           | NONE ->
               (match StringTree.lookup
                        (constComps (valOf (findTopStruct ids))) id
                with
                | NONE -> Some (Qid (ids, id))
                | Some _ -> NONE))
    let rec structUndef =
      function
      | Qid (nil, id) ->
          (match HashTable.lookup topStructNamespace id with
           | NONE -> Some (Qid (nil, id))
           | Some _ -> NONE)
      | Qid (ids, id) ->
          (match findTopUndefStruct ids with
           | Some _ as opt -> opt
           | NONE ->
               (match StringTree.lookup
                        (structComps (valOf (findTopStruct ids))) id
                with
                | NONE -> Some (Qid (ids, id))
                | Some _ -> NONE))
    let rec structPath mid ids =
      let strdec = IntSyn.sgnStructLookup mid in
      let ids' = (IntSyn.strDecName strdec) :: ids in
      match IntSyn.strDecParent strdec with
      | NONE -> ids'
      | Some mid' -> structPath (mid', ids')
    let rec maybeShadow __21__ __22__ =
      match (__21__, __22__) with
      | (qid, false__) -> qid
      | (Qid (nil, id), true__) -> Qid (nil, (("%" ^ id) ^ "%"))
      | (Qid (id::ids, name), true__) ->
          Qid (((("%" ^ id) ^ "%") :: ids), name)
    let rec conDecQid condec =
      let id = IntSyn.conDecName condec in
      match IntSyn.conDecParent condec with
      | NONE -> Qid (nil, id)
      | Some mid -> Qid ((structPath (mid, nil)), id)
    let rec constQid cid =
      let condec = IntSyn.sgnLookup cid in
      let qid = conDecQid condec in
      maybeShadow (qid, ((<>) (constLookup qid) Some cid))
    let rec structQid mid =
      let strdec = IntSyn.sgnStructLookup mid in
      let id = IntSyn.strDecName strdec in
      let qid =
        match IntSyn.strDecParent strdec with
        | NONE -> Qid (nil, id)
        | Some mid -> Qid ((structPath (mid, nil)), id) in
      maybeShadow (qid, ((<>) (structLookup qid) Some mid))
    let rec installFixity cid fixity =
      let name = qidToString (constQid cid) in
      checkFixity (name, cid, (argNumber fixity));
      Array.update (fixityArray, cid, fixity)
    let rec getFixity cid = Array.sub (fixityArray, cid)
    let rec fixityLookup qid =
      match constLookup qid with
      | NONE -> Fixity.Nonfix
      | Some cid -> getFixity cid
    let rec installNamePref' cid (ePref, uPref) =
      let __L = IntSyn.constUni cid in
      let _ =
        match __L with
        | IntSyn.Type ->
            raise
              (Error
                 ((((^) "Object constant " qidToString (constQid cid)) ^
                     " cannot be given name preference\n")
                    ^
                    "Name preferences can only be established for type families"))
        | IntSyn.Kind -> () in
      Array.update (namePrefArray, cid, (Some (ePref, uPref)))
    let rec installNamePref __23__ __24__ =
      match (__23__, __24__) with
      | (cid, (ePref, nil)) ->
          installNamePref'
            (cid, (ePref, [String.map Char.toLower (hd ePref)]))
      | (cid, (ePref, uPref)) -> installNamePref' (cid, (ePref, uPref))
    let rec getNamePref cid = Array.sub (namePrefArray, cid)
    let rec installComponents mid namespace =
      Array.update (componentsArray, mid, namespace)
    let rec getComponents mid = Array.sub (componentsArray, mid)
    type __Extent =
      | Local 
      | Global 
    type __Role =
      | Exist 
      | Univ of __Extent 
    let rec extent = function | Exist -> Global | Univ ext -> ext
    let rec namePrefOf'' __25__ __26__ =
      match (__25__, __26__) with
      | (Exist, NONE) -> "X"
      | (Univ _, NONE) -> "x"
      | (Exist, Some (ePref, uPref)) -> hd ePref
      | (Univ _, Some (ePref, uPref)) -> hd uPref
    let rec namePrefOf' __27__ __28__ =
      match (__27__, __28__) with
      | (Exist, NONE) -> "X"
      | (Univ _, NONE) -> "x"
      | (role, Some (Const cid)) ->
          namePrefOf'' (role, (Array.sub (namePrefArray, cid)))
      | (role, Some (Def cid)) ->
          namePrefOf'' (role, (Array.sub (namePrefArray, cid)))
      | (role, Some (FVar _)) -> namePrefOf'' (role, NONE)
      | (role, Some (NSDef cid)) ->
          namePrefOf'' (role, (Array.sub (namePrefArray, cid)))(* the following only needed because reconstruction replaces
           undetermined types with FVars *)
    let rec namePrefOf role (__V) =
      namePrefOf' (role, (IntSyn.targetHeadOpt __V))
    type varEntry =
      | EVAR of IntSyn.__Exp 
    let (varTable : varEntry StringTree.__Table) = StringTree.new__ 0
    let varInsert = StringTree.insert varTable
    let varLookup = StringTree.lookup varTable
    let rec varClear () = StringTree.clear varTable
    let (varContext : IntSyn.dctx ref) = ref IntSyn.Null
    let (evarList : (IntSyn.__Exp * string) list ref) = ref nil
    let rec evarReset () = evarList := nil
    let rec evarLookup (__X) =
      let rec evlk __43__ __44__ =
        match (__43__, __44__) with
        | (r, nil) -> NONE
        | (r, (EVar (r', _, _, _), name)::l) ->
            if r = r' then Some name else evlk (r, l)
        | (r, (AVar r', name)::l) ->
            if r = r' then Some name else evlk (r, l) in
      match __X with
      | EVar (r, _, _, _) -> evlk (r, (!evarList))
      | AVar r -> evlk (r, (!evarList))
    let rec evarInsert entry = (evarList := entry) :: (!evarList)
    let rec namedEVars () = !evarList
    let rec evarCnstr' __45__ __46__ =
      match (__45__, __46__) with
      | (nil, acc) -> acc
      | (((EVar ({ contents = NONE }, _, _, cnstrs), name) as Xn)::l, acc) ->
          (match Constraints.simplify (!cnstrs) with
           | nil -> evarCnstr' (l, acc)
           | _::_ -> evarCnstr' (l, (Xn :: acc)))
      | (_::l, acc) -> evarCnstr' (l, acc)
    let rec evarCnstr () = evarCnstr' ((!evarList), nil)
    let (indexTable : int StringTree.__Table) = StringTree.new__ 0
    let indexInsert = StringTree.insert indexTable
    let indexLookup = StringTree.lookup indexTable
    let rec indexClear () = StringTree.clear indexTable
    let rec nextIndex' __47__ __48__ =
      match (__47__, __48__) with
      | (name, NONE) -> (indexInsert (name, 1); 1)
      | (name, Some i) -> (indexInsert (name, (i + 1)); i + 1)
    let rec nextIndex name = nextIndex' (name, (indexLookup name))
    let rec varReset (__G) =
      varClear (); evarReset (); indexClear (); varContext := __G
    let rec addEVar (__X) name =
      evarInsert (__X, name); varInsert (name, (EVAR __X))
    let rec getEVarOpt name =
      match varLookup name with
      | NONE -> NONE
      | Some (EVAR (__X)) -> Some __X
    let rec varDefined name =
      match varLookup name with | NONE -> false__ | Some _ -> true__
    let rec conDefined name =
      match constLookup (Qid (nil, name)) with
      | NONE -> false__
      | Some _ -> true__
    let rec ctxDefined (__G) name =
      let rec cdfd =
        function
        | IntSyn.Null -> false__
        | Decl (__G', Dec (Some name', _)) -> (name = name') || (cdfd __G')
        | Decl (__G', BDec (Some name', _)) -> (name = name') || (cdfd __G')
        | Decl (__G', NDec (Some name')) -> (name = name') || (cdfd __G')
        | Decl (__G', _) -> cdfd __G' in
      cdfd __G
    let rec tryNextName (__G) base =
      let name = (^) base Int.toString (nextIndex base) in
      if (varDefined name) || ((conDefined name) || (ctxDefined (__G, name)))
      then tryNextName (__G, base)
      else name
    let rec findNameLocal (__G) base i =
      let name = base ^ (if i = 0 then "" else Int.toString i) in
      if (varDefined name) || ((conDefined name) || (ctxDefined (__G, name)))
      then findNameLocal (__G, base, (i + 1))
      else name
    let rec findName __29__ __30__ __31__ =
      match (__29__, __30__, __31__) with
      | (__G, base, Local) -> findNameLocal (__G, base, 0)
      | (__G, base, Global) -> tryNextName (__G, base)
    let takeNonDigits = Substring.takel (not o Char.isDigit)
    let rec baseOf name =
      Substring.string (takeNonDigits (Compat.Substring.full name))
    let rec newEVarName __32__ __33__ =
      match (__32__, __33__) with
      | (__G, (EVar (r, _, __V, Cnstr) as X)) ->
          let name = tryNextName (__G, (namePrefOf (Exist, __V))) in
          (((evarInsert (__X, name); name))
            (* use name preferences below *))
      | (__G, (AVar r as X)) ->
          let name = tryNextName (__G, (namePrefOf' (Exist, NONE))) in
          (((evarInsert (__X, name); name))
            (* use name preferences below *))
    let rec evarName (__G) (__X) =
      match evarLookup __X with
      | NONE ->
          let name = newEVarName (__G, __X) in
          (varInsert (name, (EVAR __X)); name)
      | Some name -> name
    let rec bvarName (__G) k =
      ((match IntSyn.ctxLookup (__G, k) with
        | Dec (Some name, _) -> name
        | ADec (Some name, _) -> name
        | NDec (Some name) -> name
        | ADec (None, _) -> "ADec_"
        | Dec (None, _) -> "Dec_"
        | _ -> raise Unprintable)
      (* Evars can depend on NDec :-( *))
    let rec decName' __34__ __35__ __36__ =
      match (__34__, __35__, __36__) with
      | (role, __G, Dec (NONE, __V)) ->
          let name = findName (__G, (namePrefOf (role, __V)), (extent role)) in
          IntSyn.Dec ((Some name), __V)
      | (role, __G, (Dec (Some name, __V) as D)) ->
          if
            (varDefined name) ||
              ((conDefined name) || (ctxDefined (__G, name)))
          then IntSyn.Dec ((Some (tryNextName (__G, (baseOf name)))), __V)
          else __D
      | (role, __G, (BDec (NONE, ((cid, t) as b)) as D)) ->
          let name =
            findName
              (__G, ((^) "#" IntSyn.conDecName (IntSyn.sgnLookup cid)),
                Local) in
          IntSyn.BDec ((Some name), b)
      | (role, __G, (BDec (Some name, ((cid, t) as b)) as D)) ->
          if
            (varDefined name) ||
              ((conDefined name) || (ctxDefined (__G, name)))
          then IntSyn.BDec ((Some (tryNextName (__G, (baseOf name)))), b)
          else __D
      | (role, __G, ADec (NONE, d)) ->
          let name =
            findName (__G, (namePrefOf' (role, NONE)), (extent role)) in
          IntSyn.ADec ((Some name), d)
      | (role, __G, (ADec (Some name, d) as D)) ->
          if
            (varDefined name) ||
              ((conDefined name) || (ctxDefined (__G, name)))
          then IntSyn.ADec ((Some (tryNextName (__G, (baseOf name)))), d)
          else __D
      | (role, __G, (NDec (NONE) as D)) ->
          let name = findName (__G, "@x", Local) in
          let _ = print name in IntSyn.NDec (Some name)
      | (role, __G, (NDec (Some name) as D)) ->
          if
            (varDefined name) ||
              ((conDefined name) || (ctxDefined (__G, name)))
          then IntSyn.NDec (Some (tryNextName (__G, (baseOf name))))
          else __D(*      IntSyn.ADec(Some(name), d) *)
      (* use #l as base name preference for label l *)
    let decName = decName' Exist
    let decEName = decName' Exist
    let decUName = decName' (Univ Global)
    let decLUName = decName' (Univ Local)
    let rec ctxName =
      function
      | IntSyn.Null -> IntSyn.Null
      | Decl (__G, __D) ->
          let __G' = ctxName __G in IntSyn.Decl (__G', (decName (__G', __D)))
    let rec ctxLUName =
      function
      | IntSyn.Null -> IntSyn.Null
      | Decl (__G, __D) ->
          let __G' = ctxLUName __G in
          IntSyn.Decl (__G', (decLUName (__G', __D)))
    let rec pisEName' __37__ __38__ __39__ =
      match (__37__, __38__, __39__) with
      | (__G, 0, __V) -> __V
      | (__G, i, Pi ((__D, IntSyn.Maybe), __V)) ->
          let __D' = decEName (__G, __D) in
          IntSyn.Pi
            ((__D', IntSyn.Maybe),
              (pisEName' ((IntSyn.Decl (__G, __D')), (i - 1), __V)))(* i > 0 *)
    let rec pisEName i (__V) = pisEName' (IntSyn.Null, i, __V)
    let rec defEName' __40__ __41__ __42__ =
      match (__40__, __41__, __42__) with
      | (__G, 0, UV) -> UV
      | (__G, i,
         (Lam (__D, __U), Pi ((((_, __P))(* = D *)), __V)))
          ->
          let __D' = decEName (__G, __D) in
          let (__U', __V') =
            defEName' ((IntSyn.Decl (__G, __D')), (i - 1), (__U, __V)) in
          ((IntSyn.Lam (__D', __U')), (IntSyn.Pi ((__D', __P), __V')))
      (* i > 0 *)
    let rec defEName imp (UV) = defEName' (IntSyn.Null, imp, UV)
    let rec nameConDec' =
      function
      | ConDec (name, parent, imp, status, __V, __L) ->
          IntSyn.ConDec
            (name, parent, imp, status, (pisEName (imp, __V)), __L)
      | ConDef (name, parent, imp, __U, __V, __L, Anc) ->
          let (__U', __V') = defEName (imp, (__U, __V)) in
          IntSyn.ConDef (name, parent, imp, __U', __V', __L, Anc)
      | AbbrevDef (name, parent, imp, __U, __V, __L) ->
          let (__U', __V') = defEName (imp, (__U, __V)) in
          IntSyn.AbbrevDef (name, parent, imp, __U', __V', __L)
      | skodec -> skodec
    let rec nameConDec conDec = ((varReset IntSyn.Null; nameConDec' conDec)
      (* declaration is always closed *))
    let rec skonstName name = tryNextName (IntSyn.Null, name)
    let namedEVars = namedEVars
    let evarCnstr = evarCnstr
  end ;;




module Names =
  (Make_Names)(struct
                 module Global = Global
                 module Constraints = Constraints
                 module HashTable = StringHashTable
                 module StringTree = StringRedBlackTree
               end);;
