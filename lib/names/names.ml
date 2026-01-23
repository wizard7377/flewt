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
    val less : (precedence * precedence) -> bool
    val leq : (precedence * precedence) -> bool
    val compare : (precedence * precedence) -> order
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
    type qid_ =
      | Qid of (string list * string) 
    val qidToString : qid_ -> string
    val stringToQid : string -> qid_ option
    val unqualified : qid_ -> string option
    type nonrec namespace
    val newNamespace : unit -> namespace
    val insertConst : (namespace * IntSyn.cid) -> unit
    val insertStruct : (namespace * IntSyn.mid) -> unit
    val appConsts : ((string * IntSyn.cid) -> unit) -> namespace -> unit
    val appStructs : ((string * IntSyn.mid) -> unit) -> namespace -> unit
    val reset : unit -> unit
    val resetFrom : (IntSyn.cid * IntSyn.mid) -> unit
    val installConstName : IntSyn.cid -> unit
    val installStructName : IntSyn.mid -> unit
    val constLookup : qid_ -> IntSyn.cid option
    val structLookup : qid_ -> IntSyn.mid option
    val constUndef : qid_ -> qid_ option
    val structUndef : qid_ -> qid_ option
    val constLookupIn : (namespace * qid_) -> IntSyn.cid option
    val structLookupIn : (namespace * qid_) -> IntSyn.mid option
    val constUndefIn : (namespace * qid_) -> qid_ option
    val structUndefIn : (namespace * qid_) -> qid_ option
    val conDecQid : IntSyn.conDec_ -> qid_
    val constQid : IntSyn.cid -> qid_
    val structQid : IntSyn.mid -> qid_
    val installFixity : (IntSyn.cid * Fixity.fixity) -> unit
    val getFixity : IntSyn.cid -> Fixity.fixity
    val fixityLookup : qid_ -> Fixity.fixity
    val installNamePref : (IntSyn.cid * (string list * string list)) -> unit
    val getNamePref : IntSyn.cid -> (string list * string list) option
    val installComponents : (IntSyn.mid * namespace) -> unit
    val getComponents : IntSyn.mid -> namespace
    val varReset : IntSyn.dctx -> unit
    val addEVar : (IntSyn.exp_ * string) -> unit
    val getEVarOpt : string -> IntSyn.exp_ option
    val evarName : (IntSyn.dctx * IntSyn.exp_) -> string
    val bvarName : (IntSyn.dctx * int) -> string
    val decName : (IntSyn.dctx * IntSyn.dec_) -> IntSyn.dec_
    val decEName : (IntSyn.dctx * IntSyn.dec_) -> IntSyn.dec_
    val decUName : (IntSyn.dctx * IntSyn.dec_) -> IntSyn.dec_
    val decLUName : (IntSyn.dctx * IntSyn.dec_) -> IntSyn.dec_
    val ctxName : IntSyn.dctx -> IntSyn.dctx
    val ctxLUName : IntSyn.dctx -> IntSyn.dctx
    val nameConDec : IntSyn.conDec_ -> IntSyn.conDec_
    val skonstName : string -> string
    val namedEVars : unit -> (IntSyn.exp_ * string) list
    val evarCnstr : unit -> (IntSyn.exp_ * string) list
  end


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
        let rec less (Strength p, Strength q) = p < q
        let rec leq (Strength p, Strength q) = p <= q
        let rec compare (Strength p, Strength q) = Int.compare (p, q)
        let rec inc (Strength p) = Strength (p + 1)
        let rec dec (Strength p) = Strength (p - 1)
        type fixity =
          | Nonfix 
          | Infix of (precedence * associativity) 
          | Prefix of precedence 
          | Postfix of precedence 
        let rec precToIntAsc =
          begin function
          | Infix (Strength n, _) -> (maxPrecInt + 1) - n
          | Prefix (Strength n) -> (maxPrecInt + 1) - n
          | Postfix (Strength n) -> (maxPrecInt + 1) - n
          | Nonfix -> minPrecInt end
        let rec prec =
          begin function
          | Infix (p, _) -> p
          | Prefix p -> p
          | Postfix p -> p
          | Nonfix -> inc maxPrec end
      let rec toString =
        begin function
        | Infix (Strength p, Left) -> (^) "%infix left " Int.toString p
        | Infix (Strength p, Right) -> (^) "%infix right " Int.toString p
        | Infix (Strength p, None) -> (^) "%infix none " Int.toString p
        | Prefix (Strength p) -> (^) "%prefix " Int.toString p
        | Postfix (Strength p) -> (^) "%postfix " Int.toString p
        | Nonfix -> "%nonfix" end
  end 
let rec argNumber =
  begin function
  | Fixity.Nonfix -> 0
  | Infix _ -> 2
  | Prefix _ -> 1
  | Postfix _ -> 1 end
let rec checkAtomic =
  begin function
  | (name, Pi (d_, v_), 0) -> true
  | (name, Pi (d_, v_), n) -> checkAtomic (name, v_, (n - 1))
  | (_, Uni _, 0) -> true
  | (_, Root _, 0) -> true
  | (name, _, _) -> false end(* raise Error ("Constant " ^ name ^ " takes too many explicit arguments for given fixity") *)
(* allow extraneous arguments, Sat Oct 23 14:18:27 1999 -fp *)
let rec checkArgNumber =
  begin function
  | (ConDec (name, _, i, _, v_, l_), n) -> checkAtomic (name, v_, (i + n))
  | (SkoDec (name, _, i, v_, l_), n) -> checkAtomic (name, v_, (i + n))
  | (ConDef (name, _, i, _, v_, l_, _), n) -> checkAtomic (name, v_, (i + n))
  | (AbbrevDef (name, _, i, _, v_, l_), n) -> checkAtomic (name, v_, (i + n)) end
let rec checkFixity =
  begin function
  | (name, _, 0) -> ()
  | (name, cid, n) ->
      if checkArgNumber ((IntSyn.sgnLookup cid), n) then begin () end
      else begin
        raise
          (Error
             (("Constant " ^ name) ^
                " takes too few explicit arguments for given fixity")) end end
type qid_ =
  | Qid of (string list * string) 
let rec qidToString (Qid (ids, name)) =
  List.foldr (begin function | (id, s) -> (id ^ ".") ^ s end) name ids
let rec validateQualName =
  begin function
  | [] -> None
  | id::ids as l -> if List.exists (begin function | s -> s = "" end) l
      then begin None end
  else begin Some (Qid ((rev ids), id)) end end
let rec stringToQid name =
  validateQualName
    (rev (String.fields (begin function | c -> c = '.' end) name))
let rec unqualified =
  begin function | Qid ([], id) -> Some id | _ -> None end
type nonrec namespace =
  (IntSyn.mid StringTree.table_ * IntSyn.cid StringTree.table_)
let rec newNamespace () =
  (((StringTree.new_ 0), (StringTree.new_ 0)) : namespace)
let rec insertConst ((structTable, constTable), cid) =
  let condec = IntSyn.sgnLookup cid in
  let id = IntSyn.conDecName condec in
  begin match StringTree.insertShadow constTable (id, cid) with
  | None -> ()
  | Some _ ->
      raise
        (Error
           (("Shadowing: A constant named " ^ id) ^
              "\nhas already been declared in this signature")) end
let rec insertStruct ((structTable, constTable), mid) =
  let strdec = IntSyn.sgnStructLookup mid in
  let id = IntSyn.strDecName strdec in
  begin match StringTree.insertShadow structTable (id, mid) with
  | None -> ()
  | Some _ ->
      raise
        (Error
           (("Shadowing: A structure named " ^ id) ^
              "\nhas already been declared in this signature")) end
let rec appConsts f (structTable, constTable) = StringTree.app f constTable
let rec appStructs f (structTable, constTable) = StringTree.app f structTable
let rec fromTo f (from, to_) = if from >= to_ then begin () end
  else begin (begin f from; fromTo f ((from + 1), to_) end) end
let maxCid = Global.maxCid
let (shadowArray : IntSyn.cid option Array.array) =
  Array.array ((maxCid + 1), None)
let rec shadowClear () = Array.modify (begin function | _ -> None end)
  shadowArray
let (fixityArray : Fixity.fixity Array.array) =
  Array.array ((maxCid + 1), Fixity.Nonfix)
let rec fixityClear () =
  Array.modify (begin function | _ -> Fixity.Nonfix end) fixityArray
let (namePrefArray : (string list * string list) option Array.array) =
  Array.array ((maxCid + 1), None)
let rec namePrefClear () = Array.modify (begin function | _ -> None end)
  namePrefArray
let (topNamespace : IntSyn.cid HashTable.table_) = HashTable.new_ 4096
let topInsert = HashTable.insertShadow topNamespace
let topLookup = HashTable.lookup topNamespace
let topDelete = HashTable.delete topNamespace
let rec topClear () = HashTable.clear topNamespace
let dummyNamespace = (((StringTree.new_ 0), (StringTree.new_ 0)) : namespace)
let maxMid = Global.maxMid
let (structShadowArray : IntSyn.mid option Array.array) =
  Array.array ((maxMid + 1), None)
let rec structShadowClear () = Array.modify (begin function | _ -> None end)
  structShadowArray
let (componentsArray : namespace Array.array) =
  Array.array ((maxMid + 1), dummyNamespace)
let rec componentsClear () =
  Array.modify (begin function | _ -> dummyNamespace end) componentsArray
let (topStructNamespace : IntSyn.mid HashTable.table_) = HashTable.new_ 4096
let topStructInsert = HashTable.insertShadow topStructNamespace
let topStructLookup = HashTable.lookup topStructNamespace
let topStructDelete = HashTable.delete topStructNamespace
let rec topStructClear () = HashTable.clear topStructNamespace
let rec installConstName cid =
  let condec = IntSyn.sgnLookup cid in
  let id = IntSyn.conDecName condec in
  begin match topInsert (id, cid) with
  | None -> ()
  | Some (_, cid') -> Array.update (shadowArray, cid, (Some cid')) end
let rec uninstallConst cid =
  let condec = IntSyn.sgnLookup cid in
  let id = IntSyn.conDecName condec in
  begin (begin match Array.sub (shadowArray, cid) with
         | None -> if (=) (topLookup id) Some cid then begin topDelete id end
             else begin () end
    | Some cid' ->
        (begin topInsert (id, cid'); Array.update (shadowArray, cid, None) end) end);
  Array.update (fixityArray, cid, Fixity.Nonfix);
  Array.update (namePrefArray, cid, None) end
let rec installStructName mid =
  let strdec = IntSyn.sgnStructLookup mid in
  let id = IntSyn.strDecName strdec in
  begin match topStructInsert (id, mid) with
  | None -> ()
  | Some (_, mid') -> Array.update (structShadowArray, mid, (Some mid')) end
let rec uninstallStruct mid =
  let strdec = IntSyn.sgnStructLookup mid in
  let id = IntSyn.strDecName strdec in
  begin (begin match Array.sub (structShadowArray, mid) with
         | None ->
             if (=) (topStructLookup id) Some mid
             then begin topStructDelete id end else begin () end
    | Some mid' ->
        (begin topStructInsert (id, mid');
         Array.update (structShadowArray, mid, None) end) end);
  Array.update (componentsArray, mid, dummyNamespace) end
let rec resetFrom (mark, markStruct) =
  let (limit, limitStruct) = IntSyn.sgnSize () in
  let rec ct f (i, j) = if j < i then begin () end
    else begin (begin f j; ct f (i, (j - 1)) end) end in
begin ct uninstallConst (mark, (limit - 1));
ct uninstallStruct (markStruct, (limitStruct - 1)) end
let rec reset () =
  begin topClear ();
  topStructClear ();
  shadowClear ();
  structShadowClear ();
  fixityClear ();
  namePrefClear ();
  componentsClear () end
let rec structComps mid = (fun r -> r.1) (Array.sub (componentsArray, mid))
let rec constComps mid = (fun r -> r.2) (Array.sub (componentsArray, mid))
let rec findStruct =
  begin function
  | (structTable, id::[]) -> StringTree.lookup structTable id
  | (structTable, id::ids) ->
      (begin match StringTree.lookup structTable id with
       | None -> None
       | Some mid -> findStruct ((structComps mid), ids) end) end
let rec findTopStruct =
  begin function
  | id::[] -> HashTable.lookup topStructNamespace id
  | id::ids ->
      (begin match HashTable.lookup topStructNamespace id with
       | None -> None
       | Some mid -> findStruct ((structComps mid), ids) end) end
let rec findUndefStruct =
  begin function
  | (structTable, id::[], ids') ->
      (begin match StringTree.lookup structTable id with
       | None -> Some (Qid ((rev ids'), id))
       | Some _ -> None end)
  | (structTable, id::ids, ids') ->
      (begin match StringTree.lookup structTable id with
       | None -> Some (Qid ((rev ids'), id))
       | Some mid -> findUndefStruct ((structComps mid), ids, (id :: ids')) end) end
let rec findTopUndefStruct =
  begin function
  | id::[] ->
      (begin match HashTable.lookup topStructNamespace id with
       | None -> Some (Qid ([], id))
       | Some _ -> None end)
  | id::ids ->
      (begin match HashTable.lookup topStructNamespace id with
       | None -> Some (Qid ([], id))
       | Some mid -> findUndefStruct ((structComps mid), ids, [id]) end) end
let rec constLookupIn =
  begin function
  | ((structTable, constTable), Qid ([], id)) ->
      StringTree.lookup constTable id
  | ((structTable, constTable), Qid (ids, id)) ->
      (begin match findStruct (structTable, ids) with
       | None -> None
       | Some mid -> StringTree.lookup (constComps mid) id end) end
let rec structLookupIn =
  begin function
  | ((structTable, constTable), Qid ([], id)) ->
      StringTree.lookup structTable id
  | ((structTable, constTable), Qid (ids, id)) ->
      (begin match findStruct (structTable, ids) with
       | None -> None
       | Some mid -> StringTree.lookup (structComps mid) id end) end
let rec constUndefIn =
  begin function
  | ((structTable, constTable), Qid ([], id)) ->
      (begin match StringTree.lookup constTable id with
       | None -> Some (Qid ([], id))
       | Some _ -> None end)
  | ((structTable, constTable), Qid (ids, id)) ->
      (begin match findUndefStruct (structTable, ids, []) with
       | Some _ as opt -> opt
       | None ->
           (begin match StringTree.lookup
                          (constComps (valOf (findStruct (structTable, ids))))
                          id
                  with
            | None -> Some (Qid (ids, id))
            | Some _ -> None end) end) end
let rec structUndefIn =
  begin function
  | ((structTable, constTable), Qid ([], id)) ->
      (begin match StringTree.lookup structTable id with
       | None -> Some (Qid ([], id))
       | Some _ -> None end)
  | ((structTable, constTable), Qid (ids, id)) ->
      (begin match findUndefStruct (structTable, ids, []) with
       | Some _ as opt -> opt
       | None ->
           (begin match StringTree.lookup
                          (structComps
                             (valOf (findStruct (structTable, ids)))) id
                  with
            | None -> Some (Qid (ids, id))
            | Some _ -> None end) end) end
let rec constLookup =
  begin function
  | Qid ([], id) -> HashTable.lookup topNamespace id
  | Qid (ids, id) ->
      (begin match findTopStruct ids with
       | None -> None
       | Some mid -> StringTree.lookup (constComps mid) id end) end
let rec structLookup =
  begin function
  | Qid ([], id) -> HashTable.lookup topStructNamespace id
  | Qid (ids, id) ->
      (begin match findTopStruct ids with
       | None -> None
       | Some mid -> StringTree.lookup (structComps mid) id end) end
let rec constUndef =
  begin function
  | Qid ([], id) ->
      (begin match HashTable.lookup topNamespace id with
       | None -> Some (Qid ([], id))
       | Some _ -> None end)
  | Qid (ids, id) ->
      (begin match findTopUndefStruct ids with
       | Some _ as opt -> opt
       | None ->
           (begin match StringTree.lookup
                          (constComps (valOf (findTopStruct ids))) id
                  with
            | None -> Some (Qid (ids, id))
            | Some _ -> None end) end) end
let rec structUndef =
  begin function
  | Qid ([], id) ->
      (begin match HashTable.lookup topStructNamespace id with
       | None -> Some (Qid ([], id))
       | Some _ -> None end)
  | Qid (ids, id) ->
      (begin match findTopUndefStruct ids with
       | Some _ as opt -> opt
       | None ->
           (begin match StringTree.lookup
                          (structComps (valOf (findTopStruct ids))) id
                  with
            | None -> Some (Qid (ids, id))
            | Some _ -> None end) end) end
let rec structPath (mid, ids) =
  let strdec = IntSyn.sgnStructLookup mid in
  let ids' = (IntSyn.strDecName strdec) :: ids in
  begin match IntSyn.strDecParent strdec with
  | None -> ids'
  | Some mid' -> structPath (mid', ids') end
let rec maybeShadow =
  begin function
  | (qid, false) -> qid
  | (Qid ([], id), true) -> Qid ([], (("%" ^ id) ^ "%"))
  | (Qid (id::ids, name), true) -> Qid (((("%" ^ id) ^ "%") :: ids), name) end
let rec conDecQid condec =
  let id = IntSyn.conDecName condec in
  begin match IntSyn.conDecParent condec with
  | None -> Qid ([], id)
  | Some mid -> Qid ((structPath (mid, [])), id) end
let rec constQid cid =
  let condec = IntSyn.sgnLookup cid in
  let qid = conDecQid condec in
  maybeShadow (qid, ((<>) (constLookup qid) Some cid))
let rec structQid mid =
  let strdec = IntSyn.sgnStructLookup mid in
  let id = IntSyn.strDecName strdec in
  let qid =
    begin match IntSyn.strDecParent strdec with
    | None -> Qid ([], id)
    | Some mid -> Qid ((structPath (mid, [])), id) end in
  maybeShadow (qid, ((<>) (structLookup qid) Some mid))
let rec installFixity (cid, fixity) =
  let name = qidToString (constQid cid) in
  begin checkFixity (name, cid, (argNumber fixity));
  Array.update (fixityArray, cid, fixity) end
let rec getFixity cid = Array.sub (fixityArray, cid)
let rec fixityLookup qid =
  begin match constLookup qid with
  | None -> Fixity.Nonfix
  | Some cid -> getFixity cid end
let rec installNamePref' (cid, (ePref, uPref)) =
  let l_ = IntSyn.constUni cid in
  let _ =
    begin match l_ with
    | IntSyn.Type ->
        raise
          (Error
             ((((^) "Object constant " qidToString (constQid cid)) ^
                 " cannot be given name preference\n")
                ^
                "Name preferences can only be established for type families"))
    | IntSyn.Kind -> () end in
  Array.update (namePrefArray, cid, (Some (ePref, uPref)))
let rec installNamePref =
  begin function
  | (cid, (ePref, [])) ->
      installNamePref'
        (cid, (ePref, [String.map Char.toLower (List.hd ePref)]))
  | (cid, (ePref, uPref)) -> installNamePref' (cid, (ePref, uPref)) end
let rec getNamePref cid = Array.sub (namePrefArray, cid)
let rec installComponents (mid, namespace) =
  Array.update (componentsArray, mid, namespace)
let rec getComponents mid = Array.sub (componentsArray, mid)
type extent_ =
  | Local 
  | Global 
type role_ =
  | Exist 
  | Univ of extent_ 
let rec extent = begin function | Exist -> Global | Univ ext -> ext end
let rec namePrefOf'' =
  begin function
  | (Exist, None) -> "X"
  | (Univ _, None) -> "x"
  | (Exist, Some (ePref, uPref)) -> List.hd ePref
  | (Univ _, Some (ePref, uPref)) -> List.hd uPref end
let rec namePrefOf' =
  begin function
  | (Exist, None) -> "X"
  | (Univ _, None) -> "x"
  | (role, Some (Const cid)) ->
      namePrefOf'' (role, (Array.sub (namePrefArray, cid)))
  | (role, Some (Def cid)) ->
      namePrefOf'' (role, (Array.sub (namePrefArray, cid)))
  | (role, Some (FVar _)) -> namePrefOf'' (role, None)
  | (role, Some (NSDef cid)) ->
      namePrefOf'' (role, (Array.sub (namePrefArray, cid))) end(* the following only needed because reconstruction replaces
           undetermined types with FVars *)
let rec namePrefOf (role, v_) = namePrefOf' (role, (IntSyn.targetHeadOpt v_))
type varEntry =
  | EVAR of IntSyn.exp_ 
let (varTable : varEntry StringTree.table_) = StringTree.new_ 0
let varInsert = StringTree.insert varTable
let varLookup = StringTree.lookup varTable
let rec varClear () = StringTree.clear varTable
let (varContext : IntSyn.dctx ref) = ref IntSyn.Null
let (evarList : (IntSyn.exp_ * string) list ref) = ref []
let rec evarReset () = evarList := []
let rec evarLookup (x_) =
  let rec evlk =
    begin function
    | (r, []) -> None
    | (r, (EVar (r', _, _, _), name)::l) ->
        if r = r' then begin Some name end else begin evlk (r, l) end
    | (r, (AVar r', name)::l) -> if r = r' then begin Some name end
        else begin evlk (r, l) end end in
begin match x_ with
| EVar (r, _, _, _) -> evlk (r, !evarList)
| AVar r -> evlk (r, !evarList) end
let rec evarInsert entry = (evarList := entry) :: !evarList
let rec namedEVars () = !evarList
let rec evarCnstr' =
  begin function
  | ([], acc) -> acc
  | (((EVar ({ contents = None }, _, _, cnstrs), name) as Xn)::l, acc) ->
      (begin match Constraints.simplify !cnstrs with
       | [] -> evarCnstr' (l, acc)
       | _::_ -> evarCnstr' (l, (Xn :: acc)) end)
  | (_::l, acc) -> evarCnstr' (l, acc) end
let rec evarCnstr () = evarCnstr' (!evarList, [])
let (indexTable : int StringTree.table_) = StringTree.new_ 0
let indexInsert = StringTree.insert indexTable
let indexLookup = StringTree.lookup indexTable
let rec indexClear () = StringTree.clear indexTable
let rec nextIndex' =
  begin function | (name, None) -> (begin indexInsert (name, 1); 1 end)
  | (name, Some i) -> (begin indexInsert (name, (i + 1)); i + 1 end) end
let rec nextIndex name = nextIndex' (name, (indexLookup name))
let rec varReset (g_) =
  begin varClear (); evarReset (); indexClear (); varContext := g_ end
let rec addEVar (x_, name) =
  begin evarInsert (x_, name); varInsert (name, (EVAR x_)) end
let rec getEVarOpt name =
  begin match varLookup name with
  | None -> None
  | Some (EVAR (x_)) -> Some x_ end
let rec varDefined name =
  begin match varLookup name with | None -> false | Some _ -> true end
let rec conDefined name =
  begin match constLookup (Qid ([], name)) with
  | None -> false
  | Some _ -> true end
let rec ctxDefined (g_, name) =
  let rec cdfd =
    begin function
    | IntSyn.Null -> false
    | Decl (g'_, Dec (Some name', _)) -> (name = name') || (cdfd g'_)
    | Decl (g'_, BDec (Some name', _)) -> (name = name') || (cdfd g'_)
    | Decl (g'_, NDec (Some name')) -> (name = name') || (cdfd g'_)
    | Decl (g'_, _) -> cdfd g'_ end in
cdfd g_
let rec tryNextName (g_, base) =
  let name = (^) base Int.toString (nextIndex base) in
  if (varDefined name) || ((conDefined name) || (ctxDefined (g_, name)))
  then begin tryNextName (g_, base) end else begin name end
let rec findNameLocal (g_, base, i) =
  let name = base ^ (if i = 0 then begin "" end else begin Int.toString i end) in
if (varDefined name) || ((conDefined name) || (ctxDefined (g_, name)))
then begin findNameLocal (g_, base, (i + 1)) end else begin name end
let rec findName =
  begin function
  | (g_, base, Local) -> findNameLocal (g_, base, 0)
  | (g_, base, Global) -> tryNextName (g_, base) end
let takeNonDigits = Substring.takel (not o Char.isDigit)
let rec baseOf name =
  Substring.string (takeNonDigits (Compat.Substring.full name))
let rec newEVarName =
  begin function
  | (g_, (EVar (r, _, v_, Cnstr) as x_)) ->
      let name = tryNextName (g_, (namePrefOf (Exist, v_))) in
      (((begin evarInsert (x_, name); name end))
      (* use name preferences below *))
  | (g_, (AVar r as x_)) ->
      let name = tryNextName (g_, (namePrefOf' (Exist, None))) in
      (((begin evarInsert (x_, name); name end))
      (* use name preferences below *)) end
let rec evarName (g_, x_) =
  begin match evarLookup x_ with
  | None ->
      let name = newEVarName (g_, x_) in
      (begin varInsert (name, (EVAR x_)); name end)
  | Some name -> name end
let rec bvarName (g_, k) =
  ((begin match IntSyn.ctxLookup (g_, k) with
    | Dec (Some name, _) -> name
    | ADec (Some name, _) -> name
    | NDec (Some name) -> name
    | ADec (None, _) -> "ADec_"
    | Dec (None, _) -> "Dec_"
    | _ -> raise Unprintable end)
  (* Evars can depend on NDec :-( *))
let rec decName' arg__0 arg__1 =
  begin match (arg__0, arg__1) with
  | (role, (g_, Dec (None, v_))) ->
      let name = findName (g_, (namePrefOf (role, v_)), (extent role)) in
      IntSyn.Dec ((Some name), v_)
  | (role, (g_, (Dec (Some name, v_) as d_))) ->
      if (varDefined name) || ((conDefined name) || (ctxDefined (g_, name)))
      then begin IntSyn.Dec ((Some (tryNextName (g_, (baseOf name)))), v_) end
      else begin d_ end
  | (role, (g_, (BDec (None, ((cid, t) as b)) as d_))) ->
      let name =
        findName
          (g_, ((^) "#" IntSyn.conDecName (IntSyn.sgnLookup cid)), Local) in
      IntSyn.BDec ((Some name), b)
  | (role, (g_, (BDec (Some name, ((cid, t) as b)) as d_))) ->
      if (varDefined name) || ((conDefined name) || (ctxDefined (g_, name)))
      then begin IntSyn.BDec ((Some (tryNextName (g_, (baseOf name)))), b) end
      else begin d_ end
| (role, (g_, ADec (None, d))) ->
    let name = findName (g_, (namePrefOf' (role, None)), (extent role)) in
    IntSyn.ADec ((Some name), d)
| (role, (g_, (ADec (Some name, d) as d_))) ->
    if (varDefined name) || ((conDefined name) || (ctxDefined (g_, name)))
    then begin IntSyn.ADec ((Some (tryNextName (g_, (baseOf name)))), d) end
    else begin d_ end
| (role, (g_, (NDec (None) as d_))) ->
    let name = findName (g_, "@x", Local) in
    let _ = print name in IntSyn.NDec (Some name)
| (role, (g_, (NDec (Some name) as d_))) ->
    if (varDefined name) || ((conDefined name) || (ctxDefined (g_, name)))
    then begin IntSyn.NDec (Some (tryNextName (g_, (baseOf name)))) end
    else begin d_ end end(*      IntSyn.ADec(SOME(name), d) *)(* use #l as base name preference for label l *)
let decName = decName' Exist
let decEName = decName' Exist
let decUName = decName' (Univ Global)
let decLUName = decName' (Univ Local)
let rec ctxName =
  begin function
  | IntSyn.Null -> IntSyn.Null
  | Decl (g_, d_) ->
      let g'_ = ctxName g_ in IntSyn.Decl (g'_, (decName (g'_, d_))) end
let rec ctxLUName =
  begin function
  | IntSyn.Null -> IntSyn.Null
  | Decl (g_, d_) ->
      let g'_ = ctxLUName g_ in IntSyn.Decl (g'_, (decLUName (g'_, d_))) end
let rec pisEName' =
  begin function
  | (g_, 0, v_) -> v_
  | (g_, i, Pi ((d_, IntSyn.Maybe), v_)) ->
      let d'_ = decEName (g_, d_) in
      IntSyn.Pi
        ((d'_, IntSyn.Maybe),
          (pisEName' ((IntSyn.Decl (g_, d'_)), (i - 1), v_))) end(* i > 0 *)
let rec pisEName (i, v_) = pisEName' (IntSyn.Null, i, v_)
let rec defEName' =
  begin function
  | (g_, 0, UV) -> UV
  | (g_, i, (Lam (d_, u_), Pi ((((_, p_))(* = D *)), v_)))
      ->
      let d'_ = decEName (g_, d_) in
      let (u'_, v'_) = defEName' ((IntSyn.Decl (g_, d'_)), (i - 1), (u_, v_)) in
      ((IntSyn.Lam (d'_, u'_)), (IntSyn.Pi ((d'_, p_), v'_))) end(* i > 0 *)
let rec defEName (imp, UV) = defEName' (IntSyn.Null, imp, UV)
let rec nameConDec' =
  begin function
  | ConDec (name, parent, imp, status, v_, l_) ->
      IntSyn.ConDec (name, parent, imp, status, (pisEName (imp, v_)), l_)
  | ConDef (name, parent, imp, u_, v_, l_, Anc) ->
      let (u'_, v'_) = defEName (imp, (u_, v_)) in
      IntSyn.ConDef (name, parent, imp, u'_, v'_, l_, Anc)
  | AbbrevDef (name, parent, imp, u_, v_, l_) ->
      let (u'_, v'_) = defEName (imp, (u_, v_)) in
      IntSyn.AbbrevDef (name, parent, imp, u'_, v'_, l_)
  | skodec -> skodec end
let rec nameConDec conDec =
  ((begin varReset IntSyn.Null; nameConDec' conDec end)
  (* declaration is always closed *))
let rec skonstName name = tryNextName (IntSyn.Null, name)
let namedEVars = namedEVars
let evarCnstr = evarCnstr end



module Names =
  (Names)(struct
                 module Global = Global
                 module Constraints = Constraints
                 module HashTable = StringHashTable
                 module StringTree = StringRedBlackTree
               end)