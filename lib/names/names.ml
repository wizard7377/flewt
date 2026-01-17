
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
    exception Error of
      ((string)(*! structure IntSyn : INTSYN !*)(* signature FIXITY *)
      (* returns integer for precedence such that lower values correspond to higher precedence, useful for exports *)
      (* Modified: Jeff Polakow *)(* Author: Frank Pfenning *)
      (* Names of Constants and Variables *)) 
    exception Unprintable 
    module Fixity : FIXITY
    type __Qid =
      | Qid of (((string)(* Constant names and fixities *))
      list * string) 
    val qidToString : __Qid -> string
    val stringToQid : string -> __Qid option
    val unqualified : __Qid -> string option
    type nonrec namespace
    val newNamespace : unit -> namespace
    val insertConst : (namespace * IntSyn.cid) -> unit
    val insertStruct :
      (namespace * IntSyn.mid) ->
        ((unit)(* shadowing disallowed *))
    val appConsts :
      ((string * IntSyn.cid) -> unit) ->
        namespace -> ((unit)(* shadowing disallowed *))
    val appStructs : ((string * IntSyn.mid) -> unit) -> namespace -> unit
    val reset : unit -> unit
    val resetFrom : (IntSyn.cid * IntSyn.mid) -> unit
    val installConstName :
      IntSyn.cid ->
        ((unit)(* The following functions have to do with the mapping from names
     to cids/mids only. *))
    val installStructName : IntSyn.mid -> unit
    val constLookup : __Qid -> IntSyn.cid option
    val structLookup : __Qid -> IntSyn.mid option
    val constUndef : __Qid -> __Qid option
    val structUndef :
      __Qid ->
        ((__Qid)(* shortest undefined prefix of Qid *))
          option
    val constLookupIn : (namespace * __Qid) -> IntSyn.cid option
    val structLookupIn : (namespace * __Qid) -> IntSyn.mid option
    val constUndefIn : (namespace * __Qid) -> __Qid option
    val structUndefIn : (namespace * __Qid) -> __Qid option
    val conDecQid :
      IntSyn.__ConDec ->
        ((__Qid)(* This function maps cids/mids to names.  It uses the information in
     the IntSyn.ConDec or IntSyn.StrDec entries only, and only considers
     the name->cid/mid mapping defined above in order to tell whether a
     name is shadowed (any constant or structure whose canonical name
     would map to something else, or to nothing at all, in the case of
     an anonymous structure, is shadowed). *))
    val constQid : IntSyn.cid -> __Qid
    val structQid :
      IntSyn.mid -> ((__Qid)(* will mark if shadowed *))
    val installFixity :
      (IntSyn.cid * Fixity.fixity) ->
        ((unit)(* will mark if shadowed *))
    val getFixity : IntSyn.cid -> Fixity.fixity
    val fixityLookup : __Qid -> Fixity.fixity
    val installNamePref :
      (IntSyn.cid * (string list * string list)) ->
        ((unit)(* Name preferences for anonymous variables: a, EPref, UPref *)
        (* Nonfix if undefined *))
    val getNamePref : IntSyn.cid -> (string list * string list) option
    val installComponents : (IntSyn.mid * namespace) -> unit
    val getComponents : IntSyn.mid -> namespace
    val varReset :
      IntSyn.dctx ->
        ((unit)(* EVar and BVar name choices *))
    val addEVar :
      (IntSyn.__Exp * string) ->
        ((unit)(* context in which EVars are created *))
    val getEVarOpt :
      string ->
        ((IntSyn.__Exp)(* assumes name not already used *))
          option
    val evarName :
      (IntSyn.dctx * IntSyn.__Exp) ->
        ((string)(* NONE, if undefined or not EVar *))
    val bvarName :
      (IntSyn.dctx * int) ->
        ((string)(* create, if undefined *))
    val decName :
      (IntSyn.dctx * IntSyn.__Dec) ->
        ((IntSyn.__Dec)(* raises Unprintable if undefined *))
    val decEName :
      (IntSyn.dctx * IntSyn.__Dec) ->
        ((IntSyn.__Dec)(* status unknown, like decEName *))
    val decUName :
      (IntSyn.dctx * IntSyn.__Dec) ->
        ((IntSyn.__Dec)(* assign existential name *))
    val decLUName :
      (IntSyn.dctx * IntSyn.__Dec) ->
        ((IntSyn.__Dec)(* assign universal name *))
    val ctxName :
      IntSyn.dctx ->
        ((IntSyn.dctx)(* assign local universal name *))
    val ctxLUName :
      IntSyn.dctx ->
        ((IntSyn.dctx)(* assign global existential names *))
    val nameConDec :
      IntSyn.__ConDec ->
        ((IntSyn.__ConDec)(* assign local universal names *))
    val skonstName :
      string -> ((string)(* Skolem constants *))
    val namedEVars :
      unit ->
        (((IntSyn.__Exp)(* Named EVars, used for queries *))
          * string) list
    val evarCnstr :
      unit ->
        (((IntSyn.__Exp)(* Uninstantiated named EVars with constraints *))
          * string) list
  end;;




module Names(Names:sig
                     module Global : GLOBAL
                     module Constraints : CONSTRAINTS
                     module HashTable : TABLE
                     module StringTree :
                     ((TABLE)(* Names of Constants and Variables *)
                     (* Author: Frank Pfenning *)(* Modified: Jeff Polakow *)
                     (*! structure IntSyn' : INTSYN !*)
                     (*! sharing Constraints.IntSyn = IntSyn' !*))
                   end) : NAMES =
  struct
    exception Error of
      ((string)(*! structure IntSyn = IntSyn' !*)) 
    exception Unprintable (*
     Unprintable is raised when trying to resolve the names
     of unnamed variables.  Usually, this signals an error
     in Twelf; the only exception is the use of anonymous
     bound variables [_] or {_} in the source.
  *)
    module Fixity : FIXITY =
      struct
        type associativity =
          | Left 
          | Right 
          | None (* Associativity ascribed to infix operators
       assoc ::= left    e.g. `<-'
               | right   e.g. `->'
               | none    e.g. `==' from some object language
    *)
        (***********************)(* Operator Precedence *)
        (***********************)
        type precedence =
          | Strength of ((int)(* Operator Precedence *)) 
        let ((maxPrecInt)(* Maximal and minimal precedence which can be declared explicitly *))
          = 9999
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
          | Infix of
          (((precedence)(* Fixities ascribed to constants *))
          * associativity) 
          | Prefix of precedence 
          | Postfix of precedence 
        let rec precToIntAsc =
          function
          | Infix
              (Strength
               ((n)(* returns integer for precedence such that lower values correspond to higher precedence, useful for exports *)),
               _)
              -> (maxPrecInt + 1) - n
          | Prefix (Strength n) -> (maxPrecInt + 1) - n
          | Postfix (Strength n) -> (maxPrecInt + 1) - n
          | Nonfix -> minPrecInt
        let rec prec =
          function
          | Infix
              (((p)(* prec (fix) = precedence of fix *)), _)
              -> p
          | Prefix p -> p
          | Postfix p -> p
          | Nonfix -> inc maxPrec
        let rec toString =
          function
          | Infix
              (Strength
               ((p)(* toString (fix) = declaration corresponding to fix *)),
               Left)
              -> (^) "%infix left " Int.toString p
          | Infix (Strength p, Right) -> (^) "%infix right " Int.toString p
          | Infix (Strength p, None) -> (^) "%infix none " Int.toString p
          | Prefix (Strength p) -> (^) "%prefix " Int.toString p
          | Postfix (Strength p) -> (^) "%postfix " Int.toString p
          | Nonfix -> "%nonfix"
      end 
    let rec argNumber =
      function
      | ((Fixity.Nonfix)(* not legal input *)(* structure Fixity *)
          (* argNumber (fix) = minimum # of explicit arguments required *)
          (* for operator with fixity fix (0 if there are no requirements) *))
          -> 0
      | Infix _ -> 2
      | Prefix _ -> 1
      | Postfix _ -> 1
    let rec checkAtomic =
      function
      | (((name)(* checkAtomic (name, V, n) = ()
     if V expects exactly n arguments,
     raises Error(msg) otherwise
  *)),
         Pi (D, V), 0) -> true__
      | (((name)(* allow extraneous arguments, Sat Oct 23 14:18:27 1999 -fp *)
         (* raise Error ("Constant " ^ name ^ " takes too many explicit arguments for given fixity") *)),
         Pi (D, V), n) -> checkAtomic (name, V, (n - 1))
      | (_, Uni _, 0) -> true__
      | (_, Root _, 0) -> true__
      | (name, _, _) -> false__
    let rec checkArgNumber =
      function
      | (ConDec
         (((name)(* checkArgNumber (c, n) = ()
     if constant c expects exactly n explicit arguments,
     raises Error (msg) otherwise
  *)),
          _, i, _, V, L),
         n) -> checkAtomic (name, V, (i + n))
      | (SkoDec (name, _, i, V, L), n) -> checkAtomic (name, V, (i + n))
      | (ConDef (name, _, i, _, V, L, _), n) ->
          checkAtomic (name, V, (i + n))
      | (AbbrevDef (name, _, i, _, V, L), n) ->
          checkAtomic (name, V, (i + n))
    let rec checkFixity =
      function
      | (((name)(* checkFixity (name, cidOpt, n) = ()
     if n = 0 (no requirement on arguments)
     or name is declared and has n exactly explicit arguments,
     raises Error (msg) otherwise
  *)),
         _, 0) -> ()
      | (name, cid, n) ->
          if checkArgNumber ((IntSyn.sgnLookup cid), n)
          then ()
          else
            raise
              (Error
                 (("Constant " ^ name) ^
                    " takes too few explicit arguments for given fixity"))
    type __Qid =
      | Qid of
      (((string)(*
     Names (strings) are associated with constants (cids) in two ways:
     (1) There is an array nameArray mapping constants to print names (string),
     (2) there is a hashtable sgnHashTable mapping identifiers (strings) to constants.

     The mapping from constants to their print names must be maintained
     separately from the global signature, since constants which have
     been shadowed must be marked as such when printing.  Otherwise,
     type checking can generate very strange error messages such as
     "Constant clash: c <> c".

     In the same table we also record the fixity property of constants,
     since it is more a syntactic then semantic property which would
     pollute the lambda-calculus core.

     The mapping from identifers (strings) to constants is used during
     parsing.

     There are global invariants which state the mappings must be
     consistent with each other.
  *)
      (****************************************)(* Constants Names and Name Preferences *)
      (****************************************)) list *
      string) 
    let rec qidToString (Qid (ids, name)) =
      List.foldr (function | (id, s) -> (id ^ ".") ^ s) name ids
    let rec validateQualName =
      function
      | nil -> NONE
      | id::ids as l ->
          if List.exists (function | s -> s = "") l
          then NONE
          else SOME (Qid ((rev ids), id))
    let rec stringToQid name =
      validateQualName (rev (String.fields (function | c -> c = '.') name))
    let rec unqualified = function | Qid (nil, id) -> SOME id | _ -> NONE
    type nonrec namespace =
      (IntSyn.mid StringTree.__Table * IntSyn.cid StringTree.__Table)
    let rec newNamespace () =
      (((StringTree.new__ 0), (StringTree.new__ 0)) : namespace)
    let rec insertConst ((structTable, constTable), cid) =
      let condec = IntSyn.sgnLookup cid in
      let id = IntSyn.conDecName condec in
      match StringTree.insertShadow constTable (id, cid) with
      | NONE -> ()
      | SOME _ ->
          raise
            (Error
               (("Shadowing: A constant named " ^ id) ^
                  "\nhas already been declared in this signature"))
    let rec insertStruct ((structTable, constTable), mid) =
      let strdec = IntSyn.sgnStructLookup mid in
      let id = IntSyn.strDecName strdec in
      match StringTree.insertShadow structTable (id, mid) with
      | NONE -> ()
      | SOME _ ->
          raise
            (Error
               (("Shadowing: A structure named " ^ id) ^
                  "\nhas already been declared in this signature"))
    let rec appConsts f (structTable, constTable) =
      StringTree.app f constTable
    let rec appStructs f (structTable, constTable) =
      StringTree.app f structTable
    let rec fromTo f (from, to__) =
      if from >= to__ then () else (f from; fromTo f ((from + 1), to__))
    let maxCid = Global.maxCid
    let (shadowArray : IntSyn.cid option Array.array) =
      Array.array ((maxCid + 1), NONE)
    let rec shadowClear () = Array.modify (function | _ -> NONE) shadowArray
    let (fixityArray : Fixity.fixity Array.array) =
      Array.array ((maxCid + 1), Fixity.Nonfix)
    let rec fixityClear () =
      Array.modify (function | _ -> Fixity.Nonfix) fixityArray
    let (namePrefArray : (string list * string list) option Array.array) =
      Array.array ((maxCid + 1), NONE)
    let rec namePrefClear () =
      Array.modify (function | _ -> NONE) namePrefArray
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
      Array.modify (function | _ -> NONE) structShadowArray
    let (componentsArray : namespace Array.array) =
      Array.array ((maxMid + 1), dummyNamespace)
    let rec componentsClear () =
      Array.modify (function | _ -> dummyNamespace) componentsArray
    let (topStructNamespace : IntSyn.mid HashTable.__Table) =
      HashTable.new__ 4096
    let topStructInsert = HashTable.insertShadow topStructNamespace
    let topStructLookup = HashTable.lookup topStructNamespace
    let topStructDelete = HashTable.delete topStructNamespace
    let rec topStructClear () = HashTable.clear topStructNamespace
    let rec installConstName
      ((cid)(* installName (name, cid) = ()
       Effect: update mapping from identifiers
               to constants, taking into account shadowing
    *))
      =
      let condec = IntSyn.sgnLookup cid in
      let id = IntSyn.conDecName condec in
      match topInsert (id, cid) with
      | NONE -> ()
      | SOME (_, cid') -> Array.update (shadowArray, cid, (SOME cid'))
    let rec uninstallConst cid =
      let condec = IntSyn.sgnLookup cid in
      let id = IntSyn.conDecName condec in
      (match Array.sub (shadowArray, cid) with
       | NONE -> if (=) (topLookup id) SOME cid then topDelete id else ()
       | SOME cid' ->
           (topInsert (id, cid'); Array.update (shadowArray, cid, NONE)));
      Array.update (fixityArray, cid, Fixity.Nonfix);
      Array.update (namePrefArray, cid, NONE)
    let rec installStructName mid =
      let strdec = IntSyn.sgnStructLookup mid in
      let id = IntSyn.strDecName strdec in
      match topStructInsert (id, mid) with
      | NONE -> ()
      | SOME (_, mid') -> Array.update (structShadowArray, mid, (SOME mid'))
    let rec uninstallStruct mid =
      let strdec = IntSyn.sgnStructLookup mid in
      let id = IntSyn.strDecName strdec in
      (match Array.sub (structShadowArray, mid) with
       | NONE ->
           if (=) (topStructLookup id) SOME mid
           then topStructDelete id
           else ()
       | SOME mid' ->
           (topStructInsert (id, mid');
            Array.update (structShadowArray, mid, NONE)));
      Array.update (componentsArray, mid, dummyNamespace)
    let rec resetFrom (mark, markStruct) =
      let (limit, limitStruct) = IntSyn.sgnSize () in
      let ct f (i, j) = if j < i then () else (f j; ct f (i, (j - 1))) in
      ct uninstallConst (mark, (limit - 1));
      ct uninstallStruct (markStruct, (limitStruct - 1))
    let rec reset
      ((())(* reset () = ()
       Effect: clear name tables related to constants
    *))
      =
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
    let rec findStruct =
      function
      | (structTable, id::[]) -> StringTree.lookup structTable id
      | (structTable, id::ids) ->
          (match StringTree.lookup structTable id with
           | NONE -> NONE
           | SOME mid -> findStruct ((structComps mid), ids))
    let rec findTopStruct =
      function
      | id::[] -> HashTable.lookup topStructNamespace id
      | id::ids ->
          (match HashTable.lookup topStructNamespace id with
           | NONE -> NONE
           | SOME mid -> findStruct ((structComps mid), ids))
    let rec findUndefStruct =
      function
      | (structTable, id::[], ids') ->
          (match StringTree.lookup structTable id with
           | NONE -> SOME (Qid ((rev ids'), id))
           | SOME _ -> NONE)
      | (structTable, id::ids, ids') ->
          (match StringTree.lookup structTable id with
           | NONE -> SOME (Qid ((rev ids'), id))
           | SOME mid ->
               findUndefStruct ((structComps mid), ids, (id :: ids')))
    let rec findTopUndefStruct =
      function
      | id::[] ->
          (match HashTable.lookup topStructNamespace id with
           | NONE -> SOME (Qid (nil, id))
           | SOME _ -> NONE)
      | id::ids ->
          (match HashTable.lookup topStructNamespace id with
           | NONE -> SOME (Qid (nil, id))
           | SOME mid -> findUndefStruct ((structComps mid), ids, [id]))
    let rec constLookupIn =
      function
      | ((structTable, constTable), Qid (nil, id)) ->
          StringTree.lookup constTable id
      | ((structTable, constTable), Qid (ids, id)) ->
          (match findStruct (structTable, ids) with
           | NONE -> NONE
           | SOME mid -> StringTree.lookup (constComps mid) id)
    let rec structLookupIn =
      function
      | ((structTable, constTable), Qid (nil, id)) ->
          StringTree.lookup structTable id
      | ((structTable, constTable), Qid (ids, id)) ->
          (match findStruct (structTable, ids) with
           | NONE -> NONE
           | SOME mid -> StringTree.lookup (structComps mid) id)
    let rec constUndefIn =
      function
      | ((structTable, constTable), Qid (nil, id)) ->
          (match StringTree.lookup constTable id with
           | NONE -> SOME (Qid (nil, id))
           | SOME _ -> NONE)
      | ((structTable, constTable), Qid (ids, id)) ->
          (match findUndefStruct (structTable, ids, nil) with
           | SOME _ as opt -> opt
           | NONE ->
               (match StringTree.lookup
                        (constComps (valOf (findStruct (structTable, ids))))
                        id
                with
                | NONE -> SOME (Qid (ids, id))
                | SOME _ -> NONE))
    let rec structUndefIn =
      function
      | ((structTable, constTable), Qid (nil, id)) ->
          (match StringTree.lookup structTable id with
           | NONE -> SOME (Qid (nil, id))
           | SOME _ -> NONE)
      | ((structTable, constTable), Qid (ids, id)) ->
          (match findUndefStruct (structTable, ids, nil) with
           | SOME _ as opt -> opt
           | NONE ->
               (match StringTree.lookup
                        (structComps (valOf (findStruct (structTable, ids))))
                        id
                with
                | NONE -> SOME (Qid (ids, id))
                | SOME _ -> NONE))
    let rec constLookup =
      function
      | Qid
          (((nil)(* nameLookup (qid) = SOME(cid),  if qid refers to cid in the current context,
                        = NONE,       if there is no such constant
    *)),
           id)
          -> HashTable.lookup topNamespace id
      | Qid (ids, id) ->
          (match findTopStruct ids with
           | NONE -> NONE
           | SOME mid -> StringTree.lookup (constComps mid) id)
    let rec structLookup =
      function
      | Qid (nil, id) -> HashTable.lookup topStructNamespace id
      | Qid (ids, id) ->
          (match findTopStruct ids with
           | NONE -> NONE
           | SOME mid -> StringTree.lookup (structComps mid) id)
    let rec constUndef =
      function
      | Qid (nil, id) ->
          (match HashTable.lookup topNamespace id with
           | NONE -> SOME (Qid (nil, id))
           | SOME _ -> NONE)
      | Qid (ids, id) ->
          (match findTopUndefStruct ids with
           | SOME _ as opt -> opt
           | NONE ->
               (match StringTree.lookup
                        (constComps (valOf (findTopStruct ids))) id
                with
                | NONE -> SOME (Qid (ids, id))
                | SOME _ -> NONE))
    let rec structUndef =
      function
      | Qid (nil, id) ->
          (match HashTable.lookup topStructNamespace id with
           | NONE -> SOME (Qid (nil, id))
           | SOME _ -> NONE)
      | Qid (ids, id) ->
          (match findTopUndefStruct ids with
           | SOME _ as opt -> opt
           | NONE ->
               (match StringTree.lookup
                        (structComps (valOf (findTopStruct ids))) id
                with
                | NONE -> SOME (Qid (ids, id))
                | SOME _ -> NONE))
    let rec structPath (mid, ids) =
      let strdec = IntSyn.sgnStructLookup mid in
      let ids' = (IntSyn.strDecName strdec) :: ids in
      match IntSyn.strDecParent strdec with
      | NONE -> ids'
      | SOME mid' -> structPath (mid', ids')
    let rec maybeShadow =
      function
      | (qid, false__) -> qid
      | (Qid (nil, id), true__) -> Qid (nil, (("%" ^ id) ^ "%"))
      | (Qid (id::ids, name), true__) ->
          Qid (((("%" ^ id) ^ "%") :: ids), name)
    let rec conDecQid condec =
      let id = IntSyn.conDecName condec in
      match IntSyn.conDecParent condec with
      | NONE -> Qid (nil, id)
      | SOME mid -> Qid ((structPath (mid, nil)), id)
    let rec constQid
      ((cid)(* constQid (cid) = qid,
       where `qid' is the print name of cid
    *))
      =
      let condec = IntSyn.sgnLookup cid in
      let qid = conDecQid condec in
      maybeShadow (qid, ((<>) (constLookup qid) SOME cid))
    let rec structQid mid =
      let strdec = IntSyn.sgnStructLookup mid in
      let id = IntSyn.strDecName strdec in
      let qid =
        match IntSyn.strDecParent strdec with
        | NONE -> Qid (nil, id)
        | SOME mid -> Qid ((structPath (mid, nil)), id) in
      maybeShadow (qid, ((<>) (structLookup qid) SOME mid))
    let rec installFixity
      (((cid)(* installFixity (cid, fixity) = ()
       Effect: install fixity for constant cid,
               possibly print declaration depending on chatter level
    *)),
       fixity)
      =
      let name = qidToString (constQid cid) in
      checkFixity (name, cid, (argNumber fixity));
      Array.update (fixityArray, cid, fixity)
    let rec getFixity
      ((cid)(* getFixity (cid) = fixity
       fixity defaults to Fixity.Nonfix, if nothing has been declared
    *))
      = Array.sub (fixityArray, cid)
    let rec fixityLookup
      ((qid)(* fixityLookup qid = fixity
       where fixity is the fixity associated with constant named qid,
       defaults to Fixity.Nonfix if qid or fixity are undeclared
    *))
      =
      match constLookup qid with
      | NONE -> Fixity.Nonfix
      | SOME cid -> getFixity cid
    let rec installNamePref'
      (((cid)(* Name Preferences *)(* ePref is the name preference for existential variables of given type *)
       (* uPref is the name preference for universal variables of given type *)
       (* installNamePref' (cid, (ePref, uPref)) see installNamePref *)),
       (ePref, uPref))
      =
      let L = IntSyn.constUni cid in
      let _ =
        match L with
        | IntSyn.Type ->
            raise
              (Error
                 ((((^) "Object constant " qidToString (constQid cid)) ^
                     " cannot be given name preference\n")
                    ^
                    "Name preferences can only be established for type families"))
        | IntSyn.Kind -> () in
      Array.update (namePrefArray, cid, (SOME (ePref, uPref)))
    let rec installNamePref =
      function
      | (((cid)(* installNamePref (cid, (ePref, uPrefOpt)) = ()
       Effect: install name preference for type family cid
       raise Error if cid does not refer to a type family
    *)),
         (ePref, nil)) ->
          installNamePref'
            (cid, (ePref, [String.map Char.toLower (hd ePref)]))
      | (cid, (ePref, uPref)) -> installNamePref' (cid, (ePref, uPref))
    let rec getNamePref cid = Array.sub (namePrefArray, cid)
    let rec installComponents (mid, namespace) =
      Array.update (componentsArray, mid, namespace)
    let rec getComponents mid = Array.sub (componentsArray, mid)
    type __Extent =
      | Local 
      | Global (* local names are more easily re-used: they don't increment the
       counter associated with a name
    *)
    type __Role =
      | Exist 
      | Univ of __Extent 
    let rec extent = function | Exist -> Global | Univ ext -> ext
    let rec namePrefOf'' =
      function
      | (Exist, NONE) -> "X"
      | (Univ _, NONE) -> "x"
      | (Exist, SOME (ePref, uPref)) -> hd ePref
      | (Univ _, SOME (ePref, uPref)) -> hd uPref
    let rec namePrefOf' =
      function
      | (Exist, NONE) -> "X"
      | (Univ _, NONE) -> "x"
      | (role, SOME (Const cid)) ->
          namePrefOf'' (role, (Array.sub (namePrefArray, cid)))
      | (role, SOME (Def cid)) ->
          namePrefOf'' (role, (Array.sub (namePrefArray, cid)))
      | (((role)(* the following only needed because reconstruction replaces
           undetermined types with FVars *)),
         SOME (FVar _)) -> namePrefOf'' (role, NONE)
      | (role, SOME (NSDef cid)) ->
          namePrefOf'' (role, (Array.sub (namePrefArray, cid)))
    let rec namePrefOf
      (((role)(* namePrefOf (role, V) = name
       where name is the preferred base name for a variable with type V

       V should be a type, but the code is robust, returning the default "X" or "x"
    *)),
       V)
      = namePrefOf' (role, (IntSyn.targetHeadOpt V))
    type varEntry =
      | EVAR of IntSyn.__Exp 
    let (varTable : varEntry StringTree.__Table) = StringTree.new__ 0
    let varInsert = StringTree.insert varTable
    let varLookup = StringTree.lookup varTable
    let rec varClear () = StringTree.clear varTable
    let (varContext : IntSyn.dctx ref) = ref IntSyn.Null
    let (evarList : (IntSyn.__Exp * string) list ref) = ref nil
    let rec evarReset () = evarList := nil
    let rec evarLookup (X) =
      let evlk =
        function
        | (r, nil) -> NONE
        | (r, (EVar (r', _, _, _), name)::l) ->
            if r = r' then SOME name else evlk (r, l)
        | (r, (AVar r', name)::l) ->
            if r = r' then SOME name else evlk (r, l) in
      match X with
      | EVar (r, _, _, _) -> evlk (r, (!evarList))
      | AVar r -> evlk (r, (!evarList))
    let rec evarInsert entry = (evarList := entry) :: (!evarList)
    let rec namedEVars () = !evarList
    let rec evarCnstr' =
      function
      | (nil, acc) -> acc
      | (((EVar (ref (NONE), _, _, cnstrs), name) as Xn)::l, acc) ->
          (match Constraints.simplify (!cnstrs) with
           | nil -> evarCnstr' (l, acc)
           | _::_ -> evarCnstr' (l, (Xn :: acc)))
      | (_::l, acc) -> evarCnstr' (l, acc)
    let rec evarCnstr () = evarCnstr' ((!evarList), nil)
    let (indexTable : int StringTree.__Table) = StringTree.new__ 0
    let indexInsert = StringTree.insert indexTable
    let indexLookup = StringTree.lookup indexTable
    let rec indexClear () = StringTree.clear indexTable
    let rec nextIndex' =
      function
      | (name, NONE) -> (indexInsert (name, 1); 1)
      | (name, SOME i) -> (indexInsert (name, (i + 1)); i + 1)
    let rec nextIndex name = nextIndex' (name, (indexLookup name))
    let rec varReset
      ((g)(* local ... *)(******************)(* Variable Names *)
      (******************)(*
     Picking variable names is tricky, since we need to avoid capturing.
     This is entirely a matter of parsing and printing, since the
     internal representation relies on deBruijn indices and explicit
     substitutions.

     During parsing, a name is resolved as follows:
       lower case id => bound variable, constant, error
       upper case id => bound variable, constant, free variable
     where a free variable could become either an FVar
     (in constant declarations) or an EVar (in queries).

     Names are either given by the declaration or query itself, or
     assigned as late as possible.  For example, EVars which are never
     printed are never assigned a name.

     This may be a problem for contexts: if a name is not assigned when
     a declaration is entered into the context, terms in this context
     may not be printable.  Function decName below guarantees that new
     names are assigned to variables added to a context.
  *)
      (*
     There are three data structures:
     1. varTable mapping names (strings) to EVars and FVar types
          -- Actually, FVar types now handled entirely in recon-term.fun
          -- where there needs to be more info for approximate types.
          -- I don't see why EVar/BVar names should be generated apart from
          -- FVar names anyway, since the latter are printed with "`".
          -- -kw
     2. evarList mapping EVars to names (string)
     3. indexTable mapping base names B to integer suffixes to generate
        new names B1, B2, ...

     These are reset for each declaration or query, since
     EVars and FVars are local.
  *)
      (* X *)(* remove this datatype? -kw *)(* varTable mapping identifiers (strings) to EVars and FVars *)
      (* A hashtable is too inefficient, since it is cleared too often; *)
      (* so we use a red/black trees instead *)(* initial size hint *)
      (* what is this for?  -kw *)(* evarList mapping EVars to names *)
      (* names are assigned only when EVars are parsed or printed *)
      (* the mapping must be implemented as an association list *)
      (* since EVars are identified by reference *)(* an alternative becomes possible if time stamps are introduced *)
      (* Since constraints are not printable at present, we only *)
      (* return a list of names of EVars that have constraints on them *)
      (* Note that EVars which don't have names, will not be considered! *)
      (* The indexTable maps a name to the last integer suffix used for it.
       The resulting identifer is not guaranteed to be new, and must be
       checked against the names of constants, FVars, EVars, and BVars.
    *)
      (* nextIndex (name) = i
       where i is the next available integer suffix for name,
       starting at 1.
       Effect: initialize or increment the indexTable entry for name
    *)
      (* varReset () = ()
       Effect: clear variable tables
       This must be called for each declaration or query
    *))
      = varClear (); evarReset (); indexClear (); varContext := g
    let rec addEVar
      (((X)(* addEVar (X, name) = ()
       effect: adds (X, name) to varTable and evarList
       assumes name not already used *)),
       name)
      = evarInsert (X, name); varInsert (name, (EVAR X))
    let rec getEVarOpt name =
      match varLookup name with | NONE -> NONE | SOME (EVAR (X)) -> SOME X
    let rec varDefined
      ((name)(* varDefined (name) = true iff `name' refers to a free variable, *)
      (* which could be an EVar for constant declarations or FVar for queries *))
      = match varLookup name with | NONE -> false__ | SOME _ -> true__
    let rec conDefined
      ((name)(* conDefined (name) = true iff `name' refers to a constant *))
      =
      match constLookup (Qid (nil, name)) with
      | NONE -> false__
      | SOME _ -> true__
    let rec ctxDefined
      (((g)(* ctxDefined (g, name) = true iff `name' is declared in context g *)),
       name)
      =
      let cdfd =
        function
        | IntSyn.Null -> false__
        | Decl (g', Dec (SOME name', _)) -> (name = name') || (cdfd g')
        | Decl (g', BDec (SOME name', _)) -> (name = name') || (cdfd g')
        | Decl (g', NDec (SOME name')) -> (name = name') || (cdfd g')
        | Decl (g', _) -> cdfd g' in
      cdfd g
    let rec tryNextName
      (((g)(* tryNextName (g, base) = baseN
       where N is the next suffix such that baseN is unused in
       g, as a variable, or as a constant.
    *)),
       base)
      =
      let name = (^) base Int.toString (nextIndex base) in
      if (varDefined name) || ((conDefined name) || (ctxDefined (g, name)))
      then tryNextName (g, base)
      else name
    let rec findNameLocal (g, base, i) =
      let name = base ^ (if i = 0 then "" else Int.toString i) in
      if (varDefined name) || ((conDefined name) || (ctxDefined (g, name)))
      then findNameLocal (g, base, (i + 1))
      else name
    let rec findName =
      function
      | (g, base, Local) -> findNameLocal (g, base, 0)
      | (g, base, Global) -> tryNextName (g, base)
    let takeNonDigits = Substring.takel (not o Char.isDigit)
    let rec baseOf
      ((name)(* baseOf (name) = name',
       where name' is the prefix of name not containing a digit
    *))
      = Substring.string (takeNonDigits (Compat.Substring.full name))
    let rec newEVarName =
      function
      | (((g)(* newEvarName (g, X) = name
       where name is the next unused name appropriate for X,
       based on the name preference declaration for A if X:A
    *)),
         (EVar (r, _, V, Cnstr) as X)) ->
          let ((name)(* use name preferences below *)) =
            tryNextName (g, (namePrefOf (Exist, V))) in
          (evarInsert (X, name); name)
      | (g, (AVar r as X)) ->
          let ((name)(* use name preferences below *)) =
            tryNextName (g, (namePrefOf' (Exist, NONE))) in
          (evarInsert (X, name); name)
    let rec evarName
      (((g)(* evarName (g, X) = name
       where `name' is the print name X.
       If no name has been assigned yet, assign a new one.
       Effect: if a name is assigned, update varTable
    *)),
       X)
      =
      match evarLookup X with
      | NONE ->
          let name = newEVarName (g, X) in (varInsert (name, (EVAR X)); name)
      | SOME name -> name
    let rec bvarName
      (((g)(* bvarName (g, k) = name
       where `name' is the print name for variable with deBruijn index k.
       Invariant: 1 <= k <= |g|
                  G_k must assign a name
       If no name has been assigned, the context might be built the wrong
       way---check decName below instread of IntSyn.Dec
    *)),
       k)
      =
      match IntSyn.ctxLookup (g, k) with
      | Dec (SOME name, _) -> name
      | ADec (SOME name, _) -> name
      | NDec (SOME name) -> name
      | ADec (None, _) -> (("ADec_")
          (* Evars can depend on NDec :-( *))
      | Dec (None, _) -> "Dec_"
      | _ -> raise Unprintable
    let rec decName' arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (((role)(* decName' role (g, D) = g,D'
       where D' is a possible renaming of the declaration D
       in order to avoid shadowing other variables or constants
       If D does not assign a name, this picks, based on the name
       preference declaration.
    *)),
         (g, Dec (NONE, V))) ->
          let name = findName (g, (namePrefOf (role, V)), (extent role)) in
          IntSyn.Dec ((SOME name), V)
      | (role, (g, (Dec (SOME name, V) as D))) ->
          if
            (varDefined name) ||
              ((conDefined name) || (ctxDefined (g, name)))
          then IntSyn.Dec ((SOME (tryNextName (g, (baseOf name)))), V)
          else D
      | (role, (g, (BDec (NONE, ((cid, t) as b)) as D))) ->
          let ((name)(* use #l as base name preference for label l *))
            =
            findName
              (g, ((^) "#" IntSyn.conDecName (IntSyn.sgnLookup cid)), Local) in
          IntSyn.BDec ((SOME name), b)
      | (role, (g, (BDec (SOME name, ((cid, t) as b)) as D))) ->
          if
            (varDefined name) ||
              ((conDefined name) || (ctxDefined (g, name)))
          then IntSyn.BDec ((SOME (tryNextName (g, (baseOf name)))), b)
          else D
      | (role, (g, ADec (NONE, d))) ->
          let name = findName (g, (namePrefOf' (role, NONE)), (extent role)) in
          IntSyn.ADec ((SOME name), d)
      | (role, (g, (ADec (SOME name, d) as D))) ->
          if
            (varDefined name) ||
              ((conDefined name) || (ctxDefined (g, name)))
          then IntSyn.ADec ((SOME (tryNextName (g, (baseOf name)))), d)
          else ((D)(*      IntSyn.ADec(SOME(name), d) *))
      | (role, (g, (NDec (NONE) as D))) ->
          let name = findName (g, "@x", Local) in
          let _ = print name in IntSyn.NDec (SOME name)
      | (role, (g, (NDec (SOME name) as D))) ->
          if
            (varDefined name) ||
              ((conDefined name) || (ctxDefined (g, name)))
          then IntSyn.NDec (SOME (tryNextName (g, (baseOf name))))
          else D
    let decName = decName' Exist
    let decEName = decName' Exist
    let decUName = decName' (Univ Global)
    let decLUName = decName' (Univ Local)
    let rec ctxName =
      function
      | ((IntSyn.Null)(* ctxName g = g'

        Invariant:
        |- g == g' ctx
        where some Declaration in g' have been named/renamed
    *))
          -> IntSyn.Null
      | Decl (g, D) ->
          let g' = ctxName g in IntSyn.Decl (g', (decName (g', D)))
    let rec ctxLUName =
      function
      | ((IntSyn.Null)(* ctxLUName g = g'
       like ctxName, but names assigned are local universal names.
    *))
          -> IntSyn.Null
      | Decl (g, D) ->
          let g' = ctxLUName g in IntSyn.Decl (g', (decLUName (g', D)))
    let rec pisEName' =
      function
      | (((g)(* pisEName' (g, i, V) = V'
       Assigns names to dependent Pi prefix of V with i implicit abstractions
       Used for implicit EVar in constant declarations after abstraction.
    *)),
         0, V) -> V
      | (g, i, Pi ((D, IntSyn.Maybe), V)) ->
          let ((D')(* i > 0 *)) = decEName (g, D) in
          IntSyn.Pi
            ((D', IntSyn.Maybe),
              (pisEName' ((IntSyn.Decl (g, D')), (i - 1), V)))
    let rec pisEName
      (((i)(* | pisEName' (g, i, V) = V *)), V) =
      pisEName' (IntSyn.Null, i, V)
    let rec defEName' =
      function
      | (((g)(* defEName' (g, i, (U,V)) = (U',V')
       Invariant: g |- U : V  and g |- U' : V' since U == U' and V == V'.
       Assigns name to dependent Pi prefix of V and corresponding lam prefix of U
       with i implicit abstractions
       Used for implicit EVar in constant definitions after abstraction.
    *)),
         0, UV) -> UV
      | (g, i, (Lam (D, U), Pi ((_, ((P)(* = D *))), V))) ->
          let ((D')(* i > 0 *)) = decEName (g, D) in
          let (U', V') = defEName' ((IntSyn.Decl (g, D')), (i - 1), (U, V)) in
          ((IntSyn.Lam (D', U')), (IntSyn.Pi ((D', P), V')))
    let rec defEName
      (((imp)(* | defEName' (g, i, (U, V)) = (U, V) *)), UV)
      = defEName' (IntSyn.Null, imp, UV)
    let rec nameConDec' =
      function
      | ConDec (name, parent, imp, status, V, L) ->
          IntSyn.ConDec (name, parent, imp, status, (pisEName (imp, V)), L)
      | ConDef (name, parent, imp, U, V, L, Anc) ->
          let (U', V') = defEName (imp, (U, V)) in
          IntSyn.ConDef (name, parent, imp, U', V', L, Anc)
      | AbbrevDef (name, parent, imp, U, V, L) ->
          let (U', V') = defEName (imp, (U, V)) in
          IntSyn.AbbrevDef (name, parent, imp, U', V', L)
      | skodec -> skodec
    let rec nameConDec
      ((conDec)(* fix ??? *)(* Assigns names to variables in a constant declaration *)
      (* The varReset (); is necessary so that explicitly named variables keep their name *))
      =
      varReset IntSyn.Null;
      nameConDec' ((conDec)
        (* declaration is always closed *))
    let rec skonstName name = tryNextName (IntSyn.Null, name)
    let namedEVars = namedEVars
    let evarCnstr = evarCnstr
  end ;;




module Names =
  (Make_Names)(struct
                 module Global = Global
                 module Constraints =
                   ((Constraints)(*! structure IntSyn' = IntSyn !*))
                 module HashTable = StringHashTable
                 module StringTree = StringRedBlackTree
               end);;
