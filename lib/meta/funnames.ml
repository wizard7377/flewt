
module type FUNNAMES  =
  sig
    exception Error of
      ((string)(*! structure FunSyn : FUNSYN !*)(* Author: Carsten Schuermann *)
      (* Names of Constants and Variables *)) 
    val reset :
      unit -> ((unit)(* Constant names and fixities *))
    val installName : (string * FunSyn.lemma) -> unit
    val nameLookup : string -> FunSyn.lemma option
    val constName : FunSyn.lemma -> string
  end;;




module FunNames(FunNames:sig
                           module Global : GLOBAL
                           module HashTable :
                           ((TABLE)(* Names of Constants and Variables *)
                           (* Author: Carsten Schuermann *)
                           (*! structure FunSyn' : FUNSYN !*))
                         end) : FUNNAMES =
  struct
    exception Error of
      ((string)(*! structure FunSyn = FunSyn' !*)) 
    type nameInfo =
      | NameInfo of
      ((string)(* nameInfo carries the print name and fixity for a constant *)
      (*
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
      (****************************************)) 
    let maxCid = Global.maxCid
    let nameArray =
      (Array.array ((maxCid + 1), (NameInfo "")) : nameInfo Array.array)
    let (sgnHashTable : IntSyn.cid HashTable.__Table) = HashTable.new__ 4096
    let hashInsert = HashTable.insertShadow sgnHashTable
    let hashLookup = HashTable.lookup sgnHashTable
    let rec hashClear () = HashTable.clear sgnHashTable
    let rec reset
      ((())(* nameArray maps constants to print names and fixity *)
      (* sgnHashTable maps identifiers (strings) to constants (cids) *)
      (* returns optional shadowed entry *)(* returns optional cid *)
      (* reset () = ()
       Effect: clear name tables related to constants

       nameArray does not need to be reset, since it is reset individually
       for every constant as it is declared
    *))
      = hashClear ()
    let rec override
      (((cid)(* override (cid, nameInfo) = ()
       Effect: mark cid as shadowed --- it will henceforth print as %name%
    *)),
       NameInfo name)
      =
      Array.update
        (((nameArray)
          (* should shadowed identifiers keep their fixity? *)), cid,
          (NameInfo (("%" ^ name) ^ "%")))
    let rec shadow =
      function
      | NONE -> ()
      | SOME (_, cid) -> override (cid, (Array.sub (nameArray, cid)))
    let rec installName
      (((name)(* installName (name, cid) = ()
       Effect: update mappings from constants to print names and identifiers
               to constants, taking into account shadowing
    *)),
       lemma)
      =
      let shadowed = hashInsert (name, lemma) in
      Array.update (nameArray, lemma, (NameInfo name));
      shadow ((shadowed)
        (* returns optional shadowed entry *))
    let rec nameLookup
      ((name)(* nameLookup (name) = SOME(cid),  if cid has name and is not shadowed,
                         = NONE,   if there is no such constant
    *))
      = hashLookup name
    let rec constName
      ((cid)(* constName (cid) = name,
       where `name' is the print name of cid
    *))
      = match Array.sub (nameArray, cid) with | NameInfo name -> name
  end ;;
