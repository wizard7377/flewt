
module type FUNNAMES  =
  sig
    exception Error of string 
    val reset : unit -> unit
    val installName : string -> FunSyn.lemma -> unit
    val nameLookup : string -> FunSyn.lemma option
    val constName : FunSyn.lemma -> string
  end;;




module FunNames(FunNames:sig module Global : GLOBAL module HashTable : TABLE
                         end) : FUNNAMES =
  struct
    exception Error of string 
    type nameInfo =
      | NameInfo of string 
    let maxCid = Global.maxCid
    let nameArray =
      (Array.array ((maxCid + 1), (NameInfo "")) : nameInfo Array.array)
    let (sgnHashTable : IntSyn.cid HashTable.__Table) = HashTable.new__ 4096
    let hashInsert = HashTable.insertShadow sgnHashTable
    let hashLookup = HashTable.lookup sgnHashTable
    let rec hashClear () = HashTable.clear sgnHashTable
    let rec reset () = hashClear ()
    let rec override cid (NameInfo name) =
      Array.update (nameArray, cid, (NameInfo (("%" ^ name) ^ "%")))(* should shadowed identifiers keep their fixity? *)
    let rec shadow =
      function
      | None -> ()
      | Some (_, cid) -> override (cid, (Array.sub (nameArray, cid)))
    let rec installName name lemma =
      let shadowed = hashInsert (name, lemma) in
      ((Array.update (nameArray, lemma, (NameInfo name)); shadow shadowed)
        (* returns optional shadowed entry *))
    let rec nameLookup name = hashLookup name
    let rec constName cid =
      match Array.sub (nameArray, cid) with | NameInfo name -> name
  end ;;
