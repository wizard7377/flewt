
module type TABLEDSYN  =
  sig
    exception Error of
      ((string)(*! structure IntSyn : INTSYN !*)(* Author: Brigitte Pientka *)
      (* Tabled Syntax *)) 
    val reset : unit -> unit
    val installTabled : IntSyn.cid -> unit
    val installKeepTable : IntSyn.cid -> unit
    val tabledLookup : IntSyn.cid -> bool
    val keepTable : IntSyn.cid -> bool
  end;;




module TabledSyn(TabledSyn:sig
                             module Names : NAMES
                             module Table : TABLE
                             module Index :
                             ((INDEX)(* Tabled Syntax *)
                             (* Author: Brigitte Pientka *)
                             (*! structure IntSyn' : INTSYN !*)(*! sharing Names.IntSyn = IntSyn' !*))
                           end) : TABLEDSYN =
  struct
    exception Error of
      ((string)(*! structure IntSyn = IntSyn' !*)(*! sharing Index.IntSyn = IntSyn' !*))
      
    type __Tabled =
      | yes [@sml.renamed "yes"][@sml.renamed "yes"]
      | no [@sml.renamed "no"][@sml.renamed "no"]
    module I = IntSyn
    let (tabledSignature : bool Table.__Table) = Table.new__ 0
    let rec reset () = Table.clear tabledSignature
    let rec installTabled a = Table.insert tabledSignature (a, false__)
    let rec installKeepTable a =
      Table.insertShadow tabledSignature (a, true__); ()
    let rec tabledLookup a =
      match Table.lookup tabledSignature a with
      | NONE -> false__
      | SOME _ -> true__
    let rec keepTable a =
      match Table.lookup tabledSignature a with
      | NONE -> false__
      | SOME true__ -> true__
      | SOME false__ -> false__
    let ((reset)(*  datatype ModeSpine = Mnil | Mapp of Marg * ModeSpine
  and  Marg = Marg of Mode * string option
  *)
      (* reset () = ()

       Effect: Resets tabled array
    *)
      (* installTabled (a, tabled) = ()

       Effect: the tabled is stored with the type family a
    *)
      (* installTabled (a, tabled) = ()

       Effect: the tabled is stored with the type family a
    *)
      (* Table.delete tabledSignature a; *)(* tablingLookup a = bool

       Looks up whether the predicat a is tabled

    *)
      (* keepTable a = bool

       if we should keep the table for this predicate a
        then returns true
          otherwise false
    *))
      = reset
    let installTabled = installTabled
    let installKeepTable = installKeepTable
    let tabledLookup = tabledLookup
    let keepTable = keepTable
  end ;;
