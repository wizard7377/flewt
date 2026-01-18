
(* Tabled Syntax *)
(* Author: Brigitte Pientka *)
module type TABLEDSYN  =
  sig
    (*! structure IntSyn : INTSYN !*)
    exception Error of string 
    val reset : unit -> unit
    val installTabled : IntSyn.cid -> unit
    val installKeepTable : IntSyn.cid -> unit
    val tabledLookup : IntSyn.cid -> bool
    val keepTable : IntSyn.cid -> bool
  end;;




(* Tabled Syntax *)
(* Author: Brigitte Pientka *)
module TabledSyn(TabledSyn:sig
                             (*! structure IntSyn' : INTSYN !*)
                             module Names : NAMES
                             module Table : TABLE
                             (*! sharing Names.IntSyn = IntSyn' !*)
                             module Index : INDEX
                           end) : TABLEDSYN =
  struct
    (*! sharing Index.IntSyn = IntSyn' !*)
    (*! structure IntSyn = IntSyn' !*)
    exception Error of string 
    type __Tabled =
      | Yes [@sml.renamed "yes"]
      | No [@sml.renamed "no"]
    (*  datatype ModeSpine = Mnil | Mapp of Marg * ModeSpine
  and  Marg = Marg of Mode * string option
  *)
    module I = IntSyn
    let (tabledSignature : bool Table.__Table) = Table.new__ 0
    let rec reset () = Table.clear tabledSignature
    let rec installTabled a = Table.insert tabledSignature (a, false)
    let rec installKeepTable a =
      Table.insertShadow tabledSignature (a, true__); ()
    let rec tabledLookup a =
      match Table.lookup tabledSignature a with
      | None -> false
      | Some _ -> true__
    let rec keepTable a =
      match Table.lookup tabledSignature a with
      | None -> false
      | Some true__ -> true__
      | Some false -> false
    (* reset () = ()

       Effect: Resets tabled array
    *)
    (* installTabled (a, tabled) = ()

       Effect: the tabled is stored with the type family a
    *)
    (* installTabled (a, tabled) = ()

       Effect: the tabled is stored with the type family a
    *)
    (* Table.delete tabledSignature a; *)
    (* tablingLookup a = bool

       Looks up whether the predicat a is tabled

    *)
    (* keepTable a = bool

       if we should keep the table for this predicate a
        then returns true
          otherwise false
    *)
    let reset = reset
    let installTabled = installTabled
    let installKeepTable = installKeepTable
    let tabledLookup = tabledLookup
    let keepTable = keepTable
  end ;;
