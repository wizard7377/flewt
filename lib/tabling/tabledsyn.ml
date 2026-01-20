
module type TABLEDSYN  =
  sig
    exception Error of string 
    val reset : unit -> unit
    val installTabled : IntSyn.cid -> unit
    val installKeepTable : IntSyn.cid -> unit
    val tabledLookup : IntSyn.cid -> bool
    val keepTable : IntSyn.cid -> bool
  end;;




module TabledSyn(TabledSyn:sig
                             module Names : NAMES
                             module Table : TABLE
                             module Index : INDEX
                           end) : TABLEDSYN =
  struct
    exception Error of string 
    type __Tabled =
      | yes [@sml.renamed "yes"][@sml.renamed "yes"]
      | no [@sml.renamed "no"][@sml.renamed "no"]
    module I = IntSyn
    let (tabledSignature : bool Table.__Table) = Table.new__ 0
    let rec reset () = Table.clear tabledSignature
    let rec installTabled a = Table.insert tabledSignature (a, false__)
    let rec installKeepTable a =
      ((Table.insertShadow tabledSignature (a, true__); ())
      (* Table.delete tabledSignature a; *))
    let rec tabledLookup a =
      match Table.lookup tabledSignature a with
      | NONE -> false__
      | Some _ -> true__
    let rec keepTable a =
      match Table.lookup tabledSignature a with
      | NONE -> false__
      | Some true__ -> true__
      | Some false__ -> false__
    let reset = reset
    let installTabled = installTabled
    let installKeepTable = installKeepTable
    let tabledLookup = tabledLookup
    let keepTable = keepTable
  end ;;
