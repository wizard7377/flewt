module type TABLEDSYN  =
  sig
    exception Error of string 
    val reset : unit -> unit
    val installTabled : IntSyn.cid -> unit
    val installKeepTable : IntSyn.cid -> unit
    val tabledLookup : IntSyn.cid -> bool
    val keepTable : IntSyn.cid -> bool
  end


module TabledSyn(TabledSyn:sig
                             module Names : NAMES
                             module Table : TABLE
                             module Index : INDEX
                           end) : TABLEDSYN =
  struct
    exception Error of string 
    type tabled_ =
      | yes [@sml.renamed "yes"][@sml.renamed "yes"]
      | no [@sml.renamed "no"][@sml.renamed "no"]
    module I = IntSyn
    let (tabledSignature : bool Table.table_) = Table.new_ 0
    let rec reset () = Table.clear tabledSignature
    let rec installTabled a = Table.insert tabledSignature (a, false)
    let rec installKeepTable a =
      ((begin Table.insertShadow tabledSignature (a, true); () end)
      (* Table.delete tabledSignature a; *))
    let rec tabledLookup a =
      begin match Table.lookup tabledSignature a with
      | None -> false
      | Some _ -> true end
  let rec keepTable a =
    begin match Table.lookup tabledSignature a with
    | None -> false
    | Some true -> true
    | Some false -> false end
let reset = reset
let installTabled = installTabled
let installKeepTable = installKeepTable
let tabledLookup = tabledLookup
let keepTable = keepTable end
