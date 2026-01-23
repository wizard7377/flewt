module type MODETABLE  =
  sig
    exception Error of string 
    val reset : unit -> unit
    val installMode : (IntSyn.cid * ModeSyn.modeSpine_) -> unit
    val modeLookup : IntSyn.cid -> ModeSyn.modeSpine_ option
    val uninstallMode : IntSyn.cid -> bool
    val installMmode : (IntSyn.cid * ModeSyn.modeSpine_) -> unit
    val mmodeLookup : IntSyn.cid -> ModeSyn.modeSpine_ list
  end


module ModeTable(ModeTable:sig module Table : TABLE end) : MODETABLE =
  struct
    exception Error of string 
    module I = IntSyn
    module M = ModeSyn
    let (modeSignature : M.modeSpine_ list Table.table_) = Table.new_ 0
    let rec reset () = Table.clear modeSignature
    let rec modeLookup a =
      begin match Table.lookup modeSignature a with
      | Some (mS::_) -> Some mS
      | None -> None end
    let rec mmodeLookup a =
      begin match Table.lookup modeSignature a with
      | Some mSs -> mSs
      | None -> [] end
  let rec installMode (a, mS) = Table.insert modeSignature (a, [mS])
  let rec uninstallMode a =
    begin match modeLookup a with
    | None -> false
    | Some _ -> (begin Table.delete modeSignature a; true end) end
let rec installMmode (a, mS) =
  let mSs = mmodeLookup a in Table.insert modeSignature (a, (mS :: mSs))
let reset = reset
let installMode = installMode
let modeLookup = modeLookup
let uninstallMode = uninstallMode
let installMmode = installMmode
let mmodeLookup = mmodeLookup end
