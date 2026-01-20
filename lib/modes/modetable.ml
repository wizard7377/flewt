
module type MODETABLE  =
  sig
    exception Error of string 
    val reset : unit -> unit
    val installMode : IntSyn.cid -> ModeSyn.__ModeSpine -> unit
    val modeLookup : IntSyn.cid -> ModeSyn.__ModeSpine option
    val uninstallMode : IntSyn.cid -> bool
    val installMmode : IntSyn.cid -> ModeSyn.__ModeSpine -> unit
    val mmodeLookup : IntSyn.cid -> ModeSyn.__ModeSpine list
  end;;




module ModeTable(ModeTable:sig module Table : TABLE end) : MODETABLE =
  struct
    exception Error of string 
    module I = IntSyn
    module M = ModeSyn
    let (modeSignature : M.__ModeSpine list Table.__Table) = Table.new__ 0
    let rec reset () = Table.clear modeSignature
    let rec modeLookup a =
      match Table.lookup modeSignature a with
      | Some (mS::_) -> Some mS
      | None -> None
    let rec mmodeLookup a =
      match Table.lookup modeSignature a with | Some mSs -> mSs | None -> nil
    let rec installMode a mS = Table.insert modeSignature (a, [mS])
    let rec uninstallMode a =
      match modeLookup a with
      | None -> false
      | Some _ -> (Table.delete modeSignature a; true)
    let rec installMmode a mS =
      let mSs = mmodeLookup a in Table.insert modeSignature (a, (mS :: mSs))
    let reset = reset
    let installMode = installMode
    let modeLookup = modeLookup
    let uninstallMode = uninstallMode
    let installMmode = installMmode
    let mmodeLookup = mmodeLookup
  end ;;
