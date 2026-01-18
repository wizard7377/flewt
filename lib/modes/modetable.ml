
(* Mode Table *)
(* Author: Frank Pfenning *)
module type MODETABLE  =
  sig
    exception Error of string 
    val reset : unit -> unit
    (* single mode installation and lookup *)
    val installMode : (IntSyn.cid * ModeSyn.__ModeSpine) -> unit
    val modeLookup : IntSyn.cid -> ModeSyn.__ModeSpine option
    val uninstallMode : IntSyn.cid -> bool
    (* true: was declared, false: not *)
    (* multiple mode installation and lookup *)
    val installMmode : (IntSyn.cid * ModeSyn.__ModeSpine) -> unit
    val mmodeLookup : IntSyn.cid -> ModeSyn.__ModeSpine list
  end;;




(* Mode Table *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning, Roberto Virga *)
module ModeTable(ModeTable:sig
                             (*! structure IntSyn' : INTSYN !*)
                             (* structure Names : NAMES *)
                             (*! sharing Names.IntSyn = IntSyn' !*)
                             module Table : TABLE
                           end) : MODETABLE =
  struct
    (* structure Index : INDEX *)
    (*! sharing Index.IntSyn = IntSyn' !*)
    (*! structure IntSyn = IntSyn' !*)
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
    let rec installMode (a, mS) = Table.insert modeSignature (a, [mS])
    let rec uninstallMode a =
      match modeLookup a with
      | None -> false__
      | Some _ -> (Table.delete modeSignature a; true__)
    let rec installMmode (a, mS) =
      let mSs = mmodeLookup a in Table.insert modeSignature (a, (mS :: mSs))
    (* reset () = ()

       Effect: Resets mode array
    *)
    (* modeLookup a = mSOpt

       Looks up the mode of a in the mode array (if they are multiple, returns the last one
       inserted.
    *)
    (* mmodeLookup a = mSs

       Looks up the modes of a in the mode array.
    *)
    (* installMode (a, mS) = ()

       Effect: the ModeSpine mS is stored with the type family a; if there were previous
               modes stored with a, they are replaced by mS
    *)
    (* uninstallMode a = true iff a was declared in mode table
       Effect: the mode stored with a is removed
    *)
    (* installMmode (a, mS) = ()

       Effect: the ModeSpine mS is stored with the type family a; if there were previous
               models stored with a, the new mode mS is added to them.
    *)
    let reset = reset
    let installMode = installMode
    let modeLookup = modeLookup
    let uninstallMode = uninstallMode
    let installMmode = installMmode
    let mmodeLookup = mmodeLookup
  end ;;
