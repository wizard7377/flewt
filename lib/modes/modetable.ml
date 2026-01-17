
module type MODETABLE  =
  sig
    exception Error of
      ((string)(* Author: Frank Pfenning *)(* Mode Table *))
      
    val reset : unit -> unit
    val installMode :
      (IntSyn.cid * ModeSyn.__ModeSpine) ->
        ((unit)(* single mode installation and lookup *))
    val modeLookup : IntSyn.cid -> ModeSyn.__ModeSpine option
    val uninstallMode : IntSyn.cid -> bool
    val installMmode :
      (IntSyn.cid * ModeSyn.__ModeSpine) ->
        ((unit)(* multiple mode installation and lookup *)
        (* true: was declared, false: not *))
    val mmodeLookup : IntSyn.cid -> ModeSyn.__ModeSpine list
  end;;




module ModeTable(ModeTable:sig
                             module Table :
                             ((TABLE)(* Mode Table *)
                             (* Author: Carsten Schuermann *)(* Modified: Frank Pfenning, Roberto Virga *)
                             (*! structure IntSyn' : INTSYN !*)(* structure Names : NAMES *)
                             (*! sharing Names.IntSyn = IntSyn' !*))
                           end) : MODETABLE =
  struct
    exception Error of
      ((string)(*! structure IntSyn = IntSyn' !*)(*! sharing Index.IntSyn = IntSyn' !*)
      (* structure Index : INDEX *)) 
    module I = IntSyn
    module M = ModeSyn
    let (modeSignature : M.__ModeSpine list Table.__Table) = Table.new__ 0
    let rec reset () = Table.clear modeSignature
    let rec modeLookup a =
      match Table.lookup modeSignature a with
      | SOME (mS::_) -> SOME mS
      | NONE -> NONE
    let rec mmodeLookup a =
      match Table.lookup modeSignature a with | SOME mSs -> mSs | NONE -> nil
    let rec installMode (a, mS) = Table.insert modeSignature (a, [mS])
    let rec uninstallMode a =
      match modeLookup a with
      | NONE -> false__
      | SOME _ -> (Table.delete modeSignature a; true__)
    let rec installMmode (a, mS) =
      let mSs = mmodeLookup a in Table.insert modeSignature (a, (mS :: mSs))
    let ((reset)(* reset () = ()

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
    *))
      = reset
    let installMode = installMode
    let modeLookup = modeLookup
    let uninstallMode = uninstallMode
    let installMmode = installMmode
    let mmodeLookup = mmodeLookup
  end ;;
