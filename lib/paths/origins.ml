
module type ORIGINS  =
  sig
    val reset :
      unit ->
        ((unit)(*! structure Paths : PATHS !*)(*! structure IntSyn : INTSYN !*)
        (* Author: Frank Pfenning *)(* Origins of Declarations *))
    val installLinesInfo : (string * Paths.linesInfo) -> unit
    val linesInfoLookup : string -> Paths.linesInfo option
    val installOrigin :
      (IntSyn.cid * (string * Paths.occConDec option)) -> unit
    val originLookup : IntSyn.cid -> (string * Paths.occConDec option)
  end;;




module Origins(Origins:sig
                         module Global : GLOBAL
                         module Table :
                         ((TABLE)(* Origins of Declarations *)(* Author: Frank Pfenning *))
                       end) : ORIGINS =
  struct
    let (linesInfoTable : Paths.linesInfo Table.__Table) = Table.new__ 31
    let rec reset () = Table.clear linesInfoTable
    let rec install (string, linesInfo) =
      Table.insert linesInfoTable (string, linesInfo)
    let rec lookup string = Table.lookup linesInfoTable string
    let ((reset)(*! structure IntSyn' : INTSYN !*)(*! structure Paths' : PATHS !*)
      (*! structure IntSyn = IntSyn' !*)(*! structure Paths = Paths' !*))
      = reset
    let installLinesInfo = install
    let linesInfoLookup = lookup
    let originArray =
      (Array.array ((Global.maxCid + 1), ("", NONE)) : (string *
                                                         Paths.occConDec
                                                         option) Array.array)
    let rec installOrigin (cid, fileNameOpt) =
      Array.update (originArray, cid, fileNameOpt)
    let rec originLookup cid = Array.sub (originArray, cid)
  end ;;
