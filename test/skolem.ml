
;;Twelf.reset () ;;Twelf.loadFile "TEST/cp.elf"
let SOME cpt = Names.nameLookup "cpt" let _ = Skolem.install [cpt]
let SOME cpt1 = Names.nameLookup "cpt#1"
let SOME cpt2 = Names.nameLookup "cpt#2"
let _ =
  TextIO.print
    ((Print.expToString (IntSyn.Null, (IntSyn.constType cpt1))) ^ "\n")
let _ =
  TextIO.print
    ((Print.expToString (IntSyn.Null, (IntSyn.constType cpt2))) ^ "\n");;
