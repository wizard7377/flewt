
module CompatTextIO97 : COMPAT_TEXT_IO =
  struct
    let rec inputLine
      ((instream)(* Compatibility shim from Basis-current TextIO to Basis-97 TextIO *)
      (* Author: Christopher Richards *)) =
      let line = TextIO.inputLine instream in
      match line with | "" -> NONE | str -> SOME str
  end ;;
