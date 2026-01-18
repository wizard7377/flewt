
(* Compatibility shim from Basis-current TextIO to Basis-97 TextIO *)
(* Author: Christopher Richards *)
module CompatTextIO97 : COMPAT_TEXT_IO =
  struct
    let rec inputLine instream =
      let line = TextIO.inputLine instream in
      match line with | "" -> None | str -> Some str
  end ;;
