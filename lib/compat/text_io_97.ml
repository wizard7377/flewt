
module CompatTextIO97 : COMPAT_TEXT_IO =
  struct
    let rec inputLine instream =
      let line = TextIO.inputLine instream in
      match line with | "" -> NONE | str -> Some str
  end ;;
