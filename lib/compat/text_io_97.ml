module CompatTextIO97 : COMPAT_TEXT_IO =
  struct
    let rec inputLine instream =
      let line = TextIO.inputLine instream in
      begin match line with | "" -> None | str -> Some str end end 