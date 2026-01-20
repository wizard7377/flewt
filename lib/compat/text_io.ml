
module type COMPAT_TEXT_IO  =
  sig val inputLine : TextIO.instream -> string option end;;
