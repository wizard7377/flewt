module type TEXT_IO =
  sig
include IMPERATIVE_IO
module StreamIO : TEXT_STREAM_IO
with type reader = TextPrimIO.reader
  and type writer = TextPrimIO.writer
  and type pos = TextPrimIO.pos
val inputLine : instream -> string option
val outputSubstr : outstream * substring -> unit
val openIn  : string -> instream
val openOut : string -> outstream
val openAppend : string -> outstream
val openString : string -> instream
val stdIn  : instream
val stdOut : outstream
val stdErr : outstream
val print : string -> unit
val scanStream : ((Char.char, StreamIO.instream)
                       StringCvt.reader
                     -> ('a, StreamIO.instream)
                       StringCvt.reader)
                   -> instream -> 'a option
end