module type TEXT_STREAM_IO =
  sig 
include STREAM_IO
with type vector = CharVector.vector
  and type elem = Char.char
val inputLine : instream -> (string * instream) option
val outputSubstr : outstream * substring -> unit
end