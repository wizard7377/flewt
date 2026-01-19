(* ImperativeIO module - SML Basis Library compatibility *)
(* See https://smlfamily.github.io/Basis/imperative-io.html *)

(** Module type for imperative stream I/O *)
module type IMPERATIVE_IO = sig
  (** Type of stream elements *)
  type elem

  (** Type of element vectors *)
  type vector

  (** Mutable input stream *)
  type instream

  (** Mutable output stream *)
  type outstream

  (** Associated functional stream I/O module *)
  module StreamIO : StreamIO.STREAM_IO

  (** Read from input stream *)
  val input : instream -> vector

  (** Read single element from input stream *)
  val input1 : instream -> elem option

  (** Read n elements from input stream *)
  val inputN : instream * int -> vector

  (** Read all remaining input *)
  val inputAll : instream -> vector

  (** Check if n elements can be read without blocking *)
  val canInput : instream * int -> int option

  (** Look at next element without consuming it *)
  val lookahead : instream -> elem option

  (** Close input stream *)
  val closeIn : instream -> unit

  (** Test if at end of stream *)
  val endOfStream : instream -> bool

  (** Write vector to output stream *)
  val output : outstream * vector -> unit

  (** Write single element to output stream *)
  val output1 : outstream * elem -> unit

  (** Flush output stream *)
  val flushOut : outstream -> unit

  (** Close output stream *)
  val closeOut : outstream -> unit

  (** Create imperative stream from functional stream *)
  val mkInstream : StreamIO.instream -> instream

  (** Get underlying functional stream *)
  val getInstream : instream -> StreamIO.instream

  (** Set underlying functional stream *)
  val setInstream : instream * StreamIO.instream -> unit

  (** Create imperative output stream from functional stream *)
  val mkOutstream : StreamIO.outstream -> outstream

  (** Get underlying functional output stream *)
  val getOutstream : outstream -> StreamIO.outstream

  (** Set underlying functional output stream *)
  val setOutstream : outstream * StreamIO.outstream -> unit

  (** Get current output position *)
  val getPosOut : outstream -> StreamIO.out_pos

  (** Set output position *)
  val setPosOut : outstream * StreamIO.out_pos -> unit
end