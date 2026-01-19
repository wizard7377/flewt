(* StreamIO module - SML Basis Library compatibility *)
(* See https://smlfamily.github.io/Basis/stream-io.html *)

type order = LESS | EQUAL | GREATER

(** Buffer mode for output streams *)
type buffer_mode = NO_BUF | LINE_BUF | BLOCK_BUF

(** Module type for functional stream I/O *)
module type STREAM_IO = sig
  type elem
  type vector

  type instream
  type outstream
  type out_pos

  type reader
  type writer
  type pos

  (** Read from input stream, returning data and new stream *)
  val input : instream -> vector * instream

  (** Read single element from input stream *)
  val input1 : instream -> (elem * instream) option

  (** Read n elements from input stream *)
  val inputN : instream * int -> vector * instream

  (** Read all remaining input *)
  val inputAll : instream -> vector * instream

  (** Check if n elements can be read without blocking *)
  val canInput : instream * int -> int option

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

  (** Create input stream from reader and initial data *)
  val mkInstream : reader * vector -> instream

  (** Get underlying reader and remaining data from input stream *)
  val getReader : instream -> reader * vector

  (** Get current position in input stream *)
  val filePosIn : instream -> pos

  (** Set buffer mode for output stream *)
  val setBufferMode : outstream * buffer_mode -> unit

  (** Get buffer mode for output stream *)
  val getBufferMode : outstream -> buffer_mode

  (** Create output stream from writer and buffer mode *)
  val mkOutstream : writer * buffer_mode -> outstream

  (** Get underlying writer and buffer mode from output stream *)
  val getWriter : outstream -> writer * buffer_mode

  (** Get current output position *)
  val getPosOut : outstream -> out_pos

  (** Set output position *)
  val setPosOut : out_pos -> outstream

  (** Get file position from output position *)
  val filePosOut : out_pos -> pos
end 