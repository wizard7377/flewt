(* IO module - SML Basis Library compatibility *)
(* See https://smlfamily.github.io/Basis/io.html *)

type order = LESS | EQUAL | GREATER

(** Module type for I/O exceptions and types *)
module type IO = sig
  (** Exception for I/O errors *)
  exception Io of { name : string; function_ : string; cause : exn }

  (** Exception for operations requiring blocking not supported *)
  exception BlockingNotSupported

  (** Exception for operations requiring non-blocking not supported *)
  exception NonblockingNotSupported

  (** Exception for random access operations not supported *)
  exception RandomAccessNotSupported

  (** Exception for operations on closed streams *)
  exception ClosedStream

  (** Buffer mode for output streams *)
  type buffer_mode =
    | NO_BUF    (** No buffering *)
    | LINE_BUF  (** Line buffering *)
    | BLOCK_BUF (** Block buffering *)
end

module IO : IO = struct
  exception Io of { name : string; function_ : string; cause : exn }
  exception BlockingNotSupported
  exception NonblockingNotSupported
  exception RandomAccessNotSupported
  exception ClosedStream

  type buffer_mode =
    | NO_BUF
    | LINE_BUF
    | BLOCK_BUF
end