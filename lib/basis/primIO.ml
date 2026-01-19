(* PrimIO module - SML Basis Library compatibility *)
(* See https://smlfamily.github.io/Basis/prim-io.html *)

type order = LESS | EQUAL | GREATER

(** Module type for primitive I/O operations *)
module type PRIM_IO = sig
  type elem
  type vector
  type vector_slice
  type array
  type array_slice
  type pos

  val compare : pos * pos -> order

  (** Reader type for input operations *)
  type reader = {
    name : string;
    chunkSize : int;
    readVec : (int -> vector) option;
    readArr : (array_slice -> int) option;
    readVecNB : (int -> vector option) option;
    readArrNB : (array_slice -> int option) option;
    block : (unit -> unit) option;
    canInput : (unit -> bool) option;
    avail : unit -> int option;
    getPos : (unit -> pos) option;
    setPos : (pos -> unit) option;
    endPos : (unit -> pos) option;
    verifyPos : (unit -> pos) option;
    close : unit -> unit;
    ioDesc : Unix.file_descr option;
  }

  (** Writer type for output operations *)
  type writer = {
    name : string;
    chunkSize : int;
    writeVec : (vector_slice -> int) option;
    writeArr : (array_slice -> int) option;
    writeVecNB : (vector_slice -> int option) option;
    writeArrNB : (array_slice -> int option) option;
    block : (unit -> unit) option;
    canOutput : (unit -> bool) option;
    getPos : (unit -> pos) option;
    setPos : (pos -> unit) option;
    endPos : (unit -> pos) option;
    verifyPos : (unit -> pos) option;
    close : unit -> unit;
    ioDesc : Unix.file_descr option;
  }

  val openVector : vector -> reader
  val nullRd : unit -> reader
  val nullWr : unit -> writer
  val augmentReader : reader -> reader
  val augmentWriter : writer -> writer
end