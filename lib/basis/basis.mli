(* Basis module interface - SML Basis Library compatibility *)
(* This file exports all the standard basis library module types and modules *)

(** Order type for comparisons *)
type order = LESS | EQUAL | GREATER

(** Substring type *)
type substring = Substring.Substring.substring

(** General module - basic types and exceptions *)
module type GENERAL = General.GENERAL
module General : GENERAL

(** Option module - optional values *)
module type OPTION = Option.OPTION
module SmlOption : OPTION

(** Bool module - boolean operations *)
module type BOOL = Bool.BOOL
module Bool : BOOL

(** List module - list operations *)
module type LIST = List.LIST
module SmlList : LIST

(** StringCvt module - string conversion utilities *)
module type STRING_CVT = StringCvt.STRING_CVT
module StringCvt : STRING_CVT

(** String module - string operations *)
module type STRING = String.STRING
module SmlString : STRING

(** Time module - time operations *)
module type TIME = Time.TIME
module Time : TIME

(** IO module - I/O exceptions and types *)
module type IO = Io.IO
module IO : IO

(** Char module - character operations *)
module type CHAR = Char.CHAR
module SmlChar : CHAR

(** CharVector module - character vectors (strings) *)
module type CHAR_VECTOR = CharVector.CHAR_VECTOR
module CharVector : CHAR_VECTOR

(** Substring module - string slices *)
module type SUBSTRING = Substring.SUBSTRING
module Substring : SUBSTRING

(** PrimIO module - primitive I/O operations *)
module type PRIM_IO = PrimIO.PRIM_IO

(** TextPrimIO module - primitive text I/O *)
module TextPrimIO : sig
  type elem = char
  type vector = string
  type vector_slice = string * int * int
  type array = bytes
  type array_slice = bytes * int * int
  type pos = int

  type order = LESS | EQUAL | GREATER
  val compare : pos * pos -> order

  type reader
  type writer

  val openVector : vector -> reader
  val nullRd : unit -> reader
  val nullWr : unit -> writer
  val stdInReader : unit -> reader
  val stdOutWriter : unit -> writer
  val stdErrWriter : unit -> writer
  val openRd : string -> reader
  val openWr : string -> writer
  val openApp : string -> writer
end

(** StreamIO module - functional stream I/O *)
module type STREAM_IO = StreamIO.STREAM_IO

(** TextStreamIO module - text stream I/O *)
module type TEXT_STREAM_IO = TextStreamIO.TEXT_STREAM_IO
module TextStreamIO : TEXT_STREAM_IO

(** ImperativeIO module - imperative stream I/O *)
module type IMPERATIVE_IO = ImperativeIO.IMPERATIVE_IO

(** TextIO module - high-level text I/O *)
module type TEXT_IO = TextIO.TEXT_IO
module TextIO : TEXT_IO
