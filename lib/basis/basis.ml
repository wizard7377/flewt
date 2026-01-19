(* Basis module - SML Basis Library compatibility layer for OCaml *)
(* This module re-exports all the standard basis library modules *)

(* Order type for comparisons *)
type order = LESS | EQUAL | GREATER

(* Substring type *)
type substring = Substring.Substring.substring

(* General module *)
module type GENERAL = General.GENERAL
module General = General.General

(* Option module *)
module type OPTION = Option.OPTION
module SmlOption = Option.SmlOption

(* Bool module *)
module type BOOL = Bool.BOOL
module Bool = Bool.Bool

(* List module *)
module type LIST = List.LIST
module SmlList = List.SmlList

(* String conversion module *)
module type STRING_CVT = StringCvt.STRING_CVT
module StringCvt = StringCvt.StringCvt

(* String module *)
module type STRING = String.STRING
module SmlString = String.SmlString

(* Time module *)
module type TIME = Time.TIME
module Time = Time.Time

(* IO module *)
module type IO = Io.IO
module IO = Io.IO

(* Char module *)
module type CHAR = Char.CHAR
module SmlChar = Char.SmlChar

(* CharVector module *)
module type CHAR_VECTOR = CharVector.CHAR_VECTOR
module CharVector = CharVector.CharVector

(* Substring module *)
module type SUBSTRING = Substring.SUBSTRING
module Substring = Substring.Substring

(* Primitive IO modules *)
module type PRIM_IO = PrimIO.PRIM_IO
module TextPrimIO = TextPrimIO

(* Stream IO modules *)
module type STREAM_IO = StreamIO.STREAM_IO
module type TEXT_STREAM_IO = TextStreamIO.TEXT_STREAM_IO
module TextStreamIO = TextStreamIO.TextStreamIO

(* Imperative IO module *)
module type IMPERATIVE_IO = ImperativeIO.IMPERATIVE_IO

(* Text IO module *)
module type TEXT_IO = TextIO.TEXT_IO
module TextIO = TextIO.TextIO
