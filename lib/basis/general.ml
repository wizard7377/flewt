(* General module - SML Basis Library compatibility *)
(* See https://smlfamily.github.io/Basis/general.html *)

(** Order type for comparisons *)
type order = LESS | EQUAL | GREATER

(** Module type for general utilities *)
module type GENERAL = sig
  (** Standard exceptions *)
  exception Bind
  exception Match
  exception Chr
  exception Div
  exception Domain
  exception Fail of string
  exception Overflow
  exception Size
  exception Span
  exception Subscript

  (** Comparison order type *)
  type order = LESS | EQUAL | GREATER

  (** Get name of exception *)
  val exnName : exn -> string

  (** Get message from exception *)
  val exnMessage : exn -> string

  (** Function composition *)
  val o : ('b -> 'c) * ('a -> 'b) -> 'a -> 'c

  (** Evaluate first arg, return first arg, discard second *)
  val before : 'a * unit -> 'a

  (** Ignore value *)
  val ignore : 'a -> unit
end

module General : GENERAL = struct
  exception Bind
  exception Match
  exception Chr
  exception Div
  exception Domain
  exception Fail of string
  exception Overflow
  exception Size
  exception Span
  exception Subscript

  type order = LESS | EQUAL | GREATER

  let exnName e = Printexc.exn_slot_name e

  let exnMessage e = Printexc.to_string e

  let o (f, g) x = f (g x)

  let before (x, ()) = x

  let ignore _ = ()
end
