(* Bool module - SML Basis Library compatibility *)
(* See https://smlfamily.github.io/Basis/bool.html *)

(** Module type for boolean operations *)
module type BOOL = sig
  (** Logical negation *)
  val not : bool -> bool

  (** Convert string to boolean *)
  val fromString : string -> bool option

  (** Convert boolean to string *)
  val toString : bool -> string
end

module Bool : BOOL = struct
  let not = not

  let fromString s =
    match Stdlib.String.lowercase_ascii s with
    | "true" -> Some true
    | "false" -> Some false
    | _ -> None

  let toString = function
    | true -> "true"
    | false -> "false"
end
