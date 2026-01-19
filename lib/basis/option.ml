(* Option module - SML Basis Library compatibility *)
(* See https://smlfamily.github.io/Basis/option.html *)

(** Option type for optional values *)
type 'a option = None | Some of 'a

(** Module type for option operations *)
module type OPTION = sig
  (** Option type *)
  type 'a option = None | Some of 'a

  (** Exception raised by valOf on None *)
  exception Option

  (** Get value or default *)
  val getOpt : 'a option * 'a -> 'a

  (** Test if Some *)
  val isSome : 'a option -> bool

  (** Extract value (raises Option if None) *)
  val valOf : 'a option -> 'a

  (** Apply function to option value for side effect *)
  val app : ('a -> unit) -> 'a option -> unit

  (** Compose function with partial function *)
  val compose : ('a -> 'b) * ('c -> 'a option) -> 'c -> 'b option

  (** Compose two partial functions *)
  val composePartial : ('a -> 'b option) * ('c -> 'a option) -> 'c -> 'b option

  (** Filter value by predicate *)
  val filter : ('a -> bool) -> 'a -> 'a option

  (** Flatten nested option *)
  val join : 'a option option -> 'a option

  (** Map function over option *)
  val map : ('a -> 'b) -> 'a option -> 'b option

  (** Map partial function over option *)
  val mapPartial : ('a -> 'b option) -> 'a option -> 'b option
end

module SmlOption : OPTION = struct
  type 'a option = None | Some of 'a

  exception Option

  let getOpt (opt, default) =
    match opt with
    | None -> default
    | Some v -> v

  let isSome = function
    | None -> false
    | Some _ -> true

  let valOf = function
    | None -> raise Option
    | Some v -> v

  let map f = function
    | None -> None
    | Some a -> Some (f a)

  let app f opt =
    ignore (map f opt)

  let compose (f, g) c =
    map f (g c)

  let join = function
    | None -> None
    | Some v -> v

  let mapPartial f opt =
    join (map f opt)

  let composePartial (f, g) c =
    mapPartial f (g c)

  let filter p a =
    if p a then Some a else None
end
