
module type COMPAT_ARRAY  =
  sig val appi : (int -> 'a -> unit) -> 'a Array.array -> unit end;;
