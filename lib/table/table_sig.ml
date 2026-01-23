module type TABLE  =
  sig
    type nonrec key
    type nonrec 'a entry = (key * 'a)
    type nonrec 'a table_
    val new_ : int -> 'a table_
    val insert : 'a table_ -> 'a entry -> unit
    val insertShadow : 'a table_ -> 'a entry -> 'a entry option
    val lookup : 'a table_ -> key -> 'a option
    val delete : 'a table_ -> key -> unit
    val clear : 'a table_ -> unit
    val app : ('a entry -> unit) -> 'a table_ -> unit
  end
