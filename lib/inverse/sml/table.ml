module type TABLE  =
  sig
    type nonrec key
    type nonrec 'a table
    val table : int -> 'a table
    val insert : 'a table -> (key * 'a) -> 'a table
    val lookup : 'a table -> key -> 'a
    val size : 'a table -> int
    val app : ('a -> unit) -> 'a table -> unit
    val appi : ((int * 'a) -> unit) -> 'a table -> unit
    val clear : 'a table -> unit
  end


module ArrayTable : TABLE =
  struct
    module L = Lib
    module A = Array
    type nonrec key = int
    type nonrec 'a table = < arr: 'a option array  ;used: int ref   > 
    let rec table n = { arr = (A.array (n, None)); used = (ref 0) }
    let rec clear { arr; used; used } =
      begin used := 0; A.modify (begin function | _ -> None end) arr end
  let rec insert ({ arr; used; used } as t) (n, v) =
    if (n < 0) || ((>) n A.length arr) then begin raise Subscript end
    else begin
      (begin match A.sub (arr, n) with
       | None ->
           (begin A.update (arr, n, (Some v));
            if (!) ((>) n) used then begin used := n end
            else begin () end;
       t end)
    | Some _ -> raise (Fail "insert: key already present") end) end
let rec lookup ({ arr } : 'a table) n =
  if (n < 0) || ((>) n A.length arr) then begin raise Subscript end
  else begin
    (begin match A.sub (arr, n) with | None -> raise Subscript | Some v -> v end) end
let rec size ({ arr } : 'a table) = A.length arr
exception Done 
let rec app f { arr; used; used } =
  let used' = !used in
  let rec f' (i, x) = if i >= used' then begin raise Done end
    else begin (begin match x with | Some n -> f n | None -> () end) end in
begin try A.appi f' arr with | Done -> () end
let rec appi f { arr; used; used } =
  let used' = !used in
  let rec f' (i, x) = if i >= used' then begin raise Done end
    else begin (begin match x with | Some n -> f (i, n) | None -> () end) end in
begin try A.appi f' arr with | Done -> () end end 
module Table = ArrayTable