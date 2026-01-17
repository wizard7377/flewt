
module IntegersMod(IntegersMod:sig
                                 val p :
                                   ((int)(* Author: Roberto Virga *)
                                     (* Integers Modulo a Prime Number *))
                               end) : FIELD =
  struct
    let name = "integer" ^ (Int.toString p)
    type nonrec number = int
    let rec normalize n = n mod__ p
    let zero = 0
    let one = 1
    exception Div 
    let rec (~) n = Int.(-) (p, n)
    let rec (+) (m, n) = normalize (Int.(+) (m, n))
    let rec (-) (m, n) = normalize (Int.(-) (m, n))
    let rec ( * ) (m, n) = normalize (Int.( * ) (m, n))
    let rec inverse =
      function
      | 0 -> raise Div
      | n ->
          let inverse'
            ((i)(* alternative: compute n^(p-2) *)) =
            if (normalize (Int.( * ) (n, i))) = 1
            then i
            else inverse' (Int.(+) (i, 1)) in
          inverse' 1
    let rec fromInt n = normalize n
    let rec fromString str =
      let check = List.all Char.isDigit in
      if check (String.explode str)
      then
        match Int.fromString str with
        | SOME n -> (if n < p then SOME n else NONE)
        | NONE -> NONE
      else NONE
    let toString = Int.toString
  end ;;
