module type RATIONALS  =
  sig
    include ORDERED_FIELD
    module Integers : INTEGERS
    val fromInteger : Integers.int -> number
    val floor : number -> Integers.int
    val ceiling : number -> Integers.int
    val numerator : number -> Integers.int
    val denominator : number -> Integers.int
  end


module Rationals(Integers:INTEGERS) : RATIONALS =
  struct
    module Integers = Integers
    let name = "rational"
    exception Div = Div
    module I = Integers
    type number =
      | Fract of (Int.int * I.int * I.int) 
    let zero = Fract (0, (I.fromInt 0), (I.fromInt 1))
    let one = Fract (1, (I.fromInt 1), (I.fromInt 1))
    exception Div 
    let rec normalize =
      begin function
      | Fract (0, _, _) -> zero
      | Fract (s, n, d) ->
          let rec gcd (m, n) = if (=) m I.fromInt 0 then begin n end
            else begin if (=) n I.fromInt 0 then begin m end
              else begin
                if I.(>) (m, n) then begin gcd ((I.mod_ (m, n)), n) end
                else begin gcd (m, (I.mod_ (n, m))) end end end in
  let g = gcd (n, d) in Fract (s, (I.div (n, g)), (I.div (d, g))) end
let rec (~-) (Fract (s, n, d)) = Fract ((Int.(~-) s), n, d)
let rec (+) (Fract (s1, n1, d1), Fract (s2, n2, d2)) =
  let n =
    I.(+)
      ((I.( * ) ((I.( * ) ((I.fromInt s1), n1)), d2)),
        (I.( * ) ((I.( * ) ((I.fromInt s2), n2)), d1))) in
  normalize (Fract ((I.sign n), (I.abs n), (I.( * ) (d1, d2))))
let rec (-) (Fract (s1, n1, d1), Fract (s2, n2, d2)) =
  let n =
    I.(-)
      ((I.( * ) ((I.( * ) ((I.fromInt s1), n1)), d2)),
        (I.( * ) ((I.( * ) ((I.fromInt s2), n2)), d1))) in
  normalize (Fract ((I.sign n), (I.abs n), (I.( * ) (d1, d2))))
let rec ( * ) (Fract (s1, n1, d1), Fract (s2, n2, d2)) =
  normalize
    (Fract ((Int.( * ) (s1, s2)), (I.( * ) (n1, n2)), (I.( * ) (d1, d2))))
let rec inverse =
  begin function
  | Fract (0, _, _) -> raise Div
  | Fract (s, n, d) -> Fract (s, d, n) end
let rec sign (Fract (s, n, d)) = s
let rec numerator (Fract (s, n, d)) = n
let rec denominator (Fract (s, n, d)) = d
let rec abs (Fract (s, n, d)) = Fract ((Int.abs s), n, d)
let rec compare (Fract (s1, n1, d1), Fract (s2, n2, d2)) =
  I.compare
    ((I.( * ) ((I.( * ) ((I.fromInt s1), n1)), d2)),
      (I.( * ) ((I.( * ) ((I.fromInt s2), n2)), d1)))
let rec (>) (q1, q2) = (compare (q1, q2)) = GREATER
let rec (<) (q1, q2) = (compare (q1, q2)) = LESS
let rec (>=) (q1, q2) = (q1 = q2) || (q1 > q2)
let rec (<=) (q1, q2) = (q1 = q2) || (q1 < q2)
let rec fromInt n =
  Fract ((Int.sign n), (I.fromInt (Int.abs n)), (I.fromInt 1))
let rec fromString str =
  let rec check_numerator =
    begin function
    | c::chars' as chars ->
        if c = '~' then begin List.all Char.isDigit chars' end
        else begin List.all Char.isDigit chars end
    | [] -> false end in
let rec check_denominator chars = List.all Char.isDigit chars in
let fields = String.fields (begin function | c -> c = '/' end) str in
if (List.length fields) = 1
then
begin let numerator = List.nth (fields, 0) in
      (if check_numerator (String.explode numerator)
       then
         begin begin match I.fromString numerator with
               | Some n ->
                   Some (Fract ((I.sign n), (I.abs n), (I.fromInt 1)))
               | _ -> None end end
else begin None end) end
else begin
  if (List.length fields) = 2
  then
    begin (let numerator = List.nth (fields, 0) in
           let denominator = List.nth (fields, 1) in
           if
             (check_numerator (String.explode numerator)) &&
               (check_denominator (String.explode denominator))
           then
             begin begin match ((I.fromString numerator),
                                 (I.fromString denominator))
                         with
                   | (Some n, Some d) ->
                       Some (normalize (Fract ((I.sign n), (I.abs n), d)))
                   | _ -> None end end
             else begin None end) end
else begin None end end
let rec toString (Fract (s, n, d)) =
  let nStr = I.toString (I.( * ) ((I.fromInt s), n)) in
  let dStr = I.toString d in if (=) d I.fromInt 1 then begin nStr end
    else begin (nStr ^ "/") ^ dStr end
let rec fromInteger n = Fract ((I.sign n), (I.abs n), (I.fromInt 1))
let rec floor (Fract (s, n, d) as q) =
  if Int.(>=) (s, 0) then begin I.quot (n, d) end
  else begin Integers.(~-) (ceiling (- q)) end
let rec ceiling (Fract (s, n, d) as q) =
  if Int.(>=) (s, 0)
  then begin I.quot ((I.(+) (n, (I.(-) (d, (I.fromInt 1))))), d) end
  else begin Integers.(~-) (floor (- q)) end
type nonrec number = number
let zero = zero
let one = one
let (~-) = (~-)
let (+) = (+)
let (-) = (-)
let ( * ) = ( * )
let inverse = inverse
let fromInt = fromInt
let fromString = fromString
let toString = toString
let sign = sign
let abs = abs
let (>) = (>)
let (<) = (<)
let (>=) = (>=)
let (<=) = (<=)
let compare = compare
let fromInteger = fromInteger
let floor = floor
let ceiling = ceiling
let numerator = numerator
let denominator = denominator end
