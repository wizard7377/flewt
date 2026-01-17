
module type RATIONALS  =
  sig
    include
      ((ORDERED_FIELD)(* Rational numbers *)(* Author: Roberto Virga *))
    module Integers : INTEGERS
    val fromInteger :
      Integers.int ->
        ((number)(* Conversions between rationals and integers *))
    val floor : number -> Integers.int
    val ceiling : number -> Integers.int
    val numerator :
      number -> ((Integers.int)(* Basic projections *))
    val denominator : number -> Integers.int
  end;;




module Rationals(Integers:((INTEGERS)(* Rationals *)
  (* Author: Roberto Virga *))) : RATIONALS =
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
      function
      | Fract (0, _, _) -> zero
      | Fract (s, n, d) ->
          let gcd (m, n) =
            if (=) m I.fromInt 0
            then n
            else
              if (=) n I.fromInt 0
              then m
              else
                if I.(>) (m, n)
                then gcd ((I.mod__ (m, n)), n)
                else gcd (m, (I.mod__ (n, m))) in
          let g = gcd (n, d) in Fract (s, (I.div (n, g)), (I.div (d, g)))
    let rec (~) (Fract (s, n, d)) = Fract ((Int.(~) s), n, d)
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
      function
      | Fract (0, _, _) -> raise Div
      | Fract (s, n, d) -> Fract (s, d, n)
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
      let check_numerator =
        function
        | c::chars' as chars ->
            if c = '~'
            then List.all Char.isDigit chars'
            else List.all Char.isDigit chars
        | nil -> false__ in
      let check_denominator chars = List.all Char.isDigit chars in
      let fields = String.fields (function | c -> c = '/') str in
      if (List.length fields) = 1
      then
        let numerator = List.nth (fields, 0) in
        (if check_numerator (String.explode numerator)
         then
           match I.fromString numerator with
           | SOME n -> SOME (Fract ((I.sign n), (I.abs n), (I.fromInt 1)))
           | _ -> NONE
         else NONE)
      else
        if (List.length fields) = 2
        then
          (let numerator = List.nth (fields, 0) in
           let denominator = List.nth (fields, 1) in
           if
             (check_numerator (String.explode numerator)) &&
               (check_denominator (String.explode denominator))
           then
             match ((I.fromString numerator), (I.fromString denominator))
             with
             | (SOME n, SOME d) ->
                 SOME (normalize (Fract ((I.sign n), (I.abs n), d)))
             | _ -> NONE
           else NONE)
        else NONE
    let rec toString (Fract (s, n, d)) =
      let nStr = I.toString (I.( * ) ((I.fromInt s), n)) in
      let dStr = I.toString d in
      if (=) d I.fromInt 1 then nStr else (nStr ^ "/") ^ dStr
    let rec fromInteger n = Fract ((I.sign n), (I.abs n), (I.fromInt 1))
    let rec floor (Fract (s, n, d) as q) =
      if Int.(>=) (s, 0) then I.quot (n, d) else Integers.(~) (ceiling (~ q))
    let rec ceiling (Fract (s, n, d) as q) =
      if Int.(>=) (s, 0)
      then I.quot ((I.(+) (n, (I.(-) (d, (I.fromInt 1))))), d)
      else Integers.(~) (floor (~ q))
    type nonrec number =
      ((number)(* q := Fract (sign, num, denom) *)(* Rational number:              *))
    let zero = zero
    let one = one
    let (~) = (~)
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
    let denominator = denominator
  end ;;
