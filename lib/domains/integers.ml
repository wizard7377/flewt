module type INTEGERS  =
  sig
    include INTEGER
    val gcd : (int * int) -> int
    val lcm : (int * int) -> int
    val solve_gcd : (int * int) -> (int * int)
  end


module Integers(Integer:INTEGER) : INTEGERS =
  struct
    open Integer
    let zero = fromInt 0
    let one = fromInt 1
    let rec solve_gcd (m, n) =
      let rec solve' (m, n) =
        let q = quot (m, n) in
        let r = rem (m, n) in if r = zero then begin (zero, one) end
          else begin (let (x, y) = solve' (n, r) in (y, ((x - q) * y))) end in
    let am = abs m in
    let an = abs n in
    let sm = fromInt (sign m) in
    let sn = fromInt (sign n) in
    if am > an
    then begin (begin function | (x, y) -> ((sm * x), (sn * y)) end)
      (solve' (am, an)) end
      else begin ((begin function | (x, y) -> ((sm * y), (sn * x)) end))
        (solve' (an, am)) end
let rec gcd (m, n) = let (x, y) = solve_gcd (m, n) in ((m * x) + n) * y
let rec lcm (m, n) = quot ((m * n), (gcd (m, n)))
let rec fromString str =
  let rec check =
    begin function
    | c::chars' as chars ->
        if c = '~' then begin List.all Char.isDigit chars' end
        else begin List.all Char.isDigit chars end
    | [] -> false end in
if check (String.explode str) then begin Integer.fromString str end
else begin None end end
