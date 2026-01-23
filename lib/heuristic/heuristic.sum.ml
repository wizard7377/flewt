module Heuristic : HEURISTIC =
  struct
    type nonrec index =
      <
        sd: int
          (* 0 = non-recursive
                                           1 = recursive *)
          (* maximal number of cases *)(* Number of cases *)
          (* Induction variable *)(* Splitting depth *) ;
        ind: int option  ;c: int  ;m: int  ;r: int  ;p: int   > 
    let rec recToString =
      begin function | 0 -> "non-rec = 2" | 1 -> "rec = 1" end
    let rec realFmt r = Real.fmt (StringCvt.FIX (Some 2)) r
    let rec ratio =
      begin function
      | (0, 0) -> 1.0
      | (c, 0) -> 1.1
      | (c, m) -> (Real.fromInt c) / (Real.fromInt m) end
  let rec sqr (x : real) = x * x
  let rec sum =
    begin function
    | { sd = k1; ind = None; c = c1; m = m1; r = r1; p = p1; ind = None;
        c = c1; m = m1; r = r1; p = p1; c = c1; m = m1; r = r1; p = p1;
        m = m1; r = r1; p = p1; r = r1; p = p1; p = p1 } ->
        if c1 = 0
        then
          begin ((sqr (Real.fromInt k1)) + ((-) 5.0 ratio (c1, m1))) +
                  (Real.fromInt r1) end
        else begin
          ((sqr (Real.fromInt k1)) + ((-) 1.0 ratio (c1, m1))) +
            (Real.fromInt r1) end
    | { sd = k1; ind = Some 0; c = c1; m = m1; r = r1; p = p1; ind = Some 0;
        c = c1; m = m1; r = r1; p = p1; c = c1; m = m1; r = r1; p = p1;
        m = m1; r = r1; p = p1; r = r1; p = p1; p = p1 } ->
        if c1 = 0
        then
          begin ((sqr (Real.fromInt k1)) + ((-) 5.0 ratio (c1, m1))) +
                  (Real.fromInt r1) end
        else begin
          (((+) (sqr (Real.fromInt k1)) ratio (3, 2)) +
             ((-) 1.0 ratio (c1, m1)))
            + (Real.fromInt r1) end
| { sd = k1; ind = Some i1; c = c1; m = m1; r = r1; p = p1; ind = Some i1;
    c = c1; m = m1; r = r1; p = p1; c = c1; m = m1; r = r1; p = p1; m = m1;
    r = r1; p = p1; r = r1; p = p1; p = p1 } ->
    if c1 = 0
    then
      begin ((sqr (Real.fromInt k1)) + ((-) 5.0 ratio (c1, m1))) +
              (Real.fromInt r1) end
    else begin
      (((+) (sqr (Real.fromInt k1)) ratio (1, i1)) + ((-) 1.0 ratio (c1, m1)))
        + (Real.fromInt r1) end end
let rec conv =
  begin function
  | { sd = k1; ind = i; c = c1; m = m1; r = 1; p = p1; ind = i; c = c1;
      m = m1; r = 1; p = p1; c = c1; m = m1; r = 1; p = p1; m = m1; r = 1;
      p = p1; r = 1; p = p1; p = p1 } ->
      { sd = k1; ind = i; c = c1; m = m1; r = 1; p = p1 }
  | { sd = k1; ind = i; c = c1; m = m1; r = 0; p = p1; ind = i; c = c1;
      m = m1; r = 0; p = p1; c = c1; m = m1; r = 0; p = p1; m = m1; r = 0;
      p = p1; r = 0; p = p1; p = p1 } ->
      { sd = k1; ind = i; c = c1; m = m1; r = 2; p = p1 } end
let rec ccompare
  ({ sd = k1; ind = i1; c = c1; m = m1; r = r1; p = p1; ind = i1; c = c1;
     m = m1; r = r1; p = p1; c = c1; m = m1; r = r1; p = p1; m = m1; 
     r = r1; p = p1; r = r1; p = p1; p = p1 },
   { sd = k2; ind = i2; c = c2; m = m2; r = r2; p = p2; ind = i2; c = c2;
     m = m2; r = r2; p = p2; c = c2; m = m2; r = r2; p = p2; m = m2; 
     r = r2; p = p2; r = r2; p = p2; p = p2 })
  =
  ((begin match ((Real.compare
                    ((sum
                        { sd = k2; ind = i2; c = c2; m = m2; r = r2; p = p2 }),
                      (sum
                         { sd = k1; ind = i1; c = c1; m = m1; r = r1; p = p1
                         }))), (Int.compare (p1, p2)))
          with
    | (EQUAL, result) -> result
    | (result, _) -> result end)
  (* p                 *))
let rec compare
  ({ sd = k1; ind = i1; c = c1; m = m1; r = r1; p = p1; ind = i1; c = c1;
     m = m1; r = r1; p = p1; c = c1; m = m1; r = r1; p = p1; m = m1; 
     r = r1; p = p1; r = r1; p = p1; p = p1 },
   { sd = k2; ind = i2; c = c2; m = m2; r = r2; p = p2; ind = i2; c = c2;
     m = m2; r = r2; p = p2; c = c2; m = m2; r = r2; p = p2; m = m2; 
     r = r2; p = p2; r = r2; p = p2; p = p2 })
  =
  ccompare
    ((conv { sd = k1; ind = i1; c = c1; m = m1; r = r1; p = p1 }),
      (conv { sd = k2; ind = i2; c = c2; m = m2; r = r2; p = p2 }))
let rec indexToString =
  begin function
  | { sd = s1; ind = None; c = c1; m = m1; r = 0; p = p1; ind = None; 
      c = c1; m = m1; r = 0; p = p1; c = c1; m = m1; r = 0; p = p1; m = m1;
      r = 0; p = p1; r = 0; p = p1; p = p1 } ->
      ((^) (((((((((((((((("(sd * r =" ^ (Int.toString (s1 * 3))) ^ ", sd=")
                           ^ (Int.toString s1))
                          ^ ", ")
                         ^ (recToString 0))
                        ^ " = 2")
                       ^ ", c/m=")
                      ^ (Int.toString c1))
                     ^ "/")
                    ^ (Int.toString m1))
                   ^ "=")
                  ^ (realFmt ((-) 1.0 ratio (c1, m1))))
                 ^ ", ind=.,")
                ^ ", p=")
               ^ (Int.toString p1))
              ^ " sum = ")
         realFmt (sum { sd = s1; ind = None; c = c1; m = m1; r = 2; p = p1 }))
        ^ " )"
  | { sd = s1; ind = None; c = c1; m = m1; r = 1; p = p1; ind = None; 
      c = c1; m = m1; r = 1; p = p1; c = c1; m = m1; r = 1; p = p1; m = m1;
      r = 1; p = p1; r = 1; p = p1; p = p1 } ->
      ((^) (((((((((((((((("(sd * r =" ^ (Int.toString (s1 * 1))) ^ ", sd=")
                           ^ (Int.toString s1))
                          ^ ", ")
                         ^ (recToString 1))
                        ^ " = 1")
                       ^ ", c/m=")
                      ^ (Int.toString c1))
                     ^ "/")
                    ^ (Int.toString m1))
                   ^ "=")
                  ^ (realFmt ((-) 1.0 ratio (c1, m1))))
                 ^ ", ind=.,")
                ^ ", p=")
               ^ (Int.toString p1))
              ^ " sum = ")
         realFmt (sum { sd = s1; ind = None; c = c1; m = m1; r = 1; p = p1 }))
        ^ " )"
  | { sd = s1; ind = Some idx; c = c1; m = m1; r = 0; p = p1; ind = Some idx;
      c = c1; m = m1; r = 0; p = p1; c = c1; m = m1; r = 0; p = p1; m = m1;
      r = 0; p = p1; r = 0; p = p1; p = p1 } ->
      let i = if idx = 0 then begin 0.0 end else begin ratio (1, idx) end in
((^) (((((^) ((((((((((((((("(sd * r =" ^ (Int.toString (s1 * 3))) ^ ", sd=")
                            ^ (Int.toString s1))
                           ^ ", ")
                          ^ (recToString 0))
                         ^ " = 2")
                        ^ ", c/m=")
                       ^ (Int.toString c1))
                      ^ "/")
                     ^ (Int.toString m1))
                    ^ "=")
                   ^ (realFmt ((-) 1.0 ratio (c1, m1))))
                  ^ ", ind=")
                 ^ (Int.toString idx))
                ^ " = ")
           realFmt i)
          ^ ", p=")
         ^ (Int.toString p1))
        ^ " sum = ")
   realFmt (sum { sd = s1; ind = (Some idx); c = c1; m = m1; r = 2; p = p1 }))
  ^ ")"
  | { sd = s1; ind = Some idx; c = c1; m = m1; r = 1; p = p1; ind = Some idx;
      c = c1; m = m1; r = 1; p = p1; c = c1; m = m1; r = 1; p = p1; m = m1;
      r = 1; p = p1; r = 1; p = p1; p = p1 } ->
      let i = if idx = 0 then begin 0.0 end else begin ratio (1, idx) end in
((^) ((((((((((((((((((("(sd * r =" ^ (Int.toString (s1 * 1))) ^ ", sd=") ^
                        (Int.toString s1))
                       ^ ", ")
                      ^ (recToString 1))
                     ^ " =  1")
                    ^ ", c/m=")
                   ^ (Int.toString c1))
                  ^ "/")
                 ^ (Int.toString m1))
                ^ "=")
               ^ (realFmt ((-) 1.0 ratio (c1, m1))))
              ^ ", ind=")
             ^ (Int.toString idx))
            ^ " = ")
           ^ (realFmt i))
          ^ ", p=")
         ^ (Int.toString p1))
        ^ " sum = ")
   realFmt (sum { sd = s1; ind = (Some idx); c = c1; m = m1; r = 1; p = p1 }))
  ^ ")" end
let compare = compare
let indexToString = indexToString end
