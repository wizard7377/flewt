
module type HEURISTIC  =
  sig
    type nonrec index =
      <
        sd: int
          (* 0 = non-recursive
					   1 = recursive *)(* maximal number of cases *)
          (* Number of cases *)(* Induction variable *)
          (* Splitting depth *) ;ind: int option  ;c: int  ;
        m: int  ;r: int  ;p: int   > 
    val compare : index -> index -> order
    val indexToString : index -> string
  end;;




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
    let rec compare __0__ __1__ =
      match (__0__, __1__) with
      | ({ sd = k1; ind = None; c = c1; m = m1; r = r1; p = p1; ind = None;
           c = c1; m = m1; r = r1; p = p1; c = c1; m = m1; r = r1; p = p1;
           m = m1; r = r1; p = p1; r = r1; p = p1; p = p1 },
         { sd = k2; ind = None; c = c2; m = m2; r = r2; p = p2; ind = None;
           c = c2; m = m2; r = r2; p = p2; c = c2; m = m2; r = r2; p = p2;
           m = m2; r = r2; p = p2; r = r2; p = p2; p = p2 })
          ->
          (match ((Int.compare ((c1 * m2), (c2 * m1))),
                   (Int.compare (k2, k1)), (Int.compare (r1, r2)),
                   (Int.compare (p1, p2)))
           with
           | (EQUAL, EQUAL, EQUAL, result) -> result
           | (EQUAL, EQUAL, result, _) -> result
           | (EQUAL, result, _, _) -> result
           | (result, _, _, _) -> result)
      | ({ sd = k1; ind = None; c = c1; m = m1; r = r1; p = p1; ind = None;
           c = c1; m = m1; r = r1; p = p1; c = c1; m = m1; r = r1; p = p1;
           m = m1; r = r1; p = p1; r = r1; p = p1; p = p1 },
         { sd = k2; ind = Some i2; c = c2; m = m2; r = r2; p = p2;
           ind = Some i2; c = c2; m = m2; r = r2; p = p2; c = c2; m = m2;
           r = r2; p = p2; m = m2; r = r2; p = p2; r = r2; p = p2; p = p2 })
          ->
          (match Int.compare ((c1 * m2), (c2 * m1)) with
           | LESS -> LESS
           | EQUAL -> GREATER
           | GREATER -> GREATER)
      | ({ sd = k1; ind = Some i1; c = c1; m = m1; r = r1; p = p1;
           ind = Some i1; c = c1; m = m1; r = r1; p = p1; c = c1; m = m1;
           r = r1; p = p1; m = m1; r = r1; p = p1; r = r1; p = p1; p = p1 },
         { sd = k2; ind = None; c = c2; m = m2; r = r2; p = p2; ind = None;
           c = c2; m = m2; r = r2; p = p2; c = c2; m = m2; r = r2; p = p2;
           m = m2; r = r2; p = p2; r = r2; p = p2; p = p2 })
          ->
          (match Int.compare ((c1 * m2), (c2 * m1)) with
           | LESS -> LESS
           | EQUAL -> LESS
           | GREATER -> GREATER)
      | ({ sd = k1; ind = Some i1; c = c1; m = m1; r = r1; p = p1;
           ind = Some i1; c = c1; m = m1; r = r1; p = p1; c = c1; m = m1;
           r = r1; p = p1; m = m1; r = r1; p = p1; r = r1; p = p1; p = p1 },
         { sd = k2; ind = Some i2; c = c2; m = m2; r = r2; p = p2;
           ind = Some i2; c = c2; m = m2; r = r2; p = p2; c = c2; m = m2;
           r = r2; p = p2; m = m2; r = r2; p = p2; r = r2; p = p2; p = p2 })
          ->
          (match ((Int.compare ((c1 * m2), (c2 * m1))),
                   (Int.compare (k2, k1)), (Int.compare (r1, r2)),
                   (Int.compare (i1, i2)), (Int.compare (p1, p2)))
           with
           | (EQUAL, EQUAL, EQUAL, EQUAL, result) -> result
           | (EQUAL, EQUAL, EQUAL, result, _) -> result
           | (EQUAL, EQUAL, result, _, _) -> result
           | (EQUAL, result, _, _, _) -> result
           | (result, _, _, _, _) -> result)
    let rec recToString = function | 0 -> "non-rec" | 1 -> "rec"
    let rec realFmt r = Real.fmt (StringCvt.FIX (Some 2)) r
    let rec ratio c m = (Real.fromInt c) / (Real.fromInt m)
    let rec sum =
      function
      | { sd = k1; ind = None; c = c1; m = m1; r = r1; p = p1; ind = None;
          c = c1; m = m1; r = r1; p = p1; c = c1; m = m1; r = r1; p = p1;
          m = m1; r = r1; p = p1; r = r1; p = p1; p = p1 } ->
          realFmt
            (((+) (Real.fromInt k1) ratio (m1, c1)) + (Real.fromInt r1))
      | { sd = k1; ind = Some i1; c = c1; m = m1; r = r1; p = p1;
          ind = Some i1; c = c1; m = m1; r = r1; p = p1; c = c1; m = m1;
          r = r1; p = p1; m = m1; r = r1; p = p1; r = r1; p = p1; p = p1 } ->
          realFmt
            (((+) ((+) (Real.fromInt k1) ratio (1, i1)) ratio (m1, c1)) +
               (Real.fromInt r1))
    let rec indexToString =
      function
      | { sd = s1; ind = None; c = c1; m = m1; r = r1; p = p1; ind = None;
          c = c1; m = m1; r = r1; p = p1; c = c1; m = m1; r = r1; p = p1;
          m = m1; r = r1; p = p1; r = r1; p = p1; p = p1 } ->
          ((((((((((((("(c/m=" ^ (Int.toString c1)) ^ "/") ^
                       (Int.toString m1))
                      ^ "=")
                     ^ (realFmt (ratio (c1, m1))))
                    ^ ", ind=., sd=")
                   ^ (Int.toString s1))
                  ^ ", ")
                 ^ (recToString r1))
                ^ ", p=")
               ^ (Int.toString p1))
              ^ "sum = ")
             ^ (sum { sd = s1; ind = None; c = c1; m = m1; r = r1; p = p1 }))
            ^ " )"
      | { sd = s1; ind = Some idx; c = c1; m = m1; r = r1; p = p1;
          ind = Some idx; c = c1; m = m1; r = r1; p = p1; c = c1; m = m1;
          r = r1; p = p1; m = m1; r = r1; p = p1; r = r1; p = p1; p = p1 } ->
          ((((((((((((((("(c/m=" ^ (Int.toString c1)) ^ "/") ^
                         (Int.toString m1))
                        ^ "=")
                       ^ (realFmt (ratio (c1, m1))))
                      ^ ", ind=")
                     ^ (Int.toString idx))
                    ^ ", sd=")
                   ^ (Int.toString s1))
                  ^ ", ")
                 ^ (recToString r1))
                ^ ", p=")
               ^ (Int.toString p1))
              ^ " sum = ")
             ^
             (sum
                { sd = s1; ind = (Some idx); c = c1; m = m1; r = r1; p = p1 }))
            ^ ")"
    let compare = compare
    let indexToString = indexToString
  end ;;
