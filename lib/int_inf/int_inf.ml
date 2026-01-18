
(* int-inf.sml
 *
 * COPYRIGHT (c) 1995 by AT&T Bell Laboratories. See COPYRIGHT file for details.
 *
 * This package is derived from Andrzej Filinski's bignum package.  It is versy
 * close to the definition of the optional IntInf structure in the SML'97 basis.
 * 
 * It is implemented almost totally on the abstraction presented by
 * the BigNat structure. The only concrete type information it assumes 
 * is that BigNat.bignat = 'a list and that BigNat.zero = [].
 * Some trivial additional efficiency could be obtained by assuming that
 * type bignat is really int list, and that if (v : bignat) = [d], then
 * bignat d = [d].
 *
 * At some point, this should be reimplemented to make use of Word32, or
 * have compiler/runtime support.
 *
 * Also, for booting, this module could be broken into one that has
 * all the types and arithmetic functions, but doesn't use NumScan,
 * constructing values from strings using bignum arithmetic. Various
 * integer and word scanning, such as NumScan, could then be constructed 
 * from IntInf. Finally, a user-level IntInf could be built by 
 * importing the basic IntInf, but replacing the scanning functions
 * by more efficient ones based on the functions in NumScan.
 *
 *)
open Base
open Basis 
open Int_inf_sig
module IntInf : INT_INF =
  struct
    (* It is not clear what advantage there is to having NumFormat as
   * a submodule.
   *)
    module NumScan :
      sig
        val skipWS : (char, 'a) StringCvt.reader -> 'a -> 'a
        val scanWord :
          StringCvt.radix ->
            (char, 'a) StringCvt.reader -> 'a -> (Int32.t * 'a) option
        val scanInt :
          StringCvt.radix ->
            (char, 'a) StringCvt.reader -> 'a -> (int * 'a) option
      end =
      struct
        (** should be to int32 **)
        module W = Int32
        module I = Int31
        let (<) = W.(<)
        let (>=) = W.(>=)
        let (+) = W.(+)
        let (-) = W.(-)
        let ( * ) = W.( * )
        let (largestWordDiv10 : Int64.t) = Int64.of_int 429496729
        (* 2^32-1 divided by 10 *)
        let (largestWordMod10 : Int64.t) = Int64.of_int 5
        (* remainder *)
        let (largestNegInt : Int64.t) = Int64.of_int 1073741824
        (* absolute value of ~2^30 *)
        let (largestPosInt : Int32.t) = Int32.of_int 1073741823
        (* 2^30-1 *)
        type nonrec 'a chr_strm = < getc: (char, 'a) StringCvt.reader   > 
        (* A table for mapping digits to values.  Whitespace characters map to
       * 128, "+" maps to 129, "-","~" map to 130, "." maps to 131, and the
       * characters 0-9,A-Z,a-z map to their * base-36 value.  All other
       * characters map to 255.
       *)
        let cvtTable =
          "\255\255\255\255\255\255\255\255\255\128\128\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\128\255\255\255\255\255\255\255\255\255\255\129\255\130\131\255\000\001\002\003\004\005\006\007\b\t\255\255\255\255\255\255\255\n\011\012\r\014\015\016\017\018\019\020\021\022\023\024\025\026\027\028\029\030\031 !\"#\255\255\255\255\255\255\n\011\012\r\014\015\016\017\018\019\020\021\022\023\024\025\026\027\028\029\030\031 !\"#\255\255\255\130\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255"
        let ord = Char.ord
        let rec code (c : char) =
          W.fromInt (ord (CharVector.sub (cvtTable, (ord c))))
        let (wsCode : Int32.t) = Int32.of_int 128
        let (plusCode : Int32.t) = Int32.of_int 129
        let (minusCode : Int32.t) = Int32.of_int 130
        (* local *)
        let rec skipWS (getc : (char, 'a) StringCvt.reader) cs =
          let rec skip cs =
            ((match getc cs with
              | NONE -> cs
              | SOME (c, cs') -> if (code c) = wsCode then skip cs' else cs)
            (* end case *)) in
          skip cs
        (* skip leading whitespace and any sign (+, -, or ~) *)
        let rec scanPrefix (getc : (char, 'a) StringCvt.reader) cs =
          let rec skipWS cs =
            ((match getc cs with
              | NONE -> NONE
              | SOME (c, cs') ->
                  let c' = code c in
                  if c' = wsCode then skipWS cs' else SOME (c', cs'))
            (* end case *)) in
          let rec getNext (neg, cs) =
            ((match getc cs with
              | NONE -> NONE
              | SOME (c, cs) -> SOME { neg; next = (code c); rest = cs })
            (* end case *)) in
          ((match skipWS cs with
            | NONE -> NONE
            | SOME (c, cs') ->
                if c = plusCode
                then getNext (false__, cs')
                else
                  if c = minusCode
                  then getNext (true__, cs')
                  else SOME { neg = false__; next = c; rest = cs' })
            (* end case *))
        (* for power of 2 bases (2, 8 & 16), we can check for overflow by looking
       * at the hi (1, 3 or 4) bits.
       *)
        let rec chkOverflow mask w =
          if (W.andb (mask, w)) = 0w0 then () else raise Overflow
        let rec scanBin (getc : (char, 'a) StringCvt.reader) cs =
          ((match scanPrefix getc cs with
            | NONE -> NONE
            | SOME { neg; next; rest; next; rest; rest } ->
                let rec isDigit (d : Int32.t) = d < 0w2 in
                let chkOverflow = chkOverflow 0x80000000 in
                let rec cvt (w, rest) =
                  ((match getc rest with
                    | NONE -> SOME { neg; word = w; rest }
                    | SOME (c, rest') ->
                        let d = code c in
                        if isDigit d
                        then
                          (chkOverflow w;
                           cvt ((W.(+) ((W.(<<) (w, 0w1)), d)), rest'))
                        else SOME { neg; word = w; rest })
                  (* end case *)) in
                if isDigit next then cvt (next, rest) else NONE)
          (* end case *))
        let rec scanOct getc cs =
          ((match scanPrefix getc cs with
            | NONE -> NONE
            | SOME { neg; next; rest; next; rest; rest } ->
                let rec isDigit (d : Int32.t) = d < 0w8 in
                let chkOverflow = chkOverflow 0xE0000000 in
                let rec cvt (w, rest) =
                  ((match getc rest with
                    | NONE -> SOME { neg; word = w; rest }
                    | SOME (c, rest') ->
                        let d = code c in
                        if isDigit d
                        then
                          (chkOverflow w;
                           cvt ((W.(+) ((W.(<<) (w, 0w3)), d)), rest'))
                        else SOME { neg; word = w; rest })
                  (* end case *)) in
                if isDigit next then cvt (next, rest) else NONE)
          (* end case *))
        let rec scanDec getc cs =
          ((match scanPrefix getc cs with
            | NONE -> NONE
            | SOME { neg; next; rest; next; rest; rest } ->
                let rec isDigit (d : Int32.t) = d < 0w10 in
                let rec cvt (w, rest) =
                  ((match getc rest with
                    | NONE -> SOME { neg; word = w; rest }
                    | SOME (c, rest') ->
                        let d = code c in
                        if isDigit d
                        then
                          (if
                             (w >= largestWordDiv10) &&
                               ((largestWordDiv10 < w) ||
                                  (largestWordMod10 < d))
                           then raise Overflow
                           else ();
                           cvt (((0w10 * w) + d), rest'))
                        else SOME { neg; word = w; rest })
                  (* end case *)) in
                if isDigit next then cvt (next, rest) else NONE)
          (* end case *))
        let rec scanHex getc cs =
          ((match scanPrefix getc cs with
            | NONE -> NONE
            | SOME { neg; next; rest; next; rest; rest } ->
                let rec isDigit (d : Int32.t) = d < 0w16 in
                let chkOverflow = chkOverflow 0xF0000000 in
                let rec cvt (w, rest) =
                  ((match getc rest with
                    | NONE -> SOME { neg; word = w; rest }
                    | SOME (c, rest') ->
                        let d = code c in
                        if isDigit d
                        then
                          (chkOverflow w;
                           cvt ((W.(+) ((W.(<<) (w, 0w4)), d)), rest'))
                        else SOME { neg; word = w; rest })
                  (* end case *)) in
                if isDigit next then cvt (next, rest) else NONE)
          (* end case *))
        let rec finalWord scanFn getc cs =
          ((match scanFn getc cs with
            | NONE -> NONE
            | SOME { neg = true__ } -> NONE
            | SOME { neg = false__; word; rest; word; rest; rest } ->
                SOME (word, rest))
          (* end case *))
        let rec scanWord =
          function
          | StringCvt.BIN -> finalWord scanBin
          | StringCvt.OCT -> finalWord scanOct
          | StringCvt.DEC -> finalWord scanDec
          | StringCvt.HEX -> finalWord scanHex
        let rec finalInt scanFn getc cs =
          ((match scanFn getc cs with
            | NONE -> NONE
            | SOME { neg = true__; word; rest; word; rest; rest } ->
                if largestNegInt < word
                then raise Overflow
                else SOME ((I.(~) (W.toInt word)), rest)
            | SOME { word; rest; rest } ->
                if largestPosInt < word
                then raise Overflow
                else SOME ((W.toInt word), rest))
          (* end case *))
        let rec scanInt =
          function
          | StringCvt.BIN -> finalInt scanBin
          | StringCvt.OCT -> finalInt scanOct
          | StringCvt.DEC -> finalInt scanDec
          | StringCvt.HEX -> finalInt scanHex
      end 
    (* structure NumScan *)
    module NumFormat :
      sig
        val fmtWord : StringCvt.radix -> Int32.t -> string
        val fmtInt : StringCvt.radix -> int -> string
      end =
      struct
        (** should be int32 **)
        module W = Word32
        module I = Int
        let (<) = W.(<)
        let (-) = W.(-)
        let ( * ) = W.( * )
        let div = W.div
        let rec mkDigit (w : Int32.t) =
          CharVector.sub ("0123456789abcdef", (W.toInt w))
        let rec wordToBin w =
          let rec mkBit w = if (W.andb (w, 0w1)) = 0w0 then '0' else '1' in
          let rec f =
            function
            | (0w0, n, l) -> ((I.(+) (n, 1)), ('0' :: l))
            | (0w1, n, l) -> ((I.(+) (n, 1)), ('1' :: l))
            | (w, n, l) ->
                f ((W.(>>) (w, 0w1)), (I.(+) (n, 1)), ((mkBit w) :: l)) in
          f (w, 0, [])
        let rec wordToOct w =
          let rec f (w, n, l) =
            if w < 0w8
            then ((I.(+) (n, 1)), ((mkDigit w) :: l))
            else
              f
                ((W.(>>) (w, 0w3)), (I.(+) (n, 1)),
                  ((mkDigit (W.andb (w, 0w7))) :: l)) in
          f (w, 0, [])
        let rec wordToDec w =
          let rec f (w, n, l) =
            if w < 0w10
            then ((I.(+) (n, 1)), ((mkDigit w) :: l))
            else
              (let j = w div 0w10 in
               f (j, (I.(+) (n, 1)), ((mkDigit ((w - 0w10) * j)) :: l))) in
          f (w, 0, [])
        let rec wordToHex w =
          let rec f (w, n, l) =
            if w < 0w16
            then ((I.(+) (n, 1)), ((mkDigit w) :: l))
            else
              f
                ((W.(>>) (w, 0w4)), (I.(+) (n, 1)),
                  ((mkDigit (W.andb (w, 0w15))) :: l)) in
          f (w, 0, [])
        let rec fmtW =
          function
          | StringCvt.BIN -> ((fun r -> r.2)) o wordToBin
          | StringCvt.OCT -> ((fun r -> r.2)) o wordToOct
          | StringCvt.DEC -> ((fun r -> r.2)) o wordToDec
          | StringCvt.HEX -> ((fun r -> r.2)) o wordToHex
        let rec fmtWord radix = String.implode o (fmtW radix)
        (** NOTE: this currently uses 31-bit integers, but really should use 32-bit
     ** ints (once they are supported).
     **)
        let rec fmtInt radix =
          let fmtW = fmtW radix in
          let itow = W.fromInt in
          let rec fmt i =
            if I.(<) (i, 0)
            then
              try
                let digits = fmtW (itow (I.(~) i)) in
                String.implode ('~' :: digits)
              with
              | _ ->
                  (((match radix with
                     | StringCvt.BIN -> "~1111111111111111111111111111111"
                     | StringCvt.OCT -> "~7777777777"
                     | StringCvt.DEC -> "~1073741824"
                     | StringCvt.HEX -> "~3fffffff"))
                  (* end case *))
            else String.implode (fmtW (itow i)) in
          fmt
      end 
    (* structure NumFormat *)
    module BigNat =
      struct
        exception Negative 
        let itow = Word.fromInt
        let wtoi = Word.toIntX
        let lgBase = 30
        (* No. of bits per digit; must be even *)
        let nbase = ~0x40000000
        (* = ~2^lgBase *)
        let maxDigit = ~ (nbase + 1)
        let realBase = (real maxDigit) + 1.0
        let lgHBase = Int.quot (lgBase, 2)
        (* half digits *)
        let hbase = Word.(<<) (0w1, (itow lgHBase))
        let hmask = hbase - 0w1
        let rec quotrem (i, j) = ((Int.quot (i, j)), (Int.rem (i, j)))
        let rec scale i = if i = maxDigit then 1 else nbase div (~ (i + 1))
        type nonrec bignat = int list
        (* least significant digit first *)
        let zero = []
        let one = [1]
        let rec bignat =
          function
          | 0 -> zero
          | i ->
              let notNbase = Word.notb (itow nbase) in
              let rec bn =
                function
                | 0w0 -> []
                | i ->
                    let rec dmbase n =
                      ((Word.(>>) (n, (itow lgBase))),
                        (Word.andb (n, notNbase))) in
                    let (q, r) = dmbase i in (wtoi r) :: (bn q) in
              if i > 0
              then (if i <= maxDigit then [i] else bn (itow i))
              else raise Negative
        let rec int =
          function
          | [] -> 0
          | d::[] -> d
          | d::e::[] -> (~ (nbase * e)) + d
          | d::r -> (~ (( * ) nbase int r)) + d
        let rec consd = function | (0, []) -> [] | (d, r) -> d :: r
        let rec hl i =
          let w = itow i in
          ((((wtoi (Word.(~>>) (w, (itow lgHBase)))),
              (wtoi (Word.andb (w, hmask)))))
            (* MUST sign-extend *))
        let rec sh i = wtoi (Word.(<<) ((itow i), (itow lgHBase)))
        let rec addOne =
          function
          | [] -> [1]
          | m::rm ->
              let c = (nbase + m) + 1 in
              if c < 0 then (c - nbase) :: rm else c :: (addOne rm)
        let rec add =
          function
          | ([], digits) -> digits
          | (digits, []) -> digits
          | (dm::rm, dn::rn) -> addd (((nbase + dm) + dn), rm, rn)
        let rec addd (s, m, n) =
          if s < 0 then (::) (s - nbase) add (m, n) else (::) s addc (m, n)
        let rec addc =
          function
          | (m, []) -> addOne m
          | ([], n) -> addOne n
          | (dm::rm, dn::rn) -> addd ((((nbase + dm) + dn) + 1), rm, rn)
        let rec subtOne =
          function
          | 0::mr -> maxDigit :: (subtOne mr)
          | 1::[] -> []
          | n::mr -> (n - 1) :: mr
          | [] -> raise (Fail "")
        let rec subt =
          function
          | (m, []) -> m
          | ([], n) -> raise Negative
          | (dm::rm, dn::rn) -> subd ((dm - dn), rm, rn)
        let rec subb =
          function
          | ([], n) -> raise Negative
          | (dm::rm, []) -> subd ((dm - 1), rm, [])
          | (dm::rm, dn::rn) -> subd (((dm - dn) - 1), rm, rn)
        let rec subd (d, m, n) =
          if d >= 0
          then consd (d, (subt (m, n)))
          else consd ((d - nbase), (subb (m, n)))
        (* multiply 2 digits *)
        let rec mul2 (m, n) =
          let (mh, ml) = hl m in
          let (nh, nl) = hl n in
          let x = mh * nh in
          let y = (mh - ml) * (nh - nl) in
          let z = ml * nl in
          let (zh, zl) = hl z in
          let (uh, ul) = hl ((((nbase + x) + z) - y) + zh) in
          (((((+) (x + uh) wtoi hbase), ((sh ul) + zl)))
            (* x-y+z = mh*nl + ml*nh *)(* can't overflow *))
        (* multiply bigint by digit *)
        let rec muld =
          function
          | (m, 0) -> []
          | (m, 1) -> m
          | (m, i) ->
              let rec muldc =
                function
                | ([], 0) -> []
                | ([], c) -> [c]
                | (d::r, c) ->
                    let (h, l) = mul2 (d, i) in
                    let l1 = (l + nbase) + c in
                    if l1 >= 0
                    then (::) l1 muldc (r, (h + 1))
                    else (::) (l1 - nbase) muldc (r, h) in
              muldc (m, 0)(* speedup *)
        let rec mult =
          function
          | (m, []) -> []
          | (m, d::[]) -> muld (m, d)
          | (m, 0::r) -> consd (0, (mult (m, r)))
          | (m, n) ->
              let rec muln =
                function
                | [] -> []
                | d::r -> add ((muld (n, d)), (consd (0, (muln r)))) in
              muln m(* speedup *)(* speedup *)
        (* divide DP number by digit; assumes u < i , i >= base/2 *)
        let rec divmod2 ((u, v), i) =
          let (vh, vl) = hl v in
          let (ih, il) = hl i in
          let rec adj (q, r) =
            if r < 0 then adj ((q - 1), (r + i)) else (q, r) in
          let (q1, r1) = quotrem (u, ih) in
          let (q1, r1) = adj (q1, ((((sh r1) + vh) - q1) * il)) in
          let (q0, r0) = quotrem (r1, ih) in
          let (q0, r0) = adj (q0, ((((sh r0) + vl) - q0) * il)) in
          (((sh q1) + q0), r0)
        (* divide bignat by digit>0 *)
        let rec divmodd =
          function
          | (m, 1) -> (m, 0)
          | (m, i) ->
              let scale = scale i in
              let i' = i * scale in
              let m' = muld (m, scale) in
              let rec dmi =
                function
                | [] -> ([], 0)
                | d::r ->
                    let (qt, rm) = dmi r in
                    let (q1, r1) = divmod2 ((rm, d), i') in
                    ((consd (q1, qt)), r1) in
              let (q, r) = dmi m' in (q, (r div scale))(* speedup *)
        (* From Knuth Vol II, 4.3.1, but without opt. in step D3 *)
        let rec divmod =
          function
          | (m, []) -> raise Div
          | ([], n) -> ([], [])
          | (d::r, 0::s) ->
              let (qt, rm) = divmod (r, s) in (qt, (consd (d, rm)))
          | (m, d::[]) ->
              let (qt, rm) = divmodd (m, d) in
              (qt, (if rm = 0 then [] else [rm]))
          | (m, n) ->
              let ln = length n in
              let scale = scale (List.nth (n, (ln - 1))) in
              let m' = muld (m, scale) in
              let n' = muld (n, scale) in
              let n1 = List.nth (n', (ln - 1)) in
              let rec divl =
                function
                | [] -> ([], [])
                | d::r ->
                    let (qt, rm) = divl r in
                    let m = consd (d, rm) in
                    let rec msds =
                      function
                      | ([], _) -> (0, 0)
                      | (d::[], 1) -> (0, d)
                      | (d2::d1::[], 1) -> (d1, d2)
                      | (d::r, i) -> msds (r, (i - 1)) in
                    let (m1, m2) = msds (m, ln) in
                    let tq =
                      if m1 = n1
                      then maxDigit
                      else ((fun r -> r.1)) (divmod2 ((m1, m2), n1)) in
                    let rec try__ (q, qn') =
                      try (q, (subt (m, qn')))
                      with | Negative -> try__ ((q - 1), (subt (qn', n'))) in
                    let (q, rr) = try__ (tq, (muld (n', tq))) in
                    ((consd (q, qt)), rr) in
              let (qt, rm') = divl m' in
              let (((rm, _))(*0*)) = divmodd (rm', scale) in
              (((qt, rm))
                (* >= 2 *)(* >= base/2 *))
          (* speedup *)(* speedup *)
        let rec cmp =
          function
          | ([], []) -> EQUAL
          | (_, []) -> GREATER
          | ([], _) -> LESS
          | ((i : int)::ri, j::rj) ->
              (match cmp (ri, rj) with
               | EQUAL ->
                   if i = j then EQUAL else if i < j then LESS else GREATER
               | c -> c)
        let rec exp =
          function
          | (_, 0) -> one
          | ([], n) -> if n > 0 then zero else raise Div
          | (m, n) ->
              if n < 0
              then zero
              else
                (let rec expm =
                   function
                   | 0 -> [1]
                   | 1 -> m
                   | i ->
                       let r = expm (i div 2) in
                       let r2 = mult (r, r) in
                       if (i mod__ 2) = 0 then r2 else mult (r2, m) in
                 expm n)
        let rec try__ n = if n >= lgHBase then n else try__ (2 * n)
        let pow2lgHBase = try__ 1
        let rec log2 =
          function
          | [] -> raise Domain
          | h::t ->
              let rec qlog =
                function
                | (x, 0) -> 0
                | (x, b) ->
                    if (>=) x wtoi (Word.(<<) (0w1, (itow b)))
                    then
                      (+) b qlog
                        ((wtoi (Word.(>>) ((itow x), (itow b)))), (b div 2))
                    else qlog (x, (b div 2)) in
              let rec loop =
                function
                | (d, [], lg) -> (+) lg qlog (d, pow2lgHBase)
                | (_, h::t, lg) -> loop (h, t, (lg + lgBase)) in
              loop (h, t, 0)
        (* local *)
        (* find maximal maxpow s.t. radix^maxpow < base 
             * basepow = radix^maxpow
             *)
        let rec mkPowers radix =
          let powers =
            let bnd = Int.quot (nbase, (~ radix)) in
            let rec try__ (tp, l) =
              try
                if tp <= bnd
                then try__ ((radix * tp), (tp :: l))
                else tp :: l
              with | _ -> tp :: l in
            Vector.fromList (rev (try__ (radix, [1]))) in
          let maxpow = (Vector.length powers) - 1 in
          (maxpow, (Vector.sub (powers, maxpow)), powers)
        let powers2 = mkPowers 2
        let powers8 = mkPowers 8
        let powers10 = mkPowers 10
        let powers16 = mkPowers 16
        let rec fmt (pow, radpow, puti) n =
          let pad = StringCvt.padLeft '0' pow in
          let rec ms0 =
            function
            | (0, a) -> (pad "") :: a
            | (i, a) -> (pad (puti i)) :: a in
          let rec ml (n, a) =
            match divmodd (n, radpow) with
            | ([], d) -> (puti d) :: a
            | (q, d) -> ml (q, (ms0 (d, a))) in
          concat (ml (n, []))
        let fmt2 =
          fmt
            (((fun r -> r.1) powers2), ((fun r -> r.2) powers2),
              (NumFormat.fmtInt StringCvt.BIN))
        let fmt8 =
          fmt
            (((fun r -> r.1) powers8), ((fun r -> r.2) powers8),
              (NumFormat.fmtInt StringCvt.OCT))
        let fmt10 =
          fmt
            (((fun r -> r.1) powers10), ((fun r -> r.2) powers10),
              (NumFormat.fmtInt StringCvt.DEC))
        let fmt16 =
          fmt
            (((fun r -> r.1) powers16), ((fun r -> r.2) powers16),
              (NumFormat.fmtInt StringCvt.HEX))
        let rec scan (bound, powers, geti) getc cs =
          let rec get (l, cs) =
            if l = bound
            then NONE
            else
              (match getc cs with
               | NONE -> NONE
               | SOME (c, cs') -> SOME (c, ((l + 1), cs'))) in
          let rec loop (acc, cs) =
            match geti get (0, cs) with
            | NONE -> (acc, cs)
            | SOME (0, (sh, cs')) ->
                loop
                  ((add ((muld (acc, (Vector.sub (powers, sh)))), [])), cs')
            | SOME (i, (sh, cs')) ->
                loop
                  ((add ((muld (acc, (Vector.sub (powers, sh)))), [i])), cs') in
          match geti get (0, cs) with
          | NONE -> NONE
          | SOME (0, (_, cs')) -> SOME (loop ([], cs'))
          | SOME (i, (_, cs')) -> SOME (loop ([i], cs'))
        let rec scan2 getc =
          scan
            (((fun r -> r.1) powers2), ((fun r -> r.3) powers2),
              (NumScan.scanInt StringCvt.BIN)) getc
        let rec scan8 getc =
          scan
            (((fun r -> r.1) powers8), ((fun r -> r.3) powers8),
              (NumScan.scanInt StringCvt.OCT)) getc
        let rec scan10 getc =
          scan
            (((fun r -> r.1) powers10), ((fun r -> r.3) powers10),
              (NumScan.scanInt StringCvt.DEC)) getc
        let rec scan16 getc =
          scan
            (((fun r -> r.1) powers16), ((fun r -> r.3) powers16),
              (NumScan.scanInt StringCvt.HEX)) getc
      end
    (* structure BigNat *)
    module BN = BigNat
    type sign =
      | POS 
      | NEG 
    type int =
      | BI of < sign: sign  ;digits: BN.bignat   >  
    let zero = BI { sign = POS; digits = BN.zero }
    let one = BI { sign = POS; digits = BN.one }
    let minus_one = BI { sign = NEG; digits = BN.one }
    let rec posi digits = BI { sign = POS; digits }
    let rec negi digits = BI { sign = NEG; digits }
    let rec zneg =
      function | [] -> zero | digits -> BI { sign = NEG; digits }
    let minNeg = valOf Int.minInt
    let bigNatMinNeg = BN.addOne (BN.bignat (~- (minNeg + 1)))
    let bigIntMinNeg = negi bigNatMinNeg
    let rec toInt =
      function
      | BI { digits = [] } -> 0
      | BI { sign = POS; digits; digits } -> BN.int digits
      | BI { sign = NEG; digits; digits } ->
          (try ~- (BN.int digits)
           with
           | _ -> if digits = bigNatMinNeg then minNeg else raise Overflow)
    let rec fromInt =
      function
      | 0 -> zero
      | i ->
          if i < 0
          then
            (if i = minNeg
             then bigIntMinNeg
             else BI { sign = NEG; digits = (BN.bignat (~ i)) })
          else BI { sign = POS; digits = (BN.bignat i) }
    (* local *)
    (* The following assumes LargeInt = Int32.
       * If IntInf is provided, it will be LargeInt and toLarge and fromLarge
       * will be the identity function.
       *)
    let minNeg = valOf LargeInt.minInt
    let maxDigit = LargeInt.fromInt BN.maxDigit
    let nbase = LargeInt.fromInt BN.nbase
    let lgBase = Word.fromInt BN.lgBase
    let notNbase = Word32.notb (Word32.fromInt BN.nbase)
    let rec largeNat =
      function
      | (0 : LargeInt.int) -> []
      | i ->
          let rec bn =
            function
            | (0w0 : Int32.t) -> []
            | i ->
                let rec dmbase n =
                  ((Word32.(>>) (n, lgBase)), (Word32.andb (n, notNbase))) in
                let (q, r) = dmbase i in (Word32.toInt r) :: (bn q) in
          if i <= maxDigit
          then [LargeInt.toInt i]
          else bn (Word32.fromLargeInt i)
    let rec large =
      function
      | [] -> 0
      | d::[] -> LargeInt.fromInt d
      | d::e::[] -> (~- (nbase * (LargeInt.fromInt e))) + (LargeInt.fromInt d)
      | d::r -> (~- (( * ) nbase large r)) + (LargeInt.fromInt d)
    let bigNatMinNeg = BN.addOne (largeNat (~ (minNeg + 1)))
    let bigIntMinNeg = negi bigNatMinNeg
    let rec toLarge =
      function
      | BI { digits = [] } -> 0
      | BI { sign = POS; digits; digits } -> large digits
      | BI { sign = NEG; digits; digits } ->
          (try ~- (large digits)
           with
           | _ -> if digits = bigNatMinNeg then minNeg else raise Overflow)
    let rec fromLarge =
      function
      | 0 -> zero
      | i ->
          if i < 0
          then
            (if i = minNeg
             then bigIntMinNeg
             else BI { sign = NEG; digits = (largeNat (~ i)) })
          else BI { sign = POS; digits = (largeNat i) }
    (* local *)
    let rec negSign = function | POS -> NEG | NEG -> POS
    let rec subtNat =
      function
      | (m, []) -> { sign = POS; digits = m }
      | ([], n) -> { sign = NEG; digits = n }
      | (m, n) ->
          (try { sign = POS; digits = (BN.subt (m, n)) }
           with | BN.Negative -> { sign = NEG; digits = (BN.subt (n, m)) })
    let precision = NONE
    let minInt = NONE
    let maxInt = NONE
    let rec (~) =
      function
      | BI { digits = [] } as i -> i
      | BI { sign = POS; digits; digits } -> BI { sign = NEG; digits }
      | BI { sign = NEG; digits; digits } -> BI { sign = POS; digits }
    let rec ( * ) =
      function
      | (_, BI { digits = [] }) -> zero
      | (BI { digits = [] }, _) -> zero
      | (BI { sign = POS; digits = d1; digits = d1 }, BI
         { sign = NEG; digits = d2; digits = d2 }) ->
          BI { sign = NEG; digits = (BN.mult (d1, d2)) }
      | (BI { sign = NEG; digits = d1; digits = d1 }, BI
         { sign = POS; digits = d2; digits = d2 }) ->
          BI { sign = NEG; digits = (BN.mult (d1, d2)) }
      | (BI { digits = d1 }, BI { digits = d2 }) ->
          BI { sign = POS; digits = (BN.mult (d1, d2)) }
    let rec (+) =
      function
      | (BI { digits = [] }, i2) -> i2
      | (i1, BI { digits = [] }) -> i1
      | (BI { sign = POS; digits = d1; digits = d1 }, BI
         { sign = NEG; digits = d2; digits = d2 }) -> BI (subtNat (d1, d2))
      | (BI { sign = NEG; digits = d1; digits = d1 }, BI
         { sign = POS; digits = d2; digits = d2 }) -> BI (subtNat (d2, d1))
      | (BI { sign; digits = d1; digits = d1 }, BI { digits = d2 }) ->
          BI { sign; digits = (BN.add (d1, d2)) }
    let rec (-) =
      function
      | (i1, BI { digits = [] }) -> i1
      | (BI { digits = [] }, BI { sign; digits; digits }) ->
          BI { sign = (negSign sign); digits }
      | (BI { sign = POS; digits = d1; digits = d1 }, BI
         { sign = POS; digits = d2; digits = d2 }) -> BI (subtNat (d1, d2))
      | (BI { sign = NEG; digits = d1; digits = d1 }, BI
         { sign = NEG; digits = d2; digits = d2 }) -> BI (subtNat (d2, d1))
      | (BI { sign; digits = d1; digits = d1 }, BI { digits = d2 }) ->
          BI { sign; digits = (BN.add (d1, d2)) }
    let rec quotrem =
      function
      | (BI { sign = POS; digits = m; digits = m }, BI
         { sign = POS; digits = n; digits = n }) ->
          (match BN.divmod (m, n) with | (q, r) -> ((posi q), (posi r)))
      | (BI { sign = POS; digits = m; digits = m }, BI
         { sign = NEG; digits = n; digits = n }) ->
          (match BN.divmod (m, n) with | (q, r) -> ((zneg q), (posi r)))
      | (BI { sign = NEG; digits = m; digits = m }, BI
         { sign = POS; digits = n; digits = n }) ->
          (match BN.divmod (m, n) with | (q, r) -> ((zneg q), (zneg r)))
      | (BI { sign = NEG; digits = m; digits = m }, BI
         { sign = NEG; digits = n; digits = n }) ->
          (match BN.divmod (m, n) with | (q, r) -> ((posi q), (zneg r)))
    let rec divmod =
      function
      | (BI { sign = POS; digits = m; digits = m }, BI
         { sign = POS; digits = n; digits = n }) ->
          (match BN.divmod (m, n) with | (q, r) -> ((posi q), (posi r)))
      | (BI { sign = POS; digits = []; digits = [] }, BI
         { sign = NEG; digits = n; digits = n }) -> (zero, zero)
      | (BI { sign = POS; digits = m; digits = m }, BI
         { sign = NEG; digits = n; digits = n }) ->
          let (q, r) = BN.divmod ((BN.subtOne m), n) in
          ((negi (BN.addOne q)), (zneg (BN.subtOne (BN.subt (n, r)))))
      | (BI { sign = NEG; digits = m; digits = m }, BI
         { sign = POS; digits = n; digits = n }) ->
          let (q, r) = BN.divmod ((BN.subtOne m), n) in
          ((negi (BN.addOne q)), (posi (BN.subtOne (BN.subt (n, r)))))
      | (BI { sign = NEG; digits = m; digits = m }, BI
         { sign = NEG; digits = n; digits = n }) ->
          (match BN.divmod (m, n) with | (q, r) -> ((posi q), (zneg r)))
    let rec div arg = (fun r -> r.1) (divmod arg)
    let rec mod__ arg = (fun r -> r.2) (divmod arg)
    let rec quot arg = (fun r -> r.1) (quotrem arg)
    let rec rem arg = (fun r -> r.2) (quotrem arg)
    let rec compare =
      function
      | (BI { sign = NEG }, BI { sign = POS }) -> LESS
      | (BI { sign = POS }, BI { sign = NEG }) -> GREATER
      | (BI { sign = POS; digits = d; digits = d }, BI
         { sign = POS; digits = d'; digits = d' }) -> BN.cmp (d, d')
      | (BI { sign = NEG; digits = d; digits = d }, BI
         { sign = NEG; digits = d'; digits = d' }) -> BN.cmp (d', d)
    let rec (<) arg = match compare arg with | LESS -> true__ | _ -> false__
    let rec (>) arg =
      match compare arg with | GREATER -> true__ | _ -> false__
    let rec (<=) arg =
      match compare arg with | GREATER -> false__ | _ -> true__
    let rec (>=) arg = match compare arg with | LESS -> false__ | _ -> true__
    let rec abs =
      function
      | BI { sign = NEG; digits; digits } -> BI { sign = POS; digits }
      | i -> i
    let rec max arg =
      match compare arg with
      | GREATER -> ((fun r -> r.1)) arg
      | _ -> ((fun r -> r.2)) arg
    let rec min arg =
      match compare arg with
      | LESS -> ((fun r -> r.1)) arg
      | _ -> ((fun r -> r.2)) arg
    let rec sign =
      function | BI { sign = NEG } -> (-1) | BI { digits = [] } -> 0 | _ -> 1
    let rec sameSign (i, j) = (=) (sign i) sign j
    let rec fmt' fmtFn i =
      match i with
      | BI { digits = [] } -> "0"
      | BI { sign = NEG; digits; digits } -> "~" ^ (fmtFn digits)
      | BI { sign = POS; digits; digits } -> fmtFn digits
    let rec fmt =
      function
      | StringCvt.BIN -> fmt' BN.fmt2
      | StringCvt.OCT -> fmt' BN.fmt8
      | StringCvt.DEC -> fmt' BN.fmt10
      | StringCvt.HEX -> fmt' BN.fmt16
    let toString = fmt StringCvt.DEC
    let rec scan' scanFn getc cs =
      let cs' = NumScan.skipWS getc cs in
      let rec cvt =
        function
        | (NONE, _) -> NONE
        | (SOME (i, cs), wr) -> SOME ((wr i), cs) in
      match getc cs' with
      | SOME ('~', cs'') -> cvt ((scanFn getc cs''), zneg)
      | SOME ('-', cs'') -> cvt ((scanFn getc cs''), zneg)
      | SOME ('+', cs'') -> cvt ((scanFn getc cs''), posi)
      | SOME _ -> cvt ((scanFn getc cs'), posi)
      | NONE -> NONE
    (* end case *)
    let rec scan =
      function
      | StringCvt.BIN -> scan' BN.scan2
      | StringCvt.OCT -> scan' BN.scan8
      | StringCvt.DEC -> scan' BN.scan10
      | StringCvt.HEX -> scan' BN.scan16
    let rec fromString s = StringCvt.scanString (scan StringCvt.DEC) s
    let rec pow =
      function
      | (_, 0) -> one
      | (BI { sign = POS; digits; digits }, n) -> posi (BN.exp (digits, n))
      | (BI { sign = NEG; digits; digits }, n) ->
          if (Int.mod__ (n, 2)) = 0
          then posi (BN.exp (digits, n))
          else zneg (BN.exp (digits, n))
    let rec log2 =
      function
      | BI { sign = POS; digits; digits } -> BN.log2 digits
      | _ -> raise Domain
  end ;;
