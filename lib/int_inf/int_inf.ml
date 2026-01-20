
module IntInf : INT_INF =
  struct
    module NumScan :
      sig
        val skipWS : (char, 'a) StringCvt.reader -> 'a -> 'a
        val scanWord :
          StringCvt.radix ->
            (char, 'a) StringCvt.reader -> 'a -> (Word32.word * 'a) option
        val scanInt :
          StringCvt.radix ->
            (char, 'a) StringCvt.reader -> 'a -> (int * 'a) option
      end =
      struct
        module W = Word32
        module I = Int31
        let (<) = W.(<)
        let (>=) = W.(>=)
        let (+) = W.(+)
        let (-) = W.(-)
        let ( * ) = W.( * )
        let (largestWordDiv10 : Word32.word) = 0w429496729
        let (largestWordMod10 : Word32.word) = 0w5
        let (largestNegInt : Word32.word) = 0w1073741824
        let (largestPosInt : Word32.word) = 0w1073741823
        type nonrec 'a chr_strm = < getc: (char, 'a) StringCvt.reader   > 
        let cvtTable =
          "\255\255\255\255\255\255\255\255\255\128\128\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\128\255\255\255\255\255\255\255\255\255\255\129\255\130\131\255\000\001\002\003\004\005\006\007\b\t\255\255\255\255\255\255\255\n\011\012\r\014\015\016\017\018\019\020\021\022\023\024\025\026\027\028\029\030\031 !\"#\255\255\255\255\255\255\n\011\012\r\014\015\016\017\018\019\020\021\022\023\024\025\026\027\028\029\030\031 !\"#\255\255\255\130\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255"
        let ord = Char.ord
        let rec code c = W.fromInt (ord (CharVector.sub (cvtTable, (ord c))))
        let (wsCode : Word32.word) = 0w128
        let (plusCode : Word32.word) = 0w129
        let (minusCode : Word32.word) = 0w130
        let rec skipWS getc cs =
          let rec skip cs =
            ((match getc cs with
              | None -> cs
              | Some (c, cs') -> if (code c) = wsCode then skip cs' else cs)
            (* end case *)) in
          skip cs
        let rec scanPrefix getc cs =
          let rec skipWS cs =
            ((match getc cs with
              | None -> None
              | Some (c, cs') ->
                  let c' = code c in
                  if c' = wsCode then skipWS cs' else Some (c', cs'))
            (* end case *)) in
          let rec getNext neg cs =
            ((match getc cs with
              | None -> None
              | Some (c, cs) -> Some { neg; next = (code c); rest = cs })
            (* end case *)) in
          ((match skipWS cs with
            | None -> None
            | Some (c, cs') ->
                if c = plusCode
                then getNext (false, cs')
                else
                  if c = minusCode
                  then getNext (true, cs')
                  else Some { neg = false; next = c; rest = cs' })
            (* end case *))
        let rec chkOverflow mask w =
          if (W.andb (mask, w)) = 0w0 then () else raise Overflow
        let rec scanBin getc cs =
          ((match scanPrefix getc cs with
            | None -> None
            | Some { neg; next; rest; next; rest; rest } ->
                let rec isDigit d = d < 0w2 in
                let chkOverflow = chkOverflow 0x80000000 in
                let rec cvt w rest =
                  ((match getc rest with
                    | None -> Some { neg; word = w; rest }
                    | Some (c, rest') ->
                        let d = code c in
                        if isDigit d
                        then
                          (chkOverflow w;
                           cvt ((W.(+) ((W.(<<) (w, 0w1)), d)), rest'))
                        else Some { neg; word = w; rest })
                  (* end case *)) in
                if isDigit next then cvt (next, rest) else None)
          (* end case *))
        let rec scanOct getc cs =
          ((match scanPrefix getc cs with
            | None -> None
            | Some { neg; next; rest; next; rest; rest } ->
                let rec isDigit d = d < 0w8 in
                let chkOverflow = chkOverflow 0xE0000000 in
                let rec cvt w rest =
                  ((match getc rest with
                    | None -> Some { neg; word = w; rest }
                    | Some (c, rest') ->
                        let d = code c in
                        if isDigit d
                        then
                          (chkOverflow w;
                           cvt ((W.(+) ((W.(<<) (w, 0w3)), d)), rest'))
                        else Some { neg; word = w; rest })
                  (* end case *)) in
                if isDigit next then cvt (next, rest) else None)
          (* end case *))
        let rec scanDec getc cs =
          ((match scanPrefix getc cs with
            | None -> None
            | Some { neg; next; rest; next; rest; rest } ->
                let rec isDigit d = d < 0w10 in
                let rec cvt w rest =
                  ((match getc rest with
                    | None -> Some { neg; word = w; rest }
                    | Some (c, rest') ->
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
                        else Some { neg; word = w; rest })
                  (* end case *)) in
                if isDigit next then cvt (next, rest) else None)
          (* end case *))
        let rec scanHex getc cs =
          ((match scanPrefix getc cs with
            | None -> None
            | Some { neg; next; rest; next; rest; rest } ->
                let rec isDigit d = d < 0w16 in
                let chkOverflow = chkOverflow 0xF0000000 in
                let rec cvt w rest =
                  ((match getc rest with
                    | None -> Some { neg; word = w; rest }
                    | Some (c, rest') ->
                        let d = code c in
                        if isDigit d
                        then
                          (chkOverflow w;
                           cvt ((W.(+) ((W.(<<) (w, 0w4)), d)), rest'))
                        else Some { neg; word = w; rest })
                  (* end case *)) in
                if isDigit next then cvt (next, rest) else None)
          (* end case *))
        let rec finalWord scanFn getc cs =
          ((match scanFn getc cs with
            | None -> None
            | Some { neg = true } -> None
            | Some { neg = false; word; rest; word; rest; rest } ->
                Some (word, rest))
          (* end case *))
        let rec scanWord =
          function
          | StringCvt.BIN -> finalWord scanBin
          | StringCvt.OCT -> finalWord scanOct
          | StringCvt.DEC -> finalWord scanDec
          | StringCvt.HEX -> finalWord scanHex
        let rec finalInt scanFn getc cs =
          ((match scanFn getc cs with
            | None -> None
            | Some { neg = true; word; rest; word; rest; rest } ->
                if largestNegInt < word
                then raise Overflow
                else Some ((I.(~) (W.toInt word)), rest)
            | Some { word; rest; rest } ->
                if largestPosInt < word
                then raise Overflow
                else Some ((W.toInt word), rest))
          (* end case *))
        let rec scanInt =
          function
          | StringCvt.BIN -> finalInt scanBin
          | StringCvt.OCT -> finalInt scanOct
          | StringCvt.DEC -> finalInt scanDec
          | StringCvt.HEX -> finalInt scanHex
      end 
    module NumFormat :
      sig
        val fmtWord : StringCvt.radix -> Word32.word -> string
        val fmtInt : StringCvt.radix -> int -> string
      end =
      struct
        module W = Word32
        module I = Int
        let (<) = W.(<)
        let (-) = W.(-)
        let ( * ) = W.( * )
        let div = W.div
        let rec mkDigit w = CharVector.sub ("0123456789abcdef", (W.toInt w))
        let rec wordToBin w =
          let rec mkBit w = if (W.andb (w, 0w1)) = 0w0 then '0' else '1' in
          let rec f __0__ __1__ __2__ =
            match (__0__, __1__, __2__) with
            | (0w0, n, l) -> ((I.(+) (n, 1)), ('0' :: l))
            | (0w1, n, l) -> ((I.(+) (n, 1)), ('1' :: l))
            | (w, n, l) ->
                f ((W.(>>) (w, 0w1)), (I.(+) (n, 1)), ((mkBit w) :: l)) in
          f (w, 0, [])
        let rec wordToOct w =
          let rec f w n l =
            if w < 0w8
            then ((I.(+) (n, 1)), ((mkDigit w) :: l))
            else
              f
                ((W.(>>) (w, 0w3)), (I.(+) (n, 1)),
                  ((mkDigit (W.andb (w, 0w7))) :: l)) in
          f (w, 0, [])
        let rec wordToDec w =
          let rec f w n l =
            if w < 0w10
            then ((I.(+) (n, 1)), ((mkDigit w) :: l))
            else
              (let j = w div 0w10 in
               f (j, (I.(+) (n, 1)), ((mkDigit ((w - 0w10) * j)) :: l))) in
          f (w, 0, [])
        let rec wordToHex w =
          let rec f w n l =
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
    module BigNat =
      struct
        exception Negative 
        let itow = Word.fromInt
        let wtoi = Word.toIntX
        let lgBase = 30
        let nbase = ~0x40000000
        let maxDigit = ~ (nbase + 1)
        let realBase = (real maxDigit) + 1.0
        let lgHBase = Int.quot (lgBase, 2)
        let hbase = Word.(<<) (0w1, (itow lgHBase))
        let hmask = hbase - 0w1
        let rec quotrem i j = ((Int.quot (i, j)), (Int.rem (i, j)))
        let rec scale i = if i = maxDigit then 1 else nbase div (~ (i + 1))
        type nonrec bignat = int list
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
        let rec consd __3__ __4__ =
          match (__3__, __4__) with | (0, []) -> [] | (d, r) -> d :: r
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
        let rec add __5__ __6__ =
          match (__5__, __6__) with
          | ([], digits) -> digits
          | (digits, []) -> digits
          | (dm::rm, dn::rn) -> addd (((nbase + dm) + dn), rm, rn)
        let rec addd s m n =
          if s < 0 then (::) (s - nbase) add (m, n) else (::) s addc (m, n)
        let rec addc __7__ __8__ =
          match (__7__, __8__) with
          | (m, []) -> addOne m
          | ([], n) -> addOne n
          | (dm::rm, dn::rn) -> addd ((((nbase + dm) + dn) + 1), rm, rn)
        let rec subtOne =
          function
          | 0::mr -> maxDigit :: (subtOne mr)
          | 1::[] -> []
          | n::mr -> (n - 1) :: mr
          | [] -> raise (Fail "")
        let rec subt __9__ __10__ =
          match (__9__, __10__) with
          | (m, []) -> m
          | ([], n) -> raise Negative
          | (dm::rm, dn::rn) -> subd ((dm - dn), rm, rn)
        let rec subb __11__ __12__ =
          match (__11__, __12__) with
          | ([], n) -> raise Negative
          | (dm::rm, []) -> subd ((dm - 1), rm, [])
          | (dm::rm, dn::rn) -> subd (((dm - dn) - 1), rm, rn)
        let rec subd d m n =
          if d >= 0
          then consd (d, (subt (m, n)))
          else consd ((d - nbase), (subb (m, n)))
        let rec mul2 m n =
          let (mh, ml) = hl m in
          let (nh, nl) = hl n in
          let x = mh * nh in
          let y = (mh - ml) * (nh - nl) in
          let z = ml * nl in
          let (zh, zl) = hl z in
          let (uh, ul) = hl ((((nbase + x) + z) - y) + zh) in
          (((((+) (x + uh) wtoi hbase), ((sh ul) + zl)))
            (* x-y+z = mh*nl + ml*nh *)(* can't overflow *))
        let rec muld __15__ __16__ =
          match (__15__, __16__) with
          | (m, 0) -> []
          | (m, 1) -> m
          | (m, i) ->
              let rec muldc __13__ __14__ =
                match (__13__, __14__) with
                | ([], 0) -> []
                | ([], c) -> [c]
                | (d::r, c) ->
                    let (h, l) = mul2 (d, i) in
                    let l1 = (l + nbase) + c in
                    if l1 >= 0
                    then (::) l1 muldc (r, (h + 1))
                    else (::) (l1 - nbase) muldc (r, h) in
              muldc (m, 0)(* speedup *)
        let rec mult __17__ __18__ =
          match (__17__, __18__) with
          | (m, []) -> []
          | (m, d::[]) -> muld (m, d)
          | (m, 0::r) -> consd (0, (mult (m, r)))
          | (m, n) ->
              let rec muln =
                function
                | [] -> []
                | d::r -> add ((muld (n, d)), (consd (0, (muln r)))) in
              muln m(* speedup *)(* speedup *)
        let rec divmod2 (u, v) i =
          let (vh, vl) = hl v in
          let (ih, il) = hl i in
          let rec adj q r = if r < 0 then adj ((q - 1), (r + i)) else (q, r) in
          let (q1, r1) = quotrem (u, ih) in
          let (q1, r1) = adj (q1, ((((sh r1) + vh) - q1) * il)) in
          let (q0, r0) = quotrem (r1, ih) in
          let (q0, r0) = adj (q0, ((((sh r0) + vl) - q0) * il)) in
          (((sh q1) + q0), r0)
        let rec divmodd __19__ __20__ =
          match (__19__, __20__) with
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
        let rec divmod __23__ __24__ =
          match (__23__, __24__) with
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
                    let rec msds __21__ __22__ =
                      match (__21__, __22__) with
                      | ([], _) -> (0, 0)
                      | (d::[], 1) -> (0, d)
                      | (d2::d1::[], 1) -> (d1, d2)
                      | (d::r, i) -> msds (r, (i - 1)) in
                    let (m1, m2) = msds (m, ln) in
                    let tq =
                      if m1 = n1
                      then maxDigit
                      else ((fun r -> r.1)) (divmod2 ((m1, m2), n1)) in
                    let rec try__ q qn' =
                      try (q, (subt (m, qn')))
                      with | Negative -> try__ ((q - 1), (subt (qn', n'))) in
                    let (q, rr) = try__ (tq, (muld (n', tq))) in
                    ((consd (q, qt)), rr) in
              let (qt, rm') = divl m' in
              let (((rm, _))(*0*)) = divmodd (rm', scale) in
              (((qt, rm))
                (* >= 2 *)(* >= base/2 *))
          (* speedup *)(* speedup *)
        let rec cmp __25__ __26__ =
          match (__25__, __26__) with
          | ([], []) -> EQUAL
          | (_, []) -> GREATER
          | ([], _) -> LESS
          | ((i : int)::ri, j::rj) ->
              (match cmp (ri, rj) with
               | EQUAL ->
                   if i = j then EQUAL else if i < j then LESS else GREATER
               | c -> c)
        let rec exp __27__ __28__ =
          match (__27__, __28__) with
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
              let rec qlog __29__ __30__ =
                match (__29__, __30__) with
                | (x, 0) -> 0
                | (x, b) ->
                    if (>=) x wtoi (Word.(<<) (0w1, (itow b)))
                    then
                      (+) b qlog
                        ((wtoi (Word.(>>) ((itow x), (itow b)))), (b div 2))
                    else qlog (x, (b div 2)) in
              let rec loop __31__ __32__ __33__ =
                match (__31__, __32__, __33__) with
                | (d, [], lg) -> (+) lg qlog (d, pow2lgHBase)
                | (_, h::t, lg) -> loop (h, t, (lg + lgBase)) in
              loop (h, t, 0)
        let rec mkPowers radix =
          let powers =
            let bnd = Int.quot (nbase, (~ radix)) in
            let rec try__ tp l =
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
        let rec fmt pow radpow puti n =
          let pad = StringCvt.padLeft '0' pow in
          let rec ms0 __34__ __35__ =
            match (__34__, __35__) with
            | (0, a) -> (pad "") :: a
            | (i, a) -> (pad (puti i)) :: a in
          let rec ml n a =
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
        let rec scan bound powers geti getc cs =
          let rec get l cs =
            if l = bound
            then None
            else
              (match getc cs with
               | None -> None
               | Some (c, cs') -> Some (c, ((l + 1), cs'))) in
          let rec loop acc cs =
            match geti get (0, cs) with
            | None -> (acc, cs)
            | Some (0, (sh, cs')) ->
                loop
                  ((add ((muld (acc, (Vector.sub (powers, sh)))), [])), cs')
            | Some (i, (sh, cs')) ->
                loop
                  ((add ((muld (acc, (Vector.sub (powers, sh)))), [i])), cs') in
          match geti get (0, cs) with
          | None -> None
          | Some (0, (_, cs')) -> Some (loop ([], cs'))
          | Some (i, (_, cs')) -> Some (loop ([i], cs'))
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
    let bigNatMinNeg = BN.addOne (BN.bignat (~ (minNeg + 1)))
    let bigIntMinNeg = negi bigNatMinNeg
    let rec toInt =
      function
      | BI { digits = [] } -> 0
      | BI { sign = POS; digits; digits } -> BN.int digits
      | BI { sign = NEG; digits; digits } ->
          (try ~ (BN.int digits)
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
    let minNeg = valOf LargeInt.minInt
    let maxDigit = LargeInt.fromInt BN.maxDigit
    let nbase = LargeInt.fromInt BN.nbase
    let lgBase = Word.fromInt BN.lgBase
    let notNbase = Word32.notb (Word32.fromInt BN.nbase)
    let rec largeNat =
      function
      | 0 -> []
      | i ->
          let rec bn =
            function
            | 0w0 -> []
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
      | d::e::[] -> (~ (nbase * (LargeInt.fromInt e))) + (LargeInt.fromInt d)
      | d::r -> (~ (( * ) nbase large r)) + (LargeInt.fromInt d)
    let bigNatMinNeg = BN.addOne (largeNat (~ (minNeg + 1)))
    let bigIntMinNeg = negi bigNatMinNeg
    let rec toLarge =
      function
      | BI { digits = [] } -> 0
      | BI { sign = POS; digits; digits } -> large digits
      | BI { sign = NEG; digits; digits } ->
          (try ~ (large digits)
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
    let rec negSign = function | POS -> NEG | NEG -> POS
    let rec subtNat __36__ __37__ =
      match (__36__, __37__) with
      | (m, []) -> { sign = POS; digits = m }
      | ([], n) -> { sign = NEG; digits = n }
      | (m, n) ->
          (try { sign = POS; digits = (BN.subt (m, n)) }
           with | BN.Negative -> { sign = NEG; digits = (BN.subt (n, m)) })
    let precision = None
    let minInt = None
    let maxInt = None
    let rec (~) =
      function
      | BI { digits = [] } as i -> i
      | BI { sign = POS; digits; digits } -> BI { sign = NEG; digits }
      | BI { sign = NEG; digits; digits } -> BI { sign = POS; digits }
    let rec ( * ) __38__ __39__ =
      match (__38__, __39__) with
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
    let rec (+) __40__ __41__ =
      match (__40__, __41__) with
      | (BI { digits = [] }, i2) -> i2
      | (i1, BI { digits = [] }) -> i1
      | (BI { sign = POS; digits = d1; digits = d1 }, BI
         { sign = NEG; digits = d2; digits = d2 }) -> BI (subtNat (d1, d2))
      | (BI { sign = NEG; digits = d1; digits = d1 }, BI
         { sign = POS; digits = d2; digits = d2 }) -> BI (subtNat (d2, d1))
      | (BI { sign; digits = d1; digits = d1 }, BI { digits = d2 }) ->
          BI { sign; digits = (BN.add (d1, d2)) }
    let rec (-) __42__ __43__ =
      match (__42__, __43__) with
      | (i1, BI { digits = [] }) -> i1
      | (BI { digits = [] }, BI { sign; digits; digits }) ->
          BI { sign = (negSign sign); digits }
      | (BI { sign = POS; digits = d1; digits = d1 }, BI
         { sign = POS; digits = d2; digits = d2 }) -> BI (subtNat (d1, d2))
      | (BI { sign = NEG; digits = d1; digits = d1 }, BI
         { sign = NEG; digits = d2; digits = d2 }) -> BI (subtNat (d2, d1))
      | (BI { sign; digits = d1; digits = d1 }, BI { digits = d2 }) ->
          BI { sign; digits = (BN.add (d1, d2)) }
    let rec quotrem __44__ __45__ =
      match (__44__, __45__) with
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
    let rec divmod __46__ __47__ =
      match (__46__, __47__) with
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
    let rec compare __48__ __49__ =
      match (__48__, __49__) with
      | (BI { sign = NEG }, BI { sign = POS }) -> LESS
      | (BI { sign = POS }, BI { sign = NEG }) -> GREATER
      | (BI { sign = POS; digits = d; digits = d }, BI
         { sign = POS; digits = d'; digits = d' }) -> BN.cmp (d, d')
      | (BI { sign = NEG; digits = d; digits = d }, BI
         { sign = NEG; digits = d'; digits = d' }) -> BN.cmp (d', d)
    let rec (<) arg = match compare arg with | LESS -> true | _ -> false
    let rec (>) arg =
      match compare arg with | GREATER -> true | _ -> false
    let rec (<=) arg =
      match compare arg with | GREATER -> false | _ -> true
    let rec (>=) arg = match compare arg with | LESS -> false | _ -> true
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
    let rec sameSign i j = (=) (sign i) sign j
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
      let rec cvt __50__ __51__ =
        match (__50__, __51__) with
        | (None, _) -> None
        | (Some (i, cs), wr) -> Some ((wr i), cs) in
      ((match getc cs' with
        | Some ('~', cs'') -> cvt ((scanFn getc cs''), zneg)
        | Some ('-', cs'') -> cvt ((scanFn getc cs''), zneg)
        | Some ('+', cs'') -> cvt ((scanFn getc cs''), posi)
        | Some _ -> cvt ((scanFn getc cs'), posi)
        | None -> None)(* end case *))
    let rec scan =
      function
      | StringCvt.BIN -> scan' BN.scan2
      | StringCvt.OCT -> scan' BN.scan8
      | StringCvt.DEC -> scan' BN.scan10
      | StringCvt.HEX -> scan' BN.scan16
    let rec fromString s = StringCvt.scanString (scan StringCvt.DEC) s
    let rec pow __52__ __53__ =
      match (__52__, __53__) with
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
