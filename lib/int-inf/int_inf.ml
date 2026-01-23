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
        let rec code (c : char) =
          W.fromInt (ord (CharVector.sub (cvtTable, (ord c))))
        let (wsCode : Word32.word) = 0w128
        let (plusCode : Word32.word) = 0w129
        let (minusCode : Word32.word) = 0w130
        let rec skipWS (getc : (char, 'a) StringCvt.reader) cs =
          let rec skip cs =
            ((begin match getc cs with
              | None -> cs
              | Some (c, cs') -> if (code c) = wsCode then begin skip cs' end
                  else begin cs end end)
          (* end case *)) in
      skip cs
    let rec scanPrefix (getc : (char, 'a) StringCvt.reader) cs =
      let rec skipWS cs =
        ((begin match getc cs with
          | None -> None
          | Some (c, cs') ->
              let c' = code c in if c' = wsCode then begin skipWS cs' end
                else begin Some (c', cs') end end)
      (* end case *)) in
  let rec getNext (neg, cs) =
    ((begin match getc cs with
      | None -> None
      | Some (c, cs) -> Some { neg; next = (code c); rest = cs } end)
    (* end case *)) in
  ((begin match skipWS cs with
    | None -> None
    | Some (c, cs') -> if c = plusCode then begin getNext (false, cs') end
        else begin if c = minusCode then begin getNext (true, cs') end
          else begin Some { neg = false; next = c; rest = cs' } end end end)
(* end case *))
let rec chkOverflow mask w = if (W.andb (mask, w)) = 0w0 then begin () end
  else begin raise Overflow end
let rec scanBin (getc : (char, 'a) StringCvt.reader) cs =
  ((begin match scanPrefix getc cs with
    | None -> None
    | Some { neg; next; rest; next; rest; rest } ->
        let rec isDigit (d : Word32.word) = d < 0w2 in
        let chkOverflow = chkOverflow 0x80000000 in
        let rec cvt (w, rest) =
          ((begin match getc rest with
            | None -> Some { neg; word = w; rest }
            | Some (c, rest') ->
                let d = code c in
                if isDigit d
                then
                  begin (begin chkOverflow w;
                         cvt ((W.(+) ((W.(<<) (w, 0w1)), d)), rest') end) end
                else begin Some { neg; word = w; rest } end end)
        (* end case *)) in
  if isDigit next then begin cvt (next, rest) end
    else begin None end end)
(* end case *))
let rec scanOct getc cs =
  ((begin match scanPrefix getc cs with
    | None -> None
    | Some { neg; next; rest; next; rest; rest } ->
        let rec isDigit (d : Word32.word) = d < 0w8 in
        let chkOverflow = chkOverflow 0xE0000000 in
        let rec cvt (w, rest) =
          ((begin match getc rest with
            | None -> Some { neg; word = w; rest }
            | Some (c, rest') ->
                let d = code c in
                if isDigit d
                then
                  begin (begin chkOverflow w;
                         cvt ((W.(+) ((W.(<<) (w, 0w3)), d)), rest') end) end
                else begin Some { neg; word = w; rest } end end)
        (* end case *)) in
  if isDigit next then begin cvt (next, rest) end
    else begin None end end)
(* end case *))
let rec scanDec getc cs =
  ((begin match scanPrefix getc cs with
    | None -> None
    | Some { neg; next; rest; next; rest; rest } ->
        let rec isDigit (d : Word32.word) = d < 0w10 in
        let rec cvt (w, rest) =
          ((begin match getc rest with
            | None -> Some { neg; word = w; rest }
            | Some (c, rest') ->
                let d = code c in
                if isDigit d
                then
                  begin (begin if
                                 (w >= largestWordDiv10) &&
                                   ((largestWordDiv10 < w) ||
                                      (largestWordMod10 < d))
                               then begin raise Overflow end
                         else begin () end;
                cvt (((0w10 * w) + d), rest') end) end
          else begin Some { neg; word = w; rest } end end)
  (* end case *)) in
if isDigit next then begin cvt (next, rest) end else begin None end end)
(* end case *))
let rec scanHex getc cs =
  ((begin match scanPrefix getc cs with
    | None -> None
    | Some { neg; next; rest; next; rest; rest } ->
        let rec isDigit (d : Word32.word) = d < 0w16 in
        let chkOverflow = chkOverflow 0xF0000000 in
        let rec cvt (w, rest) =
          ((begin match getc rest with
            | None -> Some { neg; word = w; rest }
            | Some (c, rest') ->
                let d = code c in
                if isDigit d
                then
                  begin (begin chkOverflow w;
                         cvt ((W.(+) ((W.(<<) (w, 0w4)), d)), rest') end) end
                else begin Some { neg; word = w; rest } end end)
        (* end case *)) in
  if isDigit next then begin cvt (next, rest) end
    else begin None end end)
(* end case *))
let rec finalWord scanFn getc cs =
  ((begin match scanFn getc cs with
    | None -> None
    | Some { neg = true } -> None
    | Some { neg = false; word; rest; word; rest; rest } -> Some (word, rest) end)
  (* end case *))
let rec scanWord =
  begin function
  | StringCvt.BIN -> finalWord scanBin
  | StringCvt.OCT -> finalWord scanOct
  | StringCvt.DEC -> finalWord scanDec
  | StringCvt.HEX -> finalWord scanHex end
let rec finalInt scanFn getc cs =
  ((begin match scanFn getc cs with
    | None -> None
    | Some { neg = true; word; rest; word; rest; rest } ->
        if largestNegInt < word then begin raise Overflow end
        else begin Some ((I.(~-) (W.toInt word)), rest) end
  | Some { word; rest; rest } ->
      if largestPosInt < word then begin raise Overflow end
      else begin Some ((W.toInt word), rest) end end)
(* end case *))
let rec scanInt =
  begin function
  | StringCvt.BIN -> finalInt scanBin
  | StringCvt.OCT -> finalInt scanOct
  | StringCvt.DEC -> finalInt scanDec
  | StringCvt.HEX -> finalInt scanHex end end

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
    let rec mkDigit (w : Word32.word) =
      CharVector.sub ("0123456789abcdef", (W.toInt w))
    let rec wordToBin w =
      let rec mkBit w = if (W.andb (w, 0w1)) = 0w0 then begin '0' end
        else begin '1' end in
    let rec f =
      begin function
      | (0w0, n, l) -> ((I.(+) (n, 1)), ('0' :: l))
      | (0w1, n, l) -> ((I.(+) (n, 1)), ('1' :: l))
      | (w, n, l) -> f ((W.(>>) (w, 0w1)), (I.(+) (n, 1)), ((mkBit w) :: l)) end in
    f (w, 0, [])
let rec wordToOct w =
  let rec f (w, n, l) =
    if w < 0w8 then begin ((I.(+) (n, 1)), ((mkDigit w) :: l)) end
    else begin
      f
        ((W.(>>) (w, 0w3)), (I.(+) (n, 1)),
          ((mkDigit (W.andb (w, 0w7))) :: l)) end in
f (w, 0, [])
let rec wordToDec w =
  let rec f (w, n, l) =
    if w < 0w10 then begin ((I.(+) (n, 1)), ((mkDigit w) :: l)) end
    else begin
      (let j = w div 0w10 in
       f (j, (I.(+) (n, 1)), ((mkDigit ((w - 0w10) * j)) :: l))) end in
f (w, 0, [])
let rec wordToHex w =
  let rec f (w, n, l) =
    if w < 0w16 then begin ((I.(+) (n, 1)), ((mkDigit w) :: l)) end
    else begin
      f
        ((W.(>>) (w, 0w4)), (I.(+) (n, 1)),
          ((mkDigit (W.andb (w, 0w15))) :: l)) end in
f (w, 0, [])
let rec fmtW =
  begin function
  | StringCvt.BIN -> Stdlib.snd o wordToBin
  | StringCvt.OCT -> Stdlib.snd o wordToOct
  | StringCvt.DEC -> Stdlib.snd o wordToDec
  | StringCvt.HEX -> Stdlib.snd o wordToHex end
let rec fmtWord radix = String.implode o (fmtW radix)
let rec fmtInt radix =
  let fmtW = fmtW radix in
  let itow = W.fromInt in
  let rec fmt i =
    if I.(<) (i, 0)
    then
      begin begin try
                    let digits = fmtW (itow (I.(~-) i)) in
                    String.implode ('~' :: digits)
            with
            | _ ->
                (((begin match radix with
                   | StringCvt.BIN -> "~1111111111111111111111111111111"
                   | StringCvt.OCT -> "~7777777777"
                   | StringCvt.DEC -> "~1073741824"
                   | StringCvt.HEX -> "~3fffffff" end))
            (* end case *)) end end
    else begin String.implode (fmtW (itow i)) end in
fmt end

module BigNat =
  struct
    exception Negative 
    let itow = Word.fromInt
    let wtoi = Word.toIntX
    let lgBase = 30
    let nbase = ~0x40000000
    let maxDigit = - (nbase + 1)
    let realBase = (real maxDigit) + 1.0
    let lgHBase = Int.quot (lgBase, 2)
    let hbase = Word.(<<) (0w1, (itow lgHBase))
    let hmask = hbase - 0w1
    let rec quotrem (i, j) = ((Int.quot (i, j)), (Int.rem (i, j)))
    let rec scale i = if i = maxDigit then begin 1 end
      else begin nbase div (- (i + 1)) end
  type nonrec bignat = int list
  let zero = []
  let one = [1]
  let rec bignat =
    begin function
    | 0 -> zero
    | i ->
        let notNbase = Word.notb (itow nbase) in
        let rec bn =
          begin function
          | 0w0 -> []
          | i ->
              let rec dmbase n =
                ((Word.(>>) (n, (itow lgBase))), (Word.andb (n, notNbase))) in
              let (q, r) = dmbase i in (wtoi r) :: (bn q) end in
        if i > 0
        then begin (if i <= maxDigit then begin [i] end
          else begin bn (itow i) end) end
    else begin raise Negative end end
let rec int =
  begin function
  | [] -> 0
  | d::[] -> d
  | d::e::[] -> (- (nbase * e)) + d
  | d::r -> (- (( * ) nbase int r)) + d end
let rec consd = begin function | (0, []) -> [] | (d, r) -> d :: r end
let rec hl i =
  let w = itow i in
  ((((wtoi (Word.(~>>) (w, (itow lgHBase)))), (wtoi (Word.andb (w, hmask)))))
    (* MUST sign-extend *))
let rec sh i = wtoi (Word.(<<) ((itow i), (itow lgHBase)))
let rec addOne =
  begin function
  | [] -> [1]
  | m::rm ->
      let c = (nbase + m) + 1 in if c < 0 then begin (c - nbase) :: rm end
        else begin c :: (addOne rm) end end
let rec add =
  begin function
  | ([], digits) -> digits
  | (digits, []) -> digits
  | (dm::rm, dn::rn) -> addd (((nbase + dm) + dn), rm, rn) end
let rec addd (s, m, n) = if s < 0 then begin (::) (s - nbase) add (m, n) end
  else begin (::) s addc (m, n) end
let rec addc =
  begin function
  | (m, []) -> addOne m
  | ([], n) -> addOne n
  | (dm::rm, dn::rn) -> addd ((((nbase + dm) + dn) + 1), rm, rn) end
let rec subtOne =
  begin function
  | 0::mr -> maxDigit :: (subtOne mr)
  | 1::[] -> []
  | n::mr -> (n - 1) :: mr
  | [] -> raise (Fail "") end
let rec subt =
  begin function
  | (m, []) -> m
  | ([], n) -> raise Negative
  | (dm::rm, dn::rn) -> subd ((dm - dn), rm, rn) end
let rec subb =
  begin function
  | ([], n) -> raise Negative
  | (dm::rm, []) -> subd ((dm - 1), rm, [])
  | (dm::rm, dn::rn) -> subd (((dm - dn) - 1), rm, rn) end
let rec subd (d, m, n) = if d >= 0 then begin consd (d, (subt (m, n))) end
  else begin consd ((d - nbase), (subb (m, n))) end
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
let rec muld =
  begin function
  | (m, 0) -> []
  | (m, 1) -> m
  | (m, i) ->
      let rec muldc =
        begin function
        | ([], 0) -> []
        | ([], c) -> [c]
        | (d::r, c) ->
            let (h, l) = mul2 (d, i) in
            let l1 = (l + nbase) + c in
            if l1 >= 0 then begin (::) l1 muldc (r, (h + 1)) end
              else begin (::) (l1 - nbase) muldc (r, h) end end in
muldc (m, 0) end(* speedup *)
let rec mult =
  begin function
  | (m, []) -> []
  | (m, d::[]) -> muld (m, d)
  | (m, 0::r) -> consd (0, (mult (m, r)))
  | (m, n) ->
      let rec muln =
        begin function
        | [] -> []
        | d::r -> add ((muld (n, d)), (consd (0, (muln r)))) end in
    muln m end(* speedup *)(* speedup *)
let rec divmod2 ((u, v), i) =
  let (vh, vl) = hl v in
  let (ih, il) = hl i in
  let rec adj (q, r) = if r < 0 then begin adj ((q - 1), (r + i)) end
    else begin (q, r) end in
  let (q1, r1) = quotrem (u, ih) in
  let (q1, r1) = adj (q1, ((((sh r1) + vh) - q1) * il)) in
  let (q0, r0) = quotrem (r1, ih) in
  let (q0, r0) = adj (q0, ((((sh r0) + vl) - q0) * il)) in
  (((sh q1) + q0), r0)
let rec divmodd =
  begin function
  | (m, 1) -> (m, 0)
  | (m, i) ->
      let scale = scale i in
      let i' = i * scale in
      let m' = muld (m, scale) in
      let rec dmi =
        begin function
        | [] -> ([], 0)
        | d::r ->
            let (qt, rm) = dmi r in
            let (q1, r1) = divmod2 ((rm, d), i') in ((consd (q1, qt)), r1) end in
      let (q, r) = dmi m' in (q, (r div scale)) end(* speedup *)
let rec divmod =
  begin function
  | (m, []) -> raise Div
  | ([], n) -> ([], [])
  | (d::r, 0::s) -> let (qt, rm) = divmod (r, s) in (qt, (consd (d, rm)))
  | (m, d::[]) ->
      let (qt, rm) = divmodd (m, d) in
      (qt, (if rm = 0 then begin [] end else begin [rm] end))
  | (m, n) ->
      let ln = length n in
      let scale = scale (List.nth (n, (ln - 1))) in
      let m' = muld (m, scale) in
      let n' = muld (n, scale) in
      let n1 = List.nth (n', (ln - 1)) in
      let rec divl =
        begin function
        | [] -> ([], [])
        | d::r ->
            let (qt, rm) = divl r in
            let m = consd (d, rm) in
            let rec msds =
              begin function
              | ([], _) -> (0, 0)
              | (d::[], 1) -> (0, d)
              | (d2::d1::[], 1) -> (d1, d2)
              | (d::r, i) -> msds (r, (i - 1)) end in
            let (m1, m2) = msds (m, ln) in
            let tq = if m1 = n1 then begin maxDigit end
              else begin ((fun r -> r.1)) (divmod2 ((m1, m2), n1)) end in
            let rec try_ (q, qn') =
              begin try (q, (subt (m, qn')))
              with | Negative -> try_ ((q - 1), (subt (qn', n'))) end in
            let (q, rr) = try_ (tq, (muld (n', tq))) in ((consd (q, qt)), rr) end in
      let (qt, rm') = divl m' in
      let (((rm, _))(*0*)) = divmodd (rm', scale) in
      (((qt, rm))(* >= 2 *)(* >= base/2 *)) end
(* speedup *)(* speedup *)
let rec cmp =
  begin function
  | ([], []) -> EQUAL
  | (_, []) -> GREATER
  | ([], _) -> LESS
  | ((i : int)::ri, j::rj) ->
      (begin match cmp (ri, rj) with
       | EQUAL -> if i = j then begin EQUAL end
           else begin if i < j then begin LESS end else begin GREATER end end
  | c -> c end) end
let rec exp =
  begin function
  | (_, 0) -> one
  | ([], n) -> if n > 0 then begin zero end else begin raise Div end
  | (m, n) -> if n < 0 then begin zero end
      else begin
        (let rec expm =
           begin function
           | 0 -> [1]
           | 1 -> m
           | i ->
               let r = expm (i div 2) in
               let r2 = mult (r, r) in if (i mod_ 2) = 0 then begin r2 end
                 else begin mult (r2, m) end end in
expm n) end end
let rec try_ n = if n >= lgHBase then begin n end else begin try_ (2 * n) end
let pow2lgHBase = try_ 1
let rec log2 =
  begin function
  | [] -> raise Domain
  | h::t ->
      let rec qlog =
        begin function
        | (x, 0) -> 0
        | (x, b) ->
            if (>=) x wtoi (Word.(<<) (0w1, (itow b)))
            then
              begin (+) b qlog
                      ((wtoi (Word.(>>) ((itow x), (itow b)))), (b div 2)) end
            else begin qlog (x, (b div 2)) end end in
let rec loop =
  begin function
  | (d, [], lg) -> (+) lg qlog (d, pow2lgHBase)
  | (_, h::t, lg) -> loop (h, t, (lg + lgBase)) end in
loop (h, t, 0) end
let rec mkPowers radix =
  let powers =
    let bnd = Int.quot (nbase, (- radix)) in
    let rec try_ (tp, l) =
      begin try
              if tp <= bnd then begin try_ ((radix * tp), (tp :: l)) end
              else begin tp :: l end
      with | _ -> tp :: l end in
  Vector.fromList (rev (try_ (radix, [1]))) in
let maxpow = (Vector.length powers) - 1 in
(maxpow, (Vector.sub (powers, maxpow)), powers)
let powers2 = mkPowers 2
let powers8 = mkPowers 8
let powers10 = mkPowers 10
let powers16 = mkPowers 16
let rec fmt (pow, radpow, puti) n =
  let pad = StringCvt.padLeft '0' pow in
  let rec ms0 =
    begin function | (0, a) -> (pad "") :: a | (i, a) -> (pad (puti i)) :: a end in
  let rec ml (n, a) =
    begin match divmodd (n, radpow) with
    | ([], d) -> (puti d) :: a
    | (q, d) -> ml (q, (ms0 (d, a))) end in
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
  let rec get (l, cs) = if l = bound then begin None end
    else begin
      (begin match getc cs with
       | None -> None
       | Some (c, cs') -> Some (c, ((l + 1), cs')) end) end in
let rec loop (acc, cs) =
begin match geti get (0, cs) with
| None -> (acc, cs)
| Some (0, (sh, cs')) ->
    loop ((add ((muld (acc, (Vector.sub (powers, sh)))), [])), cs')
| Some (i, (sh, cs')) ->
    loop ((add ((muld (acc, (Vector.sub (powers, sh)))), [i])), cs') end in
begin match geti get (0, cs) with
| None -> None
| Some (0, (_, cs')) -> Some (loop ([], cs'))
| Some (i, (_, cs')) -> Some (loop ([i], cs')) end
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
  begin function | [] -> zero | digits -> BI { sign = NEG; digits } end
let minNeg = valOf Int.minInt
let bigNatMinNeg = BN.addOne (BN.bignat (- (minNeg + 1)))
let bigIntMinNeg = negi bigNatMinNeg
let rec toInt =
  begin function
  | BI { digits = [] } -> 0
  | BI { sign = POS; digits; digits } -> BN.int digits
  | BI { sign = NEG; digits; digits } ->
      (begin try - (BN.int digits)
       with
       | _ -> if digits = bigNatMinNeg then begin minNeg end
           else begin raise Overflow end end) end
let rec fromInt =
  begin function
  | 0 -> zero
  | i ->
      if i < 0
      then begin (if i = minNeg then begin bigIntMinNeg end
        else begin BI { sign = NEG; digits = (BN.bignat (- i)) } end) end
  else begin BI { sign = POS; digits = (BN.bignat i) } end end
let minNeg = valOf LargeInt.minInt
let maxDigit = LargeInt.fromInt BN.maxDigit
let nbase = LargeInt.fromInt BN.nbase
let lgBase = Word.fromInt BN.lgBase
let notNbase = Word32.notb (Word32.fromInt BN.nbase)
let rec largeNat =
  begin function
  | (0 : LargeInt.int) -> []
  | i ->
      let rec bn =
        begin function
        | (0w0 : Word32.word) -> []
        | i ->
            let rec dmbase n =
              ((Word32.(>>) (n, lgBase)), (Word32.andb (n, notNbase))) in
            let (q, r) = dmbase i in (Word32.toInt r) :: (bn q) end in
    if i <= maxDigit then begin [LargeInt.toInt i] end
      else begin bn (Word32.fromLargeInt i) end end
let rec large =
  begin function
  | [] -> 0
  | d::[] -> LargeInt.fromInt d
  | d::e::[] -> (- (nbase * (LargeInt.fromInt e))) + (LargeInt.fromInt d)
  | d::r -> (- (( * ) nbase large r)) + (LargeInt.fromInt d) end
let bigNatMinNeg = BN.addOne (largeNat (- (minNeg + 1)))
let bigIntMinNeg = negi bigNatMinNeg
let rec toLarge =
  begin function
  | BI { digits = [] } -> 0
  | BI { sign = POS; digits; digits } -> large digits
  | BI { sign = NEG; digits; digits } ->
      (begin try - (large digits)
       with
       | _ -> if digits = bigNatMinNeg then begin minNeg end
           else begin raise Overflow end end) end
let rec fromLarge =
  begin function
  | 0 -> zero
  | i ->
      if i < 0
      then begin (if i = minNeg then begin bigIntMinNeg end
        else begin BI { sign = NEG; digits = (largeNat (- i)) } end) end
  else begin BI { sign = POS; digits = (largeNat i) } end end
let rec negSign = begin function | POS -> NEG | NEG -> POS end
let rec subtNat =
  begin function
  | (m, []) -> { sign = POS; digits = m }
  | ([], n) -> { sign = NEG; digits = n }
  | (m, n) ->
      (begin try { sign = POS; digits = (BN.subt (m, n)) }
       with | BN.Negative -> { sign = NEG; digits = (BN.subt (n, m)) } end) end
let precision = None
let minInt = None
let maxInt = None
let rec (~-) =
  begin function
  | BI { digits = [] } as i -> i
  | BI { sign = POS; digits; digits } -> BI { sign = NEG; digits }
  | BI { sign = NEG; digits; digits } -> BI { sign = POS; digits } end
let rec ( * ) =
  begin function
  | (_, BI { digits = [] }) -> zero
  | (BI { digits = [] }, _) -> zero
  | (BI { sign = POS; digits = d1; digits = d1 }, BI
     { sign = NEG; digits = d2; digits = d2 }) ->
      BI { sign = NEG; digits = (BN.mult (d1, d2)) }
  | (BI { sign = NEG; digits = d1; digits = d1 }, BI
     { sign = POS; digits = d2; digits = d2 }) ->
      BI { sign = NEG; digits = (BN.mult (d1, d2)) }
  | (BI { digits = d1 }, BI { digits = d2 }) ->
      BI { sign = POS; digits = (BN.mult (d1, d2)) } end
let rec (+) =
  begin function
  | (BI { digits = [] }, i2) -> i2
  | (i1, BI { digits = [] }) -> i1
  | (BI { sign = POS; digits = d1; digits = d1 }, BI
     { sign = NEG; digits = d2; digits = d2 }) -> BI (subtNat (d1, d2))
  | (BI { sign = NEG; digits = d1; digits = d1 }, BI
     { sign = POS; digits = d2; digits = d2 }) -> BI (subtNat (d2, d1))
  | (BI { sign; digits = d1; digits = d1 }, BI { digits = d2 }) ->
      BI { sign; digits = (BN.add (d1, d2)) } end
let rec (-) =
  begin function
  | (i1, BI { digits = [] }) -> i1
  | (BI { digits = [] }, BI { sign; digits; digits }) ->
      BI { sign = (negSign sign); digits }
  | (BI { sign = POS; digits = d1; digits = d1 }, BI
     { sign = POS; digits = d2; digits = d2 }) -> BI (subtNat (d1, d2))
  | (BI { sign = NEG; digits = d1; digits = d1 }, BI
     { sign = NEG; digits = d2; digits = d2 }) -> BI (subtNat (d2, d1))
  | (BI { sign; digits = d1; digits = d1 }, BI { digits = d2 }) ->
      BI { sign; digits = (BN.add (d1, d2)) } end
let rec quotrem =
  begin function
  | (BI { sign = POS; digits = m; digits = m }, BI
     { sign = POS; digits = n; digits = n }) ->
      (begin match BN.divmod (m, n) with | (q, r) -> ((posi q), (posi r)) end)
  | (BI { sign = POS; digits = m; digits = m }, BI
     { sign = NEG; digits = n; digits = n }) ->
      (begin match BN.divmod (m, n) with | (q, r) -> ((zneg q), (posi r)) end)
  | (BI { sign = NEG; digits = m; digits = m }, BI
     { sign = POS; digits = n; digits = n }) ->
      (begin match BN.divmod (m, n) with | (q, r) -> ((zneg q), (zneg r)) end)
| (BI { sign = NEG; digits = m; digits = m }, BI
   { sign = NEG; digits = n; digits = n }) ->
    (begin match BN.divmod (m, n) with | (q, r) -> ((posi q), (zneg r)) end) end
let rec divmod =
  begin function
  | (BI { sign = POS; digits = m; digits = m }, BI
     { sign = POS; digits = n; digits = n }) ->
      (begin match BN.divmod (m, n) with | (q, r) -> ((posi q), (posi r)) end)
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
      (begin match BN.divmod (m, n) with | (q, r) -> ((posi q), (zneg r)) end) end
let rec div arg = (fun r -> r.1) (divmod arg)
let rec mod_ arg = (fun r -> r.2) (divmod arg)
let rec quot arg = (fun r -> r.1) (quotrem arg)
let rec rem arg = (fun r -> r.2) (quotrem arg)
let rec compare =
  begin function
  | (BI { sign = NEG }, BI { sign = POS }) -> LESS
  | (BI { sign = POS }, BI { sign = NEG }) -> GREATER
  | (BI { sign = POS; digits = d; digits = d }, BI
     { sign = POS; digits = d'; digits = d' }) -> BN.cmp (d, d')
  | (BI { sign = NEG; digits = d; digits = d }, BI
     { sign = NEG; digits = d'; digits = d' }) -> BN.cmp (d', d) end
let rec (<) arg =
  begin match compare arg with | LESS -> true | _ -> false end
let rec (>) arg =
  begin match compare arg with | GREATER -> true | _ -> false end
let rec (<=) arg =
  begin match compare arg with | GREATER -> false | _ -> true end
let rec (>=) arg =
  begin match compare arg with | LESS -> false | _ -> true end
let rec abs =
  begin function
  | BI { sign = NEG; digits; digits } -> BI { sign = POS; digits }
  | i -> i end
let rec max arg =
  begin match compare arg with
  | GREATER -> ((fun r -> r.1)) arg
  | _ -> Stdlib.snd arg end
let rec min arg =
  begin match compare arg with
  | LESS -> ((fun r -> r.1)) arg
  | _ -> Stdlib.snd arg end
let rec sign =
  begin function
  | BI { sign = NEG } -> (-1)
  | BI { digits = [] } -> 0
  | _ -> 1 end
let rec sameSign (i, j) = (=) (sign i) sign j
let rec fmt' fmtFn i =
  begin match i with
  | BI { digits = [] } -> "0"
  | BI { sign = NEG; digits; digits } -> "~" ^ (fmtFn digits)
  | BI { sign = POS; digits; digits } -> fmtFn digits end
let rec fmt =
  begin function
  | StringCvt.BIN -> fmt' BN.fmt2
  | StringCvt.OCT -> fmt' BN.fmt8
  | StringCvt.DEC -> fmt' BN.fmt10
  | StringCvt.HEX -> fmt' BN.fmt16 end
let toString = fmt StringCvt.DEC
let rec scan' scanFn getc cs =
  let cs' = NumScan.skipWS getc cs in
  let rec cvt =
    begin function
    | (None, _) -> None
    | (Some (i, cs), wr) -> Some ((wr i), cs) end in
  ((begin match getc cs' with
    | Some ('~', cs'') -> cvt ((scanFn getc cs''), zneg)
    | Some ('-', cs'') -> cvt ((scanFn getc cs''), zneg)
    | Some ('+', cs'') -> cvt ((scanFn getc cs''), posi)
    | Some _ -> cvt ((scanFn getc cs'), posi)
    | None -> None end)
  (* end case *))
let rec scan =
  begin function
  | StringCvt.BIN -> scan' BN.scan2
  | StringCvt.OCT -> scan' BN.scan8
  | StringCvt.DEC -> scan' BN.scan10
  | StringCvt.HEX -> scan' BN.scan16 end
let rec fromString s = StringCvt.scanString (scan StringCvt.DEC) s
let rec pow =
  begin function
  | (_, 0) -> one
  | (BI { sign = POS; digits; digits }, n) -> posi (BN.exp (digits, n))
  | (BI { sign = NEG; digits; digits }, n) ->
      if (Int.mod_ (n, 2)) = 0 then begin posi (BN.exp (digits, n)) end
      else begin zneg (BN.exp (digits, n)) end end
let rec log2 =
  begin function
  | BI { sign = POS; digits; digits } -> BN.log2 digits
  | _ -> raise Domain end end
