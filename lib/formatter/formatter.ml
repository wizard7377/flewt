
module type FORMATTER  =
  sig
    val Indent : int ref
    val Blanks : int ref
    val Skip : int ref
    val Pagewidth : int ref
    val Bailout : bool ref
    val BailoutIndent : int ref
    val BailoutSpot : int ref
    type nonrec format
    val Width : format -> (int * int)
    val Break : format
    val Break0 : int -> int -> format
    val String : string -> format
    val String0 : int -> string -> format
    val Space : format
    val Spaces : int -> format
    val Newline : unit -> format
    val Newlines : int -> format
    val Newpage : unit -> format
    val Vbox : format list -> format
    val Vbox0 : int -> int -> format list -> format
    val Hbox : format list -> format
    val Hbox0 : int -> format list -> format
    val HVbox : format list -> format
    val HVbox0 : int -> int -> int -> format list -> format
    val HOVbox : format list -> format
    val HOVbox0 : int -> int -> int -> format list -> format
    val makestring_fmt : format -> string
    val print_fmt : format -> unit
    type nonrec fmtstream
    val open_fmt : TextIO.outstream -> fmtstream
    val close_fmt : fmtstream -> TextIO.outstream
    val output_fmt : fmtstream -> format -> unit
    val file_open_fmt : string -> ((unit -> unit) * fmtstream)
    val with_open_fmt : string -> (fmtstream -> 'a) -> 'a
  end;;




module Formatter() : FORMATTER =
  struct
    let Indent = ref 3
    let Skip = ref 1
    let Blanks = ref 1
    let Pagewidth = ref 80
    let Bailout = ref true
    let BailoutIndent = ref 0
    let BailoutSpot = ref 40
    let rec Spaces' __0__ __1__ =
      match (__0__, __1__) with
      | (0, s) -> s
      | (n, s) -> Spaces' (n - 1) (s ^ " ")
    let rec Spaces n = if n > 0 then Spaces' n "" else ""
    let rec Newlines' __2__ __3__ =
      match (__2__, __3__) with
      | (0, s) -> s
      | (n, s) -> Newlines' (n - 1) (s ^ "\n")
    let rec Newlines n = if n > 0 then Newlines' n "" else ""
    let Sp = Spaces
    let rec Spmod n = Spaces (n mod__ (!Pagewidth))
    let Nl = Newlines
    let rec Np () = "\n\012\n"
    let rec Max x y = if (x : int) > y then x else y
    let rec sumpair (a, b) (c, d) = (((a : int) + c), ((b : int) + d))
    let rec fst a b = a
    let rec snd a b = b
    type mode =
      | Hori 
      | Vert 
    type nonrec width = (int * int)
    type nonrec widthmode = (mode * mode)
    type format =
      | Str of (int * string) 
      | Brk of (int * int) 
      | Dbk 
      | Ebk 
      | Hbx of (width * int * format list) 
      | Vbx of (width * int * int * format list) 
      | Hvx of ((width * widthmode) * int * int * int * format list) 
      | Hov of ((width * widthmode) * int * int * int * format list) 
    let rec Width0 __4__ __5__ __6__ __7__ =
      match (__4__, __5__, __6__, __7__) with
      | (m, b, i, Str (n, _)) -> (n, n)
      | (Hori, b, i, Brk (m, _)) -> (m, m)
      | (Vert, b, i, Brk (_, n)) -> (n, n)
      | (Hori, b, i, Dbk) -> (b, b)
      | (Vert, b, i, Dbk) -> (i, i)
      | (m, b, i, Ebk) -> (0, 0)
      | (m, b, i, Vbx ((min, max), _, _, _)) -> (min, max)
      | (m, b, i, Hbx ((min, max), _, _)) -> (min, max)
      | (m, b, i, Hvx (((min, max), _), _, _, _, _)) -> (min, max)
      | (m, b, i, Hov (((min, max), _), _, _, _, _)) -> (min, max)
    let rec Width fmt = Width0 (Hori, (!Blanks), (!Indent), fmt)
    let Unused = (-9999)
    let rec vlistWidth' __8__ __9__ __10__ __11__ =
      match (__8__, __9__, __10__, __11__) with
      | (i, nil, (totmin, totmax), (tmmin, tmmax)) ->
          ((Max (totmin, tmmin)), (Max (totmax, tmmax)))
      | (i, (Dbk)::t, (totmin, totmax), (tmmin, tmmax)) ->
          vlistWidth'
            (i, t, ((Max (totmin, tmmin)), (Max (totmax, tmmax))),
              (Width0 (Vert, Unused, i, Dbk)))
      | (i, (Brk _ as b)::t, (totmin, totmax), (tmmin, tmmax)) ->
          vlistWidth'
            (i, t, ((Max (totmin, tmmin)), (Max (totmax, tmmax))),
              (Width0 (Vert, Unused, i, b)))
      | (i, x::t, (totmin, totmax), (tmmin, tmmax)) ->
          vlistWidth'
            (i, t, (totmin, totmax),
              (sumpair ((Width0 (Vert, Unused, i, x)), (tmmin, tmmax))))
    let rec vlistWidth l indent = vlistWidth' (indent, l, (0, 0), (0, 0))
    let rec hlistWidth l blanks =
      List.foldr
        (fun fmt ->
           fun (x, y) ->
             sumpair ((Width0 (Hori, blanks, Unused, fmt)), (x, y))) 
        (0, 0) l
    let rec hovlistWidth l blanks indent =
      let (vmin, vmax) = vlistWidth (l, indent)
      and (hmin, hmax) = hlistWidth (l, blanks) in
      let (min, mmode) = if vmin < hmin then (vmin, Vert) else (hmin, Hori) in
      ((min, hmax), (mmode, Hori))
    let hvlistWidth = hovlistWidth
    let Break = Dbk
    let rec Break0 b i = Brk (b, i)
    let rec String s = Str ((size s), s)
    let rec String0 i s = Str (i, s)
    let Space = Str (1, (Sp 1))
    let rec Spaces n = Str (n, (Sp n))
    let rec Newline () = Str (0, (Nl 1))
    let rec Newlines n = Str (0, (Nl n))
    let rec Vbox l = Vbx ((vlistWidth (l, (!Indent))), (!Indent), (!Skip), l)
    let rec Vbox0 i s l = Vbx ((vlistWidth (l, i)), i, s, l)
    let rec Hbox l = Hbx ((hlistWidth (l, (!Blanks))), (!Blanks), l)
    let rec Hbox0 b l = Hbx ((hlistWidth (l, b)), b, l)
    let rec HVbox l =
      Hvx
        ((hvlistWidth (l, (!Blanks), (!Indent))), (!Blanks), (!Indent),
          (!Skip), l)
    let rec HVbox0 b i s l = Hvx ((hvlistWidth (l, b, i)), b, i, s, l)
    let rec HOVbox l =
      Hov
        ((hovlistWidth (l, (!Blanks), (!Indent))), (!Blanks), (!Indent),
          (!Skip), l)
    let rec HOVbox0 b i s l = Hov ((hovlistWidth (l, b, i)), b, i, s, l)
    let rec Newpage () = Str (0, (Np ()))
    let rec summaxwidth l =
      List.foldr
        (fun fmt ->
           fun ysum ->
             let (_, y) = Width0 (Hori, Unused, Unused, fmt) in y + ysum) 0 l
    let rec gh __12__ __13__ __14__ =
      match (__12__, __13__, __14__) with
      | (nil, nil, _) -> nil
      | (cg, nil, res) -> rev (((summaxwidth cg), cg, Ebk) :: res)
      | (cg, (Dbk)::t, res) ->
          gh (nil, t, (((summaxwidth cg), cg, Dbk) :: res))
      | (cg, (Brk (_, _) as b)::t, res) ->
          gh (nil, t, (((summaxwidth cg), cg, b) :: res))
      | (cg, h::t, res) -> gh ((cg @ [h]), t, res)
    let rec pphv __15__ __16__ __17__ __18__ __19__ __20__ __21__ __22__
      __23__ __24__ =
      match (__15__, __16__, __17__, __18__, __19__, __20__, __21__, __22__,
              __23__, __24__)
      with
      | (mw, li, bl, is, ss, mp, ch, lb, nil, res) -> ((Max (mp, ch)), res)
      | (mw, li, bl, is, ss, mp, ch, lb, (gpwdth, flist, brk)::t, res) ->
          let (ch1, s1, mp) =
            ((if
                (lb = Ebk) ||
                  ((((li + ch) + (fst (Width0 (Hori, bl, Unused, lb)))) +
                      gpwdth)
                     <= mw)
              then
                let (n, s) = print'p (mw, li, bl, is, ss, Hori, lb, res) in
                ((ch + n), s, mp)
              else
                (let (n, s) = print'p (mw, li, bl, is, ss, Vert, lb, res) in
                 (n, s, (Max (mp, ch)))))
            (* OK - group fits within page or has to fit:
                    horizontal break *)
            (* group will not fit: vertical break.
                    Was last line of maximum width? *)) in
          let (n2, s2) = pph (mw, (li + ch1), bl, is, ss, flist, 0, s1) in
          ((pphv (mw, li, bl, is, ss, mp, (ch1 + n2), brk, t, s2))
            (* horizontal width, string to print, max print width *)
            (* Now print the elements of the group using default for horizontal tabs *)
            (* Now print rest of horizontal-vertical box *))
    let rec ppv __25__ __26__ __27__ __28__ __29__ __30__ __31__ __32__
      __33__ __34__ =
      match (__25__, __26__, __27__, __28__, __29__, __30__, __31__, __32__,
              __33__, __34__)
      with
      | (mw, li, ci, bl, is, ss, max, gw, nil, res) -> ((Max (max, gw)), res)
      | (mw, li, ci, bl, is, ss, max, gw, (Dbk)::t, res) ->
          let (n, s) = print'p (mw, li, bl, is, ss, Vert, Dbk, res) in
          ppv (mw, li, (li + n), bl, is, ss, (Max (max, gw)), n, t, s)
      | (mw, li, ci, bl, is, ss, max, gw, (Brk (_, _) as b)::t, res) ->
          let (n, s) = print'p (mw, li, bl, is, ss, Vert, b, res) in
          ppv (mw, li, (li + n), bl, is, ss, (Max (max, gw)), n, t, s)
      | (mw, li, ci, bl, is, ss, max, gw, h::t, res) ->
          let (n, s) = print'p (mw, ci, bl, is, ss, Vert, h, res) in
          ppv (mw, li, (ci + n), bl, is, ss, max, (gw + n), t, s)
    let rec pph __35__ __36__ __37__ __38__ __39__ __40__ __41__ __42__ =
      match (__35__, __36__, __37__, __38__, __39__, __40__, __41__, __42__)
      with
      | (mw, id, bl, is, ss, nil, nres, sres) -> (nres, sres)
      | (mw, id, bl, is, ss, h::t, nres, sres) ->
          let (n, s) = print'p (mw, id, bl, is, ss, Hori, h, sres) in
          pph (mw, (id + n), bl, is, ss, t, (n + nres), s)
    let rec print'p __43__ __44__ __45__ __46__ __47__ __48__ __49__ __50__ =
      match (__43__, __44__, __45__, __46__, __47__, __48__, __49__, __50__)
      with
      | (mw, id, bl, is, ss, mo, Str (n, s), res) -> (n, (s :: res))
      | (mw, id, bl, is, ss, Hori, Brk (b, i), res) ->
          (b, ((if !Bailout then Spmod b else Sp b) :: res))
      | (mw, id, bl, is, ss, Vert, Brk (b, i), res) ->
          (i,
            (((if !Bailout then Spmod (id + i) else Sp (id + i)) :: (Nl ss))
               :: res))
      | (mw, id, bl, is, ss, Hori, Dbk, res) ->
          (bl, ((if !Bailout then Spmod bl else Sp bl) :: res))
      | (mw, id, bl, is, ss, Vert, Dbk, res) ->
          (is,
            (((if !Bailout then Spmod (id + is) else Sp (id + is)) :: (Nl ss))
               :: res))
      | (mw, id, bl, is, ss, mo, Ebk, res) -> (0, res)
      | (mw, id, bl, is, ss, mo, Hbx ((min, max), blanks, l), res) ->
          if
            (!Bailout) &&
              (((id + min) >= mw) &&
                 ((!) ((>=) (id mod__ (!Pagewidth))) BailoutSpot))
          then
            pph
              ((mw + (!Pagewidth)), (mw + (!BailoutIndent)), blanks, is, ss,
                l, 0, ((Nl ss) :: res))
          else pph (mw, id, blanks, is, ss, l, 0, res)
      | (mw, id, bl, is, ss, mo, Vbx ((min, max), indent, skip, l), res) ->
          if
            (!Bailout) &&
              (((id + min) >= mw) &&
                 ((!) ((>=) (id mod__ (!Pagewidth))) BailoutSpot))
          then
            let id = mw + (!BailoutIndent) in
            ppv
              ((mw + (!Pagewidth)), id, id, bl, indent, skip, 0, 0, l,
                ((Nl ss) :: res))
          else ppv (mw, id, id, bl, indent, skip, 0, 0, l, res)
      | (mw, id, bl, is, ss, mo, Hvx
         (((min, max), (nmode, xmode)), blanks, indent, skip, l), res) ->
          let gl = gh (nil, l, nil) in
          if
            (!Bailout) &&
              (((id + min) >= mw) &&
                 ((!) ((>=) (id mod__ (!Pagewidth))) BailoutSpot))
          then
            pphv
              ((mw + (!Pagewidth)), (mw + (!BailoutIndent)), blanks, indent,
                skip, 0, 0, Ebk, gl, ((Nl ss) :: res))
          else pphv (mw, id, blanks, indent, skip, 0, 0, Ebk, gl, res)
      | (mw, id, bl, is, ss, mo, Hov
         (((min, max), (nmode, xmode)), blanks, indent, skip, l), res) ->
          if max <= (mw - id)
          then
            (if xmode = Hori
             then pph (mw, id, blanks, is, ss, l, 0, res)
             else ppv (mw, id, id, blanks, indent, skip, 0, 0, l, res))
          else
            if
              (!Bailout) &&
                (((id + min) >= mw) &&
                   ((!) ((>=) (id mod__ (!Pagewidth))) BailoutSpot))
            then
              (if nmode = Hori
               then
                 pph
                   ((mw + (!Pagewidth)), (mw + (!BailoutIndent)), blanks, is,
                     ss, l, 0, ((Nl ss) :: res))
               else
                 (let id = mw + (!BailoutIndent) in
                  ppv
                    ((mw + (!Pagewidth)), id, id, blanks, indent, skip, 0, 0,
                      l, ((Nl ss) :: res))))
            else
              if nmode = Hori
              then pph (mw, id, blanks, is, ss, l, 0, res)
              else ppv (mw, id, id, blanks, indent, skip, 0, 0, l, res)
    let rec makestring_fmt fm =
      String.concat
        (rev
           (snd
              (print'p
                 ((!Pagewidth), 0, (!Blanks), (!Indent), (!Skip), Hori, fm,
                   nil))))
    let rec print_fmt fm =
      List.foldr (fun s -> fun _ -> print s) ()
        (snd
           (print'p
              ((!Pagewidth), 0, (!Blanks), (!Indent), (!Skip), Hori, fm, nil)))
    type fmtstream =
      | Formatstream of TextIO.outstream 
    let rec open_fmt outs = Formatstream outs
    let rec close_fmt (Formatstream outs) = outs
    let rec output_fmt (Formatstream outs) fm =
      List.foldr (fun s -> fun _ -> TextIO.output (outs, s)) ()
        (snd
           (print'p
              ((!Pagewidth), 0, (!Blanks), (!Indent), (!Skip), Hori, fm, nil)))
    let rec file_open_fmt filename =
      let fmt_stream = open_fmt (TextIO.openOut filename) in
      let close_func () = TextIO.closeOut (close_fmt fmt_stream) in
      (close_func, fmt_stream)
    let rec with_open_fmt filename func =
      let (close_func, fmt_stream) = file_open_fmt filename in
      let result =
        try func fmt_stream with | exn -> (close_func (); raise exn) in
      close_func (); result
  end ;;




module Formatter : FORMATTER = (Make_Formatter)(struct  end) ;;
