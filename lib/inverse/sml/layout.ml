module type LAYOUT  =
  sig
    type nonrec layout
    val align : layout list -> layout
    val alignPrefix : (layout list * string) -> layout
    val array : layout array -> layout
    val detailed : bool ref
    val empty : layout
    val ignore : 'a -> layout
    val isEmpty : layout -> bool
    val mayAlign : layout list -> layout
    val namedRecord : (string * (string * layout) list) -> layout
    val indent : int -> layout -> layout
    val list : layout list -> layout
    val listex : string -> string -> string -> layout list -> layout
    val paren : layout -> layout
    val print : (layout * (string -> unit)) -> unit
    val record : (string * layout) list -> layout
    val recordex : string -> (string * layout) list -> layout
    val schemeList : layout list -> layout
    val separate : (layout list * string) -> layout list
    val separateLeft : (layout list * string) -> layout list
    val separateRight : (layout list * string) -> layout list
    val seq : layout list -> layout
    val str : string -> layout
    val switch :
      < detailed: 'a -> layout  ;normal: 'a -> layout   >  -> 'a -> layout
    val tostring : layout -> string
    val tostringex : int -> layout -> string
    val tuple : layout list -> layout
    val tuple2 : (('a -> layout) * ('b -> layout)) -> ('a * 'b) -> layout
    val tuple3 :
      (('a -> layout) * ('b -> layout) * ('c -> layout)) ->
        ('a * 'b * 'c) -> layout
    val tuple4 :
      (('a -> layout) * ('b -> layout) * ('c -> layout) * ('d -> layout)) ->
        ('a * 'b * 'c * 'd) -> layout
    val tuple5 :
      (('a -> layout) * ('b -> layout) * ('c -> layout) * ('d -> layout) *
        ('e -> layout)) -> ('a * 'b * 'c * 'd * 'e) -> layout
    val vector : layout vector -> layout
  end


module Layout : LAYOUT =
  struct
    let detailed = ref false
    let rec switch { detailed = d; normal = n; normal = n } x =
      if !detailed then begin d x end else begin n x end
  type t =
    | t_ of < length: int  ;tree: tree   > 
    [@sml.renamed "t_"][@sml.renamed "t_"]
  and tree =
    | Empty 
    | String of string 
    | Sequence of t list 
    | Align of < force: bool  ;rows: t list   >  
    | Indent of (t * int) 
  type nonrec layout = t
  let rec length (t___ { length }) = length
  let empty = t_ { length = 0; tree = Empty }
  let rec isEmpty =
    begin function | t___ { length = 0 } -> true | _ -> false end
let rec str s =
  begin match s with
  | "" -> empty
  | _ -> t_ { length = (String.size s); tree = (String s) } end
let rec fold (l, b, f) = foldl f b l
let rec seq ts =
  let len = fold (ts, 0, (begin function | (t, n) -> (+) n length t end)) in
begin match len with
| 0 -> empty
| _ -> t_ { length = len; tree = (Sequence ts) } end
let rec make force ts =
  let rec loop ts =
    begin match ts with
    | [] -> (ts, 0)
    | t::ts ->
        let (ts, n) = loop ts in
        (begin match length t with
         | 0 -> (ts, n)
         | n' -> ((t :: ts), ((n + n') + 1)) end) end in
let (ts, len) = loop ts in
begin match len with
| 0 -> empty
| _ -> t_ { length = (len - 1); tree = (Align { force; rows = ts }) } end
let align = make true
let mayAlign = make false
let rec indent (t, n) = t_ { length = (length t); tree = (Indent (t, n)) }
let (tabSize : int) = 8
let rec k_ x _ = x
let rec blanks (n : int) =
  (concat
     [CharVector.tabulate ((n div tabSize), (k_ 't'));
     CharVector.tabulate ((n mod_ tabSize), (k_ ' '))] : string)
let rec layout_print
  { tree = (tree : t); print = (print : string -> unit);
    lineWidth = (lineWidth : int); print = (print : string -> unit);
    lineWidth = (lineWidth : int); lineWidth = (lineWidth : int) }
  =
  let rec newline () = print "\n" in
  let rec outputCompact (t, { at; printAt; printAt }) =
    let rec loop (t___ { tree }) =
      begin match tree with
      | Empty -> ()
      | String s -> print s
      | Sequence ts -> app loop ts
      | Indent (t, _) -> loop t
      | Align { rows } ->
          (begin match rows with
           | [] -> ()
           | t::ts ->
               (begin loop t;
                app (begin function | t -> (begin print " "; loop t end) end)
               ts end) end) end in
let at = (+) at length t in begin loop t; { at; printAt = at } end in
let rec loop
((t___ { length; tree; tree } as t), ({ at; printAt; printAt } as state)) =
let rec prePrint () = ((if at >= printAt then begin () end
  else begin print (blanks (printAt - at)) end)
(* can't back up *)) in
((begin match tree with
| Empty -> state
| Indent (t, n) -> loop (t, { at; printAt = (printAt + n) })
| Sequence ts -> fold (ts, state, loop)
| String s ->
    (begin prePrint ();
     print s;
     (let at = printAt + length in { at; printAt = at }) end)
| Align { force; rows; rows } ->
    if (not force) && ((printAt + length) <= lineWidth)
    then begin (begin prePrint (); outputCompact (t, state) end) end
else begin
  (begin match rows with
   | [] -> state
   | t::ts ->
       fold
         (ts, (loop (t, state)),
           (begin function
            | (t, _) -> (begin newline (); loop (t, { at = 0; printAt }) end) end)) end) end end)
(*Out.print (concat ["at ", Int.toString at,
                * "  printAt ", Int.toString printAt,
                * "\n"]);
                *)
(*outputTree (t, Out.error)*)) in
((begin loop (tree, { at = 0; printAt = 0 }); () end)
(*val _ = outputTree (t, out)*))
let (defaultWidth : int) = 80
let rec tostringex wid l =
  let acc = (ref [] : string list ref) in
  let rec pr s = (!) ((::) (acc := s)) acc in
  begin layout_print { tree = l; lineWidth = wid; print = pr };
  String.concat (rev !acc) end
let tostring = tostringex defaultWidth
let print =
  begin function
  | (t, p) -> layout_print { tree = t; lineWidth = defaultWidth; print = p } end
let rec ignore _ = empty
let rec separate (ts, s) =
  begin match ts with
  | [] -> []
  | t::ts ->
      t ::
        (let s = str s in
         let rec loop =
           begin function | [] -> [] | t::ts -> (s :: t) :: (loop ts) end in
         loop ts) end
let rec separateLeft (ts, s) =
  begin match ts with
  | [] -> []
  | t::[] -> ts
  | t::ts -> t :: (map (begin function | t -> seq [str s; t] end) ts) end
let rec separateRight (ts, s) =
  rev
    (let ts = rev ts in
     begin match ts with
     | [] -> []
     | t::[] -> ts
     | t::ts -> t :: (map (begin function | t -> seq [t; str s] end) ts) end)
let rec alignPrefix (ts, prefix) =
  begin match ts with
  | [] -> empty
  | t::ts ->
      mayAlign
        [t;
        indent
          ((mayAlign (map (begin function | t -> seq [str prefix; t] end) ts)),
          (- (String.size prefix)))] end
let rec sequence (start, finish, sep) ts =
  seq [str start; mayAlign (separateRight (ts, sep)); str finish]
let list = sequence ("[", "]", ",")
let rec listex start finish sep = sequence (start, finish, sep)
let schemeList = sequence ("(", ")", " ")
let tuple = sequence ("(", ")", ",")
let rec record fts =
  sequence ("{", "}", ",")
    (map (begin function | (f, t) -> seq [str (f ^ " = "); t] end) fts)
let rec recordex sep fts =
  sequence ("{", "}", ",")
    (map
       (begin function | (f, t) -> seq [str (((f ^ " ") ^ sep) ^ " "); t] end)
    fts)
let rec vector v = tuple ((::) Vector.foldr [] v)
let rec array x = list ((::) Array.foldr [] x)
let rec namedRecord (name, fields) = seq [str name; str " "; record fields]
let rec paren t = seq [str "("; t; str ")"]
let rec tuple2 (l1, l2) (x1, x2) = tuple [l1 x1; l2 x2]
let rec tuple3 (l1, l2, l3) (x1, x2, x3) = tuple [l1 x1; l2 x2; l3 x3]
let rec tuple4 (l1, l2, l3, l4) (x1, x2, x3, x4) =
  tuple [l1 x1; l2 x2; l3 x3; l4 x4]
let rec tuple5 (l1, l2, l3, l4, l5) (x1, x2, x3, x4, x5) =
  tuple [l1 x1; l2 x2; l3 x3; l4 x4; l5 x5]
let indent = begin function | x -> (begin function | y -> indent (y, x) end) end
end
