
module type LAYOUT  =
  sig
    type nonrec layout
    val align : layout list -> layout
    val alignPrefix : layout list -> string -> layout
    val array : layout array -> layout
    val detailed : bool ref
    val empty : layout
    val ignore : 'a -> layout
    val isEmpty : layout -> bool
    val mayAlign : layout list -> layout
    val namedRecord : string -> (string * layout) list -> layout
    val indent : int -> layout -> layout
    val list : layout list -> layout
    val listex : string -> string -> string -> layout list -> layout
    val paren : layout -> layout
    val print : layout -> (string -> unit) -> unit
    val record : (string * layout) list -> layout
    val recordex : string -> (string * layout) list -> layout
    val schemeList : layout list -> layout
    val separate : layout list -> string -> layout list
    val separateLeft : layout list -> string -> layout list
    val separateRight : layout list -> string -> layout list
    val seq : layout list -> layout
    val str : string -> layout
    val switch :
      < detailed: 'a -> layout  ;normal: 'a -> layout   >  -> 'a -> layout
    val tostring : layout -> string
    val tostringex : int -> layout -> string
    val tuple : layout list -> layout
    val tuple2 : ('a -> layout) -> ('b -> layout) -> 'a -> 'b -> layout
    val tuple3 :
      ('a -> layout) ->
        ('b -> layout) -> ('c -> layout) -> 'a -> 'b -> 'c -> layout
    val tuple4 :
      ('a -> layout) ->
        ('b -> layout) ->
          ('c -> layout) -> ('d -> layout) -> 'a -> 'b -> 'c -> 'd -> layout
    val tuple5 :
      ('a -> layout) ->
        ('b -> layout) ->
          ('c -> layout) ->
            ('d -> layout) ->
              ('e -> layout) -> 'a -> 'b -> 'c -> 'd -> 'e -> layout
    val vector : layout vector -> layout
  end;;




module Layout : LAYOUT =
  struct
    let detailed = ref false__
    let rec switch { detailed = d; normal = n; normal = n } x =
      if !detailed then d x else n x
    type t =
      | T of < length: int  ;tree: tree   >  
    and tree =
      | Empty 
      | String of string 
      | Sequence of t list 
      | Align of < force: bool  ;rows: t list   >  
      | Indent of (t * int) 
    type nonrec layout = t
    let rec length (__T { length }) = length
    let empty = __T { length = 0; tree = Empty }
    let rec isEmpty = function | __T { length = 0 } -> true__ | _ -> false__
    let rec str s =
      match s with
      | "" -> empty
      | _ -> __T { length = (String.size s); tree = (String s) }
    let rec fold l b f = foldl f b l
    let rec seq ts =
      let len = fold (ts, 0, (fun t -> fun n -> (+) n length t)) in
      match len with
      | 0 -> empty
      | _ -> __T { length = len; tree = (Sequence ts) }
    let rec make force ts =
      let rec loop ts =
        match ts with
        | [] -> (ts, 0)
        | t::ts ->
            let (ts, n) = loop ts in
            (match length t with
             | 0 -> (ts, n)
             | n' -> ((t :: ts), ((n + n') + 1))) in
      let (ts, len) = loop ts in
      match len with
      | 0 -> empty
      | _ -> __T { length = (len - 1); tree = (Align { force; rows = ts }) }
    let align = make true__
    let mayAlign = make false__
    let rec indent t n = __T { length = (length t); tree = (Indent (t, n)) }
    let (tabSize : int) = 8
    let rec K x _ = x
    let rec blanks n =
      (concat
         [CharVector.tabulate ((n div tabSize), (__K '\t'));
         CharVector.tabulate ((n mod__ tabSize), (__K ' '))] : string)
    let rec layout_print
      { tree = (tree : t); print = (print : string -> unit);
        lineWidth = (lineWidth : int); print = (print : string -> unit);
        lineWidth = (lineWidth : int); lineWidth = (lineWidth : int) }
      =
      let rec newline () = print "\n" in
      let rec outputCompact t { at; printAt; printAt } =
        let rec loop (__T { tree }) =
          match tree with
          | Empty -> ()
          | String s -> print s
          | Sequence ts -> app loop ts
          | Indent (t, _) -> loop t
          | Align { rows } ->
              (match rows with
               | [] -> ()
               | t::ts -> (loop t; app (fun t -> print " "; loop t) ts)) in
        let at = (+) at length t in loop t; { at; printAt = at } in
      let rec loop (__T { length; tree; tree } as t)
        ({ at; printAt; printAt } as state) =
        let rec prePrint () =
          ((if at >= printAt then () else print (blanks (printAt - at)))
          (* can't back up *)) in
        ((match tree with
          | Empty -> state
          | Indent (t, n) -> loop (t, { at; printAt = (printAt + n) })
          | Sequence ts -> fold (ts, state, loop)
          | String s ->
              (prePrint ();
               print s;
               (let at = printAt + length in { at; printAt = at }))
          | Align { force; rows; rows } ->
              if (not force) && ((printAt + length) <= lineWidth)
              then (prePrint (); outputCompact (t, state))
              else
                (match rows with
                 | [] -> state
                 | t::ts ->
                     fold
                       (ts, (loop (t, state)),
                         (fun t ->
                            fun _ ->
                              newline (); loop (t, { at = 0; printAt })))))
          (*Out.print (concat ["at ", Int.toString at,
                * "  printAt ", Int.toString printAt,
                * "\n"]);
                *)
          (*outputTree (t, Out.error)*)) in
      ((loop (tree, { at = 0; printAt = 0 }); ())
        (*val _ = outputTree (t, out)*))
    let (defaultWidth : int) = 80
    let rec tostringex wid l =
      let acc = (ref nil : string list ref) in
      let rec pr s = (!) ((::) (acc := s)) acc in
      layout_print { tree = l; lineWidth = wid; print = pr };
      String.concat (rev (!acc))
    let tostring = tostringex defaultWidth
    let print t p =
      layout_print { tree = t; lineWidth = defaultWidth; print = p }
    let rec ignore _ = empty
    let rec separate ts s =
      match ts with
      | [] -> []
      | t::ts ->
          t ::
            (let s = str s in
             let rec loop =
               function | [] -> [] | t::ts -> (s :: t) :: (loop ts) in
             loop ts)
    let rec separateLeft ts s =
      match ts with
      | [] -> []
      | t::[] -> ts
      | t::ts -> t :: (map (fun t -> seq [str s; t]) ts)
    let rec separateRight ts s =
      rev
        (let ts = rev ts in
         match ts with
         | [] -> []
         | t::[] -> ts
         | t::ts -> t :: (map (fun t -> seq [t; str s]) ts))
    let rec alignPrefix ts prefix =
      match ts with
      | [] -> empty
      | t::ts ->
          mayAlign
            [t;
            indent
              ((mayAlign (map (fun t -> seq [str prefix; t]) ts)),
                (~ (String.size prefix)))]
    let rec sequence start finish sep ts =
      seq [str start; mayAlign (separateRight (ts, sep)); str finish]
    let list = sequence ("[", "]", ",")
    let rec listex start finish sep = sequence (start, finish, sep)
    let schemeList = sequence ("(", ")", " ")
    let tuple = sequence ("(", ")", ",")
    let rec record fts =
      sequence ("{", "}", ",")
        (map (fun f -> fun t -> seq [str (f ^ " = "); t]) fts)
    let rec recordex sep fts =
      sequence ("{", "}", ",")
        (map (fun f -> fun t -> seq [str (((f ^ " ") ^ sep) ^ " "); t]) fts)
    let rec vector v = tuple ((::) Vector.foldr [] v)
    let rec array x = list ((::) Array.foldr [] x)
    let rec namedRecord name fields = seq [str name; str " "; record fields]
    let rec paren t = seq [str "("; t; str ")"]
    let rec tuple2 l1 l2 x1 x2 = tuple [l1 x1; l2 x2]
    let rec tuple3 l1 l2 l3 x1 x2 x3 = tuple [l1 x1; l2 x2; l3 x3]
    let rec tuple4 l1 l2 l3 l4 x1 x2 x3 x4 =
      tuple [l1 x1; l2 x2; l3 x3; l4 x4]
    let rec tuple5 l1 l2 l3 l4 l5 x1 x2 x3 x4 x5 =
      tuple [l1 x1; l2 x2; l3 x3; l4 x4; l5 x5]
    let indent x y = indent (y, x)
  end ;;
