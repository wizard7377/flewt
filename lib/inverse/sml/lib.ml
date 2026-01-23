module type LIB  =
  sig
    exception Not_implemented 
    val andalso' : bool -> bool -> bool
    val orelse' : bool -> bool -> bool
    val fst : ('a * 'b) -> 'a
    val snd : ('a * 'b) -> 'b
    val is_none : 'a option -> bool
    val is_some : 'a option -> bool
    val the : 'a option -> 'a
    val incr : int ref -> unit
    val (+=) : (int ref * int) -> unit
    val (-=) : (int ref * int) -> unit
    val decr : int ref -> unit
    val ::= : ('a list ref * 'a) -> unit
    val (@=) : ('a list ref * 'a list) -> unit
    type nonrec 'a stream
    val listof_s : int -> 'a stream -> 'a list
    val nth_s : int -> 'a stream -> 'a
    val curry : (('a * 'b) -> 'c) -> 'a -> 'b -> 'c
    val uncurry : ('a -> 'b -> 'c) -> ('a * 'b) -> 'c
    val curry3 : (('a * 'b * 'c) -> 'd) -> 'a -> 'b -> 'c -> 'd
    val id : 'a -> 'a
    val can : ('a -> 'b) -> 'a -> bool
    val cant : ('a -> 'b) -> 'a -> bool
    val can2 : ('a -> 'b -> 'c) -> 'a -> 'b -> bool
    val ceq : 'a -> 'a -> bool
    val swap : ('a -> 'b -> 'c) -> 'b -> 'a -> 'c
    val apply : (('a -> 'b) * 'a) -> 'b
    val repeat : ('a -> 'a) -> int -> 'a -> 'a
    val sum : int list -> int
    val max : int list -> int
    val upto : (int * int) -> int list
    val (--) : (int * int) -> int list
    val (--<) : (int * int) -> int list
    val real_max : real list -> real
    val real_sum : real list -> real
    val string_ord : (string * string) -> order
    val int_ord : (int * int) -> order
    val lex_ord :
      (('a * 'b) -> order) ->
        (('c * 'd) -> order) -> (('a * 'c) * ('b * 'd)) -> order
    val eq_ord : ('a * 'a) -> order
    val assert_ : bool -> string -> unit
    val warn : bool ref
    val warning : string -> unit
    val cons : 'a -> 'a list -> 'a list
    val list : 'a -> 'a list
    val itlist : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
    val citlist : (('a * 'b) -> 'b) -> 'a list -> 'b -> 'b
    val ith : int -> 'a list -> 'a
    val map2 : (('a * 'b) -> 'c) -> 'a list -> 'b list -> 'c list
    val map3 :
      (('a * 'b * 'c) -> 'd) -> 'a list -> 'b list -> 'c list -> 'd list
    val zip : 'a list -> 'b list -> ('a * 'b) list
    val zip3 : 'a list -> 'b list -> 'c list -> ('a * 'b * 'c) list
    val zip4 :
      'a list -> 'b list -> 'c list -> 'd list -> ('a * 'b * 'c * 'd) list
    val zip5 :
      'a list ->
        'b list ->
          'c list -> 'd list -> 'e list -> ('a * 'b * 'c * 'd * 'e) list
    val unzip : ('a * 'b) list -> ('a list * 'b list)
    val unzip3 : ('a * 'b * 'c) list -> ('a list * 'b list * 'c list)
    val unzip4 :
      ('a * 'b * 'c * 'd) list -> ('a list * 'b list * 'c list * 'd list)
    val (~~) : ('a list * 'b list) -> ('a * 'b) list
    val end_itlist : ('a -> 'a -> 'a) -> 'a list -> 'a
    val end_citlist : (('a * 'a) -> 'a) -> 'a list -> 'a
    val itlist2 : ('a -> 'b -> 'c -> 'c) -> 'a list -> 'b list -> 'c -> 'c
    val rev_itlist : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
    val rev_end_itlist : ('a -> 'a -> 'a) -> 'a list -> 'a
    val replicate : 'a -> int -> 'a list
    val exists : ('a -> bool) -> 'a list -> bool
    val forall : ('a -> bool) -> 'a list -> bool
    val last : 'a list -> 'a
    val butlast : 'a list -> 'a list
    val gen_list_eq : (('a * 'b) -> order) -> 'a list -> 'b list -> bool
    val list_eq : 'a list -> 'a list -> bool
    val partition : ('a -> bool) -> 'a list -> ('a list * 'a list)
    val filter : ('a -> bool) -> 'a list -> 'a list
    val sort : (('a * 'a) -> order) -> 'a list -> 'a list
    val uniq : (('a * 'a) -> order) -> 'a list -> 'a list
    val uniq_list : (('a * 'a) -> order) -> 'a list -> bool
    val split_at : int -> 'a list -> ('a list * 'a list)
    val list_prefix : int -> 'a list -> 'a list
    val list_slice : int -> int -> 'a list -> 'a list
    val shuffle : 'a list -> 'a list -> 'a list
    val find_index : ('a -> bool) -> 'a list -> int option
    val index : 'a -> 'a list -> int option
    val find_last_index : ('a -> bool) -> 'a list -> int option
    val last_index : 'a -> 'a list -> int option
    val flatten : 'a list list -> 'a list
    val chop_list : int -> 'a list -> ('a list * 'a list)
    val list_to_string : ('a -> string) -> 'a list -> string
    val remove : ('a -> bool) -> 'a list -> ('a * 'a list)
    val do_list : ('a -> 'b) -> 'a list -> unit
    val exn_index : ('a -> 'b) -> 'a list -> int option
    val gen_setify : (('a * 'a) -> order) -> 'a list -> 'a list
    val setify : 'a list -> 'a list
    val gen_mem : (('a * 'b) -> order) -> 'a -> 'b list -> bool
    val mem : 'a -> 'a list -> bool
    val insert : 'a -> 'a list -> 'a list
    val gen_disjoint : (('a * 'b) -> order) -> 'a list -> 'b list -> bool
    val disjoint : 'a list -> 'a list -> bool
    val gen_pairwise_disjoint : (('a * 'a) -> order) -> 'a list list -> bool
    val pairwise_disjoint : 'a list list -> bool
    val gen_set_eq : (('a * 'a) -> order) -> 'a list -> 'a list -> bool
    val diff : 'a list -> 'a list -> 'a list
    val union : 'a list -> 'a list -> 'a list
    val unions : 'a list list -> 'a list
    val intersect : 'a list -> 'a list -> 'a list
    val subtract : 'a list -> 'a list -> 'a list
    val subset : 'a list -> 'a list -> bool
    val set_eq : 'a list -> 'a list -> bool
    val find : ('a -> bool) -> 'a list -> 'a option
    val assoc : 'a -> ('a * 'b) list -> 'b option
    val rev_assoc : 'a -> ('b * 'a) list -> 'b option
    val printl : string -> unit
  end


module Lib : LIB =
  struct
    exception Not_implemented 
    let rec andalso' x y = x && y
    let rec orelse' x y = x || y
    let rec fst (x, y) = x
    let rec snd (x, y) = y
    let rec is_none = begin function | None -> true | Some _ -> false end
    let rec is_some = begin function | None -> false | Some _ -> true end
  let rec the = begin function | None -> raise (Fail "the") | Some x -> x end
let rec x ((+=)) n = (x := !x) + n
let rec x ((-=)) n = (x := !x) - n
let rec incr x = x += 1
let rec decr x = x -= 1
let rec l (::=) v = (l := v) :: !l
let rec l ((@=)) l' = (l := !l) @ l'
type 'a stream =
  | SNil 
  | SCons of (unit -> ('a * 'a stream)) 
let rec constant_s x = SCons (begin function | () -> (x, (constant_s x)) end)
let rec ones_f n = SCons (begin function | () -> (n, (ones_f (n + 1))) end)
let nat_s = ones_f 0
let rec nth_s arg__0 arg__1 =
  begin match (arg__0, arg__1) with
  | (n, SNil) -> raise (Fail "s_nth")
  | (0, SCons f) -> fst (f ())
  | (n, SCons f) -> let (_, s') = f () in nth_s (n - 1) s' end
let rec listof_s arg__2 arg__3 =
  begin match (arg__2, arg__3) with
  | (0, _) -> []
  | (n, SNil) -> raise (Fail "listof_s")
  | (n, SCons f) -> let (v, s) = f () in (::) v listof_s (n - 1) s end
let rec curry f x y = f (x, y)
let rec uncurry f (x, y) = f x y
let rec curry3 f x y z = f (x, y, z)
let rec id x = x
let rec can f x = begin try begin f x; true end with | _ -> false end
let rec cant f x = begin try begin f x; false end with | _ -> true end
let rec can2 f x y = begin try begin f x y; true end with | _ -> false end
let rec ceq x y = x = y
let rec oo f g x y = f (g x y)
let rec ooo f g x y z = f (g x y z)
let rec oooo f g x y z w = f (g x y z w)
let rec swap f x y = f y x
let rec apply (f, x) = f x
let rec repeat f n x = if n = 0 then begin x end
  else begin repeat f (n - 1) (f x) end
let rec max xs = foldr Int.max 0 xs
let rec sum ns = foldr (+) 0 ns
let rec uptoby k m n = if m > n then begin [] end
  else begin m :: (uptoby k (m + k) n) end
let upto = uncurry (uptoby 1)
let (--) = upto
let rec x ((--<)) y = x -- (y - 1)
let rec pow x n =
  begin match n with
  | 0 -> 1
  | n ->
      if (Int.mod_ (n, 2)) = 0
      then begin let n' = pow x (Int.div (n, 2)) in n' * n' end
      else begin ( * ) x pow x (n - 1) end end
let rec log n =
  let rec log n even =
    begin match n with
    | 1 -> (0, even)
    | n ->
        let (ln, even') = log (Int.div (n, 2)) even in
        let even'' = even' && ((Int.mod_ (n, 2)) = 0) in ((1 + ln), even'') end in
log n true
let rec real_max xs = foldr Real.max 0.0 xs
let rec real_sum rs = foldr (+) 0.0 rs
let rec string_ord ((s1 : string), s2) = if s1 < s2 then begin LESS end
  else begin if s1 = s2 then begin EQUAL end else begin GREATER end end
let rec int_ord ((s1 : int), s2) = if s1 < s2 then begin LESS end
  else begin if s1 = s2 then begin EQUAL end else begin GREATER end end
let rec lex_ord o1 o2 ((x1, y1), (x2, y2)) =
  begin match o1 (x1, x2) with | EQUAL -> o2 (y1, y2) | x -> x end
let rec eq_ord (x, y) = if x = y then begin EQUAL end else begin LESS end
let rec assert_ b s = if b then begin () end
  else begin raise (Fail ("Assertion Failure: " ^ s)) end
let warn = ref true
let rec warning s =
  if !warn then begin TextIO.print (("Warning: " ^ s) ^ "\n") end
  else begin () end
let rec list x = [x]
let rec cons x xs = x :: xs
let rec itlist arg__4 arg__5 arg__6 =
  begin match (arg__4, arg__5, arg__6) with
  | (f, [], b) -> b
  | (f, h::t, b) -> f h (itlist f t b) end
let rec citlist f l b = itlist (curry f) l b
let rec ith arg__7 arg__8 =
  begin match (arg__7, arg__8) with
  | (i, []) -> raise (Fail "ith: empty")
  | (0, h::t) -> h
  | (n, h::t) -> ith (n - 1) t end
let rec map2 arg__9 arg__10 arg__11 =
  begin match (arg__9, arg__10, arg__11) with
  | (f, [], []) -> []
  | (f, h1::t1, h2::t2) -> (::) (f (h1, h2)) map2 f t1 t2
  | (f, _, _) -> raise (Fail "map2: length mismatch") end
let rec map3 arg__12 arg__13 arg__14 arg__15 =
  begin match (arg__12, arg__13, arg__14, arg__15) with
  | (f, [], [], []) -> []
  | (f, h1::t1, h2::t2, h3::t3) -> (::) (f (h1, h2, h3)) map3 f t1 t2 t3
  | (f, _, _, _) -> raise (Fail "map3: unequal lengths") end
let rec map4 arg__16 arg__17 arg__18 arg__19 arg__20 =
  begin match (arg__16, arg__17, arg__18, arg__19, arg__20) with
  | (f, [], [], [], []) -> []
  | (f, h1::t1, h2::t2, h3::t3, h4::t4) ->
      (::) (f (h1, h2, h3, h4)) map4 f t1 t2 t3 t4
  | (f, _, _, _, _) -> raise (Fail "map4: unequal lengths") end
let rec map5 arg__21 arg__22 arg__23 arg__24 arg__25 arg__26 =
  begin match (arg__21, arg__22, arg__23, arg__24, arg__25, arg__26) with
  | (f, [], [], [], [], []) -> []
  | (f, h1::t1, h2::t2, h3::t3, h4::t4, h5::t5) ->
      (::) (f (h1, h2, h3, h4, h5)) map5 f t1 t2 t3 t4 t5
  | (f, _, _, _, _, _) -> raise (Fail "map5: unequal lengths") end
let rec zip l1 l2 = map2 id l1 l2
let rec zip3 l1 l2 l3 = map3 id l1 l2 l3
let rec zip4 l1 l2 l3 l4 = map4 id l1 l2 l3 l4
let rec zip5 l1 l2 l3 l4 l5 = map5 id l1 l2 l3 l4 l5
let rec unzip l =
  itlist
    (begin function
     | (h1, h2) -> (begin function | (t1, t2) -> ((h1 :: t1), (h2 :: t2)) end) end)
  l ([], [])
let rec unzip3 l =
  itlist
    (begin function
     | (h1, h2, h3) ->
         (begin function
          | (t1, t2, t3) -> ((h1 :: t1), (h2 :: t2), (h3 :: t3)) end) end)
  l ([], [], [])
let rec unzip4 l =
  itlist
    (begin function
     | (h1, h2, h3, h4) ->
         (begin function
          | (t1, t2, t3, t4) ->
              ((h1 :: t1), (h2 :: t2), (h3 :: t3), (h4 :: t4)) end) end)
  l ([], [], [], [])
let rec x ((~~)) y = zip x y
let rec end_itlist arg__27 arg__28 =
  begin match (arg__27, arg__28) with
  | (f, []) -> raise (Fail "end_itlist")
  | (f, x::[]) -> x
  | (f, h::t) -> f h (end_itlist f t) end
let rec end_citlist f l = end_itlist (curry f) l
let rec itlist2 arg__29 arg__30 arg__31 arg__32 =
  begin match (arg__29, arg__30, arg__31, arg__32) with
  | (f, [], [], b) -> b
  | (f, h1::t1, h2::t2, b) -> f h1 h2 (itlist2 f t1 t2 b)
  | (_, _, _, _) -> raise (Fail "itlist2") end
let rec rev_itlist arg__33 arg__34 arg__35 =
  begin match (arg__33, arg__34, arg__35) with
  | (f, [], b) -> b
  | (f, h::t, b) -> rev_itlist f t (f h b) end
let rec rev_end_itlist arg__36 arg__37 =
  begin match (arg__36, arg__37) with
  | (f, []) -> raise (Fail "rev_end_itlist")
  | (f, x::[]) -> x
  | (f, h::t) -> f (rev_end_itlist f t) h end
let rec replicate arg__38 arg__39 =
  begin match (arg__38, arg__39) with
  | (x, 0) -> []
  | (x, n) -> if n > 0 then begin (::) x replicate x (n - 1) end
      else begin [] end end
let rec exists arg__40 arg__41 =
  begin match (arg__40, arg__41) with
  | (f, []) -> false
  | (f, h::t) -> (f h) || (exists f t) end
let rec forall arg__42 arg__43 =
  begin match (arg__42, arg__43) with
  | (f, []) -> true
  | (f, h::t) -> (f h) && (forall f t) end
let rec last =
  begin function | [] -> raise (Fail "Last") | h::[] -> h | h::t -> last t end
let rec butlast =
  begin function
  | [] -> raise (Fail "Butlast")
  | h::[] -> []
  | h::t -> (::) h butlast t end
let rec gen_list_eq ord l1 l2 =
  itlist2
    (begin function
     | x ->
         (begin function
          | y -> (begin function | z -> ((ord (x, y)) = EQUAL) && z end) end) end)
l1 l2
true
let rec list_eq l1 l2 = gen_list_eq eq_ord l1 l2
let rec partition arg__44 arg__45 =
  begin match (arg__44, arg__45) with
  | (p, []) -> ([], [])
  | (p, h::t) ->
      let (l, r) = partition p t in if p h then begin ((h :: l), r) end
        else begin (l, (h :: r)) end end
let rec filter p l = fst (partition p l)
let rec sort arg__46 arg__47 =
  begin match (arg__46, arg__47) with
  | (ord, []) -> []
  | (ord, piv::rest) ->
      let (l, r) =
        partition (begin function | x -> (ord (x, piv)) = LESS end) rest in
    (sort ord l) @ (piv :: (sort ord r)) end
let rec uniq arg__48 arg__49 =
  begin match (arg__48, arg__49) with
  | (ord, x::(y::_ as t)) ->
      let t' = uniq ord t in if (ord (x, y)) = EQUAL then begin t' end
        else begin x :: t' end
  | (_, l) -> l end
let rec uniq_list comp l = (=) (length (uniq comp l)) length l
let rec split_at arg__50 arg__51 =
  begin match (arg__50, arg__51) with
  | (_, []) -> raise (Fail "split_at: splitting empty")
  | (0, l) -> ([], l)
  | (n, (x::ys as xs)) ->
      if n < 0 then begin raise (Fail "split_at: arg out of range") end
      else begin (let (ps, qs) = split_at (n - 1) ys in ((x :: ps), qs)) end end
let rec list_prefix n l =
  begin try fst (split_at n l) with | Fail _ -> raise (Fail "list_prefix") end
let rec list_slice n m l =
  let (_, r) = split_at n l in let (l', _) = split_at m r in l'
let rec shuffle arg__52 arg__53 =
  begin match (arg__52, arg__53) with
  | ([], l2) -> l2
  | (l1, []) -> l1
  | (h1::t1, h2::t2) -> (::) (h1 :: h2) shuffle t1 t2 end
let rec find_index p =
  let rec ind arg__54 arg__55 =
    begin match (arg__54, arg__55) with
    | (n, []) -> None
    | (n, h::t) -> if p h then begin Some n end else begin ind (n + 1) t end end in
ind 0
let rec index x l = find_index (ceq x) l
let rec find_last_index p l =
  let n = length l in
  let l' = rev l in
  begin match find_index p l' with
  | Some n' -> Some ((n - n') - 1)
  | None -> None end
let rec last_index x l = find_last_index (ceq x) l
let rec flatten l = itlist (curry (@)) l []
let rec chop_list arg__56 arg__57 =
  begin match (arg__56, arg__57) with
  | (0, l) -> ([], l)
  | (n, l) ->
      (begin try
               let (l1, l2) = chop_list (n - 1) (tl l) in
               (((List.hd l) :: l1), l2)
       with | _ -> raise (Fail "chop_list") end) end
let rec list_to_string f l =
  let l' = map f l in
  itlist (begin function | x -> (begin function | y -> (x ^ ",") ^ y end) end)
  (("[" :: l') @ ["]"]) ""
let rec remove arg__58 arg__59 =
  begin match (arg__58, arg__59) with
  | (p, []) -> raise (Fail "remove")
  | (p, h::t) -> if p h then begin (h, t) end
      else begin (let (y, n) = remove p t in (y, (h :: n))) end end
let rec do_list arg__60 arg__61 =
  begin match (arg__60, arg__61) with
  | (f, []) -> ()
  | (f, h::t) -> (begin f h; do_list f t end) end
let rec exn_index f l =
  let rec exn_index arg__62 arg__63 arg__64 =
    begin match (arg__62, arg__63, arg__64) with
    | (f, [], n) -> None
    | (f, h::t, n) -> if can f h then begin exn_index f t (n + 1) end
        else begin Some n end end in
exn_index f l 0
let rec gen_setify ord s = uniq ord (sort ord s)
let rec setify s = gen_setify eq_ord s
let rec gen_mem arg__65 arg__66 arg__67 =
  begin match (arg__65, arg__66, arg__67) with
  | (ord, x, []) -> false
  | (ord, x, h::t) -> if (ord (x, h)) = EQUAL then begin true end
      else begin gen_mem ord x t end end
let rec mem x l = gen_mem eq_ord x l
let rec insert x l = if mem x l then begin l end else begin x :: l end
let rec gen_disjoint ord l1 l2 =
  forall (begin function | x -> not (gen_mem ord x l2) end) l1
let rec disjoint l = gen_disjoint eq_ord l
let rec gen_pairwise_disjoint arg__68 arg__69 =
  begin match (arg__68, arg__69) with
  | (p, []) -> true
  | (p, h::t) -> (forall (gen_disjoint p h) t) && (gen_pairwise_disjoint p t) end
let rec pairwise_disjoint t = gen_pairwise_disjoint eq_ord t
let rec gen_set_eq ord l1 l2 =
  gen_list_eq ord (gen_setify ord l1) (gen_setify ord l2)
let rec diff arg__70 arg__71 =
  begin match (arg__70, arg__71) with
  | ([], l) -> []
  | (h::t, l) -> if mem h l then begin diff t l end
      else begin (::) h diff t l end end
let rec union l1 l2 = itlist insert l1 l2
let rec unions l = itlist union l []
let rec intersect l1 l2 = filter (begin function | x -> mem x l2 end) l1
let rec subtract l1 l2 = filter (begin function | x -> not (mem x l2) end) l1
let rec subset l1 l2 = forall (begin function | t -> mem t l2 end) l1
let rec set_eq l1 l2 = (subset l1 l2) && (subset l2 l1)
let rec find arg__72 arg__73 =
  begin match (arg__72, arg__73) with
  | (p, []) -> None
  | (p, h::t) -> if p h then begin Some h end else begin find p t end end
let rec assoc x l =
  begin match find (begin function | p -> (fst p) = x end) l with
  | Some (x, y) -> Some y | None -> None end
let rec rev_assoc x l =
  begin match find (begin function | p -> (snd p) = x end) l with
  | Some (x, y) -> Some x | None -> None end
let rec char_max c1 c2 = if (<) (Char.ord c1) Char.ord c2 then begin c1 end
  else begin c2 end
let rec string_lt (x : string) y = x < y
let rec collect l = itlist (curry (^)) l ""
let rec commas n = replicate "," n
let rec shuffle_commas l = shuffle l (commas ((length l) - 1))
let rec semis n = replicate ";" n
let rec parenify x = collect ["("; x; ")"]
let rec postfix n s = substring (s, ((size s) - n), n)
let numeric_chars = "0123456789"
let lowercase_chars = "abcdefghijklmnopqrstuvwxyz"
let uppercase_chars = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
let alpha_chars = lowercase_chars ^ uppercase_chars
let alphanum_chars = alpha_chars ^ numeric_chars
let word_sym_chars = "_'"
let word_chars = alphanum_chars ^ word_sym_chars
let explode = String.explode
let rec is_legal u s = forall (begin function | x -> mem x (explode u) end)
  (explode s)
let is_numeric = is_legal numeric_chars
let is_lower = is_legal lowercase_chars
let is_upper = is_legal uppercase_chars
let is_alpha = is_legal alpha_chars
let is_alnum = is_legal alphanum_chars
let is_word_sym = is_legal word_sym_chars
let is_word = is_legal word_chars
let to_lower = String.translate (Char.toString o Char.toLower)
let to_upper = String.translate (Char.toString o Char.toUpper)
let rec capitalize s =
  begin match map Char.toString (explode s) with
  | [] -> ""
  | h::t -> concat ([to_upper h] @ (map to_lower t)) end
let newline = Char.toString '\n'
let rec ends_with s e =
  begin try (substring (s, ((-) (size s) size e), (size e))) = e
  with | _ -> false end
let rec starts_with s e =
  begin try (substring (s, 0, (size e))) = e with | _ -> false end
let rec strip_path c s =
  let n =
    begin match index c (String.explode s) with
    | Some x -> x
    | None -> raise (Fail "strip_path") end in
let m = substring (s, 0, n) in
let m' = substring (s, (n + 1), (((size s) - n) - 1)) in (m, m')
let rec rev_strip_path c s =
  let no = last_index c (String.explode s) in
  let n =
    begin match no with | Some x -> x | None -> raise (Fail "rev_strip_path") end in
  let m = substring (s, 0, n) in
  let m' = substring (s, (n + 1), (((size s) - n) - 1)) in (m, m')
let rec the = begin function | Some x -> x | _ -> raise (Fail "the") end
let rec is_some = begin function | Some _ -> true | _ -> false end
let rec is_none = begin function | None -> true | _ -> false end
let rec list_of_opt_list =
  begin function
  | [] -> []
  | (None)::t -> list_of_opt_list t
  | (Some x)::t -> (::) x list_of_opt_list t end
let rec get_opt arg__74 arg__75 =
  begin match (arg__74, arg__75) with
  | (Some x, _) -> x
  | (None, err) -> raise (Fail err) end
let rec get_list = begin function | Some l -> l | None -> [] end
let rec conv_opt arg__76 arg__77 =
  begin match (arg__76, arg__77) with
  | (f, Some l) -> Some (f l)
  | (f, None) -> None end
let rec time f x =
  let timer = Timer.startCPUTimer () in
  begin try
          let res = f x in
          let time = Timer.checkCPUTimer timer in
          let _ =
            print
              ((^) "CPU time (user): " Time.toString ((fun r -> r.usr) time)) in
          res
  with
  | e ->
      let time = Timer.checkCPUTimer timer in
      (begin print
               ((^) "Failed after (user) CUP time of " Time.toString
                  ((fun r -> r.usr) time));
       raise e end) end
let rec printl s = print (s ^ "\n")
let rec read_file file =
  let f = TextIO.openIn file in
  let s = TextIO.inputAll f in let _ = TextIO.closeIn f in s
let rec write_file file s =
  let f = TextIO.openOut file in
  let _ = TextIO.output (f, s) in let _ = TextIO.closeOut f in ()
let rec write_file_append file s =
  let f = TextIO.openAppend file in
  let _ = TextIO.output (f, s) in let _ = TextIO.closeOut f in ()
let rec all_dir_files dir =
  let str = OS.FileSys.openDir dir in
  let fs = ref [] in
  let f = ref (OS.FileSys.readDir str) in
  begin while !f <> None do
          (begin ::= fs the !f; (:=) f OS.FileSys.readDir str end)
  done; !fs end end
