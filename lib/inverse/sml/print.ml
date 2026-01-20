
module type PRINT  =
  sig
    val exp_to_string : sgn -> exp -> string
    val spine_to_string : sgn -> spine -> string
    val sub_to_string : sgn -> sub -> string
    val print_exp : sgn -> exp -> unit
    val print_spine : sgn -> spine -> unit
    val print_sub : sgn -> sub -> unit
  end;;




let rec ($) x = Layout.str x let rec (%) x = Layout.mayAlign x
let rec (%%) x = Layout.align x let rec (&) x = Layout.seq x
let rec paren x = (&) [($) "("; x; ($) ")"]
let rec bracket x = (&) [($) "["; x; ($) "]"]
let rec squiggle x = (&) [($) "{"; x; ($) "}"]
let rec indent x = Layout.indent x
let rec uni_to_layout = function | Type -> ($) "type" | Kind -> ($) "kind"
let rec const_to_string sgn c = name (Sig.lookup sgn c)
let rec spine_to_list =
  function | Nil -> [] | App (__E, __S) -> (::) __E spine_to_list __S
let rec head_to_layout __0__ __1__ =
  match (__0__, __1__) with
  | (sgn, Const c) -> ($) (const_to_string sgn c)
  | (sgn, BVar n) -> ($) (Int.toString n)
let rec needs_parens_in_arg_pos =
  function | Uni _ -> false | Root (_, Nil) -> false | _ -> true
let rec needs_sparens_in_arg_pos =
  function
  | Nil -> false
  | App (__E, Nil) -> needs_parens_in_arg_pos __E
  | _ -> true
let rec maybe_paren (__E) l =
  if needs_parens_in_arg_pos __E then paren l else l
let rec maybe_sparen (__S) l =
  if needs_sparens_in_arg_pos __S then paren l else l
let rec spine_to_layout sgn (__S) =
  (%%) (map (exp_to_layout sgn) (spine_to_list __S))
let rec exp_to_layout __2__ __3__ =
  match (__2__, __3__) with
  | (sgn, Uni lev) -> uni_to_layout lev
  | (sgn, Pi pi) ->
      (&) [($) "PI ";
          (%%) [(&) [maybe_paren ((fun r -> r.arg) pi)
                       (exp_to_layout sgn ((fun r -> r.arg) pi));
                    ($) ". "];
               exp_to_layout sgn ((fun r -> r.body) pi)]]
  | (sgn, Lam lam) ->
      (&) [($) "LAM. "; exp_to_layout sgn ((fun r -> r.body) lam)]
  | (sgn, Root (__H, Nil)) -> head_to_layout sgn __H
  | (sgn, Root (__H, __S)) ->
      (&) [head_to_layout sgn __H;
          ($) " ^ ";
          maybe_sparen __S (spine_to_layout sgn __S)]
type subelem =
  | SubShift of int 
  | SubExp of exp 
let rec sub_to_list =
  function
  | Shift n as sub -> [SubShift n]
  | Dot (__M, sub) -> (::) (SubExp __M) sub_to_list sub
  | Comp (s1, s2) -> (@) (sub_to_list s1) sub_to_list s2
let rec sub_to_layout sgn sub =
  let sub' = sub_to_list sub in
  let rec mapfn =
    function
    | SubShift n -> ($) ((^) "^" Int.toString n)
    | SubExp exp -> exp_to_layout sgn exp in
  let sub'' = map mapfn sub' in Layout.list sub''
let rec exp_to_string sgn exp = Layout.tostring (exp_to_layout sgn exp)
let rec spine_to_string sgn sp = Layout.tostring (spine_to_layout sgn sp)
let rec sub_to_string sgn sub = Layout.tostring (sub_to_layout sgn sub)
let rec print_exp sgn exp = print (((^) "\n" exp_to_string sgn exp) ^ "\n")
let rec print_spine sgn sp = print (((^) "\n" spine_to_string sgn sp) ^ "\n")
let rec print_sub sgn sub = print (((^) "\n" sub_to_string sgn sub) ^ "\n");;
