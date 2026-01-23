module type PRINT  =
  sig
    val exp_to_string : sgn -> exp -> string
    val spine_to_string : sgn -> spine -> string
    val sub_to_string : sgn -> sub -> string
    val print_exp : sgn -> exp -> unit
    val print_spine : sgn -> spine -> unit
    val print_sub : sgn -> sub -> unit
  end


let rec ($) x = Layout.str x let rec (%) x = Layout.mayAlign x
let rec (%%) x = Layout.align x let rec (&) x = Layout.seq x
let rec paren x = (&) [($) "("; x; ($) ")"]
let rec bracket x = (&) [($) "["; x; ($) "]"]
let rec squiggle x = (&) [($) "{"; x; ($) "}"]
let rec indent x = Layout.indent x
let rec uni_to_layout =
  begin function | Type -> ($) "type" | Kind -> ($) "kind" end
let rec const_to_string sgn c = name (Sig.lookup sgn c)
let rec spine_to_list =
  begin function | Nil -> [] | App (e_, s_) -> (::) e_ spine_to_list s_ end
let rec head_to_layout arg__0 arg__1 =
  begin match (arg__0, arg__1) with
  | (sgn, Const c) -> ($) (const_to_string sgn c)
  | (sgn, BVar n) -> ($) (Int.toString n) end
let rec needs_parens_in_arg_pos =
  begin function | Uni _ -> false | Root (_, Nil) -> false | _ -> true end
let rec needs_sparens_in_arg_pos =
  begin function
  | Nil -> false
  | App (e_, Nil) -> needs_parens_in_arg_pos e_
  | _ -> true end
let rec maybe_paren (e_) l =
  if needs_parens_in_arg_pos e_ then begin paren l end else begin l end
let rec maybe_sparen (s_) l =
  if needs_sparens_in_arg_pos s_ then begin paren l end else begin l end
let rec spine_to_layout sgn (s_) =
  (%%) (map (exp_to_layout sgn) (spine_to_list s_))
let rec exp_to_layout arg__2 arg__3 =
  begin match (arg__2, arg__3) with
  | (sgn, Uni lev) -> uni_to_layout lev
  | (sgn, Pi pi) ->
      (&) [($) "PI ";
          (%%) [(&) [maybe_paren ((fun r -> r.arg) pi)
                       (exp_to_layout sgn ((fun r -> r.arg) pi));
                    ($) ". "];
               exp_to_layout sgn ((fun r -> r.body) pi)]]
  | (sgn, Lam lam) ->
      (&) [($) "LAM. "; exp_to_layout sgn ((fun r -> r.body) lam)]
  | (sgn, Root (h_, Nil)) -> head_to_layout sgn h_
  | (sgn, Root (h_, s_)) ->
      (&) [head_to_layout sgn h_;
          ($) " ^ ";
          maybe_sparen s_ (spine_to_layout sgn s_)] end
type subelem =
  | SubShift of int 
  | SubExp of exp 
let rec sub_to_list =
  begin function
  | Shift n as sub -> [SubShift n]
  | Dot (m_, sub) -> (::) (SubExp m_) sub_to_list sub
  | Comp (s1, s2) -> (@) (sub_to_list s1) sub_to_list s2 end
let rec sub_to_layout sgn sub =
  let sub' = sub_to_list sub in
  let rec mapfn =
    begin function
    | SubShift n -> ($) ((^) "^" Int.toString n)
    | SubExp exp -> exp_to_layout sgn exp end in
  let sub'' = map mapfn sub' in Layout.list sub''
let rec exp_to_string sgn exp = Layout.tostring (exp_to_layout sgn exp)
let rec spine_to_string sgn sp = Layout.tostring (spine_to_layout sgn sp)
let rec sub_to_string sgn sub = Layout.tostring (sub_to_layout sgn sub)
let rec print_exp sgn exp = print (((^) "\n" exp_to_string sgn exp) ^ "\n")
let rec print_spine sgn sp = print (((^) "\n" spine_to_string sgn sp) ^ "\n")
let rec print_sub sgn sub = print (((^) "\n" sub_to_string sgn sub) ^ "\n")