module type SYNTAX  =
  sig
    type nonrec const = int
    type uni =
      | Type 
      | Kind 
    type head =
      | Const of const 
      | BVar of int 
    type depend =
      | No 
      | Maybe 
    type exp =
      | Uni of uni 
      | Pi of pi 
      | Lam of lam 
      | Root of (head * spine) 
      | Redex of (exp * spine) 
      | EClo of (exp * sub) 
    and spine =
      | Nil 
      | App of (exp * spine) 
      | SClo of (spine * sub) 
    and sub =
      | Dot of (exp * sub) 
      | Shift of int 
      | Comp of (sub * sub) 
    type nonrec decl = < id: const  ;name: string  ;exp: exp  ;uni: uni   > 
    type nonrec def =
      <
        id: const  ;name: string  ;exp: exp  ;def: exp  ;height: int  ;
        root: const  ;uni: uni   > 
    type nonrec abbrev =
      < id: const  ;name: string  ;exp: exp  ;def: exp  ;uni: uni   > 
    type dec =
      | Decl of decl 
      | Def of def 
      | Abbrev of abbrev 
    module Signat :
    sig
      type nonrec signat
      val lookup : const -> dec
      val insert : (const * dec) -> unit
      val size : unit -> int
      val app : ((const * dec) -> unit) -> unit
      val reset : unit -> unit
    end
    exception Fail_exp of (string * exp) 
    exception Fail_exp2 of (string * exp * exp) 
    exception Fail_exp_spine of (string * exp * spine) 
    exception Fail_spine_exp of (string * spine * exp) 
    exception Fail_hd_spine of (string * head * spine) 
    exception Fail_sub_exp of (string * sub * exp) 
    val eta_expand : (exp * exp) -> exp
    val expType : exp
    val expKind : exp
    val bvar : int -> exp
    val one : exp
    val shift : sub
    val id_sub : sub
    val id : dec -> const
    val name : dec -> string
    val exp : dec -> exp
    val is_def : const -> bool
    val def : const -> exp
  end


module Syntax : SYNTAX =
  struct
    module L = Lib
    type nonrec const = int
    type uni =
      | Type 
      | Kind 
    type head =
      | Const of const 
      | BVar of int 
    type depend =
      | No 
      | Maybe 
    type exp =
      | Uni of uni 
      | Pi of pi 
      | Lam of lam 
      | Root of (head * spine) 
      | Redex of (exp * spine) 
      | EClo of (exp * sub) 
    and spine =
      | Nil 
      | App of (exp * spine) 
      | SClo of (spine * sub) 
    and sub =
      | Dot of (exp * sub) 
      | Shift of int 
      | Comp of (sub * sub) 
    type pi =
      < var: string option  ;arg: exp  ;depend: depend  ;body: exp   > 
    and lam = < var: string option  ;body: exp   > 
    type nonrec decl = < id: const  ;name: string  ;exp: exp  ;uni: uni   > 
    type nonrec def =
      <
        id: const  ;name: string  ;exp: exp  ;def: exp  ;height: int  ;
        root: const  ;uni: uni   > 
    type nonrec abbrev =
      < id: const  ;name: string  ;exp: exp  ;def: exp  ;uni: uni   > 
    type dec =
      | Decl of decl 
      | Def of def 
      | Abbrev of abbrev 
    module Signat =
      struct
        module T = Table
        type nonrec signat = dec T.table
        let (global_signat : dec T.table) = T.table 100000
        let rec lookup c = T.lookup global_signat c
        let rec insert (c, d) = ignore (T.insert global_signat (c, d))
        let rec app f = T.appi f global_signat
        let rec size () = T.size global_signat
        let rec reset () = T.clear global_signat
      end
    module Sig = Signat
    let expType = Uni Type
    let expKind = Uni Kind
    let rec bvar n = Root ((BVar n), Nil)
    let one = bvar 1
    let shift = Shift 1
    let id_sub = Shift 0
    let rec id =
      begin function
      | Decl decl -> ((fun r -> r.id)) decl
      | Def def -> ((fun r -> r.id)) def
      | Abbrev abb -> ((fun r -> r.id)) abb end
    let rec name =
      begin function
      | Decl decl -> ((fun r -> r.name)) decl
      | Def def -> ((fun r -> r.name)) def
      | Abbrev abb -> ((fun r -> r.name)) abb end
  let rec exp =
    begin function
    | Decl decl -> ((fun r -> r.exp)) decl
    | Def def -> ((fun r -> r.exp)) def
    | Abbrev abb -> ((fun r -> r.exp)) abb end
let rec is_def c =
  begin match Signat.lookup c with
  | Def _ -> true
  | Abbrev _ -> true
  | Decl _ -> false end
let rec def c =
  begin match Signat.lookup c with
  | Def def -> ((fun r -> r.def)) def
  | Abbrev abb -> ((fun r -> r.def)) abb
  | Decl _ -> raise (Fail "def: not a def") end
exception Fail_exp of (string * exp) 
exception Fail_exp2 of (string * exp * exp) 
exception Fail_exp_spine of (string * exp * spine) 
exception Fail_spine_exp of (string * spine * exp) 
exception Fail_hd_spine of (string * head * spine) 
exception Fail_sub_exp of (string * sub * exp) 
exception Fail_sub_exp of (string * sub * exp) 
type skel =
  | Base 
  | Arrow of (skel * skel) 
let rec card =
  begin function
  | Nil -> 0
  | App (m_, s_) -> (+) 1 card s_
  | _ -> raise (Fail "card: no closures") end
let rec num_pi_quants =
  begin function | Pi { body } -> (+) 1 num_pi_quants body | _ -> 0 end
let rec skel_length =
  begin function | Base -> 0 | Arrow (_, tau) -> (+) 1 skel_length tau end
let rec concat =
  begin function
  | (Nil, m_) -> App (m_, Nil)
  | (App (m_, s_), m'_) -> App (m_, (concat (s_, m'_)))
  | (SClo _, _) -> raise (Fail "concat: no closures") end
let rec skeleton =
  begin function
  | (ctx, Uni (Type)) -> Base
  | (ctx, Root (Const a, s_)) ->
      let aty = exp (Sig.lookup a) in
      let n = num_pi_quants aty in
      let n' = card s_ in if n = n' then begin Base end
        else begin raise (Fail "skeleton: not eta expanded") end
  | (ctx, Root (BVar i, s_)) ->
      let aty = L.ith (i - 1) ctx in
      let n = skel_length aty in
      let n' = card s_ in if n = n' then begin Base end
        else begin raise (Fail "skeleton: not eta expanded") end
| (ctx, Pi { arg; body; body }) ->
    let tau1 = skeleton (ctx, arg) in
    let tau2 = skeleton (ctx, body) in Arrow (tau1, tau2)
| (_, exp) -> raise (Fail_exp ("skeleton: bad case", exp)) end
exception Fail_exp_skel of (string * exp * skel) 
let changed = ref false
let rec shift_head =
  begin function
  | (lev, (Const _ as con)) -> con
  | (lev, (BVar n as var)) -> if n >= lev then begin BVar (n + 1) end
      else begin var end end
let rec shift_spine =
  begin function
  | (lev, Nil) -> Nil
  | (lev, App (m_, s_)) ->
      App ((shift_exp (lev, m_)), (shift_spine (lev, s_)))
  | (lev, SClo _) ->
      raise
        (Fail "shift_spine: shouldn't have closures during eta expansion") end
let rec shift_exp =
  begin function
  | (lev, (Uni _ as uni)) -> uni
  | (lev, Pi
     { var; arg; depend; body; arg; depend; body; depend; body; body }) ->
      Pi
        {
          var;
          arg = (shift_exp (lev, arg));
          depend;
          body = (shift_exp ((lev + 1), body))
        }
  | (lev, Lam { var; body; body }) ->
      Lam { var; body = (shift_exp ((lev + 1), body)) }
  | (lev, Root (h_, s_)) ->
      Root ((shift_head (lev, h_)), (shift_spine (lev, s_)))
  | _ ->
      raise
        (Fail
           "shift_exp: shouldn't have redexes or closures during eta expansion") end
let rec shift_spine' exp = shift_spine (0, exp)
let rec long_exp =
  begin function
  | (ctx, (Uni (Type) as exp), Base) -> exp
  | (ctx, Pi { arg; body; depend; var; body; depend; var; depend; var; var },
     Base) ->
      let arg' = long_exp (ctx, arg, Base) in
      let tau = skeleton (ctx, arg') in
      let body' = long_exp ((tau :: ctx), body, Base) in
      Pi { arg = arg'; body = body'; depend; var }
  | (ctx, Lam { var; body; body }, Arrow (tau1, tau2)) ->
      let body' = long_exp ((tau1 :: ctx), body, tau2) in
      Lam { var; body = body' }
  | (ctx, (Root ((Const a as con), s_) as expr), Base) ->
      let tau = skeleton (ctx, (exp (Sig.lookup a))) in
      Root (con, (long_spine (ctx, s_, tau)))
  | (ctx, (Root ((BVar i as var), s_) as exp), Base) ->
      let tau = L.ith (i - 1) ctx in
      ((Root (var, (long_spine (ctx, s_, tau))))
        (* indices start at 1 *))
  | (ctx, Root ((Const c as con), s_), (Arrow (tau1, tau2) as tau)) ->
      let s'_ = concat ((shift_spine' s_), one) in
      (begin changed := true;
       long_exp (ctx, (Lam { var = None; body = (Root (con, s'_)) }), tau) end)
  | (ctx, Root (BVar i, s_), (Arrow (tau1, tau2) as tau)) ->
      let s'_ = concat ((shift_spine' s_), one) in
      (begin changed := true;
       long_exp
         (ctx, (Lam { var = None; body = (Root ((BVar (i + 1)), s'_)) }),
           tau) end)
  | (_, exp, skel) -> raise (Fail_exp_skel ("long_exp: bad case", exp, skel)) end
let rec long_spine =
  begin function
  | (ctx, Nil, Base) -> Nil
  | (ctx, App (m_, s_), Arrow (tau1, tau2)) ->
      let m'_ = long_exp (ctx, m_, tau1) in
      let s'_ = long_spine (ctx, s_, tau2) in App (m'_, s'_)
  | _ -> raise (Fail "long_spine: bad case") end
let rec eta_expand' =
  begin function
  | (e1, Uni (Kind)) -> e1
  | (e1, e2) ->
      let () = changed := false in
      let skel = skeleton ([], e2) in
      let e2' = long_exp ([], e1, skel) in ((e2')
        (*           if !changed then L.warning "expression is not eta long" else (); *)) end
let rec eta_expand e = Timers.time Timers.eta_normal eta_expand' e end
