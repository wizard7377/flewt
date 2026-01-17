
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
      val lookup : const -> ((dec)(** Lookup. *))
      val insert : (const * dec) -> ((unit)(** Insert. *))
      val size : unit -> ((int)(** number of constants *))
      val app :
        ((const * dec) -> unit) ->
          ((unit)(** iterate a function over the signat *))
      val reset : unit -> ((unit)(** clear the signature*))
    end
    exception Fail_exp of
      (((string)(* -------------------------------------------------------------------------- *)
      (*  Exceptions                                                                *)
      (* -------------------------------------------------------------------------- *))
      * exp) 
    exception Fail_exp2 of (string * exp * exp) 
    exception Fail_exp_spine of (string * exp * spine) 
    exception Fail_spine_exp of (string * spine * exp) 
    exception Fail_hd_spine of (string * head * spine) 
    exception Fail_sub_exp of (string * sub * exp) 
    val eta_expand :
      (exp * exp) ->
        ((exp)(** Eta expand an expression against a type.  
      Assumes the expressions are already beta-normal. *))
    val expType :
      ((exp)(* -------------------------------------------------------------------------- *)
        (*  Util                                                                      *)
        (* -------------------------------------------------------------------------- *))
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
  end;;




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
        module T =
          ((Table)(* -------------------------------------------------------------------------- *)
          (*  Signatures                                                                *)
          (* -------------------------------------------------------------------------- *))
        type nonrec signat = dec T.table
        let (global_signat : dec T.table) = T.table 100000
        let rec lookup c = T.lookup global_signat c
        let rec insert (c, d) = ignore (T.insert global_signat (c, d))
        let rec app f = T.appi f global_signat
        let rec size () = T.size global_signat
        let rec reset () = T.clear global_signat
      end
    module Sig = Signat
    let ((expType)(* -------------------------------------------------------------------------- *)
      (*  Util                                                                      *)
      (* -------------------------------------------------------------------------- *))
      = Uni Type
    let expKind = Uni Kind
    let rec bvar n = Root ((BVar n), Nil)
    let one = bvar 1
    let shift = Shift 1
    let id_sub = Shift 0
    let rec id =
      function
      | Decl decl -> ((fun r -> r.id)) decl
      | Def def -> ((fun r -> r.id)) def
      | Abbrev abb -> ((fun r -> r.id)) abb
    let rec name =
      function
      | Decl decl -> ((fun r -> r.name)) decl
      | Def def -> ((fun r -> r.name)) def
      | Abbrev abb -> ((fun r -> r.name)) abb
    let rec exp =
      function
      | Decl decl -> ((fun r -> r.exp)) decl
      | Def def -> ((fun r -> r.exp)) def
      | Abbrev abb -> ((fun r -> r.exp)) abb
    let rec is_def c =
      match Signat.lookup c with
      | Def _ -> true__
      | Abbrev _ -> true__
      | Decl _ -> false__
    let rec def c =
      match Signat.lookup c with
      | Def def -> ((fun r -> r.def)) def
      | Abbrev abb -> ((fun r -> r.def)) abb
      | Decl _ -> raise (Fail "def: not a def")
    exception Fail_exp of
      (((string)(* -------------------------------------------------------------------------- *)
      (*  Exceptions                                                                *)
      (* -------------------------------------------------------------------------- *))
      * exp) 
    exception Fail_exp2 of (string * exp * exp) 
    exception Fail_exp_spine of (string * exp * spine) 
    exception Fail_spine_exp of (string * spine * exp) 
    exception Fail_hd_spine of (string * head * spine) 
    exception Fail_sub_exp of (string * sub * exp) 
    exception Fail_sub_exp of (string * sub * exp) 
    type skel =
      | Base 
      | Arrow of
      (((skel)(* -------------------------------------------------------------------------- *)
      (*  Eta                                                                       *)
      (* -------------------------------------------------------------------------- *))
      * skel) 
    let rec card =
      function
      | Nil -> 0
      | App (M, S) -> (+) 1 card S
      | _ -> raise (Fail "card: no closures")
    let rec num_pi_quants =
      function | Pi { body } -> (+) 1 num_pi_quants body | _ -> 0
    let rec skel_length =
      function | Base -> 0 | Arrow (_, tau) -> (+) 1 skel_length tau
    let rec concat =
      function
      | (Nil, M) -> App (M, Nil)
      | (App (M, S), M') -> App (M, (concat (S, M')))
      | (SClo _, _) -> raise (Fail "concat: no closures")
    let rec skeleton =
      function
      | (ctx, Uni (Type)) -> Base
      | (ctx, Root (Const a, S)) ->
          let aty = exp (Sig.lookup a) in
          let n = num_pi_quants aty in
          let n' = card S in
          if n = n' then Base else raise (Fail "skeleton: not eta expanded")
      | (ctx, Root (BVar i, S)) ->
          let aty = L.ith (i - 1) ctx in
          let n = skel_length aty in
          let n' = card S in
          if n = n' then Base else raise (Fail "skeleton: not eta expanded")
      | (ctx, Pi { arg; body; body }) ->
          let tau1 = skeleton (ctx, arg) in
          let tau2 = skeleton (ctx, body) in Arrow (tau1, tau2)
      | (_, exp) -> raise (Fail_exp ("skeleton: bad case", exp))
    exception Fail_exp_skel of (string * exp * skel) 
    let changed = ref false__
    let rec shift_head =
      function
      | (((lev)(* A quick implementation of applying a shift substitution. 
       This is just for eta expansion, and we don't want this
       code to be tangled with the different typechecker versions.
    *)),
         (Const _ as con)) -> con
      | (lev, (BVar n as var)) -> if n >= lev then BVar (n + 1) else var
    let rec shift_spine =
      function
      | (lev, Nil) -> Nil
      | (lev, App (M, S)) ->
          App ((shift_exp (lev, M)), (shift_spine (lev, S)))
      | (lev, SClo _) ->
          raise
            (Fail "shift_spine: shouldn't have closures during eta expansion")
    let rec shift_exp =
      function
      | (lev, (Uni _ as uni)) -> uni
      | (lev, Pi
         { var; arg; depend; body; arg; depend; body; depend; body; body })
          ->
          Pi
            {
              var;
              arg = (shift_exp (lev, arg));
              depend;
              body = (shift_exp ((lev + 1), body))
            }
      | (lev, Lam { var; body; body }) ->
          Lam { var; body = (shift_exp ((lev + 1), body)) }
      | (lev, Root (H, S)) ->
          Root ((shift_head (lev, H)), (shift_spine (lev, S)))
      | _ ->
          raise
            (Fail
               "shift_exp: shouldn't have redexes or closures during eta expansion")
    let rec shift_spine' exp = shift_spine (0, exp)
    let rec long_exp =
      function
      | (ctx, (Uni (Type) as exp), Base) -> exp
      | (ctx, Pi
         { arg; body; depend; var; body; depend; var; depend; var; var },
         Base) ->
          let arg' = long_exp (ctx, arg, Base) in
          let tau = skeleton (ctx, arg') in
          let body' = long_exp ((tau :: ctx), body, Base) in
          Pi { arg = arg'; body = body'; depend; var }
      | (ctx, Lam { var; body; body }, Arrow (tau1, tau2)) ->
          let body' = long_exp ((tau1 :: ctx), body, tau2) in
          Lam { var; body = body' }
      | (ctx, (Root ((Const a as con), S) as expr), Base) ->
          let tau = skeleton (ctx, (exp (Sig.lookup a))) in
          Root (con, (long_spine (ctx, S, tau)))
      | (ctx, (Root ((BVar i as var), S) as exp), Base) ->
          let tau = L.ith (i - 1) ctx in
          Root
            (((var)(* indices start at 1 *)),
              (long_spine (ctx, S, tau)))
      | (ctx, Root ((Const c as con), S), (Arrow (tau1, tau2) as tau)) ->
          let S' = concat ((shift_spine' S), one) in
          (changed := true__;
           long_exp (ctx, (Lam { var = NONE; body = (Root (con, S')) }), tau))
      | (ctx, Root (BVar i, S), (Arrow (tau1, tau2) as tau)) ->
          let S' = concat ((shift_spine' S), one) in
          (changed := true__;
           long_exp
             (ctx, (Lam { var = NONE; body = (Root ((BVar (i + 1)), S')) }),
               tau))
      | (_, exp, skel) ->
          raise (Fail_exp_skel ("long_exp: bad case", exp, skel))
    let rec long_spine =
      function
      | (ctx, Nil, Base) -> Nil
      | (ctx, App (M, S), Arrow (tau1, tau2)) ->
          let M' = long_exp (ctx, M, tau1) in
          let S' = long_spine (ctx, S, tau2) in App (M', S')
      | _ -> raise (Fail "long_spine: bad case")
    let rec eta_expand' =
      function
      | (e1, Uni (Kind)) -> e1
      | (e1, e2) ->
          let () = changed := false__ in
          let skel = skeleton ([], e2) in
          let e2' = long_exp ([], e1, skel) in ((e2')
            (*           if !changed then L.warning "expression is not eta long" else (); *))
    let rec eta_expand e = Timers.time Timers.eta_normal eta_expand' e
  end ;;
