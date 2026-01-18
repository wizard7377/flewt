
module TypecheckEE : TYPECHECK =
  struct
    module __l = Lib
    module S = Syntax
    module Sig = S.Signat
    module C = Context
    module __d = Debug
    open S
    type ret =
      | RetExp of exp 
      | RetVar of int 
    (** check a term (type)  against a type (kind) *)
    let rec check_exp =
      function
      | (ctx, Uni (Type), Uni (Kind)) -> ()
      | (ctx, Lam { body = M }, Pi
         { var; arg = __u; body = __v; arg = __u; body = __v; body = __v }) ->
          check_exp ((C.push (ctx, (var, __u))), M, __v)
      | (ctx, Root (Const con, S), __v) ->
          let rec foc exp =
            let __u = focus (ctx, S, exp) in
            if equiv_exp (__u, __v)
            then ()
            else raise (Fail "check_exp: exps not equivalent") in
          (((match Sig.lookup con with
             | Decl decl -> foc ((fun r -> r.exp) decl)
             | Def def -> foc ((fun r -> r.exp) def)
             | Abbrev abbrev -> raise (Fail "check_exp: abbrev")))
            (* why does this fail?*)(* pull some common code out of the following case *))
      | (ctx, Root (BVar i, S), __v) ->
          (((match C.lookup (ctx, (i - 1)) with
             | Some (_, A) ->
                 let __u = focus (ctx, S, (apply_exp ((Shift i), A))) in
                 if equiv_exp (__u, __v)
                 then ()
                 else raise (Fail_exp2 ("check_exp: Root,BVar", __u, __v))
             | None -> raise (Fail "focus: var out of bounds")))
          (* DeBruijn indices start at 1 *))
      | (ctx, Pi
         { var; arg = A1; body = A2; arg = A1; body = A2; body = A2 },
         (Uni _ as uni)) ->
          (check_exp (ctx, A1, expType);
           check_exp ((C.push (ctx, (var, A1))), A2, uni))
      | _ -> raise (Fail "check: bad case")
    let rec focus =
      function
      | (ctx, Nil, (Uni (Type) as ty)) -> ty
      | (ctx, Nil, (Root (Const _, _) as hd)) -> hd
      | (ctx, App (M, S), Pi { arg = A1; body = A2; body = A2 }) ->
          (check_exp (ctx, M, A1);
           focus (ctx, S, (apply_exp ((Dot (M, id_sub)), A2))))
      | (_, S, E) -> raise (Fail_spine_exp ("focus: bad case", S, E))
    let rec check (E1) (E2) =
      Timers.time Timers.checking check_exp (C.empty, E1, E2)
    let rec apply_exp =
      function
      | (_, (Uni _ as uni)) -> uni
      | (sub, Pi
         { var; arg = __u; depend; body = __v; arg = __u; depend; body = __v; 
           depend; body = __v; body = __v })
          ->
          Pi
            {
              var;
              arg = (apply_exp (sub, __u));
              depend;
              body = (apply_exp ((push_sub sub), __v))
            }
      | (sub, Lam { var; body = __u; body = __u }) ->
          Lam { var; body = (apply_exp ((push_sub sub), __u)) }
      | (sub, (Root (H, S) as exp)) ->
          let S' = apply_spine (sub, S) in
          (match H with
           | Const _ -> Root (H, S')
           | BVar i ->
               (match apply_var (sub, i) with
                | RetVar j -> Root ((BVar j), S')
                | RetExp (M) -> reduce (M, S')))
    let rec apply_spine =
      function
      | (_, Nil) -> Nil
      | (sub, App (M, S)) ->
          App ((apply_exp (sub, M)), (apply_spine (sub, S)))
    let rec apply_var =
      function
      | (Dot (M, sub), i) ->
          if i = 1
          then
            (match M with | Root (BVar j, Nil) -> RetVar j | _ -> RetExp M)
          else apply_var (sub, (i - 1))
      | (Shift n, i) -> RetVar (i + n)
    let rec compose =
      function
      | (Dot (M, sigma), sigma') ->
          Dot ((apply_exp (sigma', M)), (compose (sigma, sigma')))
      | (Shift n, Shift m) -> Shift (n + m)
      | (Shift 0, sigma) -> sigma
      | (Shift n, Dot (M, sigma)) -> compose ((Shift (n - 1)), sigma)
    let rec push_sub s = Dot (one, (compose (s, shift)))
    let rec reduce =
      function
      | ((Root (_, _) as exp), Nil) -> exp
      | (Lam { body = M }, App (M', S)) ->
          reduce ((apply_exp ((Dot (M', id_sub)), M)), S)
      | (E, S) -> raise (Fail_exp_spine ("reduce: bad case: head: ", E, S))
    let rec equiv_exp =
      function
      | (Uni u1, Uni u2) -> u1 = u2
      | (Pi { arg = __U1; body = V1; body = V1 }, Pi
         { arg = __U2; body = V2; body = V2 }) ->
          (equiv_exp (__U1, __U2)) && (equiv_exp (V1, V2))
      | (Lam { body = __u }, Lam { body = __u' }) -> equiv_exp (__u, __u')
      | (Root (BVar i, S1), Root (BVar i', S2)) ->
          (i = i') && (equiv_spine (S1, S2))
      | ((Root (Const c, S) as exp), (Root (Const c', S') as exp')) ->
          if c = c'
          then equiv_spine (S, S')
          else
            (match ((Sig.lookup c), (Sig.lookup c')) with
             | (Decl decl, Def def) ->
                 if (<>) (((fun r -> r.root)) def) ((fun r -> r.id)) decl
                 then false__
                 else equiv_exp (exp, (reduce (((fun r -> r.def) def), S')))
             | (Def def, Decl decl) ->
                 if (<>) (((fun r -> r.root)) def) ((fun r -> r.id)) decl
                 then false__
                 else equiv_exp ((reduce (((fun r -> r.def) def), S)), exp')
             | (Abbrev { def }, _) -> equiv_exp ((reduce (def, S)), exp')
             | (_, Abbrev { def }) -> equiv_exp (exp, (reduce (def, S')))
             | (Def
                { def; height = h; root = rc; height = h; root = rc;
                  root = rc },
                Def
                { def = def'; height = h'; root = rc'; height = h';
                  root = rc'; root = rc' })
                 ->
                 if rc <> rc'
                 then false__
                 else
                   if h = h'
                   then equiv_exp ((reduce (def, S)), (reduce (def', S')))
                   else
                     if h > h'
                     then equiv_exp ((reduce (def, S)), exp')
                     else equiv_exp (exp, (reduce (def', S')))
             | (_, _) -> raise (Fail "equiv_exp: bad case"))
      | _ -> false__
    let rec equiv_spine =
      function
      | (S.Nil, Nil) -> true__
      | (App (E, S), App (E', S')) ->
          (equiv_exp (E, E')) && (equiv_spine (S, S'))
      | _ -> false__
    (* -------------------------------------------------------------------------- *)
    (*  Signatures                                                                *)
    (* -------------------------------------------------------------------------- *)
    let rec check_dec =
      function
      | (c, Decl { id; name; exp; uni; name; exp; uni; exp; uni; uni }) ->
          let uni' = Uni uni in
          let exp' = eta_expand (exp, uni') in
          (check exp' uni';
           Sig.insert (id, (Decl { id; name; exp = exp'; uni })))
      | (c, Def
         { id; name; exp; def; height; root; uni; name; exp; def; height;
           root; uni; exp; def; height; root; uni; def; height; root; 
           uni; height; root; uni; root; uni; uni })
          ->
          let uni' = Uni uni in
          let exp' = eta_expand (exp, uni') in
          let def' = eta_expand (def, exp') in
          (check exp' uni';
           check def' exp';
           Sig.insert
             (id,
               (Def { id; name; exp = exp'; def = def'; height; root; uni })))
      | (c, Abbrev
         { id; name; exp; def; uni; name; exp; def; uni; exp; def; uni; 
           def; uni; uni })
          ->
          let uni' = Uni uni in
          let exp' = exp in
          let def' = def in
          (((check exp' uni';
             check def' exp';
             Sig.insert
               (id, (Abbrev { id; name; exp = exp'; def = def'; uni }))))
            (*         val exp' = eta_expand(exp,uni') *)
            (*         val def' = eta_expand(def,exp') *))
    let rec check_signat' decs =
      List.app
        (function
         | (c, dec) as decl -> ((check_dec decl)
             (* L.printl ("checking: " ^ name dec ); *)))
        decs
    let rec check_signat decs =
      Timers.time Timers.checking check_signat' decs
    let rec check_signat_clear decs = Sig.reset (); check_signat decs
  end ;;
