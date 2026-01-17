
module TypecheckEE : TYPECHECK =
  struct
    module L = Lib
    module S = Syntax
    module Sig = S.Signat
    module C = Context
    module D = Debug
    open S
    type ret =
      | RetExp of exp 
      | RetVar of int 
    let rec check_exp =
      function
      | (((ctx)(** check a term (type)  against a type (kind) *)),
         Uni (Type), Uni (Kind)) -> ()
      | (ctx, Lam { body = M }, Pi
         { var; arg = U; body = V; arg = U; body = V; body = V }) ->
          check_exp ((C.push (ctx, (var, U))), M, V)
      | (ctx, Root (Const con, S), V) ->
          let foc
            ((exp)(* pull some common code out of the following case *))
            =
            let U = focus (ctx, S, exp) in
            if equiv_exp (U, V)
            then ()
            else raise (Fail "check_exp: exps not equivalent") in
          (match Sig.lookup con with
           | Decl decl -> foc ((fun r -> r.exp) decl)
           | Def def -> foc ((fun r -> r.exp) def)
           | Abbrev abbrev ->
               raise
                 (Fail (("check_exp: abbrev")
                    (* why does this fail?*))))
      | (ctx, Root (BVar i, S), V) ->
          (match C.lookup (ctx, (i - 1)) with
           | SOME (_, A) ->
               let ((U)(* DeBruijn indices start at 1 *)) =
                 focus (ctx, S, (apply_exp ((Shift i), A))) in
               if equiv_exp (U, V)
               then ()
               else raise (Fail_exp2 ("check_exp: Root,BVar", U, V))
           | NONE -> raise (Fail "focus: var out of bounds"))
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
      | (((_)(* -------------------------------------------------------------------------- *)
         (*  Substitutions                                                             *)
         (* -------------------------------------------------------------------------- *)),
         (Uni _ as uni)) -> uni
      | (sub, Pi
         { var; arg = U; depend; body = V; arg = U; depend; body = V; 
           depend; body = V; body = V })
          ->
          Pi
            {
              var;
              arg = (apply_exp (sub, U));
              depend;
              body = (apply_exp ((push_sub sub), V))
            }
      | (sub, Lam { var; body = U; body = U }) ->
          Lam { var; body = (apply_exp ((push_sub sub), U)) }
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
      | ((Root
            (((_)(* -------------------------------------------------------------------------- *)
             (*  Beta                                                                      *)
             (* -------------------------------------------------------------------------- *)),
             _)
            as exp),
         Nil) -> exp
      | (Lam { body = M }, App (M', S)) ->
          reduce ((apply_exp ((Dot (M', id_sub)), M)), S)
      | (E, S) -> raise (Fail_exp_spine ("reduce: bad case: head: ", E, S))
    let rec equiv_exp =
      function
      | (Uni
         ((u1)(* -------------------------------------------------------------------------- *)
         (*  Equivalence wrt Definitions                                               *)
         (* -------------------------------------------------------------------------- *)),
         Uni u2) -> u1 = u2
      | (Pi { arg = u1; body = V1; body = V1 }, Pi
         { arg = u2; body = V2; body = V2 }) ->
          (equiv_exp (u1, u2)) && (equiv_exp (V1, V2))
      | (Lam { body = U }, Lam { body = U' }) -> equiv_exp (U, U')
      | (Root (BVar i, s1), Root (BVar i', s2)) ->
          (i = i') && (equiv_spine (s1, s2))
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
    let rec check_dec =
      function
      | (((c)(* -------------------------------------------------------------------------- *)
         (*  Signatures                                                                *)
         (* -------------------------------------------------------------------------- *)),
         Decl { id; name; exp; uni; name; exp; uni; exp; uni; uni }) ->
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
          let ((exp')(*         val exp' = eta_expand(exp,uni') *)
            (*         val def' = eta_expand(def,exp') *)) =
            exp in
          let def' = def in
          (check exp' uni';
           check def' exp';
           Sig.insert
             (id, (Abbrev { id; name; exp = exp'; def = def'; uni })))
    let rec check_signat' decs =
      List.app
        (function
         | (c, dec) as decl ->
             check_dec ((decl)
               (* L.printl ("checking: " ^ name dec ); *)))
        decs
    let rec check_signat decs =
      Timers.time Timers.checking check_signat' decs
    let rec check_signat_clear decs = Sig.reset (); check_signat decs
  end ;;
