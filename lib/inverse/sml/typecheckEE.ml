
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
    let rec check_exp __0__ __1__ __2__ =
      match (__0__, __1__, __2__) with
      | (ctx, Uni (Type), Uni (Kind)) -> ()
      | (ctx, Lam { body = __M }, Pi
         { var; arg = __U; body = __V; arg = __U; body = __V; body = __V })
          -> check_exp ((C.push (ctx, (var, __U))), __M, __V)
      | (ctx, Root (Const con, __S), __V) ->
          let rec foc exp =
            let __U = focus (ctx, __S, exp) in
            if equiv_exp (__U, __V)
            then ()
            else raise (Fail "check_exp: exps not equivalent") in
          (((match Sig.lookup con with
             | Decl decl -> foc ((fun r -> r.exp) decl)
             | Def def -> foc ((fun r -> r.exp) def)
             | Abbrev abbrev -> raise (Fail "check_exp: abbrev")))
            (* why does this fail?*)(* pull some common code out of the following case *))
      | (ctx, Root (BVar i, __S), __V) ->
          (((match C.lookup (ctx, (i - 1)) with
             | Some (_, __A) ->
                 let __U = focus (ctx, __S, (apply_exp ((Shift i), __A))) in
                 if equiv_exp (__U, __V)
                 then ()
                 else raise (Fail_exp2 ("check_exp: Root,BVar", __U, __V))
             | None -> raise (Fail "focus: var out of bounds")))
          (* DeBruijn indices start at 1 *))
      | (ctx, Pi
         { var; arg = __A1; body = __A2; arg = __A1; body = __A2; body = __A2
           },
         (Uni _ as uni)) ->
          (check_exp (ctx, __A1, expType);
           check_exp ((C.push (ctx, (var, __A1))), __A2, uni))
      | _ -> raise (Fail "check: bad case")
    let rec focus __3__ __4__ __5__ =
      match (__3__, __4__, __5__) with
      | (ctx, Nil, (Uni (Type) as ty)) -> ty
      | (ctx, Nil, (Root (Const _, _) as hd)) -> hd
      | (ctx, App (__M, __S), Pi { arg = __A1; body = __A2; body = __A2 }) ->
          (check_exp (ctx, __M, __A1);
           focus (ctx, __S, (apply_exp ((Dot (__M, id_sub)), __A2))))
      | (_, __S, __E) -> raise (Fail_spine_exp ("focus: bad case", __S, __E))
    let rec check (__E1) (__E2) =
      Timers.time Timers.checking check_exp (C.empty, __E1, __E2)
    let rec apply_exp __6__ __7__ =
      match (__6__, __7__) with
      | (_, (Uni _ as uni)) -> uni
      | (sub, Pi
         { var; arg = __U; depend; body = __V; arg = __U; depend; body = __V;
           depend; body = __V; body = __V })
          ->
          Pi
            {
              var;
              arg = (apply_exp (sub, __U));
              depend;
              body = (apply_exp ((push_sub sub), __V))
            }
      | (sub, Lam { var; body = __U; body = __U }) ->
          Lam { var; body = (apply_exp ((push_sub sub), __U)) }
      | (sub, (Root (__H, __S) as exp)) ->
          let __S' = apply_spine (sub, __S) in
          (match __H with
           | Const _ -> Root (__H, __S')
           | BVar i ->
               (match apply_var (sub, i) with
                | RetVar j -> Root ((BVar j), __S')
                | RetExp (__M) -> reduce (__M, __S')))
    let rec apply_spine __8__ __9__ =
      match (__8__, __9__) with
      | (_, Nil) -> Nil
      | (sub, App (__M, __S)) ->
          App ((apply_exp (sub, __M)), (apply_spine (sub, __S)))
    let rec apply_var __10__ __11__ =
      match (__10__, __11__) with
      | (Dot (__M, sub), i) ->
          if i = 1
          then
            (match __M with
             | Root (BVar j, Nil) -> RetVar j
             | _ -> RetExp __M)
          else apply_var (sub, (i - 1))
      | (Shift n, i) -> RetVar (i + n)
    let rec compose __12__ __13__ =
      match (__12__, __13__) with
      | (Dot (__M, sigma), sigma') ->
          Dot ((apply_exp (sigma', __M)), (compose (sigma, sigma')))
      | (Shift n, Shift m) -> Shift (n + m)
      | (Shift 0, sigma) -> sigma
      | (Shift n, Dot (__M, sigma)) -> compose ((Shift (n - 1)), sigma)
    let rec push_sub s = Dot (one, (compose (s, shift)))
    let rec reduce __14__ __15__ =
      match (__14__, __15__) with
      | ((Root (_, _) as exp), Nil) -> exp
      | (Lam { body = __M }, App (__M', __S)) ->
          reduce ((apply_exp ((Dot (__M', id_sub)), __M)), __S)
      | (__E, __S) ->
          raise (Fail_exp_spine ("reduce: bad case: head: ", __E, __S))
    let rec equiv_exp __16__ __17__ =
      match (__16__, __17__) with
      | (Uni u1, Uni u2) -> u1 = u2
      | (Pi { arg = __U1; body = __V1; body = __V1 }, Pi
         { arg = __U2; body = __V2; body = __V2 }) ->
          (equiv_exp (__U1, __U2)) && (equiv_exp (__V1, __V2))
      | (Lam { body = __U }, Lam { body = __U' }) -> equiv_exp (__U, __U')
      | (Root (BVar i, __S1), Root (BVar i', __S2)) ->
          (i = i') && (equiv_spine (__S1, __S2))
      | ((Root (Const c, __S) as exp), (Root (Const c', __S') as exp')) ->
          if c = c'
          then equiv_spine (__S, __S')
          else
            (match ((Sig.lookup c), (Sig.lookup c')) with
             | (Decl decl, Def def) ->
                 if (<>) (((fun r -> r.root)) def) ((fun r -> r.id)) decl
                 then false
                 else
                   equiv_exp (exp, (reduce (((fun r -> r.def) def), __S')))
             | (Def def, Decl decl) ->
                 if (<>) (((fun r -> r.root)) def) ((fun r -> r.id)) decl
                 then false
                 else
                   equiv_exp ((reduce (((fun r -> r.def) def), __S)), exp')
             | (Abbrev { def }, _) -> equiv_exp ((reduce (def, __S)), exp')
             | (_, Abbrev { def }) -> equiv_exp (exp, (reduce (def, __S')))
             | (Def
                { def; height = h; root = rc; height = h; root = rc;
                  root = rc },
                Def
                { def = def'; height = h'; root = rc'; height = h';
                  root = rc'; root = rc' })
                 ->
                 if rc <> rc'
                 then false
                 else
                   if h = h'
                   then
                     equiv_exp ((reduce (def, __S)), (reduce (def', __S')))
                   else
                     if h > h'
                     then equiv_exp ((reduce (def, __S)), exp')
                     else equiv_exp (exp, (reduce (def', __S')))
             | (_, _) -> raise (Fail "equiv_exp: bad case"))
      | _ -> false
    let rec equiv_spine __18__ __19__ =
      match (__18__, __19__) with
      | (S.Nil, Nil) -> true
      | (App (__E, __S), App (__E', __S')) ->
          (equiv_exp (__E, __E')) && (equiv_spine (__S, __S'))
      | _ -> false
    let rec check_dec __20__ __21__ =
      match (__20__, __21__) with
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
        (fun ((c, dec) as decl) -> ((check_dec decl)
           (* L.printl ("checking: " ^ name dec ); *)))
        decs
    let rec check_signat decs =
      Timers.time Timers.checking check_signat' decs
    let rec check_signat_clear decs = Sig.reset (); check_signat decs
  end ;;
