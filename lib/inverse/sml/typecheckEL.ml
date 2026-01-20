
module TypecheckEL =
  struct
    module L = Lib
    module S = Syntax
    module Sig = S.Signat
    module C = Context
    module D = Debug
    open S
    let rec check_exp __0__ __1__ __2__ __3__ =
      match (__0__, __1__, __2__, __3__) with
      | (sgn, ctx, Uni (Type), Uni (Kind)) -> ()
      | (sgn, ctx, Lam { body = __M }, Pi
         { var; arg = __U; body = __V; arg = __U; body = __V; body = __V })
          -> check_exp sgn (C.push ctx (var, __U)) __M __V
      | (sgn, ctx, Root (Const con, __S), __V) ->
          let rec foc exp =
            let __U = focus sgn ctx __S exp in
            if equiv_exp sgn __U __V
            then ()
            else raise (Check "check_exp: exps not equivalent") in
          (((match Sig.lookup sgn con with
             | Decl decl -> foc ((fun r -> r.exp) decl)
             | Def def -> foc ((fun r -> r.exp) def)
             | Abbrev abbrev -> raise (Fail "check_exp: abbrev")))
            (* why does this fail?*)(* pull some common code out of the following case *))
      | (sgn, ctx, Root (BVar i, __S), __V) ->
          (((match C.lookup ctx (i - 1) with
             | Some (_, __A) ->
                 let __U = focus sgn ctx __S (apply_exp (Shift i) __A) in
                 if equiv_exp sgn __U __V
                 then ()
                 else raise (Fail_exp2 ("check_exp: Root,BVar", __U, __V))
             | NONE -> raise (Check "focus: var out of bounds")))
          (* DeBruijn indices start at 1 *))
      | (sgn, ctx, Pi
         { var; arg = __A1; body = __A2; arg = __A1; body = __A2; body = __A2
           },
         (Uni _ as uni)) ->
          (check_exp sgn ctx __A1 expType;
           check_exp sgn (C.push ctx (var, __A1)) __A2 uni)
      | (_, _, _, _) -> raise (Check "check: bad case")
    let rec focus __4__ __5__ __6__ __7__ =
      match (__4__, __5__, __6__, __7__) with
      | (sgn, ctx, Nil, (Uni (Type) as ty)) -> ty
      | (sgn, ctx, Nil, (Root (Const _, _) as hd)) -> hd
      | (sgn, ctx, App (__M, __S), Pi
         { arg = __A1; body = __A2; body = __A2 }) ->
          (check_exp sgn ctx __M __A1;
           focus sgn ctx __S (apply_exp (Dot (__M, id_sub)) __A2))
      | (_, _, __S, __E) ->
          raise (Fail_spine_exp ("focus: bad case", __S, __E))
    let rec check sgn (__E1) (__E2) = check_exp sgn C.empty __E1 __E2
    let rec apply_exp __8__ __9__ =
      match (__8__, __9__) with
      | (_, (Uni _ as uni)) -> uni
      | (sub, Pi
         { var; arg = __U; depend; body = __V; arg = __U; depend; body = __V;
           depend; body = __V; body = __V })
          ->
          Pi
            {
              var;
              arg = (apply_exp sub __U);
              depend;
              body = (apply_exp (push_sub sub) __V)
            }
      | (sub, Lam { var; body = __U; body = __U }) ->
          Lam { var; body = (apply_exp (push_sub sub) __U) }
      | (sub, (Root (__H, __S) as exp)) ->
          let __S' = apply_spine sub __S in
          (match __H with
           | Const _ -> Root (__H, __S')
           | BVar i ->
               (match apply_var sub i with
                | RetVar j -> Root ((BVar j), __S')
                | RetExp (__M) -> reduce __M __S'))
    let rec apply_spine __10__ __11__ =
      match (__10__, __11__) with
      | (sub, Nil) -> Nil
      | (sub, App (__M, __S)) ->
          App ((apply_exp sub __M), (apply_spine sub __S))
    let rec apply_var __12__ __13__ =
      match (__12__, __13__) with
      | (Dot (__M, sub), i) ->
          if i = 1
          then
            (match __M with
             | Root (BVar j, Nil) -> RetVar j
             | _ -> RetExp __M)
          else apply_var sub (i - 1)
      | (Shift n, i) -> RetVar (i + n)
      | (Comp (s1, s2), i) ->
          (match apply_var s1 i with
           | RetVar j -> apply_var s2 j
           | RetExp (__M) -> RetExp (apply_exp s2 __M))
    let rec compose s1 s2 = Comp (s1, s2)
    let rec push_sub s = Dot (one, (compose s shift))
    let rec reduce __14__ __15__ =
      match (__14__, __15__) with
      | ((Root (_, _) as exp), Nil) -> exp
      | (Lam { body = __M }, App (__M', __S)) ->
          reduce (apply_exp (Dot (__M', id_sub)) __M) __S
      | (__E, __S) ->
          raise (Fail_exp_spine ("reduce: bad case: head: ", __E, __S))
    let rec equiv_exp __16__ __17__ __18__ =
      match (__16__, __17__, __18__) with
      | (sgn, Uni u1, Uni u2) -> u1 = u2
      | (sgn, Pi { arg = __U1; body = __V1; body = __V1 }, Pi
         { arg = __U2; body = __V2; body = __V2 }) ->
          (equiv_exp sgn __U1 __U2) && (equiv_exp sgn __V1 __V2)
      | (sgn, Lam { body = __U }, Lam { body = __U' }) ->
          equiv_exp sgn __U __U'
      | (sgn, Root (BVar i, __S1), Root (BVar i', __S2)) ->
          (i = i') && (equiv_spine sgn __S1 __S2)
      | (sgn, (Root (Const c, __S) as exp), (Root (Const c', __S') as exp'))
          ->
          if c = c'
          then equiv_spine sgn __S __S'
          else
            (match ((Sig.lookup sgn c), (Sig.lookup sgn c')) with
             | (Decl decl, Def def) ->
                 if (<>) (((fun r -> r.root)) def) ((fun r -> r.id)) decl
                 then false__
                 else equiv_exp sgn exp (reduce ((fun r -> r.def) def) __S')
             | (Def def, Decl decl) ->
                 if (<>) (((fun r -> r.root)) def) ((fun r -> r.id)) decl
                 then false__
                 else equiv_exp sgn (reduce ((fun r -> r.def) def) __S) exp'
             | (Abbrev { def }, _) -> equiv_exp sgn (reduce def __S) exp'
             | (_, Abbrev { def }) -> equiv_exp sgn exp (reduce def __S')
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
                   then equiv_exp sgn (reduce def __S) (reduce def' __S')
                   else
                     if h > h'
                     then equiv_exp sgn (reduce def __S) exp'
                     else equiv_exp sgn exp (reduce def' __S')
             | (_, _) -> raise (Check "equiv_exp: bad case"))
      | (_, _, _) -> false__
    let rec equiv_spine __19__ __20__ __21__ =
      match (__19__, __20__, __21__) with
      | (sgn, Nil, Nil) -> true__
      | (sgn, App (__E, __S), App (__E', __S')) ->
          (equiv_exp sgn __E __E') && (equiv_spine sgn __S __S')
      | (_, _, _) -> false__
    let rec check_dec __22__ __23__ =
      match (__22__, __23__) with
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
  end;;
