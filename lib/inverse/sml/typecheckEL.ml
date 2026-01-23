module TypecheckEL =
  struct
    module L = Lib
    module S = Syntax
    module Sig = S.Signat
    module C = Context
    module D = Debug
    open S
    let rec check_exp arg__0 arg__1 arg__2 arg__3 =
      begin match (arg__0, arg__1, arg__2, arg__3) with
      | (sgn, ctx, Uni (Type), Uni (Kind)) -> ()
      | (sgn, ctx, Lam { body = m_ }, Pi
         { var; arg = u_; body = v_; arg = u_; body = v_; body = v_ }) ->
          check_exp sgn (C.push ctx (var, u_)) m_ v_
      | (sgn, ctx, Root (Const con, s_), v_) ->
          let rec foc exp =
            let u_ = focus sgn ctx s_ exp in
            if equiv_exp sgn u_ v_ then begin () end
              else begin raise (Check "check_exp: exps not equivalent") end in
    (((begin match Sig.lookup sgn con with
       | Decl decl -> foc ((fun r -> r.exp) decl)
       | Def def -> foc ((fun r -> r.exp) def)
       | Abbrev abbrev -> raise (Fail "check_exp: abbrev") end))
      (* why does this fail?*)(* pull some common code out of the following case *))
    | (sgn, ctx, Root (BVar i, s_), v_) ->
        (((begin match C.lookup ctx (i - 1) with
           | Some (_, a_) ->
               let u_ = focus sgn ctx s_ (apply_exp (Shift i) a_) in
               if equiv_exp sgn u_ v_ then begin () end
                 else begin
                   raise (Fail_exp2 ("check_exp: Root,BVar", u_, v_)) end
    | None -> raise (Check "focus: var out of bounds") end))
  (* DeBruijn indices start at 1 *))
| (sgn, ctx, Pi
   { var; arg = a1_; body = a2_; arg = a1_; body = a2_; body = a2_ },
   (Uni _ as uni)) ->
    (begin check_exp sgn ctx a1_ expType;
     check_exp sgn (C.push ctx (var, a1_)) a2_ uni end)
| (_, _, _, _) -> raise (Check "check: bad case") end
let rec focus arg__4 arg__5 arg__6 arg__7 =
  begin match (arg__4, arg__5, arg__6, arg__7) with
  | (sgn, ctx, Nil, (Uni (Type) as ty)) -> ty
  | (sgn, ctx, Nil, (Root (Const _, _) as hd)) -> List.hd
  | (sgn, ctx, App (m_, s_), Pi { arg = a1_; body = a2_; body = a2_ }) ->
      (begin check_exp sgn ctx m_ a1_;
       focus sgn ctx s_ (apply_exp (Dot (m_, id_sub)) a2_) end)
  | (_, _, s_, e_) -> raise (Fail_spine_exp ("focus: bad case", s_, e_)) end
let rec check sgn (e1_) (e2_) = check_exp sgn C.empty e1_ e2_
let rec apply_exp arg__8 arg__9 =
  begin match (arg__8, arg__9) with
  | (_, (Uni _ as uni)) -> uni
  | (sub, Pi
     { var; arg = u_; depend; body = v_; arg = u_; depend; body = v_; 
       depend; body = v_; body = v_ })
      ->
      Pi
        {
          var;
          arg = (apply_exp sub u_);
          depend;
          body = (apply_exp (push_sub sub) v_)
        }
  | (sub, Lam { var; body = u_; body = u_ }) ->
      Lam { var; body = (apply_exp (push_sub sub) u_) }
  | (sub, (Root (h_, s_) as exp)) ->
      let s'_ = apply_spine sub s_ in
      (begin match h_ with
       | Const _ -> Root (h_, s'_)
       | BVar i ->
           (begin match apply_var sub i with
            | RetVar j -> Root ((BVar j), s'_)
            | RetExp (m_) -> reduce m_ s'_ end) end) end
let rec apply_spine arg__10 arg__11 =
  begin match (arg__10, arg__11) with
  | (sub, Nil) -> Nil
  | (sub, App (m_, s_)) -> App ((apply_exp sub m_), (apply_spine sub s_)) end
let rec apply_var arg__12 arg__13 =
  begin match (arg__12, arg__13) with
  | (Dot (m_, sub), i) ->
      if i = 1
      then
        begin (begin match m_ with
               | Root (BVar j, Nil) -> RetVar j
               | _ -> RetExp m_ end) end
  else begin apply_var sub (i - 1) end | (Shift n, i) -> RetVar (i + n)
| (Comp (s1, s2), i) ->
    (begin match apply_var s1 i with
     | RetVar j -> apply_var s2 j
     | RetExp (m_) -> RetExp (apply_exp s2 m_) end) end
let rec compose s1 s2 = Comp (s1, s2)
let rec push_sub s = Dot (one, (compose s shift))
let rec reduce arg__14 arg__15 =
  begin match (arg__14, arg__15) with
  | ((Root (_, _) as exp), Nil) -> exp
  | (Lam { body = m_ }, App (m'_, s_)) ->
      reduce (apply_exp (Dot (m'_, id_sub)) m_) s_
  | (e_, s_) -> raise (Fail_exp_spine ("reduce: bad case: head: ", e_, s_)) end
let rec equiv_exp arg__16 arg__17 arg__18 =
  begin match (arg__16, arg__17, arg__18) with
  | (sgn, Uni u1, Uni u2) -> u1 = u2
  | (sgn, Pi { arg = u1_; body = v1_; body = v1_ }, Pi
     { arg = u2_; body = v2_; body = v2_ }) ->
      (equiv_exp sgn u1_ u2_) && (equiv_exp sgn v1_ v2_)
  | (sgn, Lam { body = u_ }, Lam { body = u'_ }) -> equiv_exp sgn u_ u'_
  | (sgn, Root (BVar i, s1_), Root (BVar i', s2_)) ->
      (i = i') && (equiv_spine sgn s1_ s2_)
  | (sgn, (Root (Const c, s_) as exp), (Root (Const c', s'_) as exp')) ->
      if c = c' then begin equiv_spine sgn s_ s'_ end
      else begin
        (begin match ((Sig.lookup sgn c), (Sig.lookup sgn c')) with
         | (Decl decl, Def def) ->
             if (<>) (((fun r -> r.root)) def) ((fun r -> r.id)) decl
             then begin false end
             else begin equiv_exp sgn exp (reduce ((fun r -> r.def) def) s'_) end
      | (Def def, Decl decl) ->
          if (<>) (((fun r -> r.root)) def) ((fun r -> r.id)) decl
          then begin false end
          else begin equiv_exp sgn (reduce ((fun r -> r.def) def) s_) exp' end
  | (Abbrev { def }, _) -> equiv_exp sgn (reduce def s_) exp'
  | (_, Abbrev { def }) -> equiv_exp sgn exp (reduce def s'_)
  | (Def { def; height = h; root = rc; height = h; root = rc; root = rc },
     Def
     { def = def'; height = h'; root = rc'; height = h'; root = rc';
       root = rc' })
      -> if rc <> rc' then begin false end
      else begin
        if h = h'
        then begin equiv_exp sgn (reduce def s_) (reduce def' s'_) end
        else begin
          if h > h' then begin equiv_exp sgn (reduce def s_) exp' end
          else begin equiv_exp sgn exp (reduce def' s'_) end end end
| (_, _) -> raise (Check "equiv_exp: bad case") end) end
| (_, _, _) -> false end
let rec equiv_spine arg__19 arg__20 arg__21 =
  begin match (arg__19, arg__20, arg__21) with
  | (sgn, Nil, Nil) -> true
  | (sgn, App (e_, s_), App (e'_, s'_)) ->
      (equiv_exp sgn e_ e'_) && (equiv_spine sgn s_ s'_)
  | (_, _, _) -> false end
let rec check_dec =
  begin function
  | (c, Decl { id; name; exp; uni; name; exp; uni; exp; uni; uni }) ->
      let uni' = Uni uni in
      let exp' = eta_expand (exp, uni') in
      (begin check exp' uni';
       Sig.insert (id, (Decl { id; name; exp = exp'; uni })) end)
  | (c, Def
     { id; name; exp; def; height; root; uni; name; exp; def; height; 
       root; uni; exp; def; height; root; uni; def; height; root; uni;
       height; root; uni; root; uni; uni })
      ->
      let uni' = Uni uni in
      let exp' = eta_expand (exp, uni') in
      let def' = eta_expand (def, exp') in
      (begin check exp' uni';
       check def' exp';
       Sig.insert
         (id, (Def { id; name; exp = exp'; def = def'; height; root; uni })) end)
  | (c, Abbrev
     { id; name; exp; def; uni; name; exp; def; uni; exp; def; uni; def; 
       uni; uni })
      ->
      let uni' = Uni uni in
      let exp' = exp in
      let def' = def in
      (((begin check exp' uni';
         check def' exp';
         Sig.insert (id, (Abbrev { id; name; exp = exp'; def = def'; uni })) end))
        (*         val exp' = eta_expand(exp,uni') *)
        (*         val def' = eta_expand(def,exp') *)) end
let rec check_signat' decs =
  List.app
    (begin function
     | (c, dec) as decl -> ((check_dec decl)
         (* L.printl ("checking: " ^ name dec ); *)) end)
  decs
let rec check_signat decs = Timers.time Timers.checking check_signat' decs
let rec check_signat_clear decs = begin Sig.reset (); check_signat decs end
end