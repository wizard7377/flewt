module type MODEDEC  =
  sig
    exception Error of string 
    val shortToFull :
      (IntSyn.cid * ModeSyn.modeSpine_ * Paths.region) -> ModeSyn.modeSpine_
    val checkFull : (IntSyn.cid * ModeSyn.modeSpine_ * Paths.region) -> unit
    val checkPure :
      ((IntSyn.cid * ModeSyn.modeSpine_) * Paths.region) -> unit
  end


module ModeDec() : MODEDEC =
  struct
    exception Error of string 
    module M = ModeSyn
    module I = IntSyn
    module P = Paths
    type arg_ =
      | Implicit 
      | Explicit 
      | Local 
    let rec error (r, msg) = raise (Error (P.wrap (r, msg)))
    let rec checkName =
      begin function
      | M.Mnil -> ()
      | Mapp (Marg (_, Some name), mS) ->
          let rec checkName' =
            begin function
            | M.Mnil -> ()
            | Mapp (Marg (_, Some name'), mS) ->
                if name = name'
                then
                  begin raise
                          (Error
                             (("Variable name clash: " ^ name) ^
                                " is not unique")) end
                else begin checkName' mS end end in
    checkName' mS end
let rec modeConsistent =
  begin function
  | (M.Star, M.Plus) -> false
  | (M.Star, M.Minus) -> false
  | (M.Star, M.Minus1) -> false
  | (M.Minus, M.Plus) -> false
  | (M.Minus, M.Minus1) -> false
  | (M.Minus1, M.Plus) -> false
  | _ -> true end(* m1 should be M.Plus *)(* m1 should be M.Minus1 *)
(* m1 should be M.Plus *)(* m1 should be M.Minus1 *)
(* m1 should be M.Minus *)(* m1 should be M.Plus *)
let rec empty =
  begin function
  | (0, ms, v_) -> (ms, v_)
  | (k, ms, Pi (_, v_)) ->
      empty ((k - 1), (I.Decl (ms, ((M.Marg (M.Star, None)), Implicit))), v_) end
let rec inferVar =
  begin function
  | (Decl (ms, (Marg (M.Star, nameOpt), Implicit)), mode, 1) ->
      I.Decl (ms, ((M.Marg (mode, nameOpt)), Implicit))
  | (Decl (ms, (Marg (_, nameOpt), Implicit)), M.Plus, 1) ->
      I.Decl (ms, ((M.Marg (M.Plus, nameOpt)), Implicit))
  | (Decl (ms, (Marg (M.Minus, nameOpt), Implicit)), M.Minus1, 1) ->
      I.Decl (ms, ((M.Marg (M.Minus1, nameOpt)), Implicit))
  | ((Decl (_, (_, Implicit)) as ms), _, 1) -> ms
  | ((Decl (_, (_, Local)) as ms), _, 1) -> ms
  | ((Decl (_, (Marg (mode', Some name), Explicit)) as ms), mode, 1) ->
      if modeConsistent (mode', mode) then begin ms end
      else begin
        raise
          (Error
             ((^) (("Mode declaration for " ^ name) ^ " expected to be ")
                M.modeToString mode)) end
  | (Decl (ms, md), mode, k) -> I.Decl ((inferVar (ms, mode, (k - 1))), md) end
let rec inferExp =
  begin function
  | (ms, mode, Root (BVar k, s_)) ->
      inferSpine ((inferVar (ms, mode, k)), mode, s_)
  | (ms, mode, Root (Const cid, s_)) -> inferSpine (ms, mode, s_)
  | (ms, mode, Root (Def cid, s_)) -> inferSpine (ms, mode, s_)
  | (ms, mode, Root (FgnConst (cs, conDec), s_)) -> inferSpine (ms, mode, s_)
  | (ms, mode, Lam ((Dec (nameOpt, _) as d_), u_)) ->
      I.ctxPop
        (inferExp
           ((I.Decl
               ((inferDec (ms, mode, d_)), ((M.Marg (mode, nameOpt)), Local))),
             mode, u_))
  | (ms, mode, Pi (((Dec (nameOpt, _) as d_), _), v_)) ->
      I.ctxPop
        (inferExp
           ((I.Decl
               ((inferDec (ms, mode, d_)), ((M.Marg (mode, nameOpt)), Local))),
             mode, v_))
  | (ms, mode, FgnExp _) -> ms end(* cannot make any assumptions on what is inside a foreign object *)
let rec inferSpine =
  begin function
  | (ms, mode, I.Nil) -> ms
  | (ms, mode, App (u_, s_)) ->
      inferSpine ((inferExp (ms, mode, u_)), mode, s_) end
let rec inferDec (ms, mode, Dec (_, v_)) = inferExp (ms, mode, v_)
let rec inferMode =
  begin function
  | ((ms, Uni (I.Type)), M.Mnil) -> ms
  | ((_, Uni (I.Type)), _) -> raise (Error "Too many modes specified")
  | ((ms, Pi ((Dec (name, v1_), _), v2_)), Mapp (Marg (mode, _), mS)) ->
      I.ctxPop
        (inferMode
           (((I.Decl
                ((inferExp (ms, mode, v1_)),
                  ((M.Marg (mode, name)), Explicit))), v2_), mS))
  | ((ms, Root _), _) ->
      raise (Error "Expected type family, found object constant")
  | _ -> raise (Error "Not enough modes specified") end
let rec abstractMode (ms, mS) =
  let rec abstractMode' =
    begin function
    | (I.Null, mS, _) -> mS
    | (Decl (ms, (marg, _)), mS, k) ->
        abstractMode' (ms, (M.Mapp (marg, mS)), (k + 1)) end in
abstractMode' (ms, mS, 1)
let rec shortToFull (a, mS, r) =
  let rec calcImplicit' =
    begin function
    | ConDec (_, _, k, _, v_, _) ->
        abstractMode ((inferMode ((empty (k, I.Null, v_)), mS)), mS)
    | ConDef (_, _, k, _, v_, _, _) ->
        abstractMode ((inferMode ((empty (k, I.Null, v_)), mS)), mS) end
  (* ignore definition for defined type family since they are opaque *) in
((begin try begin checkName mS; calcImplicit' (I.sgnLookup a) end
  with | Error msg -> error (r, msg) end)
(* re-raise Error with location *))
let rec checkFull (a, mS, r) =
  begin try
          begin checkName mS;
          (((begin match I.sgnLookup a with
             | ConDec (_, _, _, _, v_, _) ->
                 (begin inferMode ((I.Null, v_), mS); () end)
          | ConDef (_, _, _, _, v_, _, _) ->
              (begin inferMode ((I.Null, v_), mS); () end) end))
  (* defined type families treated as separate types for
                 purposes of mode checking (as the operational
                 semantics doesn't expand type definitions) *)) end
with | Error msg -> error (r, msg) end
let rec checkPure =
  begin function
  | ((a, M.Mnil), r) -> ()
  | ((a, Mapp (Marg (M.Minus1, _), mS)), r) ->
      error
        (r,
          "Uniqueness modes (-1) not permitted in `%mode' declarations (use `%unique')")
  | ((a, Mapp (_, mS)), r) -> checkPure ((a, mS), r) end
let shortToFull = shortToFull
let checkFull = checkFull
let checkPure = checkPure end
