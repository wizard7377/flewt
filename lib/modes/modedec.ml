
module type MODEDEC  =
  sig
    exception Error of string 
    val shortToFull :
      IntSyn.cid ->
        ModeSyn.__ModeSpine -> Paths.region -> ModeSyn.__ModeSpine
    val checkFull : IntSyn.cid -> ModeSyn.__ModeSpine -> Paths.region -> unit
    val checkPure :
      (IntSyn.cid * ModeSyn.__ModeSpine) -> Paths.region -> unit
  end;;




module ModeDec() : MODEDEC =
  struct
    exception Error of string 
    module M = ModeSyn
    module I = IntSyn
    module P = Paths
    type __Arg =
      | Implicit 
      | Explicit 
      | Local 
    let rec error r msg = raise (Error (P.wrap (r, msg)))
    let rec checkName =
      function
      | M.Mnil -> ()
      | Mapp (Marg (_, Some name), mS) ->
          let rec checkName' =
            function
            | M.Mnil -> ()
            | Mapp (Marg (_, Some name'), mS) ->
                if name = name'
                then
                  raise
                    (Error
                       (("Variable name clash: " ^ name) ^ " is not unique"))
                else checkName' mS in
          checkName' mS
    let rec modeConsistent __0__ __1__ =
      match (__0__, __1__) with
      | (M.Star, M.Plus) -> false
      | (M.Star, M.Minus) -> false
      | (M.Star, M.Minus1) -> false
      | (M.Minus, M.Plus) -> false
      | (M.Minus, M.Minus1) -> false
      | (M.Minus1, M.Plus) -> false
      | _ -> true(* m1 should be M.Plus *)(* m1 should be M.Minus1 *)
      (* m1 should be M.Plus *)(* m1 should be M.Minus1 *)
      (* m1 should be M.Minus *)(* m1 should be M.Plus *)
    let rec empty __2__ __3__ __4__ =
      match (__2__, __3__, __4__) with
      | (0, ms, __V) -> (ms, __V)
      | (k, ms, Pi (_, __V)) ->
          empty
            ((k - 1), (I.Decl (ms, ((M.Marg (M.Star, None)), Implicit))),
              __V)
    let rec inferVar __5__ __6__ __7__ =
      match (__5__, __6__, __7__) with
      | (Decl (ms, (Marg (M.Star, nameOpt), Implicit)), mode, 1) ->
          I.Decl (ms, ((M.Marg (mode, nameOpt)), Implicit))
      | (Decl (ms, (Marg (_, nameOpt), Implicit)), M.Plus, 1) ->
          I.Decl (ms, ((M.Marg (M.Plus, nameOpt)), Implicit))
      | (Decl (ms, (Marg (M.Minus, nameOpt), Implicit)), M.Minus1, 1) ->
          I.Decl (ms, ((M.Marg (M.Minus1, nameOpt)), Implicit))
      | ((Decl (_, (_, Implicit)) as ms), _, 1) -> ms
      | ((Decl (_, (_, Local)) as ms), _, 1) -> ms
      | ((Decl (_, (Marg (mode', Some name), Explicit)) as ms), mode, 1) ->
          if modeConsistent (mode', mode)
          then ms
          else
            raise
              (Error
                 ((^) (("Mode declaration for " ^ name) ^ " expected to be ")
                    M.modeToString mode))
      | (Decl (ms, md), mode, k) ->
          I.Decl ((inferVar (ms, mode, (k - 1))), md)
    let rec inferExp __8__ __9__ __10__ =
      match (__8__, __9__, __10__) with
      | (ms, mode, Root (BVar k, __S)) ->
          inferSpine ((inferVar (ms, mode, k)), mode, __S)
      | (ms, mode, Root (Const cid, __S)) -> inferSpine (ms, mode, __S)
      | (ms, mode, Root (Def cid, __S)) -> inferSpine (ms, mode, __S)
      | (ms, mode, Root (FgnConst (cs, conDec), __S)) ->
          inferSpine (ms, mode, __S)
      | (ms, mode, Lam ((Dec (nameOpt, _) as D), __U)) ->
          I.ctxPop
            (inferExp
               ((I.Decl
                   ((inferDec (ms, mode, __D)),
                     ((M.Marg (mode, nameOpt)), Local))), mode, __U))
      | (ms, mode, Pi (((Dec (nameOpt, _) as D), _), __V)) ->
          I.ctxPop
            (inferExp
               ((I.Decl
                   ((inferDec (ms, mode, __D)),
                     ((M.Marg (mode, nameOpt)), Local))), mode, __V))
      | (ms, mode, FgnExp _) -> ms(* cannot make any assumptions on what is inside a foreign object *)
    let rec inferSpine __11__ __12__ __13__ =
      match (__11__, __12__, __13__) with
      | (ms, mode, I.Nil) -> ms
      | (ms, mode, App (__U, __S)) ->
          inferSpine ((inferExp (ms, mode, __U)), mode, __S)
    let rec inferDec ms mode (Dec (_, __V)) = inferExp (ms, mode, __V)
    let rec inferMode __14__ __15__ =
      match (__14__, __15__) with
      | ((ms, Uni (I.Type)), M.Mnil) -> ms
      | ((_, Uni (I.Type)), _) -> raise (Error "Too many modes specified")
      | ((ms, Pi ((Dec (name, __V1), _), __V2)), Mapp (Marg (mode, _), mS))
          ->
          I.ctxPop
            (inferMode
               (((I.Decl
                    ((inferExp (ms, mode, __V1)),
                      ((M.Marg (mode, name)), Explicit))), __V2), mS))
      | ((ms, Root _), _) ->
          raise (Error "Expected type family, found object constant")
      | _ -> raise (Error "Not enough modes specified")
    let rec abstractMode ms mS =
      let rec abstractMode' __16__ __17__ __18__ =
        match (__16__, __17__, __18__) with
        | (I.Null, mS, _) -> mS
        | (Decl (ms, (marg, _)), mS, k) ->
            abstractMode' (ms, (M.Mapp (marg, mS)), (k + 1)) in
      abstractMode' (ms, mS, 1)
    let rec shortToFull a mS r =
      let rec calcImplicit' =
        function
        | ConDec (_, _, k, _, __V, _) ->
            abstractMode ((inferMode ((empty (k, I.Null, __V)), mS)), mS)
        | ConDef (_, _, k, _, __V, _, _) ->
            abstractMode ((inferMode ((empty (k, I.Null, __V)), mS)), mS)
        (* ignore definition for defined type family since they are opaque *) in
      ((try checkName mS; calcImplicit' (I.sgnLookup a)
        with | Error msg -> error (r, msg))
        (* re-raise Error with location *))
    let rec checkFull a mS r =
      try
        checkName mS;
        (((match I.sgnLookup a with
           | ConDec (_, _, _, _, __V, _) ->
               (inferMode ((I.Null, __V), mS); ())
           | ConDef (_, _, _, _, __V, _, _) ->
               (inferMode ((I.Null, __V), mS); ())))
        (* defined type families treated as separate types for
                 purposes of mode checking (as the operational
                 semantics doesn't expand type definitions) *))
      with | Error msg -> error (r, msg)
    let rec checkPure __19__ __20__ =
      match (__19__, __20__) with
      | ((a, M.Mnil), r) -> ()
      | ((a, Mapp (Marg (M.Minus1, _), mS)), r) ->
          error
            (r,
              "Uniqueness modes (-1) not permitted in `%mode' declarations (use `%unique')")
      | ((a, Mapp (_, mS)), r) -> checkPure ((a, mS), r)
    let shortToFull = shortToFull
    let checkFull = checkFull
    let checkPure = checkPure
  end ;;
