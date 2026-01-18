
(* Modes: short and long forms *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning *)
module type MODEDEC  =
  sig
    exception Error of string 
    val shortToFull :
      (IntSyn.cid * ModeSyn.__ModeSpine * Paths.region) ->
        ModeSyn.__ModeSpine
    val checkFull : (IntSyn.cid * ModeSyn.__ModeSpine * Paths.region) -> unit
    val checkPure :
      ((IntSyn.cid * ModeSyn.__ModeSpine) * Paths.region) -> unit
  end;;




(* Modes: short and full mode declarations *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning *)
module ModeDec() : MODEDEC =
  struct
    (*! structure ModeSyn' : MODESYN !*)
    (*! structure Paths' : PATHS !*)
    (*! structure ModeSyn = ModeSyn' !*)
    (*! structure Paths = Paths' !*)
    exception Error of string 
    module M = ModeSyn
    module I = IntSyn
    module P = Paths
    type __Arg =
      | Implicit 
      | Explicit 
      | Local 
    let rec error (r, msg) = raise (Error (P.wrap (r, msg)))
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
    let rec modeConsistent =
      function
      | (M.Star, M.Plus) -> false__
      | (M.Star, M.Minus) -> false__
      | (M.Star, M.Minus1) -> false__
      | (M.Minus, M.Plus) -> false__
      | (M.Minus, M.Minus1) -> false__
      | (M.Minus1, M.Plus) -> false__
      | _ -> true__
    let rec empty =
      function
      | (0, ms, __v) -> (ms, __v)
      | (k, ms, Pi (_, __v)) ->
          empty
            ((k - 1), (I.Decl (ms, ((M.Marg (M.Star, None)), Implicit))), __v)
    let rec inferVar =
      function
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
    let rec inferExp =
      function
      | (ms, mode, Root (BVar k, S)) ->
          inferSpine ((inferVar (ms, mode, k)), mode, S)
      | (ms, mode, Root (Const cid, S)) -> inferSpine (ms, mode, S)
      | (ms, mode, Root (Def cid, S)) -> inferSpine (ms, mode, S)
      | (ms, mode, Root (FgnConst (cs, conDec), S)) ->
          inferSpine (ms, mode, S)
      | (ms, mode, Lam ((Dec (nameOpt, _) as __d), __u)) ->
          I.ctxPop
            (inferExp
               ((I.Decl
                   ((inferDec (ms, mode, __d)),
                     ((M.Marg (mode, nameOpt)), Local))), mode, __u))
      | (ms, mode, Pi (((Dec (nameOpt, _) as __d), _), __v)) ->
          I.ctxPop
            (inferExp
               ((I.Decl
                   ((inferDec (ms, mode, __d)),
                     ((M.Marg (mode, nameOpt)), Local))), mode, __v))
      | (ms, mode, FgnExp _) -> ms
    let rec inferSpine =
      function
      | (ms, mode, I.Nil) -> ms
      | (ms, mode, App (__u, S)) ->
          inferSpine ((inferExp (ms, mode, __u)), mode, S)
    let rec inferDec (ms, mode, Dec (_, __v)) = inferExp (ms, mode, __v)
    let rec inferMode =
      function
      | ((ms, Uni (I.Type)), M.Mnil) -> ms
      | ((_, Uni (I.Type)), _) -> raise (Error "Too many modes specified")
      | ((ms, Pi ((Dec (name, V1), _), V2)), Mapp (Marg (mode, _), mS)) ->
          I.ctxPop
            (inferMode
               (((I.Decl
                    ((inferExp (ms, mode, V1)),
                      ((M.Marg (mode, name)), Explicit))), V2), mS))
      | ((ms, Root _), _) ->
          raise (Error "Expected type family, found object constant")
      | _ -> raise (Error "Not enough modes specified")
    let rec abstractMode (ms, mS) =
      let rec abstractMode' =
        function
        | (I.Null, mS, _) -> mS
        | (Decl (ms, (marg, _)), mS, k) ->
            abstractMode' (ms, (M.Mapp (marg, mS)), (k + 1)) in
      abstractMode' (ms, mS, 1)
    let rec shortToFull (a, mS, r) =
      let rec calcImplicit' =
        function
        | ConDec (_, _, k, _, __v, _) ->
            abstractMode ((inferMode ((empty (k, I.Null, __v)), mS)), mS)
        | ConDef (_, _, k, _, __v, _, _) ->
            abstractMode ((inferMode ((empty (k, I.Null, __v)), mS)), mS) in
      try checkName mS; calcImplicit' (I.sgnLookup a)
      with | Error msg -> error (r, msg)
    let rec checkFull (a, mS, r) =
      try
        checkName mS;
        (match I.sgnLookup a with
         | ConDec (_, _, _, _, __v, _) -> (inferMode ((I.Null, __v), mS); ())
         | ConDef (_, _, _, _, __v, _, _) -> (inferMode ((I.Null, __v), mS); ()))
      with | Error msg -> error (r, msg)
    let rec checkPure =
      function
      | ((a, M.Mnil), r) -> ()
      | ((a, Mapp (Marg (M.Minus1, _), mS)), r) ->
          error
            (r,
              "Uniqueness modes (-1) not permitted in `%mode' declarations (use `%unique')")
      | ((a, Mapp (_, mS)), r) -> checkPure ((a, mS), r)
    (* Representation invariant:

       The modes of parameters are represented in the following mode list

       M ::= . | M, <Marg, Arg>

       __g corresponds to a context. We say M is a mode list for __u, if
       __g |- __u : __v and M assigns modes to parameters in __g
         (and similarly for all other syntactic categories)

       The main function of this module is to
        (a) assign modes to implicit arguments in a type family
        (b) check the mode specification for consistency

       Example:

         a : type.
         b : a -> a -> type.
         c : b x x -> b x y -> type.

       Then

         %mode c +M -N.

       will infer x to be input and y to be output

         %mode +{x:a} -{y:a} +{M:b x y} -{N:b x y} (c M N).

       Generally, it is inconsistent
       for an unspecified ( * ) or output (-) argument to occur
       in the type of an input (+) argument
    *)
    (* checkname mS = ()

       Invariant:
       mS modeSpine, all modes are named.
       If mS contains two entries with the same name
       then Error is raised
    *)
    (* modeConsistent (m1, m2) = true
       iff it is consistent for a variable x with mode m1
           to occur as an index object in the type of a variable y:__v(x) with mode m2

       m1\m2 + * - -1
        +    y y y y
        *    N y n n
        -    N y y n
        -1   N y y y

       The entries y,n constitute a bug fix, Wed Aug 20 11:50:27 2003 -fp
       The entry n specifies that the type
    *)
    (* m1 should be M.Plus *)
    (* m1 should be M.Minus *)
    (* m1 should be M.Minus1 *)
    (* m1 should be M.Plus *)
    (* m1 should be M.Minus1 *)
    (* m1 should be M.Plus *)
    (* empty (k, ms, __v) = (ms', __v')

       Invariant:
       If    __v = {A_1} .. {A_n} V1   in Sigma
       and   __v has k implicit arguments
       then  ms' = ms, <( *, None), Implicit>  ... <( *, None), Implicit>   (k times)
       and   __v' = V1
    *)
    (* inferVar (ms, m, k) = ms'

       Invariant:
       If  ms is a mode list,
       and k is declared with mode mk in ms
       and m is the mode for a variable y in whose type k occurs
       then ms' is the same as ms replacing only mk by
       mk' = m o mk

        m o mk  + * - -1
        ----------------
        +       + + + +
        *       + * - -1
        -       + - - -1
        -1      + -1-1-1

        Effect: if the mode mk for k was explicitly declared and inconsistent
                with m o mk, an error is raised
    *)
    (* inferExp (ms, m, __u) = ms'

       Invariant:
       If  ms is a mode list for __u,   (__u in nf)
       and m is a mode
       then ms' is the mode list consistently updated for all parameters occurring in __u,
         wrt. to m. (see inferVar)
    *)
    (* cannot make any assumptions on what is inside a foreign object *)
    (* inferSpine (ms, m, S) = ms'

       Invariant:
       If  ms is a mode list for S,   (S in nf)
       and m is a mode
       then ms' is the mode list consistently updated for all parameters occurring in S,
         wrt. to m. (see inferVar)
    *)
    (* inferDec (ms, m, x:__v) = ms'

       Invariant:
       If  ms is a mode list for __v,   (__v in nf)
       and m is a mode
       then ms' is the mode list consistently updated for all parameters occurring in __v,
         wrt. to m.   (see inferVar)
    *)
    (* inferMode ((ms, __v), mS) = ms'

       Invariant:
       If  ms is a mode list for __v,
       and mS is a mode spine,
       then ms' is the mode list for __v which is consistent with V.
    *)
    (* abstractMode (ms, mS) = mS'

       Invariant:
       If    __v = {A1} .. {An} V1  is a type (with n implicit parameter)
       and   ms is a mode list for __v,
       then  mS' = {m1} .. {mn} mS
       where m1 .. mn are the infered modes for the implicit parameters
    *)
    (* shortToFull (cid, mS, r) = mS'

       Invariant:
       mS modeSpine, all modes are named.
       r is the text region of the mode declaration
       if mS is a mode spine in short form (implicit parameters are not moded),
       then mS' is a mode spine in full form (all parameters are moded)

       Full form can be different then intended by the user.
    *)
    (* ignore definition for defined type family since they are opaque *)
    (* re-raise Error with location *)
    (* checkFull (a, mS, r) = ()

       Invariant:
       mS modeSpine, all modes are named.
       r is the text region of the mode declaration
       if mS is not a valid mode spine in full form then
       exception Error is raised.
    *)
    (* defined type families treated as separate types for
                 purposes of mode checking (as the operational
                 semantics doesn't expand type definitions) *)
    (* re-raise error with location *)
    (* checkPure (a, mS, r) = ()
       Effect: raises Error(msg) if the modes in mS mention (-1)
    *)
    let shortToFull = shortToFull
    let checkFull = checkFull
    let checkPure = checkPure
  end ;;
