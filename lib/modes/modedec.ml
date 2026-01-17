
module type MODEDEC  =
  sig
    exception Error of
      ((string)(* Modified: Frank Pfenning *)(* Author: Carsten Schuermann *)
      (* Modes: short and long forms *)) 
    val shortToFull :
      (IntSyn.cid * ModeSyn.__ModeSpine * Paths.region) ->
        ModeSyn.__ModeSpine
    val checkFull : (IntSyn.cid * ModeSyn.__ModeSpine * Paths.region) -> unit
    val checkPure :
      ((IntSyn.cid * ModeSyn.__ModeSpine) * Paths.region) -> unit
  end;;




module ModeDec() : MODEDEC =
  struct
    exception Error of
      ((string)(*! structure Paths = Paths' !*)(*! structure ModeSyn = ModeSyn' !*))
      
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
      | Mapp (Marg (_, SOME name), mS) ->
          let checkName' =
            function
            | M.Mnil -> ()
            | Mapp (Marg (_, SOME name'), mS) ->
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
      | (0, ms, V) -> (ms, V)
      | (k, ms, Pi (_, V)) ->
          empty
            ((k - 1), (I.Decl (ms, ((M.Marg (M.Star, NONE)), Implicit))), V)
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
      | ((Decl (_, (Marg (mode', SOME name), Explicit)) as ms), mode, 1) ->
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
      | (ms, mode, Lam ((Dec (nameOpt, _) as D), U)) ->
          I.ctxPop
            (inferExp
               ((I.Decl
                   ((inferDec (ms, mode, D)),
                     ((M.Marg (mode, nameOpt)), Local))), mode, U))
      | (ms, mode, Pi (((Dec (nameOpt, _) as D), _), V)) ->
          I.ctxPop
            (inferExp
               ((I.Decl
                   ((inferDec (ms, mode, D)),
                     ((M.Marg (mode, nameOpt)), Local))), mode, V))
      | (ms, mode, FgnExp _) -> ms
    let rec inferSpine =
      function
      | (ms, mode, I.Nil) -> ms
      | (ms, mode, App (U, S)) ->
          inferSpine ((inferExp (ms, mode, U)), mode, S)
    let rec inferDec (ms, mode, Dec (_, V)) = inferExp (ms, mode, V)
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
      let abstractMode' =
        function
        | (I.Null, mS, _) -> mS
        | (Decl (ms, (marg, _)), mS, k) ->
            abstractMode' (ms, (M.Mapp (marg, mS)), (k + 1)) in
      abstractMode' (ms, mS, 1)
    let rec shortToFull (a, mS, r) =
      let calcImplicit' =
        function
        | ConDec (_, _, k, _, V, _) ->
            abstractMode ((inferMode ((empty (k, I.Null, V)), mS)), mS)
        | ConDef (_, _, k, _, V, _, _) ->
            abstractMode ((inferMode ((empty (k, I.Null, V)), mS)), mS) in
      try checkName mS; calcImplicit' (I.sgnLookup a)
      with | Error msg -> error (r, msg)
    let rec checkFull (a, mS, r) =
      try
        checkName mS;
        (match I.sgnLookup a with
         | ConDec (_, _, _, _, V, _) -> (inferMode ((I.Null, V), mS); ())
         | ConDef (_, _, _, _, V, _, _) -> (inferMode ((I.Null, V), mS); ()))
      with | Error msg -> error (r, msg)
    let rec checkPure =
      function
      | ((a, M.Mnil), r) -> ()
      | ((a, Mapp (Marg (M.Minus1, _), mS)), r) ->
          error
            (r,
              "Uniqueness modes (-1) not permitted in `%mode' declarations (use `%unique')")
      | ((a, Mapp (_, mS)), r) -> checkPure ((a, mS), r)
    let ((shortToFull)(* Representation invariant:

       The modes of parameters are represented in the following mode list

       M ::= . | M, <Marg, Arg>

       G corresponds to a context. We say M is a mode list for U, if
       G |- U : V and M assigns modes to parameters in G
         (and similarly for all other syntactic categories)

       The main function of this module is to
        (a) assign modes to implicit arguments in a type family
        (b) check the mode specification for consistency

       Example:

         a : type.
         b : a -> a -> type.
         c : b X X -> b X Y -> type.

       Then

         %mode c +M -N.

       will infer X to be input and Y to be output

         %mode +{X:a} -{Y:a} +{M:b X Y} -{N:b X Y} (c M N).

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
           to occur as an index object in the type of a variable y:V(x) with mode m2

       m1\m2 + * - -1
        +    Y Y Y Y
        *    N y n n
        -    N y Y n
        -1   N Y Y Y

       The entries y,n constitute a bug fix, Wed Aug 20 11:50:27 2003 -fp
       The entry n specifies that the type
    *)
      (* m1 should be M.Plus *)(* m1 should be M.Minus *)
      (* m1 should be M.Minus1 *)(* m1 should be M.Plus *)
      (* m1 should be M.Minus1 *)(* m1 should be M.Plus *)
      (* empty (k, ms, V) = (ms', V')

       Invariant:
       If    V = {A_1} .. {A_n} V1   in Sigma
       and   V has k implicit arguments
       then  ms' = ms, <( *, NONE), Implicit>  ... <( *, NONE), Implicit>   (k times)
       and   V' = V1
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
      (* inferExp (ms, m, U) = ms'

       Invariant:
       If  ms is a mode list for U,   (U in nf)
       and m is a mode
       then ms' is the mode list consistently updated for all parameters occurring in U,
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
      (* inferDec (ms, m, x:V) = ms'

       Invariant:
       If  ms is a mode list for V,   (V in nf)
       and m is a mode
       then ms' is the mode list consistently updated for all parameters occurring in V,
         wrt. to m.   (see inferVar)
    *)
      (* inferMode ((ms, V), mS) = ms'

       Invariant:
       If  ms is a mode list for V,
       and mS is a mode spine,
       then ms' is the mode list for V which is consistent with V.
    *)
      (* abstractMode (ms, mS) = mS'

       Invariant:
       If    V = {A1} .. {An} V1  is a type (with n implicit parameter)
       and   ms is a mode list for V,
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
      (* re-raise Error with location *)(* checkFull (a, mS, r) = ()

       Invariant:
       mS modeSpine, all modes are named.
       r is the text region of the mode declaration
       if mS is not a valid mode spine in full form then
       exception Error is raised.
    *)
      (* defined type families treated as separate types for
                 purposes of mode checking (as the operational
                 semantics doesn't expand type definitions) *)
      (* re-raise error with location *)(* checkPure (a, mS, r) = ()
       Effect: raises Error(msg) if the modes in mS mention (-1)
    *))
      = shortToFull
    let checkFull = checkFull
    let checkPure = checkPure
  end ;;
