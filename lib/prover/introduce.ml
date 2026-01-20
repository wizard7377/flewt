
module type INTRODUCE  =
  sig
    module State : STATE
    exception Error of string 
    type nonrec operator
    val expand : State.__Focus -> operator option
    val apply : operator -> unit
    val menu : operator -> string
  end;;




module Introduce(Introduce:sig
                             module State' : STATE
                             module TomegaNames : TOMEGANAMES
                           end) : INTRODUCE =
  struct
    module State = State'
    module S = State'
    module T = Tomega
    module I = IntSyn
    exception Error = S.Error
    type nonrec operator = (T.__Prg * T.__Prg)
    let rec stripTC (TC) = TC
    let rec stripTCOpt =
      function | None -> None | Some (TC) -> Some (stripTC TC)
    let rec stripDec =
      function
      | UDec (__D) -> T.UDec __D
      | PDec (name, __F, TC1, TC2) ->
          T.PDec (name, __F, TC1, (stripTCOpt TC2))
    let rec strip =
      function
      | I.Null -> I.Null
      | Decl (Psi, __D) -> I.Decl ((strip Psi), (stripDec __D))
    let rec expand =
      function
      | Focus ((EVar (Psi, r, All ((__D, _), __F), None, None, _) as R), __W)
          ->
          let __D' = TomegaNames.decName (Psi, __D) in
          Some
            (__R,
              (T.Lam (__D', (T.newEVar ((I.Decl ((strip Psi), __D')), __F)))))
      | Focus
          ((EVar (Psi, r, Ex (((Dec (_, __V) as D), _), __F), None, None, _)
              as R),
           __W)
          ->
          let __X = I.newEVar ((T.coerceCtx Psi), __V) in
          let __Y =
            T.newEVar (Psi, (T.forSub (__F, (T.Dot ((T.Exp __X), T.id))))) in
          Some (__R, (T.PairExp (__X, __Y)))
      | Focus ((EVar (Psi, r, T.True, None, None, _) as R), __W) ->
          Some (__R, T.Unit)
      | Focus (EVar (Psi, r, FClo (__F, s), TC1, TC2, __X), __W) ->
          expand
            (S.Focus
               ((T.EVar (Psi, r, (T.forSub (__F, s)), TC1, TC2, __X)), __W))
      | Focus (EVar (Psi, r, _, _, _, _), __W) -> None
    let rec apply (EVar (_, r, _, _, _, _)) (__P) = (:=) r Some __P
    let rec menu r (__P) = (^) "Intro " TomegaPrint.nameEVar r
    exception Error = Error
    type nonrec operator = operator
    let expand = expand
    let apply = apply
    let menu = menu
  end ;;
