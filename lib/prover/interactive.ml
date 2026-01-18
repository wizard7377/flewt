
(* Meta Prover Interface *)
(* Author: Carsten Schuermann *)
module type INTERACTIVE  =
  sig
    (*! structure IntSyn : INTSYN !*)
    (*! structure Tomega : TOMEGA !*)
    module State : STATE
    exception Error of string 
    val init : string list -> unit
    val select : int -> unit
    val print : unit -> unit
    val stats : unit -> unit
    val focus : string -> unit
    val return : unit -> unit
    (*   val next   : unit -> unit *)
    val reset : unit -> unit
  end;;




(* Meta Prover Interface *)
(* Author: Carsten Schuermann *)
module Interactive(Interactive:sig
                                 module Global : GLOBAL
                                 module State' : STATE
                                 module Formatter : FORMATTER
                                 module Trail : TRAIL
                                 module Ring : RING
                                 module Names : NAMES
                                 module Weaken : WEAKEN
                                 module WorldSyn : WORLDSYN
                                 module Introduce : INTRODUCE
                                 module Elim : ELIM
                                 module Split : SPLIT
                                 module FixedPoint : FIXEDPOINT
                                 (*! structure IntSyn' : INTSYN !*)
                                 (*! structure Tomega' : TOMEGA !*)
                                 (*! sharing Tomega'.IntSyn = IntSyn' !*)
                                 (*! sharing State'.IntSyn = IntSyn' !*)
                                 (*! sharing State'.Tomega = Tomega' !*)
                                 (*! sharing Names.IntSyn = IntSyn' !*)
                                 (*! sharing Weaken.IntSyn = IntSyn' !*)
                                 (* structure ModeSyn : MODESYN *)
                                 (*! sharing ModeSyn.IntSyn = IntSyn' !*)
                                 (*! sharing WorldSyn.IntSyn = IntSyn' !*)
                                 (*! sharing WorldSyn.Tomega = Tomega' !*)
                                 (*! sharing Introduce.IntSyn = IntSyn' !*)
                                 (*! sharing Introduce.Tomega = Tomega' !*)
                                 (*! sharing Elim.IntSyn = IntSyn' !*)
                                 (*! sharing Elim.Tomega = Tomega' !*)
                                 (*! sharing Split.IntSyn = IntSyn' !*)
                                 (*! sharing Split.Tomega = Tomega' !*)
                                 (*! sharing FixedPoint.IntSyn = IntSyn' !*)
                                 (*! sharing FixedPoint.Tomega = Tomega' !*)
                                 module Fill : FILL
                               end) : INTERACTIVE =
  struct
    (*! structure IntSyn = IntSyn' !*)
    (*! structure Tomega = Tomega' !*)
    module State = State'
    exception Error = State'.Error
    module I = IntSyn
    module T = Tomega
    module S = State
    module M = ModeSyn
    module W = WorldSyn
    let rec abort s = print (("* " ^ s) ^ "\n"); raise (Error s)
    let rec convertOneFor cid =
      let __v =
        match I.sgnLookup cid with
        | ConDec (name, _, _, _, __v, I.Kind) -> __v
        | _ -> raise (Error "Type Constant declaration expected") in
      let mS =
        match ModeTable.modeLookup cid with
        | None -> raise (Error "Mode declaration expected")
        | Some mS -> mS in
      let rec convertFor' =
        function
        | (Pi ((__d, _), __v), Mapp (Marg (M.Plus, _), mS), w1, w2, n) ->
            let (__F', __F'') =
              convertFor'
                (__v, mS, (I.dot1 w1), (I.Dot ((I.Idx n), w2)), (n - 1)) in
            (((function
               | F ->
                   T.All
                     (((T.UDec (Weaken.strengthenDec (__d, w1))), T.Explicit),
                       (__F' F)))), __F'')
        | (Pi ((__d, _), __v), Mapp (Marg (M.Minus, _), mS), w1, w2, n) ->
            let (__F', __F'') =
              convertFor'
                (__v, mS, (I.comp (w1, I.shift)), (I.dot1 w2), (n + 1)) in
            (__F', (T.Ex (((I.decSub (__d, w2)), T.Explicit), __F'')))
        | (Uni (I.Type), M.Mnil, _, _, _) -> (((function | F -> F)), T.True)
        | _ -> raise (Error "type family must be +/- moded") in
      let rec shiftPlus mS =
        let rec shiftPlus' =
          function
          | (M.Mnil, n) -> n
          | (Mapp (Marg (M.Plus, _), mS'), n) -> shiftPlus' (mS', (n + 1))
          | (Mapp (Marg (M.Minus, _), mS'), n) -> shiftPlus' (mS', n) in
        shiftPlus' (mS, 0) in
      let n = shiftPlus mS in
      let (F, __F') = convertFor' (__v, mS, I.id, (I.Shift n), n) in F __F'
    let rec convertFor =
      function
      | nil -> raise (Error "Empty theorem")
      | a::[] -> convertOneFor a
      | a::__l -> T.And ((convertOneFor a), (convertFor __l))
    type __MenuItem =
      | Split of Split.operator 
      | Fill of Fill.operator 
      | Introduce of Introduce.operator 
      | Fix of FixedPoint.operator 
      | Elim of Elim.operator 
    let ((Focus) : S.__State list ref) = ref []
    let ((Menu) : __MenuItem list option ref) = ref None
    let rec SplittingToMenu (O, A) = (Split O) :: A
    let rec initFocus () = Focus := []
    let rec normalize () =
      match !Focus with
      | (State (W, Psi, P, F))::Rest ->
          Focus := ((S.State (W, Psi, (T.derefPrg P), F)) :: Rest)
      | _ -> ()
    let rec reset () = initFocus (); Menu := None
    let rec format k =
      if k < 10 then (Int.toString k) ^ ".  " else (Int.toString k) ^ ". "
    let rec menuToString () =
      let rec menuToString' =
        function
        | (k, nil) -> ""
        | (k, (Split (O))::M) ->
            let s = menuToString' ((k + 1), M) in
            ((s ^ "\n  ") ^ (format k)) ^ (Split.menu O)
        | (k, (Introduce (O))::M) ->
            let s = menuToString' ((k + 1), M) in
            ((s ^ "\n  ") ^ (format k)) ^ (Introduce.menu O)
        | (k, (Fill (O))::M) ->
            let s = menuToString' ((k + 1), M) in
            ((s ^ "\n  ") ^ (format k)) ^ (Fill.menu O)
        | (k, (Fix (O))::M) ->
            let s = menuToString' ((k + 1), M) in
            ((s ^ "\n  ") ^ (format k)) ^ (FixedPoint.menu O)
        | (k, (Elim (O))::M) ->
            let s = menuToString' ((k + 1), M) in
            ((s ^ "\n  ") ^ (format k)) ^ (Elim.menu O) in
      match !Menu with
      | None -> raise (Error "Menu is empty")
      | Some (M) -> menuToString' (1, M)
    let rec printStats () =
      let nopen = 0 in
      let nsolved = 0 in
      print "Statistics:\n\n";
      print
        (("Number of goals : " ^ (Int.toString (nopen + nsolved))) ^ "\n");
      print (("     open goals : " ^ (Int.toString nopen)) ^ "\n");
      print (("   solved goals : " ^ (Int.toString nsolved)) ^ "\n")
    let rec printmenu () =
      match !Focus with
      | [] -> abort "QED"
      | (State (W, Psi, P, F))::R ->
          (print "\n=======================";
           print "\n= META THEOREM PROVER =\n";
           print (TomegaPrint.ctxToString Psi);
           print "\n-----------------------\n";
           print (TomegaPrint.forToString (Psi, F));
           print "\n-----------------------\n";
           print (TomegaPrint.prgToString (Psi, P));
           print "\n-----------------------";
           print (menuToString ());
           print "\n=======================\n")
      | (StateLF (EVar (r, __g, __v, __Cs) as x))::R ->
          (print "\n=======================";
           print "\n=== THEOREM PROVER ====\n";
           print (Print.ctxToString (I.Null, __g));
           print "\n-----------------------\n";
           print (Print.expToString (__g, __v));
           print "\n-----------------------\n";
           print (Print.expToString (__g, x));
           print "\n-----------------------";
           print (menuToString ());
           print "\n=======================\n")
    let rec menu () =
      match !Focus with
      | [] -> print "Please initialize first\n"
      | (State (W, Psi, P, F))::_ ->
          let __Xs = S.collectT P in
          let __F1 =
            map
              (function
               | EVar (Psi, r, F, TC, TCs, x) ->
                   (Names.varReset I.Null;
                    S.Focus
                      ((T.EVar ((TomegaPrint.nameCtx Psi), r, F, TC, TCs, x)),
                        W))) __Xs in
          let __Ys = S.collectLF P in
          let __F2 = map (function | y -> S.FocusLF y) __Ys in
          let rec splitMenu =
            function
            | [] -> []
            | operators::l -> (@) (map Split operators) splitMenu l in
          let _ = Global.doubleCheck := true__ in
          let rec introMenu =
            function
            | [] -> []
            | (Some oper)::l -> (::) (Introduce oper) introMenu l
            | (None)::l -> introMenu l in
          let intro = introMenu (map Introduce.expand __F1) in
          let fill =
            foldr
              (function
               | (S, l) ->
                   (@) l map ((function | O -> Fill O)) (Fill.expand S)) nil
              __F2 in
          let rec elimMenu =
            function
            | [] -> []
            | operators::l -> (@) (map Elim operators) elimMenu l in
          let elim = elimMenu (map Elim.expand __F1) in
          let split = splitMenu (map Split.expand __F1) in
          (:=) Menu Some (((intro @ split) @ fill) @ elim)
      | (StateLF (y))::_ ->
          let __Ys = Abstract.collectEVars (I.Null, (y, I.id), nil) in
          let __F2 = map (function | y -> S.FocusLF y) __Ys in
          let fill =
            foldr
              (function
               | (S, l) ->
                   (@) l map ((function | O -> Fill O)) (Fill.expand S)) nil
              __F2 in
          (:=) Menu Some fill
    let rec select k =
      let rec select' =
        function
        | (k, nil) -> abort "No such menu item"
        | (1, (Split (O))::_) -> Timers.time Timers.splitting Split.apply O
        | (1, (Introduce (O))::_) -> Introduce.apply O
        | (1, (Elim (O))::_) -> Elim.apply O
        | (1, (Fill (O))::_) -> Timers.time Timers.filling Fill.apply O
        | (k, _::M) -> select' ((k - 1), M) in
      match !Menu with
      | None -> raise (Error "No menu defined")
      | Some (M) ->
          (try select' (k, M); normalize (); menu (); printmenu ()
           with | Error s -> ())
    let rec init names =
      let _ = TomegaPrint.evarReset () in
      let cL =
        map
          (function
           | x -> valOf (Names.constLookup (valOf (Names.stringToQid x))))
          names in
      let F = convertFor cL in
      let __Ws = map W.lookup cL in
      let rec select c = try Order.selLookup c with | _ -> Order.Lex [] in
      let TC = Tomega.transformTC (I.Null, F, (map select cL)) in
      let (W)::_ = __Ws in
      let _ = Focus := [S.init (F, W)] in
      let P =
        match !Focus with
        | [] -> abort "Initialization of proof goal failed\n"
        | (State (W, Psi, P, F))::_ -> P in
      let __Xs = S.collectT P in
      let F =
        map
          (function
           | EVar (Psi, r, F, TC, TCs, x) ->
               (Names.varReset I.Null;
                S.Focus
                  ((T.EVar ((TomegaPrint.nameCtx Psi), r, F, TC, TCs, x)), W)))
          __Xs in
      let (Ofix)::[] = map (function | f -> FixedPoint.expand (f, TC)) F in
      let _ = FixedPoint.apply Ofix in
      let _ = normalize () in let _ = menu () in let _ = printmenu () in ()
    let rec focus n =
      match !Focus with
      | [] -> print "Please initialize first\n"
      | (State (W, Psi, P, F))::_ ->
          let rec findIEVar =
            function
            | nil -> raise (Error ("cannot focus on " ^ n))
            | (y)::__Ys ->
                if (Names.evarName ((T.coerceCtx Psi), y)) = n
                then
                  (Focus := ((!) ((::) (S.StateLF y)) Focus);
                   normalize ();
                   menu ();
                   printmenu ())
                else findIEVar __Ys in
          let rec findTEVar =
            function
            | nil -> findIEVar (S.collectLF P)
            | (EVar (Psi, r, F, TC, TCs, y) as x)::__Xs ->
                if (Names.evarName ((T.coerceCtx Psi), y)) = n
                then
                  (Focus :=
                     ((!) ((::) (S.State (W, (TomegaPrint.nameCtx Psi), x, F)))
                        Focus);
                   normalize ();
                   menu ();
                   printmenu ())
                else findTEVar __Xs in
          findTEVar (S.collectT P)
      | (StateLF (__u))::_ ->
          (match Names.getEVarOpt n with
           | None -> raise (Error ("cannot focus on " ^ n))
           | Some (y) ->
               (Focus := ((!) ((::) (S.StateLF y)) Focus);
                normalize ();
                menu ();
                printmenu ()))
    let rec return () =
      match !Focus with
      | (S)::[] -> if S.close S then print "[Q.E.D.]\n" else ()
      | (S)::Rest -> (Focus := Rest; normalize (); menu (); printmenu ())
    (* this is pretty preliminary:
       I think we should just adapt the internal representation for formulas
    *)
    (* convertFor' (__v, mS, w1, w2, n) = (__F', __F'')

           Invariant:
           If   __g |- __v = {{__g'}} type :kind
           and  __g |- w1 : __g+
           and  __g+, __g'+, __g- |- w2 : __g
           and  __g+, __g'+, __g- |- ^n : __g+
           and  mS is a spine for __g'
           then __F'  is a formula excepting a another formula as argument s.t.
                If __g+, __g'+ |- F formula,
                then . |- __F' F formula
           and  __g+, __g'+ |- __F'' formula
        *)
    (* shiftPlus (mS) = s'

         Invariant:
         s' = ^(# of +'s in mS)
         *)
    (* convertFor __l = __F'

       Invariant:
       If   __l is a list of type families
       then __F' is the conjunction of the logical interpretation of each
            type family
     *)
    (* here ends the preliminary stuff *)
    (*          | menuToString' (k, Inference O :: M,kOopt) =
              let
                val (kopt, s) = menuToString' (k+1, M, kOopt)
              in
                (kopt, s ^ "\n  " ^ (format k) ^ (Inference.menu O))
              end
*)
    (* no timer yet -- cs *)
    (* no timer yet -- cs *)
    (* so far omitted:  make sure that all parts of the theorem are
             declared in the same world
          *)
    (* focus n = ()

       Invariant:
       Let n be a string.
       Side effect: Focus on selected subgoal.
    *)
    (* Invariant: __u has already been printed, all EVars occuring
                 in __u are already named.
              *)
    let init = init
    let select = select
    let print = printmenu
    let stats = printStats
    let reset = reset
    let focus = focus
    let return = return
  end ;;
