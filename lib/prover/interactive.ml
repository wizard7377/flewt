
module type INTERACTIVE  =
  sig
    module State : STATE
    exception Error of string 
    val init : string list -> unit
    val select : int -> unit
    val print : unit -> unit
    val stats : unit -> unit
    val focus : string -> unit
    val return : unit -> unit
    val reset : unit -> unit
  end;;




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
                                 module Fill : FILL
                               end) : INTERACTIVE =
  struct
    module State = State'
    exception Error = State'.Error
    module I = IntSyn
    module T = Tomega
    module S = State
    module M = ModeSyn
    module W = WorldSyn
    let rec abort s = print (("* " ^ s) ^ "\n"); raise (Error s)
    let rec convertOneFor cid =
      let __V =
        match I.sgnLookup cid with
        | ConDec (name, _, _, _, __V, I.Kind) -> __V
        | _ -> raise (Error "Type Constant declaration expected") in
      let mS =
        match ModeTable.modeLookup cid with
        | NONE -> raise (Error "Mode declaration expected")
        | Some mS -> mS in
      let rec convertFor' __0__ __1__ __2__ __3__ __4__ =
        match (__0__, __1__, __2__, __3__, __4__) with
        | (Pi ((__D, _), __V), Mapp (Marg (M.Plus, _), mS), w1, w2, n) ->
            let (__F', F'') =
              convertFor'
                (__V, mS, (I.dot1 w1), (I.Dot ((I.Idx n), w2)), (n - 1)) in
            (((fun (__F) ->
                 T.All
                   (((T.UDec (Weaken.strengthenDec (__D, w1))), T.Explicit),
                     (__F' __F)))), F'')
        | (Pi ((__D, _), __V), Mapp (Marg (M.Minus, _), mS), w1, w2, n) ->
            let (__F', F'') =
              convertFor'
                (__V, mS, (I.comp (w1, I.shift)), (I.dot1 w2), (n + 1)) in
            (__F', (T.Ex (((I.decSub (__D, w2)), T.Explicit), F'')))
        | (Uni (I.Type), M.Mnil, _, _, _) -> (((fun (__F) -> __F)), T.True)
        | _ -> raise (Error "type family must be +/- moded") in
      let rec shiftPlus mS =
        let rec shiftPlus' __5__ __6__ =
          match (__5__, __6__) with
          | (M.Mnil, n) -> n
          | (Mapp (Marg (M.Plus, _), mS'), n) -> shiftPlus' (mS', (n + 1))
          | (Mapp (Marg (M.Minus, _), mS'), n) -> shiftPlus' (mS', n) in
        shiftPlus' (mS, 0) in
      let n = shiftPlus mS in
      let (__F, __F') = convertFor' (__V, mS, I.id, (I.Shift n), n) in
      ((__F __F')
        (* convertFor' (V, mS, w1, w2, n) = (F', F'')

           Invariant:
           If   G |- V = {{G'}} type :kind
           and  G |- w1 : G+
           and  G+, G'+, G- |- w2 : G
           and  G+, G'+, G- |- ^n : G+
           and  mS is a spine for G'
           then F'  is a formula excepting a another formula as argument s.t.
                If G+, G'+ |- F formula,
                then . |- F' F formula
           and  G+, G'+ |- F'' formula
        *)
        (* shiftPlus (mS) = s'

         Invariant:
         s' = ^(# of +'s in mS)
         *))
    let rec convertFor =
      function
      | nil -> raise (Error "Empty theorem")
      | a::[] -> convertOneFor a
      | a::__L -> T.And ((convertOneFor a), (convertFor __L))
    type __MenuItem =
      | Split of Split.operator 
      | Fill of Fill.operator 
      | Introduce of Introduce.operator 
      | Fix of FixedPoint.operator 
      | Elim of Elim.operator 
    let ((Focus) : S.__State list ref) = ref []
    let ((Menu) : __MenuItem list option ref) = ref NONE
    let rec SplittingToMenu (__O) (__A) = (Split __O) :: __A
    let rec initFocus () = Focus := []
    let rec normalize () =
      match !Focus with
      | (State (__W, Psi, __P, __F))::Rest ->
          Focus := ((S.State (__W, Psi, (T.derefPrg __P), __F)) :: Rest)
      | _ -> ()
    let rec reset () = initFocus (); Menu := NONE
    let rec format k =
      if k < 10 then (Int.toString k) ^ ".  " else (Int.toString k) ^ ". "
    let rec menuToString () =
      let rec menuToString' __7__ __8__ =
        match (__7__, __8__) with
        | (k, nil) -> ""
        | (k, (Split (__O))::__M) ->
            let s = menuToString' ((k + 1), __M) in
            ((s ^ "\n  ") ^ (format k)) ^ (Split.menu __O)
        | (k, (Introduce (__O))::__M) ->
            let s = menuToString' ((k + 1), __M) in
            ((s ^ "\n  ") ^ (format k)) ^ (Introduce.menu __O)
        | (k, (Fill (__O))::__M) ->
            let s = menuToString' ((k + 1), __M) in
            ((s ^ "\n  ") ^ (format k)) ^ (Fill.menu __O)
        | (k, (Fix (__O))::__M) ->
            let s = menuToString' ((k + 1), __M) in
            ((s ^ "\n  ") ^ (format k)) ^ (FixedPoint.menu __O)
        | (k, (Elim (__O))::__M) ->
            let s = menuToString' ((k + 1), __M) in
            ((s ^ "\n  ") ^ (format k)) ^ (Elim.menu __O) in
      ((match !Menu with
        | NONE -> raise (Error "Menu is empty")
        | Some (__M) -> menuToString' (1, __M))
        (*          | menuToString' (k, Inference O :: M,kOopt) =
              let
                val (kopt, s) = menuToString' (k+1, M, kOopt)
              in
                (kopt, s ^ "\n  " ^ (format k) ^ (Inference.menu O))
              end
*))
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
      | (State (__W, Psi, __P, __F))::__R ->
          (print "\n=======================";
           print "\n= META THEOREM PROVER =\n";
           print (TomegaPrint.ctxToString Psi);
           print "\n-----------------------\n";
           print (TomegaPrint.forToString (Psi, __F));
           print "\n-----------------------\n";
           print (TomegaPrint.prgToString (Psi, __P));
           print "\n-----------------------";
           print (menuToString ());
           print "\n=======================\n")
      | (StateLF (EVar (r, __G, __V, __Cs) as X))::__R ->
          (print "\n=======================";
           print "\n=== THEOREM PROVER ====\n";
           print (Print.ctxToString (I.Null, __G));
           print "\n-----------------------\n";
           print (Print.expToString (__G, __V));
           print "\n-----------------------\n";
           print (Print.expToString (__G, __X));
           print "\n-----------------------";
           print (menuToString ());
           print "\n=======================\n")
    let rec menu () =
      match !Focus with
      | [] -> print "Please initialize first\n"
      | (State (__W, Psi, __P, __F))::_ ->
          let __Xs = S.collectT __P in
          let __F1 =
            map
              (fun (EVar (Psi, r, __F, TC, TCs, __X)) ->
                 Names.varReset I.Null;
                 S.Focus
                   ((T.EVar ((TomegaPrint.nameCtx Psi), r, __F, TC, TCs, __X)),
                     __W)) __Xs in
          let __Ys = S.collectLF __P in
          let __F2 = map (fun (__Y) -> S.FocusLF __Y) __Ys in
          let rec splitMenu =
            function
            | [] -> []
            | operators::l -> (@) (map Split operators) splitMenu l in
          let _ = Global.doubleCheck := true__ in
          let rec introMenu =
            function
            | [] -> []
            | (Some oper)::l -> (::) (Introduce oper) introMenu l
            | (NONE)::l -> introMenu l in
          let intro = introMenu (map Introduce.expand __F1) in
          let fill =
            foldr
              (fun (__S) ->
                 fun l -> (@) l map (fun (__O) -> Fill __O) (Fill.expand __S))
              nil __F2 in
          let rec elimMenu =
            function
            | [] -> []
            | operators::l -> (@) (map Elim operators) elimMenu l in
          let elim = elimMenu (map Elim.expand __F1) in
          let split = splitMenu (map Split.expand __F1) in
          (:=) Menu Some (((intro @ split) @ fill) @ elim)
      | (StateLF (__Y))::_ ->
          let __Ys = Abstract.collectEVars (I.Null, (__Y, I.id), nil) in
          let __F2 = map (fun (__Y) -> S.FocusLF __Y) __Ys in
          let fill =
            foldr
              (fun (__S) ->
                 fun l -> (@) l map (fun (__O) -> Fill __O) (Fill.expand __S))
              nil __F2 in
          (:=) Menu Some fill
    let rec select k =
      let rec select' __9__ __10__ =
        match (__9__, __10__) with
        | (k, nil) -> abort "No such menu item"
        | (1, (Split (__O))::_) ->
            Timers.time Timers.splitting Split.apply __O
        | (1, (Introduce (__O))::_) -> Introduce.apply __O
        | (1, (Elim (__O))::_) -> Elim.apply __O
        | (1, (Fill (__O))::_) -> Timers.time Timers.filling Fill.apply __O
        | (k, _::__M) -> select' ((k - 1), __M)(* no timer yet -- cs *)
        (* no timer yet -- cs *) in
      match !Menu with
      | NONE -> raise (Error "No menu defined")
      | Some (__M) ->
          (try select' (k, __M); normalize (); menu (); printmenu ()
           with | Error s -> ())
    let rec init names =
      let _ = TomegaPrint.evarReset () in
      let cL =
        map
          (fun x -> valOf (Names.constLookup (valOf (Names.stringToQid x))))
          names in
      let __F = convertFor cL in
      let __Ws = map W.lookup cL in
      let rec select c = try Order.selLookup c with | _ -> Order.Lex [] in
      let TC = Tomega.transformTC (I.Null, __F, (map select cL)) in
      let (__W)::_ = __Ws in
      let _ = Focus := [S.init (__F, __W)] in
      let __P =
        match !Focus with
        | [] -> abort "Initialization of proof goal failed\n"
        | (State (__W, Psi, __P, __F))::_ -> __P in
      let __Xs = S.collectT __P in
      let __F =
        map
          (fun (EVar (Psi, r, __F, TC, TCs, __X)) ->
             Names.varReset I.Null;
             S.Focus
               ((T.EVar ((TomegaPrint.nameCtx Psi), r, __F, TC, TCs, __X)),
                 __W)) __Xs in
      let (Ofix)::[] = map (fun f -> FixedPoint.expand (f, TC)) __F in
      let _ = FixedPoint.apply Ofix in
      let _ = normalize () in
      let _ = menu () in
      let _ = printmenu () in ((())
        (* so far omitted:  make sure that all parts of the theorem are
             declared in the same world
          *))
    let rec focus n =
      ((match !Focus with
        | [] -> print "Please initialize first\n"
        | (State (__W, Psi, __P, __F))::_ ->
            let rec findIEVar =
              function
              | nil -> raise (Error ("cannot focus on " ^ n))
              | (__Y)::__Ys ->
                  if (Names.evarName ((T.coerceCtx Psi), __Y)) = n
                  then
                    (Focus := ((!) ((::) (S.StateLF __Y)) Focus);
                     normalize ();
                     menu ();
                     printmenu ())
                  else findIEVar __Ys in
            let rec findTEVar =
              function
              | nil -> findIEVar (S.collectLF __P)
              | (EVar (Psi, r, __F, TC, TCs, __Y) as X)::__Xs ->
                  if (Names.evarName ((T.coerceCtx Psi), __Y)) = n
                  then
                    (Focus :=
                       ((!) ((::) (S.State
                                     (__W, (TomegaPrint.nameCtx Psi), __X,
                                       __F)))
                          Focus);
                     normalize ();
                     menu ();
                     printmenu ())
                  else findTEVar __Xs in
            findTEVar (S.collectT __P)
        | (StateLF (__U))::_ ->
            (match Names.getEVarOpt n with
             | NONE -> raise (Error ("cannot focus on " ^ n))
             | Some (__Y) ->
                 (Focus := ((!) ((::) (S.StateLF __Y)) Focus);
                  normalize ();
                  menu ();
                  printmenu ())))
      (* Invariant: U has already been printed, all EVars occuring
                 in U are already named.
              *))
    let rec return () =
      match !Focus with
      | (__S)::[] -> if S.close __S then print "[Q.E.D.]\n" else ()
      | (__S)::Rest -> (Focus := Rest; normalize (); menu (); printmenu ())
    let init = init
    let select = select
    let print = printmenu
    let stats = printStats
    let reset = reset
    let focus = focus
    let return = return
  end ;;
