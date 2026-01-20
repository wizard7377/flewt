
module type MTPI  =
  sig
    module StateSyn : STATESYN
    exception Error of string 
    val init : int -> string list -> unit
    val select : int -> unit
    val print : unit -> unit
    val next : unit -> unit
    val auto : unit -> unit
    val solve : unit -> unit
    val check : unit -> unit
    val reset : unit -> unit
    val undo : unit -> unit
  end;;




module MTPi(MTPi:sig
                   module MTPGlobal : MTPGLOBAL
                   module StateSyn' : STATESYN
                   module RelFun : RELFUN
                   module Formatter : FORMATTER
                   module Print : PRINT
                   module FunTypeCheck : FUNTYPECHECK
                   module MTPData : MTPDATA
                   module MTPInit : MTPINIT
                   module MTPFilling : MTPFILLING
                   module Inference : INFERENCE
                   module MTPSplitting : MTPSPLITTING
                   module MTPRecursion : MTPRECURSION
                   module MTPStrategy : MTPSTRATEGY
                   module MTPrint : MTPRINT
                   module Order : ORDER
                   module Names : NAMES
                   module Timers : TIMERS
                   module Ring : RING
                 end) : MTPI =
  struct
    exception Error of string 
    module StateSyn = StateSyn'
    module I = IntSyn
    module F = FunSyn
    module S = StateSyn
    module Fmt = Formatter
    type __MenuItem =
      | Filling of MTPFilling.operator 
      | Recursion of MTPRecursion.operator 
      | Splitting of MTPSplitting.operator 
      | Inference of Inference.operator 
    let ((Open) : StateSyn.__State Ring.ring ref) = ref (Ring.init [])
    let ((Solved) : StateSyn.__State Ring.ring ref) = ref (Ring.init [])
    let ((History) :
      (StateSyn.__State Ring.ring * StateSyn.__State Ring.ring) list ref) =
      ref nil
    let ((Menu) : __MenuItem list option ref) = ref None
    let rec initOpen () = (:=) Open Ring.init []
    let rec initSolved () = (:=) Solved Ring.init []
    let rec empty () = Ring.empty (!Open)
    let rec current () = Ring.current (!Open)
    let rec delete () = (:=) Open Ring.delete (!Open)
    let rec insertOpen (__S) = (:=) Open Ring.insert ((!Open), __S)
    let rec insertSolved (__S) = (:=) Solved Ring.insert ((!Solved), __S)
    let rec insert (__S) = insertOpen __S
    let rec collectOpen () = Ring.foldr (::) nil (!Open)
    let rec collectSolved () = Ring.foldr (::) nil (!Solved)
    let rec nextOpen () = (:=) Open Ring.next (!Open)
    let rec pushHistory () = (History := ((!Open), (!Solved))) :: (!History)
    let rec popHistory () =
      match !History with
      | nil -> raise (Error "History stack empty")
      | (Open', Solved')::History' ->
          (History := History'; Open := Open'; Solved := Solved')
    let rec abort s = print ("* " ^ s); raise (Error s)
    let rec reset () =
      initOpen (); initSolved (); History := nil; Menu := None
    let rec cLToString =
      function
      | nil -> ""
      | c::nil -> I.conDecName (I.sgnLookup c)
      | c::__L -> ((I.conDecName (I.sgnLookup c)) ^ ", ") ^ (cLToString __L)
    let rec printFillResult _ (__P) =
      let rec formatTuple (__G) (__P) =
        let rec formatTuple' =
          function
          | F.Unit -> nil
          | Inx (__M, F.Unit) -> [Print.formatExp (__G, __M)]
          | Inx (__M, __P') ->
              (::) (((::) (Print.formatExp (__G, __M)) Fmt.String ",") ::
                      Fmt.Break)
                formatTuple' __P' in
        match __P with
        | Inx (_, F.Unit) -> Fmt.Hbox (formatTuple' __P)
        | _ ->
            Fmt.HVbox0 1 1 1
              ((Fmt.String "(") :: ((formatTuple' __P) @ [Fmt.String ")"])) in
      let State (n, (__G, __B), (IH, OH), d, __O, __H, __F) = current () in
      TextIO.print
        (("Filling successful with proof term:\n" ^
            (Formatter.makestring_fmt (formatTuple (__G, __P))))
           ^ "\n")
    let rec SplittingToMenu __0__ __1__ =
      match (__0__, __1__) with
      | (nil, __A) -> __A
      | ((__O)::__L, __A) -> SplittingToMenu (__L, ((Splitting __O) :: __A))
    let rec FillingToMenu (__O) (__A) = (Filling __O) :: __A
    let rec RecursionToMenu (__O) (__A) = (Recursion __O) :: __A
    let rec InferenceToMenu (__O) (__A) = (Inference __O) :: __A
    let rec menu () =
      if empty ()
      then Menu := None
      else
        (let __S = current () in
         let SplitO = MTPSplitting.expand __S in
         let InfO = Inference.expand __S in
         let RecO = MTPRecursion.expand __S in
         let FillO = MTPFilling.expand __S in
         (:=) Menu Some
           (FillingToMenu
              (FillO,
                (RecursionToMenu
                   (RecO,
                     (InferenceToMenu (InfO, (SplittingToMenu (SplitO, nil)))))))))
    let rec format k =
      if k < 10 then (Int.toString k) ^ ".  " else (Int.toString k) ^ ". "
    let rec menuToString () =
      let rec menuToString' __2__ __3__ __4__ =
        match (__2__, __3__, __4__) with
        | (k, nil, (None, _)) -> ((Some k), "")
        | (k, nil, ((Some _ as kopt'), _)) -> (kopt', "")
        | (k, (Splitting (__O))::__M, ((None, None) as kOopt')) ->
            let kOopt'' =
              if MTPSplitting.applicable __O
              then ((Some k), (Some __O))
              else kOopt' in
            let ((Some k'' as kopt), s) =
              menuToString' ((k + 1), __M, kOopt'') in
            (kopt,
              (if k = k''
               then ((s ^ "\n* ") ^ (format k)) ^ (MTPSplitting.menu __O)
               else ((s ^ "\n  ") ^ (format k)) ^ (MTPSplitting.menu __O)))
        | (k, (Splitting (__O))::__M, ((Some k', Some (__O')) as kOopt')) ->
            let kOopt'' =
              if MTPSplitting.applicable __O
              then
                match MTPSplitting.compare (__O, __O') with
                | LESS -> ((Some k), (Some __O))
                | _ -> kOopt'
              else kOopt' in
            let ((Some k'' as kopt), s) =
              menuToString' ((k + 1), __M, kOopt'') in
            (kopt,
              (if k = k''
               then ((s ^ "\n* ") ^ (format k)) ^ (MTPSplitting.menu __O)
               else ((s ^ "\n  ") ^ (format k)) ^ (MTPSplitting.menu __O)))
        | (k, (Filling (__O))::__M, kOopt) ->
            let (kopt, s) = menuToString' ((k + 1), __M, kOopt) in
            (kopt, (((s ^ "\n  ") ^ (format k)) ^ (MTPFilling.menu __O)))
        | (k, (Recursion (__O))::__M, kOopt) ->
            let (kopt, s) = menuToString' ((k + 1), __M, kOopt) in
            (kopt, (((s ^ "\n  ") ^ (format k)) ^ (MTPRecursion.menu __O)))
        | (k, (Inference (__O))::__M, kOopt) ->
            let (kopt, s) = menuToString' ((k + 1), __M, kOopt) in
            (kopt, (((s ^ "\n  ") ^ (format k)) ^ (Inference.menu __O))) in
      match !Menu with
      | None -> raise (Error "Menu is empty")
      | Some (__M) ->
          let (kopt, s) = menuToString' (1, __M, (None, None)) in s
    let rec printMenu () =
      if empty ()
      then
        (print "[QED]\n";
         print
           (("Statistics: required Twelf.Prover.maxFill := " ^
               (Int.toString (!MTPData.maxFill)))
              ^ "\n"))
      else
        (let __S = current () in
         let _ = if !Global.doubleCheck then FunTypeCheck.isState __S else () in
         print "\n";
         print (MTPrint.stateToString __S);
         print "\nSelect from the following menu:\n";
         print (menuToString ());
         print "\n")
    let rec contains __5__ __6__ =
      match (__5__, __6__) with
      | (nil, _) -> true
      | (x::__L, __L') ->
          (List.exists (fun x' -> x = x') __L') && (contains (__L, __L'))
    let rec equiv (__L1) (__L2) =
      (contains (__L1, __L2)) && (contains (__L2, __L1))
    let rec transformOrder' __7__ __8__ =
      match (__7__, __8__) with
      | (__G, Arg k) ->
          let k' = ((I.ctxLength __G) - k) + 1 in
          let Dec (_, __V) = I.ctxDec (__G, k') in
          S.Arg (((I.Root ((I.BVar k'), I.Nil)), I.id), (__V, I.id))
      | (__G, Lex (__Os)) ->
          S.Lex (map (fun (__O) -> transformOrder' (__G, __O)) __Os)
      | (__G, Simul (__Os)) ->
          S.Simul (map (fun (__O) -> transformOrder' (__G, __O)) __Os)
    let rec transformOrder __9__ __10__ __11__ =
      match (__9__, __10__, __11__) with
      | (__G, All (Prim (__D), __F), __Os) ->
          S.All (__D, (transformOrder ((I.Decl (__G, __D)), __F, __Os)))
      | (__G, And (__F1, __F2), (__O)::__Os) ->
          S.And
            ((transformOrder (__G, __F1, [__O])),
              (transformOrder (__G, __F2, __Os)))
      | (__G, Ex _, (__O)::[]) -> transformOrder' (__G, __O)
    let rec select c = try Order.selLookup c with | _ -> Order.Lex []
    let rec init k names =
      let cL =
        map
          (fun x -> valOf (Names.constLookup (valOf (Names.stringToQid x))))
          names in
      let _ = MTPGlobal.maxFill := k in
      let _ = reset () in
      let __F = RelFun.convertFor cL in
      let __O = transformOrder (I.Null, __F, (map select cL)) in
      let Slist = MTPInit.init (__F, __O) in
      let _ = if (List.length Slist) = 0 then raise Domain else () in
      try
        map (fun (__S) -> insert (MTPrint.nameState __S)) Slist;
        menu ();
        printMenu ()
      with | Error s -> abort ("MTPSplitting. Error: " ^ s)
      | Error s -> abort ("Filling Error: " ^ s)
      | Error s -> abort ("Recursion Error: " ^ s)
      | Error s -> abort ("Inference Error: " ^ s)
      | Error s -> abort ("Mpi Error: " ^ s)
    let rec select k =
      let rec select' __12__ __13__ =
        match (__12__, __13__) with
        | (k, nil) -> abort "No such menu item"
        | (1, (Splitting (__O))::_) ->
            let __S' = Timers.time Timers.splitting MTPSplitting.apply __O in
            let _ = pushHistory () in
            let _ = delete () in
            let _ = map (fun (__S) -> insert (MTPrint.nameState __S)) __S' in
            (menu (); printMenu ())
        | (1, (Recursion (__O))::_) ->
            let __S' = Timers.time Timers.recursion MTPRecursion.apply __O in
            let _ = pushHistory () in
            let _ = delete () in
            let _ = insert (MTPrint.nameState __S') in
            (menu (); printMenu ())
        | (1, (Inference (__O))::_) ->
            let __S' = Timers.time Timers.recursion Inference.apply __O in
            let _ = pushHistory () in
            let _ = delete () in
            let _ = insert (MTPrint.nameState __S') in
            (menu (); printMenu ())
        | (1, (Filling (__O))::_) ->
            let __P =
              try Timers.time Timers.filling MTPFilling.apply __O
              with | Error _ -> abort "Filling unsuccessful: no object found" in
            let _ = printFillResult __P in
            let _ = delete () in
            let _ = print "\n[Subgoal finished]\n" in
            let _ = print "\n" in (menu (); printMenu ())
        | (k, _::__M) -> select' ((k - 1), __M) in
      try
        match !Menu with
        | None -> raise (Error "No menu defined")
        | Some (__M) -> select' (k, __M)
      with | Error s -> abort ("MTPSplitting. Error: " ^ s)
      | Error s -> abort ("Filling Error: " ^ s)
      | Error s -> abort ("Recursion Error: " ^ s)
      | Error s -> abort ("Inference Errror: " ^ s)
      | Error s -> abort ("Mpi Error: " ^ s)
    let rec solve () =
      if empty ()
      then raise (Error "Nothing to prove")
      else
        (let __S = current () in
         let (Open', Solved') =
           try MTPStrategy.run [__S]
           with | Error s -> abort ("MTPSplitting. Error: " ^ s)
           | Error s -> abort ("Filling Error: " ^ s)
           | Error s -> abort ("Recursion Error: " ^ s)
           | Error s -> abort ("Inference Errror: " ^ s)
           | Error s -> abort ("Mpi Error: " ^ s) in
         let _ = pushHistory () in
         let _ = delete () in
         let _ = map insertOpen Open' in
         let _ = map insertSolved Solved' in menu (); printMenu ())
    let rec check () =
      if empty ()
      then raise (Error "Nothing to check")
      else (let __S = current () in FunTypeCheck.isState __S)
    let rec auto () =
      let (Open', Solved') =
        try MTPStrategy.run (collectOpen ())
        with | Error s -> abort ("MTPSplitting. Error: " ^ s)
        | Error s -> abort ("Filling Error: " ^ s)
        | Error s -> abort ("Recursion Error: " ^ s)
        | Error s -> abort ("Inference Errror: " ^ s)
        | Error s -> abort ("Mpi Error: " ^ s) in
      let _ = pushHistory () in
      let _ = initOpen () in
      let _ = map insertOpen Open' in
      let _ = map insertSolved Solved' in menu (); printMenu ()
    let rec next () = nextOpen (); menu (); printMenu ()
    let rec undo () = popHistory (); menu (); printMenu ()
    let init = init
    let select = select
    let print = printMenu
    let next = next
    let reset = reset
    let solve = solve
    let auto = auto
    let check = check
    let undo = undo
  end ;;
