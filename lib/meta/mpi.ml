
(* Meta Prover Interface *)
(* Author: Carsten Schuermann *)
module type MTPI  =
  sig
    (*! structure FunSyn : FUNSYN !*)
    module StateSyn : STATESYN
    exception Error of string 
    val init : (int * string list) -> unit
    val select : int -> unit
    val print : unit -> unit
    val next : unit -> unit
    val auto : unit -> unit
    val solve : unit -> unit
    val check : unit -> unit
    val reset : unit -> unit
    (*  val extract: unit -> MetaSyn.Sgn *)
    (*  val show   : unit -> unit *)
    val undo : unit -> unit
  end;;




(* Meta Prover Interface *)
(* Author: Carsten Schuermann *)
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
                   (*! structure IntSyn : INTSYN !*)
                   (*! structure FunSyn' : FUNSYN !*)
                   (*! sharing FunSyn'.IntSyn = IntSyn !*)
                   (*! sharing StateSyn'.IntSyn = IntSyn !*)
                   (*! sharing StateSyn'.FunSyn = FunSyn' !*)
                   (*! sharing RelFun.FunSyn = FunSyn' !*)
                   (*! sharing Print.IntSyn = IntSyn !*)
                   (*! sharing FunTypeCheck.FunSyn = FunSyn' !*)
                   (*! sharing MTPInit.FunSyn = FunSyn' !*)
                   (*! sharing MTPFilling.FunSyn = FunSyn' !*)
                   (*! sharing Inference.FunSyn = FunSyn' !*)
                   (*! sharing Order.IntSyn = IntSyn !*)
                   (*! sharing Names.IntSyn = IntSyn !*)
                   module Ring : RING
                 end) : MTPI =
  struct
    exception Error of string 
    (*! structure FunSyn = FunSyn' !*)
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
    let rec insertOpen (S) = (:=) Open Ring.insert ((!Open), S)
    let rec insertSolved (S) = (:=) Solved Ring.insert ((!Solved), S)
    let rec insert (S) = insertOpen S
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
      | c::__l -> ((I.conDecName (I.sgnLookup c)) ^ ", ") ^ (cLToString __l)
    let rec printFillResult (_, P) =
      let rec formatTuple (__g, P) =
        let rec formatTuple' =
          function
          | F.Unit -> nil
          | Inx (M, F.Unit) -> [Print.formatExp (__g, M)]
          | Inx (M, __P') ->
              (::) (((::) (Print.formatExp (__g, M)) Fmt.String ",") ::
                      Fmt.Break)
                formatTuple' __P' in
        match P with
        | Inx (_, F.Unit) -> Fmt.hbox (formatTuple' P)
        | _ ->
            Fmt.hVbox0 1 1 1
              ((Fmt.String "(") :: ((formatTuple' P) @ [Fmt.String ")"])) in
      let State (n, (__g, B), (IH, OH), d, O, H, F) = current () in
      TextIO.print
        (("Filling successful with proof term:\n" ^
            (Formatter.makestring_fmt (formatTuple (__g, P))))
           ^ "\n")
    let rec SplittingToMenu =
      function
      | (nil, A) -> A
      | ((O)::__l, A) -> SplittingToMenu (__l, ((Splitting O) :: A))
    let rec FillingToMenu (O, A) = (Filling O) :: A
    let rec RecursionToMenu (O, A) = (Recursion O) :: A
    let rec InferenceToMenu (O, A) = (Inference O) :: A
    let rec menu () =
      if empty ()
      then Menu := None
      else
        (let S = current () in
         let SplitO = MTPSplitting.expand S in
         let InfO = Inference.expand S in
         let RecO = MTPRecursion.expand S in
         let FillO = MTPFilling.expand S in
         (:=) Menu Some
           (FillingToMenu
              (FillO,
                (RecursionToMenu
                   (RecO,
                     (InferenceToMenu (InfO, (SplittingToMenu (SplitO, nil)))))))))
    let rec format k =
      if k < 10 then (Int.toString k) ^ ".  " else (Int.toString k) ^ ". "
    let rec menuToString () =
      let rec menuToString' =
        function
        | (k, nil, (None, _)) -> ((Some k), "")
        | (k, nil, ((Some _ as kopt'), _)) -> (kopt', "")
        | (k, (Splitting (O))::M, ((None, None) as kOopt')) ->
            let kOopt'' =
              if MTPSplitting.applicable O
              then ((Some k), (Some O))
              else kOopt' in
            let ((Some k'' as kopt), s) = menuToString' ((k + 1), M, kOopt'') in
            (kopt,
              (if k = k''
               then ((s ^ "\n* ") ^ (format k)) ^ (MTPSplitting.menu O)
               else ((s ^ "\n  ") ^ (format k)) ^ (MTPSplitting.menu O)))
        | (k, (Splitting (O))::M, ((Some k', Some (O')) as kOopt')) ->
            let kOopt'' =
              if MTPSplitting.applicable O
              then
                match MTPSplitting.compare (O, O') with
                | LESS -> ((Some k), (Some O))
                | _ -> kOopt'
              else kOopt' in
            let ((Some k'' as kopt), s) = menuToString' ((k + 1), M, kOopt'') in
            (kopt,
              (if k = k''
               then ((s ^ "\n* ") ^ (format k)) ^ (MTPSplitting.menu O)
               else ((s ^ "\n  ") ^ (format k)) ^ (MTPSplitting.menu O)))
        | (k, (Filling (O))::M, kOopt) ->
            let (kopt, s) = menuToString' ((k + 1), M, kOopt) in
            (kopt, (((s ^ "\n  ") ^ (format k)) ^ (MTPFilling.menu O)))
        | (k, (Recursion (O))::M, kOopt) ->
            let (kopt, s) = menuToString' ((k + 1), M, kOopt) in
            (kopt, (((s ^ "\n  ") ^ (format k)) ^ (MTPRecursion.menu O)))
        | (k, (Inference (O))::M, kOopt) ->
            let (kopt, s) = menuToString' ((k + 1), M, kOopt) in
            (kopt, (((s ^ "\n  ") ^ (format k)) ^ (Inference.menu O))) in
      match !Menu with
      | None -> raise (Error "Menu is empty")
      | Some (M) -> let (kopt, s) = menuToString' (1, M, (None, None)) in s
    let rec printMenu () =
      if empty ()
      then
        (print "[QED]\n";
         print
           (("Statistics: required Twelf.Prover.maxFill := " ^
               (Int.toString (!MTPData.maxFill)))
              ^ "\n"))
      else
        (let S = current () in
         let _ = if !Global.doubleCheck then FunTypeCheck.isState S else () in
         print "\n";
         print (MTPrint.stateToString S);
         print "\nSelect from the following menu:\n";
         print (menuToString ());
         print "\n")
    let rec contains =
      function
      | (nil, _) -> true__
      | (x::__l, __l') ->
          (List.exists (function | x' -> x = x') __l') && (contains (__l, __l'))
    let rec equiv (L1, L2) = (contains (L1, L2)) && (contains (L2, L1))
    let rec transformOrder' =
      function
      | (__g, Arg k) ->
          let k' = ((I.ctxLength __g) - k) + 1 in
          let Dec (_, __v) = I.ctxDec (__g, k') in
          S.Arg (((I.Root ((I.BVar k'), I.Nil)), I.id), (__v, I.id))
      | (__g, Lex (__Os)) ->
          S.Lex (map (function | O -> transformOrder' (__g, O)) __Os)
      | (__g, Simul (__Os)) ->
          S.Simul (map (function | O -> transformOrder' (__g, O)) __Os)
    let rec transformOrder =
      function
      | (__g, All (Prim (__d), F), __Os) ->
          S.All (__d, (transformOrder ((I.Decl (__g, __d)), F, __Os)))
      | (__g, And (__F1, __F2), (O)::__Os) ->
          S.And ((transformOrder (__g, __F1, [O])), (transformOrder (__g, __F2, __Os)))
      | (__g, Ex _, (O)::[]) -> transformOrder' (__g, O)
    let rec select c = try Order.selLookup c with | _ -> Order.Lex []
    let rec init (k, names) =
      let cL =
        map
          (function
           | x -> valOf (Names.constLookup (valOf (Names.stringToQid x))))
          names in
      let _ = MTPGlobal.maxFill := k in
      let _ = reset () in
      let F = RelFun.convertFor cL in
      let O = transformOrder (I.Null, F, (map select cL)) in
      let Slist = MTPInit.init (F, O) in
      let _ = if (List.length Slist) = 0 then raise Domain else () in
      try
        map (function | S -> insert (MTPrint.nameState S)) Slist;
        menu ();
        printMenu ()
      with | Error s -> abort ("MTPSplitting. Error: " ^ s)
      | Error s -> abort ("Filling Error: " ^ s)
      | Error s -> abort ("Recursion Error: " ^ s)
      | Error s -> abort ("Inference Error: " ^ s)
      | Error s -> abort ("Mpi Error: " ^ s)
    let rec select k =
      let rec select' =
        function
        | (k, nil) -> abort "No such menu item"
        | (1, (Splitting (O))::_) ->
            let S' = Timers.time Timers.splitting MTPSplitting.apply O in
            let _ = pushHistory () in
            let _ = delete () in
            let _ = map (function | S -> insert (MTPrint.nameState S)) S' in
            (menu (); printMenu ())
        | (1, (Recursion (O))::_) ->
            let S' = Timers.time Timers.recursion MTPRecursion.apply O in
            let _ = pushHistory () in
            let _ = delete () in
            let _ = insert (MTPrint.nameState S') in (menu (); printMenu ())
        | (1, (Inference (O))::_) ->
            let S' = Timers.time Timers.recursion Inference.apply O in
            let _ = pushHistory () in
            let _ = delete () in
            let _ = insert (MTPrint.nameState S') in (menu (); printMenu ())
        | (1, (Filling (O))::_) ->
            let P =
              try Timers.time Timers.filling MTPFilling.apply O
              with | Error _ -> abort "Filling unsuccessful: no object found" in
            let _ = printFillResult P in
            let _ = delete () in
            let _ = print "\n[Subgoal finished]\n" in
            let _ = print "\n" in (menu (); printMenu ())
        | (k, _::M) -> select' ((k - 1), M) in
      try
        match !Menu with
        | None -> raise (Error "No menu defined")
        | Some (M) -> select' (k, M)
      with | Error s -> abort ("MTPSplitting. Error: " ^ s)
      | Error s -> abort ("Filling Error: " ^ s)
      | Error s -> abort ("Recursion Error: " ^ s)
      | Error s -> abort ("Inference Errror: " ^ s)
      | Error s -> abort ("Mpi Error: " ^ s)
    let rec solve () =
      if empty ()
      then raise (Error "Nothing to prove")
      else
        (let S = current () in
         let (Open', Solved') =
           try MTPStrategy.run [S]
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
      else (let S = current () in FunTypeCheck.isState S)
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
