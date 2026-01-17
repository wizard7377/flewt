
module type MTPI  =
  sig
    module StateSyn :
    ((STATESYN)(* Meta Prover Interface *)(* Author: Carsten Schuermann *)
    (*! structure FunSyn : FUNSYN !*))
    exception Error of string 
    val init : (int * string list) -> unit
    val select : int -> unit
    val print : unit -> unit
    val next : unit -> unit
    val auto : unit -> unit
    val solve : unit -> unit
    val check : unit -> unit
    val reset : unit -> unit
    val undo :
      unit ->
        ((unit)(*  val show   : unit -> unit *)(*  val extract: unit -> MetaSyn.Sgn *))
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
                   module Ring :
                   ((RING)(* Meta Prover Interface *)
                   (* Author: Carsten Schuermann *)(*! structure IntSyn : INTSYN !*)
                   (*! structure FunSyn' : FUNSYN !*)
                   (*! sharing FunSyn'.IntSyn = IntSyn !*)
                   (*! sharing StateSyn'.IntSyn = IntSyn !*)
                   (*! sharing StateSyn'.FunSyn = FunSyn' !*)(*! sharing RelFun.FunSyn = FunSyn' !*)
                   (*! sharing Print.IntSyn = IntSyn !*)
                   (*! sharing FunTypeCheck.FunSyn = FunSyn' !*)
                   (*! sharing MTPInit.FunSyn = FunSyn' !*)
                   (*! sharing MTPFilling.FunSyn = FunSyn' !*)(*! sharing Inference.FunSyn = FunSyn' !*)
                   (*! sharing Order.IntSyn = IntSyn !*)
                   (*! sharing Names.IntSyn = IntSyn !*))
                 end) : MTPI =
  struct
    exception Error of string 
    module StateSyn =
      ((StateSyn')(*! structure FunSyn = FunSyn' !*))
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
    let ((Menu) : __MenuItem list option ref) = ref NONE
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
      initOpen (); initSolved (); History := nil; Menu := NONE
    let rec cLToString =
      function
      | nil -> ""
      | c::nil -> I.conDecName (I.sgnLookup c)
      | c::L -> ((I.conDecName (I.sgnLookup c)) ^ ", ") ^ (cLToString L)
    let rec printFillResult (_, P) =
      let formatTuple (g, P) =
        let formatTuple' =
          function
          | F.Unit -> nil
          | Inx (M, F.Unit) -> [Print.formatExp (g, M)]
          | Inx (M, P') ->
              (::) (((::) (Print.formatExp (g, M)) Fmt.String ",") ::
                      Fmt.Break)
                formatTuple' P' in
        match P with
        | Inx (_, F.Unit) -> Fmt.Hbox (formatTuple' P)
        | _ ->
            Fmt.HVbox0 1 1 1
              ((Fmt.String "(") :: ((formatTuple' P) @ [Fmt.String ")"])) in
      let State (n, (g, B), (IH, OH), d, O, H, F) = current () in
      TextIO.print
        (("Filling successful with proof term:\n" ^
            (Formatter.makestring_fmt (formatTuple (g, P))))
           ^ "\n")
    let rec SplittingToMenu =
      function
      | (nil, A) -> A
      | ((O)::L, A) -> SplittingToMenu (L, ((Splitting O) :: A))
    let rec FillingToMenu (O, A) = (Filling O) :: A
    let rec RecursionToMenu (O, A) = (Recursion O) :: A
    let rec InferenceToMenu (O, A) = (Inference O) :: A
    let rec menu () =
      if empty ()
      then Menu := NONE
      else
        (let S = current () in
         let SplitO = MTPSplitting.expand S in
         let InfO = Inference.expand S in
         let RecO = MTPRecursion.expand S in
         let FillO = MTPFilling.expand S in
         (:=) Menu SOME
           (FillingToMenu
              (FillO,
                (RecursionToMenu
                   (RecO,
                     (InferenceToMenu (InfO, (SplittingToMenu (SplitO, nil)))))))))
    let rec format k =
      if k < 10 then (Int.toString k) ^ ".  " else (Int.toString k) ^ ". "
    let rec menuToString () =
      let menuToString' =
        function
        | (k, nil, (NONE, _)) -> ((SOME k), "")
        | (k, nil, ((SOME _ as kopt'), _)) -> (kopt', "")
        | (k, (Splitting (O))::M, ((NONE, NONE) as kOopt')) ->
            let kOopt'' =
              if MTPSplitting.applicable O
              then ((SOME k), (SOME O))
              else kOopt' in
            let ((SOME k'' as kopt), s) = menuToString' ((k + 1), M, kOopt'') in
            (kopt,
              (if k = k''
               then ((s ^ "\n* ") ^ (format k)) ^ (MTPSplitting.menu O)
               else ((s ^ "\n  ") ^ (format k)) ^ (MTPSplitting.menu O)))
        | (k, (Splitting (O))::M, ((SOME k', SOME (O')) as kOopt')) ->
            let kOopt'' =
              if MTPSplitting.applicable O
              then
                match MTPSplitting.compare (O, O') with
                | LESS -> ((SOME k), (SOME O))
                | _ -> kOopt'
              else kOopt' in
            let ((SOME k'' as kopt), s) = menuToString' ((k + 1), M, kOopt'') in
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
      | NONE -> raise (Error "Menu is empty")
      | SOME (M) -> let (kopt, s) = menuToString' (1, M, (NONE, NONE)) in s
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
      | (x::L, L') ->
          (List.exists (function | x' -> x = x') L') && (contains (L, L'))
    let rec equiv (L1, L2) = (contains (L1, L2)) && (contains (L2, L1))
    let rec transformOrder' =
      function
      | (g, Arg k) ->
          let k' = ((I.ctxLength g) - k) + 1 in
          let Dec (_, V) = I.ctxDec (g, k') in
          S.Arg (((I.Root ((I.BVar k'), I.Nil)), I.id), (V, I.id))
      | (g, Lex (Os)) ->
          S.Lex (map (function | O -> transformOrder' (g, O)) Os)
      | (g, Simul (Os)) ->
          S.Simul (map (function | O -> transformOrder' (g, O)) Os)
    let rec transformOrder =
      function
      | (g, All (Prim (D), F), Os) ->
          S.All (D, (transformOrder ((I.Decl (g, D)), F, Os)))
      | (g, And (F1, F2), (O)::Os) ->
          S.And ((transformOrder (g, F1, [O])), (transformOrder (g, F2, Os)))
      | (g, Ex _, (O)::[]) -> transformOrder' (g, O)
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
      let select' =
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
        | NONE -> raise (Error "No menu defined")
        | SOME (M) -> select' (k, M)
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
