
module type MPI  =
  sig
    module MetaSyn :
    ((METASYN)(* Meta Prover Interface *)(* Author: Carsten Schuermann *))
    exception Error of string 
    val init : (int * string list) -> unit
    val select : int -> unit
    val print : unit -> unit
    val next : unit -> unit
    val auto : unit -> unit
    val solve : unit -> unit
    val lemma : string -> unit
    val reset : unit -> unit
    val extract : unit -> MetaSyn.__Sgn
    val show : unit -> unit
    val undo : unit -> unit
  end;;




module Mpi(Mpi:sig
                 module MetaGlobal : METAGLOBAL
                 module MetaSyn' : METASYN
                 module Init : INIT
                 module Filling : FILLING
                 module Splitting : SPLITTING
                 module Recursion : RECURSION
                 module Lemma : LEMMA
                 module Strategy : STRATEGY
                 module Qed : QED
                 module MetaPrint : METAPRINT
                 module Names : NAMES
                 module Timers : TIMERS
                 module Ring :
                 ((RING)(* Meta Prover Interface *)(* Author: Carsten Schuermann *)
                 (*! sharing Names.IntSyn = MetaSyn'.IntSyn !*))
               end) : MPI =
  struct
    module MetaSyn = MetaSyn'
    exception Error of string 
    module M = MetaSyn
    module I = IntSyn
    type __MenuItem =
      | Filling of Filling.operator 
      | Recursion of Recursion.operator 
      | Splitting of Splitting.operator 
    let ((Open) : MetaSyn.__State Ring.ring ref) = ref (Ring.init [])
    let ((Solved) : MetaSyn.__State Ring.ring ref) = ref (Ring.init [])
    let ((History) :
      (MetaSyn.__State Ring.ring * MetaSyn.__State Ring.ring) list ref) =
      ref nil
    let ((Menu) : __MenuItem list option ref) = ref NONE
    let rec initOpen () = (:=) Open Ring.init []
    let rec initSolved () = (:=) Solved Ring.init []
    let rec empty () = Ring.empty (!Open)
    let rec current () = Ring.current (!Open)
    let rec delete () = (:=) Open Ring.delete (!Open)
    let rec insertOpen (S) = (:=) Open Ring.insert ((!Open), S)
    let rec insertSolved (S) = (:=) Solved Ring.insert ((!Solved), S)
    let rec insert (S) =
      if Qed.subgoal S
      then
        (insertSolved S;
         print (MetaPrint.stateToString S);
         print "\n[Subgoal finished]\n";
         print "\n")
      else insertOpen S
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
    let rec SplittingToMenu =
      function
      | (nil, A) -> A
      | ((O)::L, A) -> SplittingToMenu (L, ((Splitting O) :: A))
    let rec FillingToMenu =
      function
      | (nil, A) -> A
      | ((O)::L, A) -> FillingToMenu (L, ((Filling O) :: A))
    let rec RecursionToMenu =
      function
      | (nil, A) -> A
      | ((O)::L, A) -> RecursionToMenu (L, ((Recursion O) :: A))
    let rec menu () =
      if empty ()
      then Menu := NONE
      else
        (let S = current () in
         let SplitO = Splitting.expand S in
         let RecO = Recursion.expandEager S in
         let (FillO, FillC) = Filling.expand S in
         (:=) Menu SOME
           (FillingToMenu
              ([FillC],
                (FillingToMenu
                   (FillO,
                     (RecursionToMenu (RecO, (SplittingToMenu (SplitO, nil)))))))))
    let rec format k =
      if k < 10 then (Int.toString k) ^ ".  " else (Int.toString k) ^ ". "
    let rec menuToString () =
      let menuToString' =
        function
        | (k, nil) -> ""
        | (k, (Splitting (O))::M) ->
            (((menuToString' ((k + 1), M)) ^ "\n") ^ (format k)) ^
              (Splitting.menu O)
        | (k, (Filling (O))::M) ->
            (((menuToString' ((k + 1), M)) ^ "\n") ^ (format k)) ^
              (Filling.menu O)
        | (k, (Recursion (O))::M) ->
            (((menuToString' ((k + 1), M)) ^ "\n") ^ (format k)) ^
              (Recursion.menu O) in
      match !Menu with
      | NONE -> raise (Error "Menu is empty")
      | SOME (M) -> menuToString' (1, M)
    let rec makeConDec (State (name, Prefix (g, M, B), V)) =
      let makeConDec' =
        function
        | (I.Null, V, k) -> I.ConDec (name, NONE, k, I.Normal, V, I.Type)
        | (Decl (g, D), V, k) ->
            makeConDec' (g, (I.Pi ((D, I.Maybe), V)), (k + 1)) in
      makeConDec' (g, V, 0)
    let rec makeSignature =
      function
      | nil -> M.SgnEmpty
      | (S)::SL -> M.ConDec ((makeConDec S), (makeSignature SL))
    let rec extract () =
      if empty ()
      then makeSignature (collectSolved ())
      else (print "[Error: Proof not completed yet]\n"; M.SgnEmpty)
    let rec show () = print ((MetaPrint.sgnToString (extract ())) ^ "\n")
    let rec printMenu () =
      if empty ()
      then (show (); print "[QED]\n")
      else
        (let S = current () in
         print "\n";
         print (MetaPrint.stateToString S);
         print "\nSelect from the following menu:\n";
         print (menuToString ());
         print "\n")
    let rec contains =
      function
      | (nil, _) -> true__
      | (x::L, L') ->
          (List.exists (function | x' -> x = x') L') && (contains (L, L'))
    let rec equiv (L1, L2) = (contains (L1, L2)) && (contains (L2, L1))
    let rec init' (k, (c::_ as cL)) =
      let _ = MetaGlobal.maxFill := k in
      let _ = reset () in
      let cL' = try Order.closure c with | Error _ -> cL in
      if equiv (cL, cL')
      then map (function | S -> insert S) (Init.init cL)
      else
        raise
          (Error
             (("Theorem by simultaneous induction not correctly stated:" ^
                 "\n            expected: ")
                ^ (cLToString cL')))
    let rec init (k, nL) =
      let cids =
        function
        | nil -> nil
        | name::nL ->
            (match Names.stringToQid name with
             | NONE ->
                 raise (Error ("Malformed qualified identifier " ^ name))
             | SOME qid ->
                 (match Names.constLookup qid with
                  | NONE ->
                      raise
                        (Error
                           (((^) "Type family " Names.qidToString qid) ^
                              " not defined"))
                  | SOME cid -> cid :: (cids nL))) in
      try init' (k, (cids nL)); menu (); printMenu ()
      with | Error s -> abort ("Splitting Error: " ^ s)
      | Error s -> abort ("Filling Error: " ^ s)
      | Error s -> abort ("Recursion Error: " ^ s)
      | Error s -> abort ("Mpi Error: " ^ s)
    let rec select k =
      let select' =
        function
        | (k, nil) -> abort "No such menu item"
        | (1, (Splitting (O))::_) ->
            let S' = Timers.time Timers.splitting Splitting.apply O in
            let _ = pushHistory () in
            let _ = delete () in
            let _ = map insert S' in (menu (); printMenu ())
        | (1, (Recursion (O))::_) ->
            let S' = Timers.time Timers.recursion Recursion.apply O in
            let _ = pushHistory () in
            let _ = delete () in let _ = insert S' in (menu (); printMenu ())
        | (1, (Filling (O))::_) ->
            let _ =
              match Timers.time Timers.filling Filling.apply O with
              | nil -> abort "Filling unsuccessful: no object found"
              | (S)::_ -> (delete (); insert S; pushHistory ()) in
            (menu (); printMenu ())
        | (k, _::M) -> select' ((k - 1), M) in
      try
        match !Menu with
        | NONE -> raise (Error "No menu defined")
        | SOME (M) -> select' (k, M)
      with | Error s -> abort ("Splitting Error: " ^ s)
      | Error s -> abort ("Filling Error: " ^ s)
      | Error s -> abort ("Recursion Error: " ^ s)
      | Error s -> abort ("Mpi Error: " ^ s)
    let rec lemma name =
      if empty ()
      then raise (Error "Nothing to prove")
      else
        (let S = current () in
         let S' =
           try
             Lemma.apply
               (S,
                 (valOf (Names.constLookup (valOf (Names.stringToQid name)))))
           with | Error s -> abort ("Splitting Error: " ^ s)
           | Error s -> abort ("Filling Error: " ^ s)
           | Error s -> abort ("Recursion Error: " ^ s)
           | Error s -> abort ("Mpi Error: " ^ s) in
         let _ = pushHistory () in
         let _ = delete () in let _ = insert S' in menu (); printMenu ())
    let rec solve () =
      if empty ()
      then raise (Error "Nothing to prove")
      else
        (let S = current () in
         let (Open', Solved') =
           try Strategy.run [S]
           with | Error s -> abort ("Splitting Error: " ^ s)
           | Error s -> abort ("Filling Error: " ^ s)
           | Error s -> abort ("Recursion Error: " ^ s)
           | Error s -> abort ("Mpi Error: " ^ s) in
         let _ = pushHistory () in
         let _ = delete () in
         let _ = map insertOpen Open' in
         let _ = map insertSolved Solved' in menu (); printMenu ())
    let rec auto () =
      let (Open', Solved') =
        try Strategy.run (collectOpen ())
        with | Error s -> abort ("Splitting Error: " ^ s)
        | Error s -> abort ("Filling Error: " ^ s)
        | Error s -> abort ("Recursion Error: " ^ s)
        | Error s -> abort ("Mpi Error: " ^ s) in
      let _ = pushHistory () in
      let _ = initOpen () in
      let _ = map insertOpen Open' in
      let _ = map insertSolved Solved' in menu (); printMenu ()
    let rec next () = nextOpen (); menu (); printMenu ()
    let rec undo () = popHistory (); menu (); printMenu ()
    let ((init)(* if no termination ordering given! *)) =
      init
    let select = select
    let print = printMenu
    let next = next
    let lemma = lemma
    let reset = reset
    let solve = solve
    let auto = auto
    let extract = extract
    let show = show
    let undo = undo
  end ;;
