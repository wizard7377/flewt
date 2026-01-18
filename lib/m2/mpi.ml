
(* Meta Prover Interface *)
(* Author: Carsten Schuermann *)
module type MPI  =
  sig
    module MetaSyn : METASYN
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




(* Meta Prover Interface *)
(* Author: Carsten Schuermann *)
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
                 (*! sharing Names.IntSyn = MetaSyn'.IntSyn !*)
                 module Ring : RING
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
    let ((Menu) : __MenuItem list option ref) = ref None
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
      initOpen (); initSolved (); History := nil; Menu := None
    let rec cLToString =
      function
      | nil -> ""
      | c::nil -> I.conDecName (I.sgnLookup c)
      | c::__l -> ((I.conDecName (I.sgnLookup c)) ^ ", ") ^ (cLToString __l)
    let rec SplittingToMenu =
      function
      | (nil, A) -> A
      | ((O)::__l, A) -> SplittingToMenu (__l, ((Splitting O) :: A))
    let rec FillingToMenu =
      function
      | (nil, A) -> A
      | ((O)::__l, A) -> FillingToMenu (__l, ((Filling O) :: A))
    let rec RecursionToMenu =
      function
      | (nil, A) -> A
      | ((O)::__l, A) -> RecursionToMenu (__l, ((Recursion O) :: A))
    let rec menu () =
      if empty ()
      then Menu := None
      else
        (let S = current () in
         let SplitO = Splitting.expand S in
         let RecO = Recursion.expandEager S in
         let (FillO, FillC) = Filling.expand S in
         (:=) Menu Some
           (FillingToMenu
              ([FillC],
                (FillingToMenu
                   (FillO,
                     (RecursionToMenu (RecO, (SplittingToMenu (SplitO, nil)))))))))
    let rec format k =
      if k < 10 then (Int.toString k) ^ ".  " else (Int.toString k) ^ ". "
    let rec menuToString () =
      let rec menuToString' =
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
      | None -> raise (Error "Menu is empty")
      | Some (M) -> menuToString' (1, M)
    let rec makeConDec (State (name, Prefix (__g, M, B), __v)) =
      let rec makeConDec' =
        function
        | (I.Null, __v, k) -> I.ConDec (name, None, k, I.Normal, __v, I.Type)
        | (Decl (__g, __d), __v, k) ->
            makeConDec' (__g, (I.Pi ((__d, I.Maybe), __v)), (k + 1)) in
      makeConDec' (__g, __v, 0)
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
      | (x::__l, __l') ->
          (List.exists (function | x' -> x = x') __l') && (contains (__l, __l'))
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
      let rec cids =
        function
        | nil -> nil
        | name::nL ->
            (match Names.stringToQid name with
             | None ->
                 raise (Error ("Malformed qualified identifier " ^ name))
             | Some qid ->
                 (match Names.constLookup qid with
                  | None ->
                      raise
                        (Error
                           (((^) "Type family " Names.qidToString qid) ^
                              " not defined"))
                  | Some cid -> cid :: (cids nL))) in
      try init' (k, (cids nL)); menu (); printMenu ()
      with | Error s -> abort ("Splitting Error: " ^ s)
      | Error s -> abort ("Filling Error: " ^ s)
      | Error s -> abort ("Recursion Error: " ^ s)
      | Error s -> abort ("Mpi Error: " ^ s)
    let rec select k =
      let rec select' =
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
        | None -> raise (Error "No menu defined")
        | Some (M) -> select' (k, M)
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
    (* if no termination ordering given! *)
    let init = init
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
