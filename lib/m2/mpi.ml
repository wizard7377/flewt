
module type MPI  =
  sig
    module MetaSyn : METASYN
    exception Error of string 
    val init : int -> string list -> unit
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
    let ((Menu) : __MenuItem list option ref) = ref NONE
    let rec initOpen () = (:=) Open Ring.init []
    let rec initSolved () = (:=) Solved Ring.init []
    let rec empty () = Ring.empty (!Open)
    let rec current () = Ring.current (!Open)
    let rec delete () = (:=) Open Ring.delete (!Open)
    let rec insertOpen (__S) = (:=) Open Ring.insert ((!Open), __S)
    let rec insertSolved (__S) = (:=) Solved Ring.insert ((!Solved), __S)
    let rec insert (__S) =
      if Qed.subgoal __S
      then
        (insertSolved __S;
         print (MetaPrint.stateToString __S);
         print "\n[Subgoal finished]\n";
         print "\n")
      else insertOpen __S
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
      | c::__L -> ((I.conDecName (I.sgnLookup c)) ^ ", ") ^ (cLToString __L)
    let rec SplittingToMenu __0__ __1__ =
      match (__0__, __1__) with
      | (nil, __A) -> __A
      | ((__O)::__L, __A) -> SplittingToMenu (__L, ((Splitting __O) :: __A))
    let rec FillingToMenu __2__ __3__ =
      match (__2__, __3__) with
      | (nil, __A) -> __A
      | ((__O)::__L, __A) -> FillingToMenu (__L, ((Filling __O) :: __A))
    let rec RecursionToMenu __4__ __5__ =
      match (__4__, __5__) with
      | (nil, __A) -> __A
      | ((__O)::__L, __A) -> RecursionToMenu (__L, ((Recursion __O) :: __A))
    let rec menu () =
      if empty ()
      then Menu := NONE
      else
        (let __S = current () in
         let SplitO = Splitting.expand __S in
         let RecO = Recursion.expandEager __S in
         let (FillO, FillC) = Filling.expand __S in
         (:=) Menu Some
           (FillingToMenu
              ([FillC],
                (FillingToMenu
                   (FillO,
                     (RecursionToMenu (RecO, (SplittingToMenu (SplitO, nil)))))))))
    let rec format k =
      if k < 10 then (Int.toString k) ^ ".  " else (Int.toString k) ^ ". "
    let rec menuToString () =
      let rec menuToString' __6__ __7__ =
        match (__6__, __7__) with
        | (k, nil) -> ""
        | (k, (Splitting (__O))::__M) ->
            (((menuToString' ((k + 1), __M)) ^ "\n") ^ (format k)) ^
              (Splitting.menu __O)
        | (k, (Filling (__O))::__M) ->
            (((menuToString' ((k + 1), __M)) ^ "\n") ^ (format k)) ^
              (Filling.menu __O)
        | (k, (Recursion (__O))::__M) ->
            (((menuToString' ((k + 1), __M)) ^ "\n") ^ (format k)) ^
              (Recursion.menu __O) in
      match !Menu with
      | NONE -> raise (Error "Menu is empty")
      | Some (__M) -> menuToString' (1, __M)
    let rec makeConDec (State (name, Prefix (__G, __M, __B), __V)) =
      let rec makeConDec' __8__ __9__ __10__ =
        match (__8__, __9__, __10__) with
        | (I.Null, __V, k) -> I.ConDec (name, NONE, k, I.Normal, __V, I.Type)
        | (Decl (__G, __D), __V, k) ->
            makeConDec' (__G, (I.Pi ((__D, I.Maybe), __V)), (k + 1)) in
      makeConDec' (__G, __V, 0)
    let rec makeSignature =
      function
      | nil -> M.SgnEmpty
      | (__S)::SL -> M.ConDec ((makeConDec __S), (makeSignature SL))
    let rec extract () =
      if empty ()
      then makeSignature (collectSolved ())
      else (print "[Error: Proof not completed yet]\n"; M.SgnEmpty)
    let rec show () = print ((MetaPrint.sgnToString (extract ())) ^ "\n")
    let rec printMenu () =
      if empty ()
      then (show (); print "[QED]\n")
      else
        (let __S = current () in
         print "\n";
         print (MetaPrint.stateToString __S);
         print "\nSelect from the following menu:\n";
         print (menuToString ());
         print "\n")
    let rec contains __11__ __12__ =
      match (__11__, __12__) with
      | (nil, _) -> true__
      | (x::__L, __L') ->
          (List.exists (fun x' -> x = x') __L') && (contains (__L, __L'))
    let rec equiv (__L1) (__L2) =
      (contains (__L1, __L2)) && (contains (__L2, __L1))
    let rec init' k (c::_ as cL) =
      let _ = MetaGlobal.maxFill := k in
      let _ = reset () in
      let cL' = try Order.closure c with | Error _ -> cL in
      ((if equiv (cL, cL')
        then map (fun (__S) -> insert __S) (Init.init cL)
        else
          raise
            (Error
               (("Theorem by simultaneous induction not correctly stated:" ^
                   "\n            expected: ")
                  ^ (cLToString cL'))))
        (* if no termination ordering given! *))
    let rec init k nL =
      let rec cids =
        function
        | nil -> nil
        | name::nL ->
            (match Names.stringToQid name with
             | NONE ->
                 raise (Error ("Malformed qualified identifier " ^ name))
             | Some qid ->
                 (match Names.constLookup qid with
                  | NONE ->
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
      let rec select' __13__ __14__ =
        match (__13__, __14__) with
        | (k, nil) -> abort "No such menu item"
        | (1, (Splitting (__O))::_) ->
            let __S' = Timers.time Timers.splitting Splitting.apply __O in
            let _ = pushHistory () in
            let _ = delete () in
            let _ = map insert __S' in (menu (); printMenu ())
        | (1, (Recursion (__O))::_) ->
            let __S' = Timers.time Timers.recursion Recursion.apply __O in
            let _ = pushHistory () in
            let _ = delete () in
            let _ = insert __S' in (menu (); printMenu ())
        | (1, (Filling (__O))::_) ->
            let _ =
              match Timers.time Timers.filling Filling.apply __O with
              | nil -> abort "Filling unsuccessful: no object found"
              | (__S)::_ -> (delete (); insert __S; pushHistory ()) in
            (menu (); printMenu ())
        | (k, _::__M) -> select' ((k - 1), __M) in
      try
        match !Menu with
        | NONE -> raise (Error "No menu defined")
        | Some (__M) -> select' (k, __M)
      with | Error s -> abort ("Splitting Error: " ^ s)
      | Error s -> abort ("Filling Error: " ^ s)
      | Error s -> abort ("Recursion Error: " ^ s)
      | Error s -> abort ("Mpi Error: " ^ s)
    let rec lemma name =
      if empty ()
      then raise (Error "Nothing to prove")
      else
        (let __S = current () in
         let __S' =
           try
             Lemma.apply
               (__S,
                 (valOf (Names.constLookup (valOf (Names.stringToQid name)))))
           with | Error s -> abort ("Splitting Error: " ^ s)
           | Error s -> abort ("Filling Error: " ^ s)
           | Error s -> abort ("Recursion Error: " ^ s)
           | Error s -> abort ("Mpi Error: " ^ s) in
         let _ = pushHistory () in
         let _ = delete () in let _ = insert __S' in menu (); printMenu ())
    let rec solve () =
      if empty ()
      then raise (Error "Nothing to prove")
      else
        (let __S = current () in
         let (Open', Solved') =
           try Strategy.run [__S]
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
