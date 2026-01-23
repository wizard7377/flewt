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
    val extract : unit -> MetaSyn.sgn_
    val show : unit -> unit
    val undo : unit -> unit
  end


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
    type menuItem_ =
      | Filling of Filling.operator 
      | Recursion of Recursion.operator 
      | Splitting of Splitting.operator 
    let ((Open) : MetaSyn.state_ Ring.ring ref) = ref (Ring.init [])
    let ((Solved) : MetaSyn.state_ Ring.ring ref) = ref (Ring.init [])
    let ((History) :
      (MetaSyn.state_ Ring.ring * MetaSyn.state_ Ring.ring) list ref) =
      ref []
    let ((Menu) : menuItem_ list option ref) = ref None
    let rec initOpen () = (:=) Open Ring.init []
    let rec initSolved () = (:=) Solved Ring.init []
    let rec empty () = Ring.empty !Open
    let rec current () = Ring.current !Open
    let rec delete () = (:=) Open Ring.delete !Open
    let rec insertOpen (s_) = (:=) Open Ring.insert (!Open, s_)
    let rec insertSolved (s_) = (:=) Solved Ring.insert (!Solved, s_)
    let rec insert (s_) =
      if Qed.subgoal s_
      then
        begin (begin insertSolved s_;
               print (MetaPrint.stateToString s_);
               print "\n[Subgoal finished]\n";
               print "\n" end) end
      else begin insertOpen s_ end
let rec collectOpen () = Ring.foldr (::) [] !Open
let rec collectSolved () = Ring.foldr (::) [] !Solved
let rec nextOpen () = (:=) Open Ring.next !Open
let rec pushHistory () = (History := (!Open, !Solved)) :: !History
let rec popHistory () =
  begin match !History with
  | [] -> raise (Error "History stack empty")
  | (Open', Solved')::History' ->
      (begin History := History'; Open := Open'; Solved := Solved' end) end
let rec abort s = begin print ("* " ^ s); raise (Error s) end
let rec reset () =
  begin initOpen (); initSolved (); History := []; Menu := None end
let rec cLToString =
  begin function
  | [] -> ""
  | c::[] -> I.conDecName (I.sgnLookup c)
  | c::l_ -> ((I.conDecName (I.sgnLookup c)) ^ ", ") ^ (cLToString l_) end
let rec SplittingToMenu =
  begin function
  | ([], a_) -> a_
  | ((o_)::l_, a_) -> SplittingToMenu (l_, ((Splitting o_) :: a_)) end
let rec FillingToMenu =
  begin function
  | ([], a_) -> a_
  | ((o_)::l_, a_) -> FillingToMenu (l_, ((Filling o_) :: a_)) end
let rec RecursionToMenu =
  begin function
  | ([], a_) -> a_
  | ((o_)::l_, a_) -> RecursionToMenu (l_, ((Recursion o_) :: a_)) end
let rec menu () = if empty () then begin Menu := None end
  else begin
    (let s_ = current () in
     let SplitO = Splitting.expand s_ in
     let RecO = Recursion.expandEager s_ in
     let (FillO, FillC) = Filling.expand s_ in
     (:=) Menu Some
       (FillingToMenu
          ([FillC],
            (FillingToMenu
               (FillO,
                 (RecursionToMenu (RecO, (SplittingToMenu (SplitO, []))))))))) end
let rec format k = if k < 10 then begin (Int.toString k) ^ ".  " end
  else begin (Int.toString k) ^ ". " end
let rec menuToString () =
  let rec menuToString' =
    begin function
    | (k, []) -> ""
    | (k, (Splitting (o_))::m_) ->
        (((menuToString' ((k + 1), m_)) ^ "\n") ^ (format k)) ^
          (Splitting.menu o_)
    | (k, (Filling (o_))::m_) ->
        (((menuToString' ((k + 1), m_)) ^ "\n") ^ (format k)) ^
          (Filling.menu o_)
    | (k, (Recursion (o_))::m_) ->
        (((menuToString' ((k + 1), m_)) ^ "\n") ^ (format k)) ^
          (Recursion.menu o_) end in
begin match !Menu with
| None -> raise (Error "Menu is empty")
| Some (m_) -> menuToString' (1, m_) end
let rec makeConDec (State (name, Prefix (g_, m_, b_), v_)) =
  let rec makeConDec' =
    begin function
    | (I.Null, v_, k) -> I.ConDec (name, None, k, I.Normal, v_, I.Type)
    | (Decl (g_, d_), v_, k) ->
        makeConDec' (g_, (I.Pi ((d_, I.Maybe), v_)), (k + 1)) end in
makeConDec' (g_, v_, 0)
let rec makeSignature =
  begin function
  | [] -> M.SgnEmpty
  | (s_)::SL -> M.ConDec ((makeConDec s_), (makeSignature SL)) end
let rec extract () =
  if empty () then begin makeSignature (collectSolved ()) end
  else begin
    (begin print "[Error: Proof not completed yet]\n"; M.SgnEmpty end) end
let rec show () = print ((MetaPrint.sgnToString (extract ())) ^ "\n")
let rec printMenu () =
  if empty () then begin (begin show (); print "[QED]\n" end) end
  else begin
    (let s_ = current () in
     begin print "\n";
     print (MetaPrint.stateToString s_);
     print "\nSelect from the following menu:\n";
     print (menuToString ());
     print "\n" end) end
let rec contains =
  begin function
  | ([], _) -> true
  | (x::l_, l'_) -> (List.exists (begin function | x' -> x = x' end) l'_) &&
      (contains (l_, l'_)) end
let rec equiv (l1_, l2_) = (contains (l1_, l2_)) && (contains (l2_, l1_))
let rec init' (k, (c::_ as cL)) =
  let _ = MetaGlobal.maxFill := k in
  let _ = reset () in
  let cL' = begin try Order.closure c with | Error _ -> cL end in
  ((if equiv (cL, cL')
    then begin map (begin function | s_ -> insert s_ end) (Init.init cL) end
    else begin
      raise
        (Error
           (("Theorem by simultaneous induction not correctly stated:" ^
               "\n            expected: ")
              ^ (cLToString cL'))) end)
  (* if no termination ordering given! *))
let rec init (k, nL) =
  let rec cids =
    begin function
    | [] -> []
    | name::nL ->
        (begin match Names.stringToQid name with
         | None -> raise (Error ("Malformed qualified identifier " ^ name))
         | Some qid ->
             (begin match Names.constLookup qid with
              | None ->
                  raise
                    (Error
                       (((^) "Type family " Names.qidToString qid) ^
                          " not defined"))
              | Some cid -> cid :: (cids nL) end) end) end in
begin try begin init' (k, (cids nL)); menu (); printMenu () end
with | Error s -> abort ("Splitting Error: " ^ s)
| Error s -> abort ("Filling Error: " ^ s)
| Error s -> abort ("Recursion Error: " ^ s)
| Error s -> abort ("Mpi Error: " ^ s) end
let rec select k =
  let rec select' =
    begin function
    | (k, []) -> abort "No such menu item"
    | (1, (Splitting (o_))::_) ->
        let s'_ = Timers.time Timers.splitting Splitting.apply o_ in
        let _ = pushHistory () in
        let _ = delete () in
        let _ = map insert s'_ in (begin menu (); printMenu () end)
    | (1, (Recursion (o_))::_) ->
        let s'_ = Timers.time Timers.recursion Recursion.apply o_ in
        let _ = pushHistory () in
        let _ = delete () in
        let _ = insert s'_ in (begin menu (); printMenu () end)
    | (1, (Filling (o_))::_) ->
        let _ =
          begin match Timers.time Timers.filling Filling.apply o_ with
          | [] -> abort "Filling unsuccessful: no object found"
          | (s_)::_ -> (begin delete (); insert s_; pushHistory () end) end in
  (begin menu (); printMenu () end)
| (k, _::m_) -> select' ((k - 1), m_) end in
begin try
      begin match !Menu with
      | None -> raise (Error "No menu defined")
      | Some (m_) -> select' (k, m_) end
with | Error s -> abort ("Splitting Error: " ^ s)
| Error s -> abort ("Filling Error: " ^ s)
| Error s -> abort ("Recursion Error: " ^ s)
| Error s -> abort ("Mpi Error: " ^ s) end
let rec lemma name =
  if empty () then begin raise (Error "Nothing to prove") end
  else begin
    (let s_ = current () in
     let s'_ =
       begin try
               Lemma.apply
                 (s_,
                   (valOf
                      (Names.constLookup (valOf (Names.stringToQid name)))))
       with | Error s -> abort ("Splitting Error: " ^ s)
       | Error s -> abort ("Filling Error: " ^ s)
       | Error s -> abort ("Recursion Error: " ^ s)
       | Error s -> abort ("Mpi Error: " ^ s) end in
     let _ = pushHistory () in
     let _ = delete () in
     let _ = insert s'_ in begin menu (); printMenu () end) end
let rec solve () =
  if empty () then begin raise (Error "Nothing to prove") end
  else begin
    (let s_ = current () in
     let (Open', Solved') =
       begin try Strategy.run [s_]
       with | Error s -> abort ("Splitting Error: " ^ s)
       | Error s -> abort ("Filling Error: " ^ s)
       | Error s -> abort ("Recursion Error: " ^ s)
       | Error s -> abort ("Mpi Error: " ^ s) end in
     let _ = pushHistory () in
     let _ = delete () in
     let _ = map insertOpen Open' in
     let _ = map insertSolved Solved' in begin menu (); printMenu () end) end
let rec auto () =
  let (Open', Solved') =
    begin try Strategy.run (collectOpen ())
    with | Error s -> abort ("Splitting Error: " ^ s)
    | Error s -> abort ("Filling Error: " ^ s)
    | Error s -> abort ("Recursion Error: " ^ s)
    | Error s -> abort ("Mpi Error: " ^ s) end in
let _ = pushHistory () in
let _ = initOpen () in
let _ = map insertOpen Open' in
let _ = map insertSolved Solved' in begin menu (); printMenu () end
let rec next () = begin nextOpen (); menu (); printMenu () end
let rec undo () = begin popHistory (); menu (); printMenu () end
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
let undo = undo end
