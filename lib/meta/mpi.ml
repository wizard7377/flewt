module type MTPI  =
  sig
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
    val undo : unit -> unit
  end


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
    type menuItem_ =
      | Filling of MTPFilling.operator 
      | Recursion of MTPRecursion.operator 
      | Splitting of MTPSplitting.operator 
      | Inference of Inference.operator 
    let ((Open) : StateSyn.state_ Ring.ring ref) = ref (Ring.init [])
    let ((Solved) : StateSyn.state_ Ring.ring ref) = ref (Ring.init [])
    let ((History) :
      (StateSyn.state_ Ring.ring * StateSyn.state_ Ring.ring) list ref) =
      ref []
    let ((Menu) : menuItem_ list option ref) = ref None
    let rec initOpen () = (:=) Open Ring.init []
    let rec initSolved () = (:=) Solved Ring.init []
    let rec empty () = Ring.empty !Open
    let rec current () = Ring.current !Open
    let rec delete () = (:=) Open Ring.delete !Open
    let rec insertOpen (s_) = (:=) Open Ring.insert (!Open, s_)
    let rec insertSolved (s_) = (:=) Solved Ring.insert (!Solved, s_)
    let rec insert (s_) = insertOpen s_
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
let rec printFillResult (_, p_) =
  let rec formatTuple (g_, p_) =
    let rec formatTuple' =
      begin function
      | F.Unit -> []
      | Inx (m_, F.Unit) -> [Print.formatExp (g_, m_)]
      | Inx (m_, p'_) ->
          (::) (((::) (Print.formatExp (g_, m_)) Fmt.String ",") :: Fmt.Break)
            formatTuple' p'_ end in
  begin match p_ with
  | Inx (_, F.Unit) -> Fmt.Hbox (formatTuple' p_)
  | _ ->
      Fmt.HVbox0 1 1 1
        ((Fmt.String "(") :: ((formatTuple' p_) @ [Fmt.String ")"])) end in
let State (n, (g_, b_), (IH, OH), d, o_, h_, f_) = current () in
TextIO.print
  (("Filling successful with proof term:\n" ^
      (Formatter.makestring_fmt (formatTuple (g_, p_))))
     ^ "\n")
let rec SplittingToMenu =
  begin function
  | ([], a_) -> a_
  | ((o_)::l_, a_) -> SplittingToMenu (l_, ((Splitting o_) :: a_)) end
let rec FillingToMenu (o_, a_) = (Filling o_) :: a_
let rec RecursionToMenu (o_, a_) = (Recursion o_) :: a_
let rec InferenceToMenu (o_, a_) = (Inference o_) :: a_
let rec menu () = if empty () then begin Menu := None end
  else begin
    (let s_ = current () in
     let SplitO = MTPSplitting.expand s_ in
     let InfO = Inference.expand s_ in
     let RecO = MTPRecursion.expand s_ in
     let FillO = MTPFilling.expand s_ in
     (:=) Menu Some
       (FillingToMenu
          (FillO,
            (RecursionToMenu
               (RecO,
                 (InferenceToMenu (InfO, (SplittingToMenu (SplitO, []))))))))) end
let rec format k = if k < 10 then begin (Int.toString k) ^ ".  " end
  else begin (Int.toString k) ^ ". " end
let rec menuToString () =
  let rec menuToString' =
    begin function
    | (k, [], (None, _)) -> ((Some k), "")
    | (k, [], ((Some _ as kopt'), _)) -> (kopt', "")
    | (k, (Splitting (o_))::m_, ((None, None) as kOopt')) ->
        let kOopt'' =
          if MTPSplitting.applicable o_ then begin ((Some k), (Some o_)) end
          else begin kOopt' end in
  let ((Some k'' as kopt), s) = menuToString' ((k + 1), m_, kOopt'') in
  (kopt,
    (if k = k''
     then begin ((s ^ "\n* ") ^ (format k)) ^ (MTPSplitting.menu o_) end
    else begin ((s ^ "\n  ") ^ (format k)) ^ (MTPSplitting.menu o_) end))
  | (k, (Splitting (o_))::m_, ((Some k', Some (o'_)) as kOopt')) ->
      let kOopt'' =
        if MTPSplitting.applicable o_
        then
          begin begin match MTPSplitting.compare (o_, o'_) with
                | LESS -> ((Some k), (Some o_))
                | _ -> kOopt' end end
        else begin kOopt' end in
let ((Some k'' as kopt), s) = menuToString' ((k + 1), m_, kOopt'') in
(kopt,
(if k = k''
 then begin ((s ^ "\n* ") ^ (format k)) ^ (MTPSplitting.menu o_) end
else begin ((s ^ "\n  ") ^ (format k)) ^ (MTPSplitting.menu o_) end))
| (k, (Filling (o_))::m_, kOopt) ->
    let (kopt, s) = menuToString' ((k + 1), m_, kOopt) in
    (kopt, (((s ^ "\n  ") ^ (format k)) ^ (MTPFilling.menu o_)))
| (k, (Recursion (o_))::m_, kOopt) ->
    let (kopt, s) = menuToString' ((k + 1), m_, kOopt) in
    (kopt, (((s ^ "\n  ") ^ (format k)) ^ (MTPRecursion.menu o_)))
| (k, (Inference (o_))::m_, kOopt) ->
    let (kopt, s) = menuToString' ((k + 1), m_, kOopt) in
    (kopt, (((s ^ "\n  ") ^ (format k)) ^ (Inference.menu o_))) end in
begin match !Menu with
| None -> raise (Error "Menu is empty")
| Some (m_) -> let (kopt, s) = menuToString' (1, m_, (None, None)) in s end
let rec printMenu () =
  if empty ()
  then
    begin (begin print "[QED]\n";
           print
             (("Statistics: required Twelf.Prover.maxFill := " ^
                 (Int.toString !MTPData.maxFill))
                ^ "\n") end) end
  else begin
    (let s_ = current () in
     let _ = if !Global.doubleCheck then begin FunTypeCheck.isState s_ end
       else begin () end in
  begin print "\n";
  print (MTPrint.stateToString s_);
  print "\nSelect from the following menu:\n";
  print (menuToString ());
  print "\n" end) end
let rec contains =
  begin function
  | ([], _) -> true
  | (x::l_, l'_) -> (List.exists (begin function | x' -> x = x' end) l'_) &&
      (contains (l_, l'_)) end
let rec equiv (l1_, l2_) = (contains (l1_, l2_)) && (contains (l2_, l1_))
let rec transformOrder' =
  begin function
  | (g_, Arg k) ->
      let k' = ((I.ctxLength g_) - k) + 1 in
      let Dec (_, v_) = I.ctxDec (g_, k') in
      S.Arg (((I.Root ((I.BVar k'), I.Nil)), I.id), (v_, I.id))
  | (g_, Lex (os_)) ->
      S.Lex (map (begin function | o_ -> transformOrder' (g_, o_) end) os_)
  | (g_, Simul (os_)) ->
      S.Simul (map (begin function | o_ -> transformOrder' (g_, o_) end) os_) end
let rec transformOrder =
  begin function
  | (g_, All (Prim (d_), f_), os_) ->
      S.All (d_, (transformOrder ((I.Decl (g_, d_)), f_, os_)))
  | (g_, And (f1_, f2_), (o_)::os_) ->
      S.And
        ((transformOrder (g_, f1_, [o_])), (transformOrder (g_, f2_, os_)))
  | (g_, Ex _, (o_)::[]) -> transformOrder' (g_, o_) end
let rec select c = begin try Order.selLookup c with | _ -> Order.Lex [] end
let rec init (k, names) =
  let cL =
    map
      (begin function
       | x -> valOf (Names.constLookup (valOf (Names.stringToQid x))) end)
    names in
let _ = MTPGlobal.maxFill := k in
let _ = reset () in
let f_ = RelFun.convertFor cL in
let o_ = transformOrder (I.Null, f_, (map select cL)) in
let Slist = MTPInit.init (f_, o_) in
let _ = if (List.length Slist) = 0 then begin raise Domain end
  else begin () end in
begin try
        begin map (begin function | s_ -> insert (MTPrint.nameState s_) end)
        Slist;
        menu ();
        printMenu () end
  with | Error s -> abort ("MTPSplitting. Error: " ^ s)
  | Error s -> abort ("Filling Error: " ^ s)
  | Error s -> abort ("Recursion Error: " ^ s)
  | Error s -> abort ("Inference Error: " ^ s)
  | Error s -> abort ("Mpi Error: " ^ s) end
let rec select k =
  let rec select' =
    begin function
    | (k, []) -> abort "No such menu item"
    | (1, (Splitting (o_))::_) ->
        let s'_ = Timers.time Timers.splitting MTPSplitting.apply o_ in
        let _ = pushHistory () in
        let _ = delete () in
        let _ =
          map (begin function | s_ -> insert (MTPrint.nameState s_) end) s'_ in
        (begin menu (); printMenu () end)
    | (1, (Recursion (o_))::_) ->
        let s'_ = Timers.time Timers.recursion MTPRecursion.apply o_ in
        let _ = pushHistory () in
        let _ = delete () in
        let _ = insert (MTPrint.nameState s'_) in
        (begin menu (); printMenu () end)
  | (1, (Inference (o_))::_) ->
      let s'_ = Timers.time Timers.recursion Inference.apply o_ in
      let _ = pushHistory () in
      let _ = delete () in
      let _ = insert (MTPrint.nameState s'_) in
      (begin menu (); printMenu () end)
  | (1, (Filling (o_))::_) ->
      let p_ =
        begin try Timers.time Timers.filling MTPFilling.apply o_
        with | Error _ -> abort "Filling unsuccessful: no object found" end in
    let _ = printFillResult p_ in
    let _ = delete () in
    let _ = print "\n[Subgoal finished]\n" in
    let _ = print "\n" in (begin menu (); printMenu () end)
| (k, _::m_) -> select' ((k - 1), m_) end in
begin try
      begin match !Menu with
      | None -> raise (Error "No menu defined")
      | Some (m_) -> select' (k, m_) end
with | Error s -> abort ("MTPSplitting. Error: " ^ s)
| Error s -> abort ("Filling Error: " ^ s)
| Error s -> abort ("Recursion Error: " ^ s)
| Error s -> abort ("Inference Errror: " ^ s)
| Error s -> abort ("Mpi Error: " ^ s) end
let rec solve () =
  if empty () then begin raise (Error "Nothing to prove") end
  else begin
    (let s_ = current () in
     let (Open', Solved') =
       begin try MTPStrategy.run [s_]
       with | Error s -> abort ("MTPSplitting. Error: " ^ s)
       | Error s -> abort ("Filling Error: " ^ s)
       | Error s -> abort ("Recursion Error: " ^ s)
       | Error s -> abort ("Inference Errror: " ^ s)
       | Error s -> abort ("Mpi Error: " ^ s) end in
     let _ = pushHistory () in
     let _ = delete () in
     let _ = map insertOpen Open' in
     let _ = map insertSolved Solved' in begin menu (); printMenu () end) end
let rec check () =
  if empty () then begin raise (Error "Nothing to check") end
  else begin (let s_ = current () in FunTypeCheck.isState s_) end
let rec auto () =
  let (Open', Solved') =
    begin try MTPStrategy.run (collectOpen ())
    with | Error s -> abort ("MTPSplitting. Error: " ^ s)
    | Error s -> abort ("Filling Error: " ^ s)
    | Error s -> abort ("Recursion Error: " ^ s)
    | Error s -> abort ("Inference Errror: " ^ s)
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
let reset = reset
let solve = solve
let auto = auto
let check = check
let undo = undo end
