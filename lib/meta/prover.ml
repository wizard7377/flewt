module type MTPROVER  =
  sig
    module StateSyn : STATESYN
    exception Error of string 
    val init : (FunSyn.for_ * StateSyn.order_) -> unit
  end


module MTProver(MTProver:sig
                           module MTPGlobal : MTPGLOBAL
                           module StateSyn : STATESYN
                           module Order : ORDER
                           module MTPInit : MTPINIT
                           module MTPStrategy : MTPSTRATEGY
                           module RelFun : RELFUN
                         end) : PROVER =
  struct
    exception Error of string 
    module I = IntSyn
    module F = FunSyn
    module S = StateSyn
    let (openStates : S.state_ list ref) = ref []
    let (solvedStates : S.state_ list ref) = ref []
    let rec transformOrder' =
      begin function
      | (g_, Arg k) ->
          let k' = ((I.ctxLength g_) - k) + 1 in
          let Dec (_, v_) = I.ctxDec (g_, k') in
          S.Arg (((I.Root ((I.BVar k'), I.Nil)), I.id), (v_, I.id))
      | (g_, Lex (os_)) ->
          S.Lex (map (begin function | o_ -> transformOrder' (g_, o_) end)
            os_)
      | (g_, Simul (os_)) ->
          S.Simul (map (begin function | o_ -> transformOrder' (g_, o_) end)
            os_) end
let rec transformOrder =
  begin function
  | (g_, All (Prim (d_), f_), os_) ->
      S.All (d_, (transformOrder ((I.Decl (g_, d_)), f_, os_)))
  | (g_, And (f1_, f2_), (o_)::os_) ->
      S.And
        ((transformOrder (g_, f1_, [o_])), (transformOrder (g_, f2_, os_)))
  | (g_, Ex _, (o_)::[]) -> transformOrder' (g_, o_)
  | (g_, F.True, (o_)::[]) -> transformOrder' (g_, o_) end
let rec select c = begin try Order.selLookup c with | _ -> Order.Lex [] end
let rec error s = raise (Error s)
let rec reset () = begin openStates := []; solvedStates := [] end
let rec contains =
  begin function
  | ([], _) -> true
  | (x::l_, l'_) -> (List.exists (begin function | x' -> x = x' end) l'_) &&
      (contains (l_, l'_)) end
let rec equiv (l1_, l2_) = (contains (l1_, l2_)) && (contains (l2_, l1_))
let rec insertState (s_) = (openStates := s_) :: !openStates
let rec cLToString =
  begin function
  | [] -> ""
  | c::[] -> I.conDecName (I.sgnLookup c)
  | c::l_ -> ((I.conDecName (I.sgnLookup c)) ^ ", ") ^ (cLToString l_) end
let rec init (k, (c::_ as cL)) =
  let _ = MTPGlobal.maxFill := k in
  let _ = reset () in
  let cL' = begin try Order.closure c with | Error _ -> cL end in
  let f_ = RelFun.convertFor cL in
  let o_ = transformOrder (I.Null, f_, (map select cL)) in
  ((if equiv (cL, cL')
    then begin List.app (begin function | s_ -> insertState s_ end)
      (MTPInit.init (f_, o_)) end
    else begin
      raise
        (Error
           (("Theorem by simultaneous induction not correctly stated:" ^
               "\n            expected: ")
              ^ (cLToString cL'))) end)
    (* if no termination ordering given! *))
let rec auto () =
  let (Open, solvedStates') =
    begin try MTPStrategy.run !openStates
    with | Error s -> error ("Splitting Error: " ^ s)
    | Error s -> error ("Filling Error: " ^ s)
    | Error s -> error ("Recursion Error: " ^ s)
    | Filling.TimeOut ->
        error "A proof could not be found -- Exceeding Time Limit\n" end in
let _ = openStates := Open in
let _ = (solvedStates := !solvedStates) @ solvedStates' in
if (List.length !openStates) > 0
then begin raise (Error "A proof could not be found") end else begin () end
let rec print () = ()
let rec install _ = ()
let init = init
let auto = auto
let print = print
let install = install end 
module CombiProver(CombiProver:sig
                                 module MTPGlobal : MTPGLOBAL
                                 module ProverOld : PROVER
                                 module ProverNew : PROVER
                               end) : PROVER =
  struct
    exception Error of string 
    let rec he f =
      begin try f ()
      with | Error s -> raise (Error s) | Error s -> raise (Error s) end
    let rec init (Args) =
      he
        (begin function
         | () ->
             (begin match !MTPGlobal.prover with
              | MTPGlobal.New -> ProverNew.init Args
              | MTPGlobal.Old -> ProverOld.init Args end) end)
let rec auto (Args) =
  he
    (begin function
     | () ->
         (begin match !MTPGlobal.prover with
          | MTPGlobal.New -> ProverNew.auto Args
          | MTPGlobal.Old -> ProverOld.auto Args end) end)
let rec print (Args) =
  he
    (begin function
     | () ->
         (begin match !MTPGlobal.prover with
          | MTPGlobal.New -> ProverNew.print Args
          | MTPGlobal.Old -> ProverOld.print Args end) end)
let rec install (Args) =
  he
    (begin function
     | () ->
         (begin match !MTPGlobal.prover with
          | MTPGlobal.New -> ProverNew.install Args
          | MTPGlobal.Old -> ProverOld.install Args end) end)
let init = init
let auto = auto
let print = print
let install = install end
