
module type MTPROVER  =
  sig
    module StateSyn : STATESYN
    exception Error of string 
    val init : FunSyn.__For -> StateSyn.__Order -> unit
  end;;




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
    let (openStates : S.__State list ref) = ref nil
    let (solvedStates : S.__State list ref) = ref nil
    let rec transformOrder' __0__ __1__ =
      match (__0__, __1__) with
      | (__G, Arg k) ->
          let k' = ((I.ctxLength __G) - k) + 1 in
          let Dec (_, __V) = I.ctxDec (__G, k') in
          S.Arg (((I.Root ((I.BVar k'), I.Nil)), I.id), (__V, I.id))
      | (__G, Lex (__Os)) ->
          S.Lex (map (fun (__O) -> transformOrder' (__G, __O)) __Os)
      | (__G, Simul (__Os)) ->
          S.Simul (map (fun (__O) -> transformOrder' (__G, __O)) __Os)
    let rec transformOrder __2__ __3__ __4__ =
      match (__2__, __3__, __4__) with
      | (__G, All (Prim (__D), __F), __Os) ->
          S.All (__D, (transformOrder ((I.Decl (__G, __D)), __F, __Os)))
      | (__G, And (__F1, __F2), (__O)::__Os) ->
          S.And
            ((transformOrder (__G, __F1, [__O])),
              (transformOrder (__G, __F2, __Os)))
      | (__G, Ex _, (__O)::[]) -> transformOrder' (__G, __O)
      | (__G, F.True, (__O)::[]) -> transformOrder' (__G, __O)
    let rec select c = try Order.selLookup c with | _ -> Order.Lex []
    let rec error s = raise (Error s)
    let rec reset () = openStates := nil; solvedStates := nil
    let rec contains __5__ __6__ =
      match (__5__, __6__) with
      | (nil, _) -> true
      | (x::__L, __L') ->
          (List.exists (fun x' -> x = x') __L') && (contains (__L, __L'))
    let rec equiv (__L1) (__L2) =
      (contains (__L1, __L2)) && (contains (__L2, __L1))
    let rec insertState (__S) = (openStates := __S) :: (!openStates)
    let rec cLToString =
      function
      | nil -> ""
      | c::nil -> I.conDecName (I.sgnLookup c)
      | c::__L -> ((I.conDecName (I.sgnLookup c)) ^ ", ") ^ (cLToString __L)
    let rec init k (c::_ as cL) =
      let _ = MTPGlobal.maxFill := k in
      let _ = reset () in
      let cL' = try Order.closure c with | Error _ -> cL in
      let __F = RelFun.convertFor cL in
      let __O = transformOrder (I.Null, __F, (map select cL)) in
      ((if equiv (cL, cL')
        then
          List.app (fun (__S) -> insertState __S) (MTPInit.init (__F, __O))
        else
          raise
            (Error
               (("Theorem by simultaneous induction not correctly stated:" ^
                   "\n            expected: ")
                  ^ (cLToString cL'))))
        (* if no termination ordering given! *))
    let rec auto () =
      let (Open, solvedStates') =
        try MTPStrategy.run (!openStates)
        with | Error s -> error ("Splitting Error: " ^ s)
        | Error s -> error ("Filling Error: " ^ s)
        | Error s -> error ("Recursion Error: " ^ s)
        | Filling.TimeOut ->
            error "A proof could not be found -- Exceeding Time Limit\n" in
      let _ = openStates := Open in
      let _ = (solvedStates := (!solvedStates)) @ solvedStates' in
      if (List.length (!openStates)) > 0
      then raise (Error "A proof could not be found")
      else ()
    let rec print () = ()
    let rec install _ = ()
    let init = init
    let auto = auto
    let print = print
    let install = install
  end 
module CombiProver(CombiProver:sig
                                 module MTPGlobal : MTPGLOBAL
                                 module ProverOld : PROVER
                                 module ProverNew : PROVER
                               end) : PROVER =
  struct
    exception Error of string 
    let rec he f =
      try f () with | Error s -> raise (Error s) | Error s -> raise (Error s)
    let rec init (Args) =
      he
        (fun () ->
           match !MTPGlobal.prover with
           | MTPGlobal.New -> ProverNew.init Args
           | MTPGlobal.Old -> ProverOld.init Args)
    let rec auto (Args) =
      he
        (fun () ->
           match !MTPGlobal.prover with
           | MTPGlobal.New -> ProverNew.auto Args
           | MTPGlobal.Old -> ProverOld.auto Args)
    let rec print (Args) =
      he
        (fun () ->
           match !MTPGlobal.prover with
           | MTPGlobal.New -> ProverNew.print Args
           | MTPGlobal.Old -> ProverOld.print Args)
    let rec install (Args) =
      he
        (fun () ->
           match !MTPGlobal.prover with
           | MTPGlobal.New -> ProverNew.install Args
           | MTPGlobal.Old -> ProverOld.install Args)
    let init = init
    let auto = auto
    let print = print
    let install = install
  end ;;
