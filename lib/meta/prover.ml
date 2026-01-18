
(* Meta Prover Version 1.3 *)
(* Author: Carsten Schuermann *)
module type MTPROVER  =
  sig
    (*! structure FunSyn : FUNSYN !*)
    module StateSyn : STATESYN
    exception Error of string 
    val init : (FunSyn.__For * StateSyn.__Order) -> unit
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
    let rec transformOrder' =
      function
      | (G, Arg k) ->
          let k' = ((I.ctxLength G) - k) + 1 in
          let Dec (_, V) = I.ctxDec (G, k') in
          S.Arg (((I.Root ((I.BVar k'), I.Nil)), I.id), (V, I.id))
      | (G, Lex (Os)) ->
          S.Lex (map (function | O -> transformOrder' (G, O)) Os)
      | (G, Simul (Os)) ->
          S.Simul (map (function | O -> transformOrder' (G, O)) Os)
    let rec transformOrder =
      function
      | (G, All (Prim (D), F), Os) ->
          S.All (D, (transformOrder ((I.Decl (G, D)), F, Os)))
      | (G, And (F1, F2), (O)::Os) ->
          S.And ((transformOrder (G, F1, [O])), (transformOrder (G, F2, Os)))
      | (G, Ex _, (O)::[]) -> transformOrder' (G, O)
      | (G, F.True, (O)::[]) -> transformOrder' (G, O)
    let rec select c = try Order.selLookup c with | _ -> Order.Lex []
    let rec error s = raise (Error s)
    let rec reset () = openStates := nil; solvedStates := nil
    let rec contains =
      function
      | (nil, _) -> true__
      | (x::L, L') ->
          (List.exists (function | x' -> x = x') L') && (contains (L, L'))
    let rec equiv (L1, L2) = (contains (L1, L2)) && (contains (L2, L1))
    let rec insertState (S) = (openStates := S) :: (!openStates)
    let rec cLToString =
      function
      | nil -> ""
      | c::nil -> I.conDecName (I.sgnLookup c)
      | c::L -> ((I.conDecName (I.sgnLookup c)) ^ ", ") ^ (cLToString L)
    let rec init (k, (c::_ as cL)) =
      let _ = MTPGlobal.maxFill := k in
      let _ = reset () in
      let cL' = try Order.closure c with | Error _ -> cL in
      let F = RelFun.convertFor cL in
      let O = transformOrder (I.Null, F, (map select cL)) in
      if equiv (cL, cL')
      then List.app (function | S -> insertState S) (MTPInit.init (F, O))
      else
        raise
          (Error
             (("Theorem by simultaneous induction not correctly stated:" ^
                 "\n            expected: ")
                ^ (cLToString cL')))
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
  end  (* Meta Theorem Prover Version 1.3 *)
(* Author: Carsten Schuermann *)
(*! structure IntSyn' : INTSYN !*)
(*! structure FunSyn : FUNSYN !*)
(*! sharing FunSyn.IntSyn = IntSyn' !*)
(*! sharing IntSyn = IntSyn' !*)
(*! sharing StateSyn.FunSyn = FunSyn !*)
(*! sharing Order.IntSyn = IntSyn' !*)
(*! sharing MTPInit.FunSyn = FunSyn !*)
(*! sharing RelFun.FunSyn = FunSyn !*)
(*! structure IntSyn = IntSyn' !*)
(* DISCLAIMER: This functor is temporary. Its purpose is to
       connect the new prover to Twelf  (see also functor below) *)
(* List of open states *)
(* List of solved states *)
(* last case: no existentials---order must be trivial *)
(* reset () = ()

       Invariant:
       Resets the internal state of open states/solved states
    *)
(* contains (L1, L2) = B'

       Invariant:
       B' holds iff L1 subset of L2 (modulo permutation)
    *)
(* equiv (L1, L2) = B'

       Invariant:
       B' holds iff L1 is equivalent to L2 (modulo permutation)
    *)
(* insertState S = ()

       Invariant:
       If S is successful prove state, S is stored in solvedStates
       else S is stored in openStates
    *)
(* cLtoString L = s

       Invariant:
       If   L is a list of cid,
       then s is a string, listing their names
    *)
(* init (k, cL) = ()

       Invariant:
       If   k is the maximal search depth
       and  cL is a complete and consistent list of cids
       then init initializes the openStates/solvedStates
       else an Error exception is raised
    *)
(* if no termination ordering given! *)
(* auto () = ()

       Invariant:
       Solves as many States in openStates
       as possible.
    *)
(* local *) (* functor MTProver *)
module CombiProver(CombiProver:sig
                                 module MTPGlobal : MTPGLOBAL
                                 module ProverOld : PROVER
                                 (*! structure IntSyn' : INTSYN !*)
                                 (*! sharing ProverOld.IntSyn = IntSyn' !*)
                                 module ProverNew : PROVER
                               end) : PROVER =
  struct
    (*! sharing ProverNew.IntSyn = IntSyn' !*)
    (*! structure IntSyn = IntSyn' !*)
    exception Error of string 
    let rec he f =
      try f () with | Error s -> raise (Error s) | Error s -> raise (Error s)
    let rec init (Args) =
      he
        (function
         | () ->
             (match !MTPGlobal.prover with
              | MTPGlobal.New -> ProverNew.init Args
              | MTPGlobal.Old -> ProverOld.init Args))
    let rec auto (Args) =
      he
        (function
         | () ->
             (match !MTPGlobal.prover with
              | MTPGlobal.New -> ProverNew.auto Args
              | MTPGlobal.Old -> ProverOld.auto Args))
    let rec print (Args) =
      he
        (function
         | () ->
             (match !MTPGlobal.prover with
              | MTPGlobal.New -> ProverNew.print Args
              | MTPGlobal.Old -> ProverOld.print Args))
    let rec install (Args) =
      he
        (function
         | () ->
             (match !MTPGlobal.prover with
              | MTPGlobal.New -> ProverNew.install Args
              | MTPGlobal.Old -> ProverOld.install Args))
    let init = init
    let auto = auto
    let print = print
    let install = install
  end ;;
