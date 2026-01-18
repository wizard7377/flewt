
(* Termination Order *)
(* Author: Carsten Schuermann *)
module type ORDER  =
  sig
    (*! structure IntSyn : INTSYN !*)
    exception Error of string 
    type 'a __Order =
      | Arg of 'a 
      | Lex of 'a __Order list 
      | Simul of 'a __Order list 
    (*     | [O1 .. On]           *)
    type __Predicate =
      | Less of (int __Order * int __Order) 
      | Leq of (int __Order * int __Order) 
      | Eq of (int __Order * int __Order) 
    (* O = O'                     *)
    type __Mutual =
      | Empty 
      | LE of (IntSyn.cid * __Mutual) 
      | LT of (IntSyn.cid * __Mutual) 
    (*     | lex order for  -     *)
    type __TDec =
      | TDec of (int __Order * __Mutual) 
    type __RDec =
      | RDec of (__Predicate * __Mutual) 
    val reset : unit -> unit
    val resetROrder : unit -> unit
    val install : (IntSyn.cid * __TDec) -> unit
    val uninstall : IntSyn.cid -> bool
    val installROrder : (IntSyn.cid * __RDec) -> unit
    val uninstallROrder : IntSyn.cid -> bool
    val selLookup : IntSyn.cid -> int __Order
    val selLookupROrder : IntSyn.cid -> __Predicate
    val mutLookup : IntSyn.cid -> __Mutual
    val closure : IntSyn.cid -> IntSyn.cid list
  end;;




(* Terminiation and Reduction Order *)
(* Author: Carsten Schuermann *)
(* Modified: Brigitte Pientka *)
module Order(Order:sig
                     (*! structure IntSyn' : INTSYN !*)
                     module Table : TABLE
                   end) : ORDER =
  struct
    (*! structure IntSyn = IntSyn' !*)
    exception Error of string 
    type 'a __Order =
      | Arg of 'a 
      | Lex of 'a __Order list 
      | Simul of 'a __Order list 
    (*     | [O1 .. On]           *)
    type __Predicate =
      | Less of (int __Order * int __Order) 
      | Leq of (int __Order * int __Order) 
      | Eq of (int __Order * int __Order) 
    (* Mutual dependencies in call patterns:                            *)
    (* A call pattern   (a1 P1) .. (ai Pi) .. (an Pn)   expresses       *)
    (* that the proof of ai can refer to                                *)
    (*   ih a1 .. ai, as long as the arguments are strictly smaller     *)
    (* and to                                                           *)
    (*   ih a(i+1) .. an as long as the arguments are smaller or equal  *)
    (* then the ones of ai.                                             *)
    type __Mutual =
      | Empty 
      | LE of (IntSyn.cid * __Mutual) 
      | LT of (IntSyn.cid * __Mutual) 
    (*     |  > (a) C             *)
    type __TDec =
      | TDec of (int __Order * __Mutual) 
    (* TDec ::= (O, C)            *)
    type __RDec =
      | RDec of (__Predicate * __Mutual) 
    (* RDec ::= (P, C)            *)
    module I = IntSyn
    let ((OrderTable) : __TDec Table.__Table) = Table.new__ 0
    let ((RedOrderTable) : __RDec Table.__Table) = Table.new__ 0
    let rec reset () = Table.clear OrderTable
    let rec resetROrder () = Table.clear RedOrderTable
    let rec install (cid, O) = Table.insert OrderTable (cid, O)
    let rec uninstall cid =
      match Table.lookup OrderTable cid with
      | NONE -> false__
      | SOME _ -> (Table.delete OrderTable cid; true__)
    let rec installROrder (cid, P) = Table.insert RedOrderTable (cid, P)
    let rec uninstallROrder cid =
      match Table.lookup RedOrderTable cid with
      | NONE -> false__
      | SOME _ -> (Table.delete RedOrderTable cid; true__)
    let rec lookup cid = Table.lookup OrderTable cid
    let rec lookupROrder cid = Table.lookup RedOrderTable cid
    let rec selLookup a =
      match lookup a with
      | NONE ->
          raise
            (Error
               ((^) "No termination order assigned for " I.conDecName
                  (I.sgnLookup a)))
      | SOME (TDec (S, _)) -> S
    let rec selLookupROrder a =
      match lookupROrder a with
      | NONE ->
          raise
            (Error
               (((^) "No reduction order assigned for " I.conDecName
                   (I.sgnLookup a))
                  ^ "."))
      | SOME (RDec (P, _)) -> P
    let rec mutLookupROrder a =
      match lookupROrder a with
      | NONE ->
          raise
            (Error
               (((^) "No order assigned for " I.conDecName (I.sgnLookup a)) ^
                  "."))
      | SOME (RDec (_, M)) -> M
    let rec mutLookup a =
      match lookup a with
      | NONE ->
          raise
            (Error
               ((^) "No order assigned for " I.conDecName (I.sgnLookup a)))
      | SOME (TDec (_, M)) -> M
    let rec mutual a =
      let rec mutual' =
        function
        | (Empty, a's) -> a's
        | (LE (a, M), a's) -> mutual' (M, (a :: a's))
        | (LT (a, M), a's) -> mutual' (M, (a :: a's)) in
      mutual' ((mutLookup a), nil)
    let rec closure =
      function
      | (nil, a2s) -> a2s
      | (a::a1s, a2s) ->
          if List.exists (function | a' -> a = a') a2s
          then closure (a1s, a2s)
          else closure (((mutual a) @ a1s), (a :: a2s))
    (* mutual a = a's

       Invariant:
       If   a occurs in a call pattern (a1 P1) .. (an Pn)
       then a's = a1 .. an
    *)
    (* closure (a1s, a2s) = a3s

       Invariant:
       If   a1s  and a2s are lists of type families,
       then a3s is a list of type fmailies, which are mutual recursive to each other
       and include a1s and a2s.
    *)
    let reset = reset
    let resetROrder = resetROrder
    let install = install
    let uninstall = uninstall
    let installROrder = installROrder
    let uninstallROrder = uninstallROrder
    let selLookup = selLookup
    let selLookupROrder = selLookupROrder
    let mutLookup = mutLookup
    let closure = function | a -> closure ([a], nil)
  end ;;




module Order =
  (Make_Order)(struct
                 (*! structure IntSyn' = IntSyn !*)
                 module Table = IntRedBlackTree
               end);;
