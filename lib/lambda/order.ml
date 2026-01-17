
module type ORDER  =
  sig
    exception Error of
      ((string)(*! structure IntSyn : INTSYN !*)(* Author: Carsten Schuermann *)
      (* Termination Order *)) 
    type 'a __Order =
      | Arg of (('a)(* Orders                     *)) 
      | Lex of (('a)(* O ::= x                    *))
      __Order list 
      | Simul of (('a)(*     | {O1 .. On}           *))
      __Order list 
    type __Predicate =
      | Less of
      (((int)(* Reduction Order            *)(*     | [O1 .. On]           *))
      __Order * int __Order) 
      | Leq of (((int)(* O < O'                     *))
      __Order * int __Order) 
      | Eq of (((int)(* O <= O'                    *))
      __Order * int __Order) 
    type __Mutual =
      | Empty 
      | LE of
      (((IntSyn.cid)(* O ::= No order specified   *)
      (* Termination ordering       *)(* O = O'                     *))
      * __Mutual) 
      | LT of
      (((IntSyn.cid)(*     | mutual dependencies  *)) *
      __Mutual) 
    type __TDec =
      | TDec of
      (((int)(* Termination declaration *)(*     | lex order for  -     *))
      __Order * __Mutual) 
    type __RDec =
      | RDec of
      (((__Predicate)(* Reduction declaration      *)) *
      __Mutual) 
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




module Order(Order:sig
                     module Table :
                     ((TABLE)(* Terminiation and Reduction Order *)
                     (* Author: Carsten Schuermann *)
                     (* Modified: Brigitte Pientka *)
                     (*! structure IntSyn' : INTSYN !*))
                   end) : ORDER =
  struct
    exception Error of
      ((string)(*! structure IntSyn = IntSyn' !*)) 
    type 'a __Order =
      | Arg of (('a)(* Orders                     *)) 
      | Lex of (('a)(* O ::= x                    *))
      __Order list 
      | Simul of (('a)(*     | {O1 .. On}           *))
      __Order list 
    type __Predicate =
      | Less of (((int)(*     | [O1 .. On]           *))
      __Order * int __Order) 
      | Leq of (int __Order * int __Order) 
      | Eq of (int __Order * int __Order) 
    type __Mutual =
      | Empty 
      | LE of
      (((IntSyn.cid)(* C ::= .                    *)
      (* Mutual dependencies        *)(* then the ones of ai.                                             *)
      (*   ih a(i+1) .. an as long as the arguments are smaller or equal  *)
      (* and to                                                           *)
      (*   ih a1 .. ai, as long as the arguments are strictly smaller     *)
      (* that the proof of ai can refer to                                *)
      (* A call pattern   (a1 P1) .. (ai Pi) .. (an Pn)   expresses       *)
      (* Mutual dependencies in call patterns:                            *))
      * __Mutual) 
      | LT of
      (((IntSyn.cid)(*     |  <= (a) C            *)) *
      __Mutual) 
    type __TDec =
      | TDec of
      (((int)(* Termination declaration    *)(*     |  > (a) C             *))
      __Order * __Mutual) 
    type __RDec =
      | RDec of
      (((__Predicate)(* Reduction declaration      *)
      (* TDec ::= (O, C)            *)) * __Mutual) 
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
      let mutual' =
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
    let ((reset)(* RDec ::= (P, C)            *)(* mutual a = a's

       Invariant:
       If   a occurs in a call pattern (a1 P1) .. (an Pn)
       then a's = a1 .. an
    *)
      (* closure (a1s, a2s) = a3s

       Invariant:
       If   a1s  and a2s are lists of type families,
       then a3s is a list of type fmailies, which are mutual recursive to each other
       and include a1s and a2s.
    *))
      = reset
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
                 module Table =
                   ((IntRedBlackTree)(*! structure IntSyn' = IntSyn !*))
               end);;
