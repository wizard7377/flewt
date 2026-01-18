
(* Indexing *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning *)
module type INDEX  =
  sig
    (*! structure IntSyn : INTSYN !*)
    val reset : unit -> unit
    val resetFrom : IntSyn.cid -> unit
    val install : IntSyn.__ConDecForm -> IntSyn.__Head -> unit
    (* lookup a = [c1,...,cn] *)
    (* c1,...,cn are all constants with target family a *)
    (* in order of declaration, defined constants are omitted *)
    val lookup : IntSyn.cid -> IntSyn.__Head list
  end;;




(* Indexing *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning *)
module Index(Index:sig module Global : GLOBAL module Queue : QUEUE end) :
  INDEX =
  struct
    (*! structure IntSyn' : INTSYN !*)
    (*! structure IntSyn = IntSyn' !*)
    module I = IntSyn
    let rec cidFromHead = function | Const c -> c | Def c -> c
    let (indexArray : IntSyn.__Head Queue.queue Array.array) =
      Array.array ((Global.maxCid + 1), Queue.empty)
    let rec reset () = Array.modify (function | _ -> Queue.empty) indexArray
    let rec update (a, c) =
      Array.update
        (indexArray, a, (Queue.insert (c, (Array.sub (indexArray, a)))))
    let rec install fromCS (Const c as H) =
      match (fromCS, (I.sgnLookup c)) with
      | (_, ConDec (_, _, _, _, A, I.Type)) ->
          update ((cidFromHead (I.targetHead A)), H)
      | (I.Clause, ConDef (_, _, _, _, A, I.Type, _)) ->
          update ((cidFromHead (I.targetHead A)), (I.Def c))
      | _ -> ()
    let rec remove (a, cid) =
      match Queue.deleteEnd (Array.sub (indexArray, a)) with
      | NONE -> ()
      | SOME ((Const cid' as c), queue') ->
          if cid = cid' then Array.update (indexArray, a, queue') else ()
    let rec uninstall cid =
      match I.sgnLookup cid with
      | ConDec (_, _, _, _, A, I.Type) ->
          remove ((cidFromHead (I.targetHead A)), cid)
      | ConDef (_, _, _, _, A, I.Type, _) ->
          remove ((cidFromHead (I.targetHead A)), cid)
      | _ -> ()
    let rec resetFrom mark =
      let (limit, _) = I.sgnSize () in
      let rec iter i =
        if i < mark
        then ()
        else (uninstall i; Array.update (indexArray, i, Queue.empty)) in
      iter (limit - 1)
    let rec lookup a =
      let rec lk =
        function
        | (l, NONE) -> l
        | (l, SOME q') -> (Array.update (indexArray, a, q'); l) in
      lk (Queue.toList (Array.sub (indexArray, a)))
    (* Index array

       Invariant:
       For all type families  a
       indexArray (a) = c1,...,cn
       where c1,...,cn is a queue consisting of all constants with
       target family a
    *)
    (* reset () = ()
       Empties index array
    *)
    (* update (a, c) = ()
       inserts c into the index queue for family a
       Invariant: a = target family of c
    *)
    (* install (c) = ()
       installs c into the correct index queue
       presently ignores definitions
    *)
    (* lookup a = [c1,...,cn] *)
    (*
       c1,...,cn are all constants with target family a
       in order of declaration, defined constants are omitted.

       A second lookup after the first without intermediate inserts will
       be in constant time.
    *)
    let reset = reset
    let resetFrom = resetFrom
    let install = install
    let lookup = lookup
  end ;;




module Index =
  (Make_Index)(struct module Global = Global
                      module Queue = Queue end)
module IndexSkolem =
  (Make_IndexSkolem)(struct module Global = Global
                            module Queue = Queue end);;
