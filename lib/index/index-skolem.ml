
module IndexSkolem(IndexSkolem:sig
                                 module Global : GLOBAL
                                 module Queue :
                                 ((QUEUE)(* Indexing (Constants and Skolem constants) *)
                                 (* Author: Carsten Schuermann *)
                                 (* Modified: Frank Pfenning *))
                               end) : INDEX =
  struct
    module I = IntSyn
    let rec cidFromHead = function | Const c -> c | Def c -> c
    let (indexArray : IntSyn.__Head Queue.queue Array.array) =
      Array.array ((Global.maxCid + 1), Queue.empty)
    let rec reset () = Array.modify (function | _ -> Queue.empty) indexArray
    let rec update (a, c) =
      Array.update
        (indexArray, a, (Queue.insert (c, (Array.sub (indexArray, a)))))
    let rec install arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (fromCS, (Const c as H)) ->
          (match (fromCS, (I.sgnLookup c)) with
           | (_, ConDec (_, _, _, _, A, I.Type)) ->
               update ((cidFromHead (I.targetHead A)), H)
           | (I.Clause, ConDef (_, _, _, _, A, I.Type, _)) ->
               update ((cidFromHead (I.targetHead A)), (I.Def c))
           | _ -> ())
      | (fromCS, (Skonst c as H)) ->
          (match I.sgnLookup c with
           | SkoDec (_, _, _, A, I.Type) ->
               update ((cidFromHead (I.targetHead A)), H)
           | _ -> ())
    let rec remove (a, cid) =
      match Queue.deleteEnd (Array.sub (indexArray, a)) with
      | NONE -> ()
      | SOME (Const cid', queue') ->
          if cid = cid' then Array.update (indexArray, a, queue') else ()
      | SOME (Skonst cid', queue') ->
          if cid = cid' then Array.update (indexArray, a, queue') else ()
    let rec uninstall cid =
      match I.sgnLookup cid with
      | ConDec (_, _, _, _, A, I.Type) ->
          remove ((cidFromHead (I.targetHead A)), cid)
      | SkoDec (_, _, _, A, I.Type) ->
          remove ((cidFromHead (I.targetHead A)), cid)
      | _ -> ()
    let rec resetFrom mark =
      let (limit, _) = I.sgnSize () in
      let iter i =
        if i < mark
        then ()
        else (uninstall i; Array.update (indexArray, i, Queue.empty)) in
      iter (limit - 1)
    let rec lookup a =
      let lk =
        function
        | (l, NONE) -> l
        | (l, SOME q') -> (Array.update (indexArray, a, q'); l) in
      lk (Queue.toList (Array.sub (indexArray, a)))
    let ((reset)(*! structure IntSyn' : INTSYN !*)(*! structure IntSyn = IntSyn' !*)
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
      (* lookup a = [c1,...,cn] *)(*
       c1,...,cn are all constants with target family a
       in order of declaration, defined constants are omitted.

       A second lookup after the first without intermediate inserts will
       be in constant time.
    *))
      = reset
    let resetFrom = resetFrom
    let install = install
    let lookup = lookup
  end ;;
