
module type FLIT  =
  sig
    val init :
      string ->
        ((unit)(* init (sym_table_file) *)(* Author: Roberto Virga *)
        (* Flit DAG generator *))
    val initForText : unit -> ((unit)(* initForText () *))
    val dump :
      (string * string) ->
        ((int)(* dump (symbol, dag_file) *))
    val dumpText :
      (string * string) ->
        ((unit)(* dumpText (outputSemant, outputChecker) *))
    val setFlag : unit -> ((unit)(* setFlag () *))
    val setEndTcb : unit -> ((unit)(* setEndTcb () *))
    val dumpFlagged :
      string -> ((unit)(* dumpFlagged (dag_file) *))
    val dumpSymTable :
      (string * string * string) ->
        ((unit)(* dumpSynTable (start_sym, end_sym, sym_table_file) *))
  end;;




module Flit(Flit:sig
                   module Global : GLOBAL
                   module Word : WORD
                   module Pack : PACK_WORD
                   module Whnf : WHNF
                   module Names : NAMES
                   module Table : TABLE
                   module Index : INDEX
                   module Print :
                   ((PRINT)(* Flit DAG generator *)(* Author: Roberto Virga *))
                 end) : FLIT =
  struct
    module W = Word
    module I = IntSyn
    module N = Names
    module F = Names.Fixity
    module Idx = Index
    module SHT = StringHashTable
    module IHT = Table
    exception Error of string 
    let size_of_expr = 3
    let (tcb_table : (string * int) list option ref) = ref NONE
    let (tcb_size : int ref) = ref 0
    let rec print_table () =
      let print_table' =
        function
        | nil -> ()
        | (name, addr)::[] ->
            print (((^) (("(\"" ^ name) ^ "\", ") Int.toString addr) ^ ")\n")
        | (name, addr)::pairs ->
            (print
               (((^) (("(\"" ^ name) ^ "\", ") Int.toString addr) ^ "),\n");
             print_table' pairs) in
      print "val tcb_table := [\n";
      print_table' (valOf (!tcb_table));
      print "];\n"
    let rec print_size () =
      print (((^) "val tcb_size = " Int.toString (!tcb_size)) ^ ";\n")
    let rec init filename =
      let stream = TextIO.openIn filename in
      let linecount = (ref 0 : int ref) in
      let get_line () =
        ((!) ((:=) linecount) linecount) + 1; Compat.inputLine97 stream in
      let error () =
        raise
          (Error
             ((("Error reading file '" ^ filename) ^ "', line ") ^
                (Int.toString (!linecount)))) in
      let read_size () =
        match Int.fromString (get_line ()) with
        | SOME tcb_size -> tcb_size
        | NONE -> error () in
      let () = (:=) tcb_size read_size () in
      let () = if (!Global.chatter) >= 3 then print_size () else () in
      let read_table =
        function
        | "" -> nil
        | line ->
            (match String.tokens Char.isSpace line with
             | id::addr::[] ->
                 (::) (id, (valOf (Int.fromString addr))) read_table
                   (get_line ())
             | _ -> error ()) in
      let () = (:=) tcb_table SOME (read_table (get_line ())) in
      let () = if (!Global.chatter) >= 3 then print_table () else () in
      let () = TextIO.closeIn stream in ()
    let closedMask = LargeWord.fromInt 256
    let predicateMask = LargeWord.fromInt 512
    let clauseMask = LargeWord.fromInt 1024
    let (baseAddr : int ref) = ref 0
    let (startClause : int option ref) = ref NONE
    let (startSemant : int option ref) = ref NONE
    let (tuples : int ref) = ref 0
    let (out : BinIO.outstream option ref) = ref NONE
    let (symTable : W.word Table.__Table) = Table.new__ 32
    let (printTable : unit Table.__Table) = Table.new__ 32
    let (shadowTable : int SHT.__Table) = SHT.new__ 32
    let (depTable : unit IHT.__Table IHT.__Table) = IHT.new__ 32
    let (recordTable : unit IHT.__Table) = IHT.new__ 32
    let (imitatesTable : int IHT.__Table) = IHT.new__ 32
    let (replaceTable : string IHT.__Table) = IHT.new__ 32
    let rec cname cid = I.conDecName (I.sgnLookup cid)
    let rec clookup name =
      let size = (fun r -> r.1) (I.sgnSize ()) in
      let clookup' cid =
        if cid = size
        then raise (Error (("symbol " ^ name) ^ " not found"))
        else if (cname cid) = name then cid else clookup' (cid + 1) in
      clookup' 0
    let rec print_once cid =
      match Table.lookup printTable cid with
      | NONE ->
          (Table.insert printTable (cid, ());
           print ((Print.conDecToString (I.sgnLookup cid)) ^ "\n"))
      | SOME _ -> ()
    let rec print_tuple (addr, code, (cld, prd, cls), arg1, arg2) =
      print
        (((((((^) (((^) (((^) (((^) ((W.fmt StringCvt.DEC addr) ^ " : ")
                                  Char.toString code)
                                 ^ "\t")
                            Bool.toString cld)
                           ^ "\t")
                      Bool.toString prd)
                     ^ "\t")
                Bool.toString cls)
               ^ "\t")
              ^ (W.fmt StringCvt.DEC arg1))
             ^ "\t")
            ^ (W.fmt StringCvt.DEC arg2))
           ^ "\n")
    let rec writeArray array =
      match !out with
      | SOME stream ->
          (((!) ((:=) tuples) tuples) + 1;
           BinIO.output
             (stream,
               (Word8ArraySlice.vector
                  (Word8ArraySlice.slice (array, 0, NONE)))))
      | NONE -> ()
    let rec tuple (code, ((cld, prd, cls) as flags), arg1, arg2) =
      let addr = W.fromInt ((!) ((+) (!tuples)) tcb_size) in
      let array =
        Word8Array.array
          ((Pack.bytesPerElem * size_of_expr), (Word8.fromInt 0)) in
      let opcode = ref (Word8.toLargeWord (Byte.charToByte code)) in
      if cld then (:=) opcode LargeWord.orb ((!opcode), closedMask) else ();
      if prd
      then (:=) opcode LargeWord.orb ((!opcode), predicateMask)
      else ();
      if cls then (:=) opcode LargeWord.orb ((!opcode), clauseMask) else ();
      Pack.update (array, 0, (!opcode));
      Pack.update (array, 1, (W.toLargeWord arg1));
      Pack.update (array, 2, (W.toLargeWord arg2));
      if (!Global.chatter) >= 4
      then print_tuple (addr, code, flags, arg1, arg2)
      else ();
      writeArray array;
      addr
    let kd = function | () -> W.fromInt 0
    let ty = function | () -> W.fromInt 1
    let rec const arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (true__, ty) ->
          tuple ('c', (true__, true__, true__), (W.fromInt 0), ty)
      | (false__, _) -> W.fromInt 0
    let rec var arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (true__, ty) ->
          tuple ('v', (false__, false__, false__), (W.fromInt 0), ty)
      | (false__, _) -> W.fromInt 0
    let rec pi arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (true__, (flags, var, exp)) -> tuple ('p', flags, var, exp)
      | (false__, _) -> W.fromInt 0
    let rec lam arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (true__, (flags, var, exp)) -> tuple ('l', flags, var, exp)
      | (false__, _) -> W.fromInt 0
    let rec app arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (true__, (flags, exp, arg)) -> tuple ('a', flags, exp, arg)
      | (false__, _) -> W.fromInt 0
    let rec annotate arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (true__, (flags, arg, exp)) -> tuple (':', flags, arg, exp)
      | (false__, _) -> W.fromInt 0
    let rec scanNumber string =
      let check =
        function
        | _::_ as chars -> List.all Char.isDigit chars
        | nil -> false__ in
      if check (String.explode string)
      then StringCvt.scanString (W.scan StringCvt.DEC) string
      else NONE
    let rec scanBinopPf oper string =
      let args = String.tokens (function | c -> c = oper) string in
      match args with
      | arg1::arg2::[] ->
          (match ((StringCvt.scanString (W.scan StringCvt.DEC) arg1),
                   (StringCvt.scanString (W.scan StringCvt.DEC) arg2))
           with
           | (SOME d1, SOME d2) -> SOME (d1, d2)
           | _ -> NONE)
      | _ -> NONE
    let rec scanTernopPf oper1 oper2 string =
      let args = String.tokens (function | c -> c = oper1) string in
      match args with
      | arg1::args2::[] ->
          let args' = String.tokens (function | c -> c = oper2) args2 in
          (match args' with
           | arg2::arg3::[] ->
               (match ((StringCvt.scanString (W.scan StringCvt.DEC) arg1),
                        (StringCvt.scanString (W.scan StringCvt.DEC) arg2),
                        (StringCvt.scanString (W.scan StringCvt.DEC) arg3))
                with
                | (SOME d1, SOME d2, SOME d3) -> SOME (d1, d2, d3)
                | _ -> NONE)
           | _ -> NONE)
      | _ -> NONE
    let rec isPredicate cid =
      match ((!startClause), (I.constUni cid)) with
      | (SOME cid', I.Kind) -> cid >= cid'
      | _ -> false__
    let rec headCID =
      function
      | Const cid -> SOME cid
      | Skonst cid -> SOME cid
      | Def cid -> SOME cid
      | NSDef cid -> SOME cid
      | _ -> NONE
    let rec isClause cid =
      match ((!startClause), (I.constUni cid)) with
      | (SOME cid', I.Type) ->
          if cid >= cid'
          then
            let a = I.targetHead (I.constType cid) in
            let clauses =
              List.mapPartial headCID (Idx.lookup (valOf (headCID a))) in
            List.exists (function | x -> x = cid) clauses
          else false__
      | _ -> false__
    let rec lookup cid =
      match Table.lookup symTable cid with
      | SOME idx -> idx
      | NONE ->
          let idx =
            compileConDec
              ((I.sgnLookup cid), ((isPredicate cid), (isClause cid))) in
          let () = Table.insert symTable (cid, idx) in
          let () = if (!Global.chatter) >= 3 then print_once cid else () in
          idx
    let rec compileUni = function | I.Kind -> kd () | I.Type -> ty ()
    let rec compileExpN arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (generate, (G, Uni (V), flags)) -> compileUni V
      | (generate, (G, Pi ((Dec (_, U1), _), U2), ((cld, _, _) as flags))) ->
          let idxU1 = compileExpN generate (G, U1, (cld, false__, false__)) in
          let idxU1var = var generate idxU1 in
          let idxU2 =
            compileExpN generate
              ((I.Decl (G, idxU1var)), U2, (false__, false__, false__)) in
          pi generate (flags, idxU1var, idxU2)
      | (generate, (G, Lam ((Dec (_, U1) as D), U2), ((cld, _, _) as flags)))
          ->
          let idxU1 = compileExpN generate (G, U1, (cld, false__, false__)) in
          let idxU1var = var generate idxU1 in
          let idxU2 =
            compileExpN generate
              ((I.Decl (G, idxU1var)), U2, (false__, false__, false__)) in
          lam generate (flags, idxU1var, idxU2)
      | (generate, (G, (Root (H, S) as U), flags)) ->
          let idx = compileHead generate (G, H) in
          compileSpine generate (G, idx, S, flags)
      | (generate, (G, FgnExp csfe, flags)) ->
          compileExp generate
            (G, (I.FgnExpStd.ToInternal.apply csfe ()), flags)
    let rec compileSpine arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (generate, (G, idx, I.Nil, flags)) -> idx
      | (generate, (G, idx, App (U1, I.Nil), ((cld, _, _) as flags))) ->
          let idxU1 = compileExpN generate (G, U1, (cld, false__, false__)) in
          app generate (flags, idx, idxU1)
      | (generate, (G, idx, App (U1, S), ((cld, _, _) as flags))) ->
          let idxU1 = compileExpN generate (G, U1, (cld, false__, false__)) in
          compileSpine generate
            (G, (app generate ((cld, false__, false__), idx, idxU1)), S,
              flags)
    let rec compileHead arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (generate, (G, BVar k)) -> I.ctxLookup (G, k)
      | (generate, (G, Const cid)) -> lookup cid
      | (generate, (G, Def cid)) -> lookup cid
      | (generate, (G, NSDef cid)) -> lookup cid
      | (generate, (G, FgnConst (cs, conDec))) ->
          compileFgnDec generate (G, conDec)
    let rec compileFgnDec arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (true__, (G, conDec)) ->
          let name = I.conDecName conDec in
          let flags = (true__, false__, false__) in
          (match scanNumber name with
           | SOME n -> tuple ('#', flags, n, (W.fromInt 0))
           | NONE ->
               (match scanBinopPf '/' name with
                | SOME (n1, n2) -> tuple ('/', flags, n1, n2)
                | NONE ->
                    (match scanBinopPf '+' name with
                     | SOME (n1, n2) -> tuple ('+', flags, n1, n2)
                     | NONE ->
                         (match scanBinopPf '*' name with
                          | SOME (n1, n2) -> tuple ('*', flags, n1, n2)
                          | NONE ->
                              raise
                                (Error ("unknown foreign constant " ^ name))))))
      | (false__, _) -> W.fromInt 0
    let rec compileExp generate (G, U, flags) =
      compileExpN generate (G, (Whnf.normalize (U, I.id)), flags)
    let rec compileConDec =
      function
      | ((ConDec (_, _, _, _, V, _) as condec), (true__, cls)) ->
          const true__
            (compileExpN true__ (I.Null, V, (true__, true__, cls)))
      | ((ConDec (_, _, _, _, _, _) as condec), (pred, cls)) ->
          raise
            (Error ("attempt to shadow constant " ^ (I.conDecName condec)))
      | ((ConDef (_, _, _, U, V, _, _) as condec), (pred, cls)) ->
          let exp =
            compileExpN true__ (I.Null, V, (true__, false__, false__)) in
          let arg = compileExpN true__ (I.Null, U, (true__, pred, cls)) in
          annotate true__ ((true__, pred, cls), arg, exp)
      | ((AbbrevDef (_, _, _, U, V, _) as condec), (pred, cls)) ->
          let exp =
            compileExpN true__ (I.Null, V, (true__, false__, false__)) in
          let arg = compileExpN true__ (I.Null, U, (true__, pred, cls)) in
          annotate true__ ((true__, pred, cls), arg, exp)
    let rec initTuples () =
      let _ = tuples := 0 in
      let _ = Table.clear symTable in
      let _ = Table.clear printTable in
      match !tcb_table with
      | SOME l ->
          List.app
            (function
             | (name, idx) ->
                 Table.insert symTable ((clookup name), (W.fromInt idx))) l
      | NONE -> raise (Error "dump(...) before init(...)")
    let rec dump (name, file) =
      let dump' cid =
        let _ = (:=) out SOME (BinIO.openOut file) in
        let stream = valOf (!out) in
        let _ = initTuples () in
        let idx = W.toInt (lookup cid) in
        let _ = BinIO.closeOut stream in idx in
      let error msg =
        let closeOut () =
          match !out with | SOME stream -> BinIO.closeOut stream | NONE -> () in
        print (("Error: " ^ msg) ^ "\n"); closeOut (); (-1) in
      match N.constLookup (valOf (N.stringToQid name)) with
      | SOME cid -> (try dump' cid with | Error msg -> error msg)
      | NONE -> error (("symbol " ^ name) ^ " not found\n")
    let rec setFlag () =
      match !startClause with
      | SOME cid -> print "Error: flag already set\n"
      | NONE -> (:=) startClause SOME (((fun r -> r.1)) (I.sgnSize ()))
    let rec setEndTcb () =
      match !startSemant with
      | SOME cid -> print "Error: flag already set\n"
      | NONE -> (:=) startSemant SOME (((fun r -> r.1)) (I.sgnSize ()))
    let rec dumpFlagged file =
      let max = (fun r -> r.1) (I.sgnSize ()) in
      let compileSeq cid =
        if cid < max then (lookup cid; compileSeq (cid + 1)) else () in
      let dump' cid =
        (:=) out SOME (BinIO.openOut file);
        initTuples ();
        compileSeq cid;
        BinIO.closeOut (valOf (!out)) in
      let error msg =
        let closeOut () =
          match !out with | SOME stream -> BinIO.closeOut stream | NONE -> () in
        print (("Error: " ^ msg) ^ "\n"); closeOut () in
      match !startClause with
      | SOME cid -> (try dump' cid with | Error msg -> error msg)
      | NONE -> error "setFlag() has not been called yet\n"
    let rec dumpSymTable (name1, name2, file) =
      let stream = TextIO.openOut file in
      let Strength nonfixLevel = F.minPrec in
      let dumpFixity cid =
        match N.getFixity cid with
        | Infix (Strength level, F.Left) -> (level, 1)
        | Infix (Strength level, F.Right) -> (level, 2)
        | Infix (Strength level, F.None) -> (level, 3)
        | F.Nonfix -> (nonfixLevel, 0) in
      let dumpEntry cid =
        match ((Table.lookup symTable cid), (dumpFixity cid)) with
        | (SOME idx, (level, assoc)) ->
            TextIO.output
              (stream,
                (((^) (((^) ((((I.conDecName (I.sgnLookup cid)) ^ "\t") ^
                                (Word.fmt StringCvt.DEC idx))
                               ^ "\t")
                          Int.toString level)
                         ^ "\t")
                    Int.toString assoc)
                   ^ "\n"))
        | (NONE, _) -> () in
      let dumpTable (cid1, cid2) =
        if cid1 <= cid2
        then (dumpEntry cid1; dumpTable ((cid1 + 1), cid2))
        else () in
      let error msg = print (("Error: " ^ msg) ^ "\n") in
      (match ((N.constLookup (valOf (N.stringToQid name1))),
               (N.constLookup (valOf (N.stringToQid name2))))
       with
       | (SOME cid1, SOME cid2) -> dumpTable (cid1, cid2)
       | (NONE, _) -> error (name1 ^ " undefined")
       | (_, NONE) -> error (name2 ^ " undefined"));
      TextIO.flushOut stream;
      TextIO.closeOut stream
    let rec sort cmp l =
      let split l =
        let s arg__0 arg__1 arg__2 =
          match (arg__0, arg__1, arg__2) with
          | (a1, a2, nil) -> (a1, a2)
          | (a1, a2, h::t) -> s a2 (h :: a1) t in
        s nil nil l in
      let merge arg__0 arg__1 =
        match (arg__0, arg__1) with
        | (a, nil) -> a
        | (nil, b) -> b
        | ((a::ta as aa), (b::tb as bb)) ->
            (match cmp (a, b) with
             | EQUAL -> (::) (a :: b) merge ta tb
             | LESS -> (::) a merge ta bb
             | GREATER -> (::) b merge aa tb) in
      let ms =
        function
        | nil -> nil
        | s::[] -> [s]
        | a::b::[] -> merge [a] [b]
        | ll -> let (a, b) = split ll in merge (ms a) (ms b) in
      ms l
    let rec sortedKeys t =
      let r = ref [] in
      let _ = IHT.app (function | x -> (!) ((::) (r := x)) r) t in
      sort Int.compare (map (fun r -> r.1) (!r))
    exception noPriorEntry of string 
    exception Error of string 
    let rec valOfE arg__0 arg__1 =
      match (arg__0, arg__1) with | (e, NONE) -> raise e | (e, SOME x) -> x
    let counter = ref 0
    let rec isShadowedBy cid =
      let name = I.conDecName (I.sgnLookup cid) in
      let currentcid =
        valOfE (noPriorEntry name) (SHT.lookup shadowTable name) in
      (name, (if currentcid <> cid then SOME currentcid else NONE))
    let rec isShadowing () =
      let _ = SHT.clear shadowTable in
      let changes = ref false__ in
      let processDep rcid cid =
        let handleProblem (currentcid, name) =
          match Table.lookup replaceTable cid with
          | SOME _ -> ()
          | _ ->
              let replacement =
                Option.map (I.conDecName o I.sgnLookup)
                  (Table.lookup imitatesTable cid) in
              (match replacement with
               | NONE ->
                   raise
                     (Error
                        (((^) (((^) (((^) (("Error: " ^ name) ^ " (")
                                        Int.toString cid)
                                       ^ ") used by cid ")
                                  Int.toString rcid)
                                 ^ " but shadowed by ")
                            Int.toString currentcid)
                           ^ ".\n"))
               | SOME x -> Table.insert replaceTable (cid, x)) in
        let (name, sb) = isShadowedBy cid in
        match sb with
        | SOME currentcid ->
            if
              ((<) cid valOf (!startSemant)) ||
                ((>=) cid valOf (!startClause))
            then handleProblem (currentcid, name)
            else
              (let newname = (^) "shadowed_" Int.toString (!counter) in
               I.rename (cid, newname);
               SHT.insert shadowTable (newname, cid);
               ((!) ((:=) counter) counter) + 1;
               changes := true__)
        | NONE -> () in
      let processCid cid =
        let name = I.conDecName (I.sgnLookup cid) in
        (try
           List.app (processDep cid)
             (sortedKeys (valOf (IHT.lookup depTable cid)))
         with | Option -> ());
        SHT.insert shadowTable (name, cid) in
      (try List.app processCid (sortedKeys recordTable)
       with
       | noPriorEntry s as e ->
           (print (("Error: No Prior Entry: " ^ s) ^ "\n"); raise e));
      !changes
    let rec is_def cid = try I.constDef cid; true__ with | Match -> false__
    let rec fixityDec cid =
      match N.getFixity cid with
      | Infix _ as f ->
          ((^) ((F.toString f) ^ " ") I.conDecName (I.sgnLookup cid)) ^ ".\n"
      | _ -> ""
    let rec record_once k cid =
      match IHT.insertShadow recordTable (cid, ()) with
      | NONE -> k cid
      | SOME _ -> ()
    let rec recordDependency (x, y) =
      let table =
        match IHT.lookup depTable x with
        | SOME y -> y
        | NONE -> let t = IHT.new__ 32 in (IHT.insert depTable (x, t); t) in
      IHT.insert table (y, ())
    open I
    let rec etaReduce arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (n, Root (h, sp)) -> if etaReduceSpine n sp then SOME h else NONE
      | (n, Lam (_, t)) -> etaReduce (n + 1) t
      | (_, _) -> NONE
    let rec etaReduceSpine arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (n, App (fst, sp)) ->
          (match etaReduce 0 fst with
           | SOME (BVar n') -> (n = n') && (etaReduceSpine (n - 1) sp)
           | _ -> false__)
      | (n, Nil) -> true__
      | (n, _) -> false__
    let rec checkTrivial cid =
      match sgnLookup cid with
      | AbbrevDef (_, _, _, M, V, _) ->
          (match etaReduce 0 M with
           | SOME (Const cid') ->
               (print
                  (((^) (((^) "DX inserting " Int.toString cid') ^ " = ")
                      Int.toString cid)
                     ^ "\n");
                Table.insert imitatesTable (cid', cid))
           | _ -> ())
      | _ -> ()
    let rec travExp arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (cid, Uni _) -> ()
      | (cid, Pi ((D, _), B)) -> (travDec cid D; travExp cid B)
      | (cid, Root (H, S)) -> (travHead cid H; travSpine cid S)
      | (cid, Redex (M, S)) -> (travExp cid M; travSpine cid S)
      | (cid, Lam (D, M)) -> (travDec cid D; travExp cid M)
      | (cid, _) -> ()
    let rec travDec arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (cid, Dec (_, A)) -> travExp cid A
      | (cid, BDec (_, (c, _))) -> (recordDependency (cid, c); traverse c)
    let rec travSpine arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (cid, Nil) -> ()
      | (cid, App (M, S)) -> (travExp cid M; travSpine cid S)
      | (cid, _) -> ()
    let rec travHead cid h =
      Option.map (function | n -> (recordDependency (cid, n); traverse n))
        (headCID h)
    let rec traverseDescendants' arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (cid, ConDec (_, _, _, _, V, _)) -> travExp cid V
      | (cid, ConDef (_, _, _, M, V, _, _)) -> (travExp cid M; travExp cid V)
      | (cid, AbbrevDef (_, _, _, M, V, _)) -> (travExp cid M; travExp cid V)
      | (cid, _) -> ()
    let rec traverseDescendants cid =
      traverseDescendants' cid (I.sgnLookup cid)
    let rec traverse cid =
      let name = conDecName (sgnLookup cid) in
      record_once traverseDescendants cid
    let rec initForText () =
      startClause := NONE;
      startSemant := NONE;
      Table.clear depTable;
      Table.clear recordTable;
      Table.clear imitatesTable;
      Table.clear replaceTable
    exception InfixWithImplicitArgs 
    let rec appRange f min max =
      if min < max then (f min; appRange f (min + 1) max) else ()
    let rec dumpAll (max, first, outputSemant, outputChecker) =
      let streamSemant = TextIO.openOut outputSemant in
      let streamChecker = TextIO.openOut outputChecker in
      let streamTcb = TextIO.openOut "dumptcb" in
      let waitUntilFalse f = if f () then waitUntilFalse f else () in
      let outputCid cid =
        let s = (Print.conDecToString (I.sgnLookup cid)) ^ "\n" in
        let s' =
          if ((>=) cid valOf (!startClause)) && (is_def cid)
          then (if isClause cid then "%clause " ^ s else s)
          else s in
        let stream =
          if (<) cid valOf (!startSemant)
          then streamTcb
          else
            if (>=) cid valOf (!startClause)
            then streamChecker
            else streamSemant in
        TextIO.output (stream, (s' ^ (fixityDec cid))) in
      appRange checkTrivial 0 max;
      appRange traverse first max;
      appRange (function | cid -> Table.insert recordTable (cid, ())) 0
        (valOf (!startSemant));
      waitUntilFalse isShadowing;
      Table.app IntSyn.rename replaceTable;
      List.app outputCid (sortedKeys recordTable);
      TextIO.closeOut streamSemant;
      TextIO.closeOut streamChecker;
      TextIO.closeOut streamTcb
    let rec dumpText (outputSemant, outputChecker) =
      let max = (fun r -> r.1) (I.sgnSize ()) in
      let correctFixities cid =
        if cid < max
        then
          ((let fixity = N.getFixity cid in
            let imp = I.constImp cid in
            let name = I.conDecName (I.sgnLookup cid) in
            let inSemant =
              ((>=) cid valOf (!startSemant)) &&
                ((<) cid valOf (!startClause)) in
            let makeNonfix =
              match (fixity, imp, inSemant) with
              | (Infix _, _, true__) -> true__
              | (Infix _, 0, false__) -> false__
              | (Infix _, _, false__) -> raise InfixWithImplicitArgs
              | (_, _, _) -> false__ in
            if makeNonfix then N.installFixity (cid, F.Nonfix) else ());
           correctFixities (cid + 1))
        else () in
      let _ = correctFixities 0 in
      let error msg = print (("Error: " ^ msg) ^ "\n") in
      match !startClause with
      | SOME cid ->
          (try dumpAll (max, cid, outputSemant, outputChecker)
           with | Error msg -> error msg)
      | NONE -> error "setFlag() has not been called yet\n"
    let ((init)(* currently unused *)(* returns a tuple of the name of the cid and SOME of the shadowing cid if any *)
      (* returns true if it changed any names *)(* val _ = print "clearing table...\n" *)
      (* Option.mapPartial
                                                    (fn x => (case isShadowedBy x of
                                                    (_, SOME _) => NONE
                                                      | (x, NONE) => SOME x)) *)
      (* XXX worrying - jcreed 7/05 *)(* print ("DX planning to subtly rename " ^ Int.toString cid ^ " to " ^ x ^ "\n");  *)
      (* problematic shadowing *)(* nonproblematic shadowing - change its name *)
      (* print ("DX renaming " ^ Int.toString cid ^ " to " ^ newname ^ "\n"); *)
      (* val _ = print ("DX processing cid " ^ Int.toString cid ^ " which has name [" ^ name ^ "].\n") *)
      (* print("DX Recording " ^ Int.toString cid ^ ".\n") ; *)
      (*        val msg = "DX dep " ^ Int.toString x ^ " on " ^ Int.toString y ^ "\n" *)
      (* val message = "DX Traversing cid = " ^ Int.toString cid ^ " name = " ^ name ^ "\n" *)
      (* DX *)(* if cid < (valOf(!startSemant)) then () else *)
      (* DX *)(* DX *)(* DX *)
      (* val _ = print ("DX startSemant = " ^ Int.toString(valOf(!startSemant)) ^ "\n") *)
      (* val _ = print ("DX startClause = " ^ Int.toString(valOf(!startClause)) ^ "\n") *)
      (* val _ = case fixity of F.Infix _ => print ("DX Infix " ^ Int.toString cid ^ " " ^ name ^ " " ^ Int.toString imp ^ " \n") | _ => () *)
      (*print ("DX setting nonfix " ^ Int.toString cid ^ "\n"); *))
      = init
    let initForText = initForText
    let dump = dump
    let dumpText = dumpText
    let setFlag = setFlag
    let setEndTcb = setEndTcb
    let dumpFlagged = dumpFlagged
    let dumpSymTable = dumpSymTable
  end ;;




module Flit =
  (Make_Flit)(struct
                module Global = Global
                module Word = Word32
                module Pack = PackWord32Little
                module IntSyn = IntSyn
                module Whnf = Whnf
                module Print = Print
                module Names = Names
                module Index = Index
                module Table = IntRedBlackTree
              end);;
