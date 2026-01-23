module type FIFO  =
  sig
    type nonrec 'a queue
    val empty : 'a queue
    exception Empty 
    val get : 'a queue -> ('a * 'a queue)
    val put : ('a * 'a queue) -> 'a queue
  end
module LrParser : LR_PARSER =
  struct
    module LrTable = LrTable
    module Streamm = Streamm
    module Token : TOKEN =
      struct
        module LrTable = LrTable
        type ('a, 'b) token =
          | TOKEN of (LrTable.term * ('a * 'b * 'b)) 
        let sameToken =
          begin function | (TOKEN (t, _), TOKEN (t', _)) -> t = t' end end
    
    open LrTable
    open Token
    let DEBUG1 = false
    let DEBUG2 = false
    exception ParseError 
    exception ParseImpossible of int 
    module Fifo : FIFO =
      struct
        type nonrec 'a queue = ('a list * 'a list)
        let empty = ([], [])
        exception Empty 
        let rec get =
          begin function
          | (a::x, y) -> (a, (x, y))
          | ([], []) -> raise Empty
          | ([], y) -> get ((rev y), []) end
        let rec put (a, (x, y)) = (x, (a :: y)) end
    
  type nonrec ('a, 'b) elem = (state * ('a * 'b * 'b))
  type nonrec ('a, 'b) stack = ('a, 'b) elem list
  type nonrec ('a, 'b) lexv = ('a, 'b) token
  type nonrec ('a, 'b) lexpair =
    (('a, 'b) lexv * ('a, 'b) lexv Streamm.stream)
  type nonrec ('a, 'b) distanceParse =
    (('a, 'b) lexpair * ('a, 'b) stack * (('a, 'b) stack * ('a, 'b) lexpair)
      Fifo.queue * int) ->
      (('a, 'b) lexpair * ('a, 'b) stack * (('a, 'b) stack * ('a, 'b)
        lexpair) Fifo.queue * int * action option)
  type nonrec ('a, 'b) ecRecord =
    <
      is_keyword: term -> bool  ;preferred_change: (term list * term list)
                                                     list  ;error: (string *
                                                                    'b * 'b)
                                                                    -> 
                                                                    unit  ;
      errtermvalue: term -> 'a  ;terms: term list  ;showTerminal: term ->
                                                                    string  ;
      noShift: term -> bool   > 
  let print = begin function | s -> TextIO.output (TextIO.stdOut, s) end
let println = begin function | s -> (begin print s; print "\n" end) end
let showState = begin function | STATE s -> "STATE " ^ (Int.toString s) end
let rec printStack ((stack : ('a, 'b) stack), (n : int)) =
  begin match stack with
  | (state, _)::rest ->
      (begin print (((^) "\t" Int.toString n) ^ ": ");
       println (showState state);
       printStack (rest, (n + 1)) end)
  | [] -> () end
let rec prAction arg__0 arg__1 =
  begin match (arg__0, arg__1) with
  | (showTerminal,
     (((state, _)::_ as stack), ((TOKEN (term, _), _) as next), action)) ->
      (begin println "Parse: state stack:";
       printStack (stack, 0);
       print
         (((^) (((^) "       state=" showState state) ^ " next=")
             showTerminal term)
            ^ " action=");
       (begin match action with
        | SHIFT state -> println ("SHIFT " ^ (showState state))
        | REDUCE i -> println ("REDUCE " ^ (Int.toString i))
        | ERROR -> println "ERROR"
        | ACCEPT -> println "ACCEPT" end) end)
  | (_, (_, _, action)) -> () end
let ssParse =
  begin function
  | (table, showTerminal, saction, fixError, arg) ->
      let prAction = prAction showTerminal in
      let action = LrTable.action table in
      let goto = LrTable.goto table in
      let rec parseStep =
        begin function
        | (((TOKEN (terminal, ((_, leftPos, _) as value)), lexer) as lexPair),
           ((state, _)::_ as stack), queue) as args ->
            let nextAction = action (state, terminal) in
            let _ =
              if DEBUG1 then begin prAction (stack, lexPair, nextAction) end
              else begin () end in
          (begin match nextAction with
           | SHIFT s ->
               let newStack = (s, value) :: stack in
               let newLexPair = Streamm.get lexer in
               let (_, newQueue) =
                 Fifo.get (Fifo.put ((newStack, newLexPair), queue)) in
               parseStep (newLexPair, ((s, value) :: stack), newQueue)
           | REDUCE i ->
               (begin match saction (i, leftPos, stack, arg) with
                | (nonterm, value, ((state, _)::_ as stack)) ->
                    parseStep
                      (lexPair, (((goto (state, nonterm)), value) :: stack),
                        queue)
                | _ -> raise (ParseImpossible 197) end)
            | ERROR -> parseStep (fixError args)
            | ACCEPT ->
                (begin match stack with
                 | (_, (topvalue, _, _))::_ ->
                     let (token, restLexer) = lexPair in
                     (topvalue, (Streamm.cons (token, restLexer)))
                 | _ -> raise (ParseImpossible 202) end) end)
        | _ -> raise (ParseImpossible 204) end in
parseStep end
let distanceParse =
  begin function
  | (table, showTerminal, saction, arg) ->
      let prAction = prAction showTerminal in
      let action = LrTable.action table in
      let goto = LrTable.goto table in
      let rec parseStep =
        begin function
        | (lexPair, stack, queue, 0) -> (lexPair, stack, queue, 0, None)
        | (((TOKEN (terminal, ((_, leftPos, _) as value)), lexer) as lexPair),
           ((state, _)::_ as stack), queue, distance) ->
            let nextAction = action (state, terminal) in
            let _ =
              if DEBUG1 then begin prAction (stack, lexPair, nextAction) end
              else begin () end in
          (begin match nextAction with
           | SHIFT s ->
               let newStack = (s, value) :: stack in
               let newLexPair = Streamm.get lexer in
               parseStep
                 (newLexPair, ((s, value) :: stack),
                   (Fifo.put ((newStack, newLexPair), queue)),
                   (distance - 1))
           | REDUCE i ->
               (begin match saction (i, leftPos, stack, arg) with
                | (nonterm, value, ((state, _)::_ as stack)) ->
                    parseStep
                      (lexPair, (((goto (state, nonterm)), value) :: stack),
                        queue, distance)
                | _ -> raise (ParseImpossible 240) end)
            | ERROR -> (lexPair, stack, queue, distance, (Some nextAction))
            | ACCEPT -> (lexPair, stack, queue, distance, (Some nextAction)) end)
        | _ -> raise (ParseImpossible 242) end in
(parseStep : ('_a, '_b) distanceParse) end
let rec mkFixError
  (({ is_keyword; terms; errtermvalue; preferred_change; noShift;
      showTerminal; error; terms; errtermvalue; preferred_change; noShift;
      showTerminal; error; errtermvalue; preferred_change; noShift;
      showTerminal; error; preferred_change; noShift; showTerminal; error;
      noShift; showTerminal; error; showTerminal; error; error }
     : ('_a, '_b) ecRecord),
   (distanceParse : ('_a, '_b) distanceParse), minAdvance, maxAdvance)
  (((TOKEN (term, ((_, leftPos, _) as value)), _) as lexv), stack, queue) =
  let _ =
    if DEBUG2
    then
      begin error
              (("syntax error found at " ^ (showTerminal term)), leftPos,
                leftPos) end
    else begin () end in
let rec tokAt (t, p) = TOKEN (t, ((errtermvalue t), p, p)) in
let minDelta = 3 in
let stateList =
  let rec f q =
    begin try let (elem, newQueue) = Fifo.get q in elem :: (f newQueue)
    with | Fifo.Empty -> [] end in
f queue in
let (_, numStateList) =
  List.foldr
    (begin function | (a, (num, r)) -> ((num + 1), ((a, num) :: r)) end)
  (0, []) stateList in
let module _Types =
  struct
    type ('a, 'b) change =
      | CHANGE of
      <
        pos: int  ;distance: int  ;leftPos: 'b  ;rightPos: 'b  ;new_: 
                                                                  ('a, 
                                                                    'b) lexv
                                                                    list  ;
        orig: ('a, 'b) lexv list   > 
      
  end in
  let showTerms =
    concat o map (begin function | TOKEN (t, _) -> (^) " " showTerminal t end) in
let printChange =
  begin function
  | c ->
      let CHANGE
        { distance; new___ = new_; orig; pos; new___ = new_; orig; pos; 
          orig; pos; pos }
        = c in
      (begin print ("{distance= " ^ (Int.toString distance));
       print ",orig =";
       print (showTerms orig);
       print ",new =";
       print (showTerms new_);
       print (",pos= " ^ (Int.toString pos));
       print "}\n" end) end in
let printChangeList = app printChange in
let rec parse (lexPair, stack, (queuePos : int)) =
  begin match distanceParse
                (lexPair, stack, Fifo.empty, ((queuePos + maxAdvance) + 1))
        with
  | (_, _, _, distance, Some (ACCEPT)) ->
      if ((maxAdvance - distance) - 1) >= 0 then begin maxAdvance end
      else begin (maxAdvance - distance) - 1 end
  | (_, _, _, distance, _) -> (maxAdvance - distance) - 1 end in
let rec catList l f = List.foldr (begin function | (a, r) -> (f a) @ r end)
  [] l in
let rec keywordsDelta new_ =
  if List.exists (begin function | TOKEN (t, _) -> is_keyword t end) new_
  then begin minDelta end else begin 0 end in
let rec tryChange
{ lex; stack; pos; leftPos; rightPos; orig; new___ = new_; stack; pos;
  leftPos; rightPos; orig; new___ = new_; pos; leftPos; rightPos; orig;
  new___ = new_; leftPos; rightPos; orig; new___ = new_; rightPos; orig;
  new___ = new_; orig; new___ = new_; new___ = new_ }
=
let lex' =
  List.foldr (begin function | (t', p) -> (t', (Streamm.cons p)) end) lex
  new_ in
let distance = parse (lex', stack, ((-) ((+) pos length new_) length orig)) in
if (+) (distance >= minAdvance) keywordsDelta new_
then begin [CHANGE { pos; leftPos; rightPos; distance; orig; new_ }] end
else begin [] end in
let rec tryDelete n ((stack, ((TOKEN (term, (_, l, r)), _) as lexPair)), qPos)
=
let rec del =
  begin function
  | (0, accum, left, right, lexPair) ->
      tryChange
        {
          lex = lexPair;
          stack;
          pos = qPos;
          leftPos = left;
          rightPos = right;
          orig = (rev accum);
          new_ = []
        }
  | (n, accum, left, right, ((TOKEN (term, (_, _, r)) as tok), lexer)) ->
      if noShift term then begin [] end
      else begin del ((n - 1), (tok :: accum), left, r, (Streamm.get lexer)) end end in
del (n, [], l, r, lexPair) in
let rec tryInsert ((stack, ((TOKEN (_, (_, l, _)), _) as lexPair)), queuePos) =
catList terms
  (begin function
   | t ->
       tryChange
         {
           lex = lexPair;
           stack;
           pos = queuePos;
           orig = [];
           new_ = [tokAt (t, l)];
           leftPos = l;
           rightPos = l
         } end) in
let rec trySubst
((stack, (((TOKEN (term, (_, l, r)) as orig), lexer) as lexPair)), queuePos)
= if noShift term then begin [] end
else begin
  catList terms
    (begin function
     | t ->
         tryChange
           {
             lex = (Streamm.get lexer);
             stack;
             pos = queuePos;
             leftPos = l;
             rightPos = r;
             orig = [orig];
             new_ = [tokAt (t, r)]
           } end) end in
let rec do_delete =
begin function
| ([], ((TOKEN (_, (_, l, _)), _) as lp)) -> Some ([], l, l, lp)
| (t::[], ((TOKEN (t', (_, l, r)) as tok), lp')) ->
    if t = t' then begin Some ([tok], l, r, (Streamm.get lp')) end
    else begin None end
| (t::rest, ((TOKEN (t', (_, l, r)) as tok), lp')) ->
    if t = t'
    then
      begin (begin match do_delete (rest, (Streamm.get lp')) with
             | Some (deleted, l', r', lp'') ->
                 Some ((tok :: deleted), l, r', lp'')
             | None -> None end) end
else begin None end end in
let rec tryPreferred ((stack, lexPair), queuePos) =
catList preferred_change
  (begin function
   | (delete, insert) -> ((if List.exists noShift delete then begin [] end
       else begin
         (begin match do_delete (delete, lexPair) with
          | Some (deleted, l, r, lp) ->
              tryChange
                {
                  lex = lp;
                  stack;
                  pos = queuePos;
                  leftPos = l;
                  rightPos = r;
                  orig = deleted;
                  new_ = (map (begin function | t -> tokAt (t, r) end) insert)
                }
         | None -> [] end) end)
(* should give warning at
						 parser-generation time *)) end) in
let changes =
(@) ((@) ((@) ((@) ((@) (catList numStateList tryPreferred) catList
                      numStateList tryInsert)
                 catList numStateList trySubst)
            catList numStateList (tryDelete 1))
       catList numStateList (tryDelete 2))
  catList numStateList (tryDelete 3) in
let findMaxDist =
begin function
| l ->
    foldr
      (begin function
       | (CHANGE { distance }, high) -> Int.max (distance, high) end)
    0 l end in
let maxDist = findMaxDist changes in
let changes =
catList changes
  (begin function
   | CHANGE { distance } as c -> if distance = maxDist then begin [c] end
       else begin [] end end) in
((begin match changes with
| change::_ as l ->
    let rec print_msg (CHANGE
      { new___ = new_; orig; leftPos; rightPos; orig; leftPos; rightPos;
        leftPos; rightPos; rightPos })
      =
      let s =
        begin match (orig, new_) with
        | (_::_, []) -> "deleting " ^ (showTerms orig)
        | ([], _::_) -> "inserting " ^ (showTerms new_)
        | _ ->
            (("replacing " ^ (showTerms orig)) ^ " with ") ^ (showTerms new_) end in
    error (("syntax error: " ^ s), leftPos, rightPos) in
  let _ =
    begin if ((length l) > 1) && DEBUG2
          then
            begin (begin print "multiple fixes possible; could fix it by:\n";
                   app print_msg l;
                   print "chosen correction:\n" end) end
    else begin () end; print_msg change end in
let findNth =
begin function
| n ->
    let rec f =
      begin function
      | (h::t, 0) -> (h, (rev t))
      | (h::t, n) -> f (t, (n - 1))
      | ([], _) -> let exception FindNth  in raise FindNth end in
  f ((rev stateList), n) end in
let CHANGE { pos; orig; new___ = new_; orig; new___ = new_; new___ = new_ } =
change in
let (last, queueFront) = findNth pos in
let (stack, lexPair) = last in
let lp1 = foldl (begin function | (_, (_, r)) -> Streamm.get r end) lexPair
orig in
let lp2 = foldr (begin function | (t, r) -> (t, (Streamm.cons r)) end) lp1 new_ in
let restQueue = Fifo.put ((stack, lp2), (foldl Fifo.put Fifo.empty queueFront)) in
let (lexPair, stack, queue, _, _) = distanceParse (lp2, stack, restQueue, pos) in
(((lexPair, stack, queue))
(* findNth: find nth queue entry from the error
		   entry.  Returns the Nth queue entry and the  portion of
		   the queue from the beginning to the nth-1 entry.  The
		   error entry is at the end of the queue.

		   Examples:

		   queue = a b c d e
		   findNth 0 = (e,a b c d)
		   findNth 1 =  (d,a b c)
		   *))
| [] ->
    (begin error
             (("syntax error found at " ^ (showTerminal term)), leftPos,
               leftPos);
     raise ParseError end) end)
(* pull all the state * lexv elements from the queue *)
(* now number elements of stateList, giving distance from
	   error token *)
(* Represent the set of potential changes as a linked list.

	   Values of datatype Change hold information about a potential change.

	   oper = oper to be applied
	   pos = the # of the element in stateList that would be altered.
	   distance = the number of tokens beyond the error token which the
	     change allows us to parse.
	   new = new terminal * value pair at that point
	   orig = original terminal * value pair at the point being changed.
	 *)
(* parse: given a lexPair, a stack, and the distance from the error
   token, return the distance past the error token that we are able to parse.*)
(* catList: concatenate results of scanning list *)(* tryDelete: Try to delete n terminals.
              Return single-element [success] or nil.
	      Do not delete unshiftable terminals. *)
(* tryInsert: try to insert tokens before the current terminal;
       return a list of the successes  *)
(* trySubst: try to substitute tokens for the current terminal;
       return a list of the successes  *)
(* do_delete(toks,lexPair) tries to delete tokens "toks" from "lexPair".
         If it succeeds, returns SOME(toks',l,r,lp), where
	     toks' is the actual tokens (with positions and values) deleted,
	     (l,r) are the (leftmost,rightmost) position of toks', 
	     lp is what remains of the stream after deletion 
     *)
(* maxDist: max distance past error taken that we could parse *)
(* remove changes which did not parse maxDist tokens past the error token *))
let parse =
  begin function
  | { arg; table; lexer; saction; void; lookahead;
      ec = (({ showTerminal } : ('_a, '_b) ecRecord) as ec); table; lexer;
      saction; void; lookahead;
      ec = (({ showTerminal } : ('_a, '_b) ecRecord) as ec); lexer; saction;
      void; lookahead; ec = (({ showTerminal } : ('_a, '_b) ecRecord) as ec);
      saction; void; lookahead;
      ec = (({ showTerminal } : ('_a, '_b) ecRecord) as ec); void; lookahead;
      ec = (({ showTerminal } : ('_a, '_b) ecRecord) as ec); lookahead;
      ec = (({ showTerminal } : ('_a, '_b) ecRecord) as ec);
      ec = (({ showTerminal } : ('_a, '_b) ecRecord) as ec) } ->
      let distance = 15 in
      let minAdvance = 1 in
      let maxAdvance = Int.max (lookahead, 0) in
      let lexPair = Streamm.get lexer in
      let (TOKEN (_, (_, leftPos, _)), _) = lexPair in
      let startStack = [((initialState table), (void, leftPos, leftPos))] in
      let startQueue = Fifo.put ((startStack, lexPair), Fifo.empty) in
      let distanceParse = distanceParse (table, showTerminal, saction, arg) in
      let fixError = mkFixError (ec, distanceParse, minAdvance, maxAdvance) in
      let ssParse = ssParse (table, showTerminal, saction, fixError, arg) in
      let rec loop =
        begin function
        | (lexPair, stack, queue, _, Some (ACCEPT)) ->
            ssParse (lexPair, stack, queue)
        | (lexPair, stack, queue, 0, _) -> ssParse (lexPair, stack, queue)
        | (lexPair, stack, queue, distance, Some (ERROR)) ->
            let (lexPair, stack, queue) = fixError (lexPair, stack, queue) in
            loop (distanceParse (lexPair, stack, queue, distance))
        | _ -> let exception ParseInternal  in raise ParseInternal end in
      ((loop (distanceParse (lexPair, startStack, startQueue, distance)))
        (* defer distance tokens *)(* must parse at least 1 token past error *)
        (* max distance for parse check *)) end end
