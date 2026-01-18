
module type FIFO  =
  sig
    type nonrec 'a queue
    val empty : 'a queue
    exception Empty 
    val get : 'a queue -> ('a * 'a queue)
    val put : ('a * 'a queue) -> 'a queue
  end
(* ML-Yacc Parser Generator (c) 1989 Andrew W. Appel, David R. Tarditi 
 *
 * $Log: not supported by cvs2svn $
 * Revision 1.1.2.1  2003/01/14 22:46:39  carsten_lf
 * delphin frontend added
 *
 * Revision 1.1  2001/11/12 23:23:09  carsten
 * mlyacc hack included
 *
 * Revision 1.1.1.1  1999/12/03 19:59:22  dbm
 * Import of 110.0.6 src
 *
 * Revision 1.2  1997/08/26 19:18:54  jhr
 *   Replaced used of "abstraction" with ":>".
 *
# Revision 1.1.1.1  1997/01/14  01:38:04  george
#   Version 109.24
#
 * Revision 1.3  1996/10/03  03:36:58  jhr
 * Qualified identifiers that are no-longer top-level (quot, rem, min, max).
 *
 * Revision 1.2  1996/02/26  15:02:29  george
 *    print no longer overloaded.
 *    use of makestring has been removed and replaced with Int.toString ..
 *    use of IO replaced with TextIO
 *
 * Revision 1.1.1.1  1996/01/31  16:01:42  george
 * Version 109
 * 
 *)
(* parser.sml:  This is a parser driver for LR tables with an error-recovery
   routine added to it.  The routine used is described in detail in this
   article:

	'A Practical Method for LR and LL Syntactic Error Diagnosis and
	 Recovery', by M. Burke and G. Fisher, ACM Transactions on
	 Programming Langauges and Systems, Vol. 9, No. 2, April 1987,
	 pp. 164-197.

    This program is an implementation is the partial, deferred method discussed
    in the article.  The algorithm and data structures used in the program
    are described below.  

    This program assumes that all semantic actions are delayed.  A semantic
    action should produce a function from unit -> value instead of producing the
    normal value.  The parser returns the semantic value on the top of the
    stack when accept is encountered.  The user can deconstruct this value
    and apply the unit -> value function in it to get the answer.

    It also assumes that the lexer is a lazy stream.

    Data Structures:
    ----------------
	
	* The parser:

	   The state stack has the type

		 (state * (semantic value * line # * line #)) list

	   The parser keeps a queue of (state stack * lexer pair).  A lexer pair
	 consists of a terminal * value pair and a lexer.  This allows the 
	 parser to reconstruct the states for terminals to the left of a
	 syntax error, and attempt to make error corrections there.

	   The queue consists of a pair of lists (x,y).  New additions to
	 the queue are cons'ed onto y.  The first element of x is the top
	 of the queue.  If x is nil, then y is reversed and used
	 in place of x.

    Algorithm:
    ----------

	* The steady-state parser:  

	    This parser keeps the length of the queue of state stacks at
	a steady state by always removing an element from the front when
	another element is placed on the end.

	    It has these arguments:

	   stack: current stack
	   queue: value of the queue
	   lexPair ((terminal,value),lex stream)

	When SHIFT is encountered, the state to shift to and the value are
	are pushed onto the state stack.  The state stack and lexPair are
	placed on the queue.  The front element of the queue is removed.

	When REDUCTION is encountered, the rule is applied to the current
	stack to yield a triple (nonterm,value,new stack).  A new
	stack is formed by adding (goto(top state of stack,nonterm),value)
	to the stack.

	When ACCEPT is encountered, the top value from the stack and the
	lexer are returned.

	When an ERROR is encountered, fixError is called.  FixError
	takes the arguments to the parser, fixes the error if possible and
        returns a new set of arguments.

	* The distance-parser:

	This parser includes an additional argument distance.  It pushes
	elements on the queue until it has parsed distance tokens, or an
	ACCEPT or ERROR occurs.  It returns a stack, lexer, the number of
	tokens left unparsed, a queue, and an action option.
*)
(* drt (12/15/89) -- the functor should be used in development work, but
   it wastes space in the release version.

functor ParserGen(structure LrTable : LR_TABLE
		  structure Streamm : STREAMM) : LR_PARSER =
*)
module LrParser : LR_PARSER =
  struct
    module LrTable = LrTable
    module Streamm = Streamm
    module Token : TOKEN =
      struct
        module LrTable = LrTable
        type ('a, 'b) token =
          | TOKEN of (LrTable.term * ('a * 'b * 'b)) 
        let sameToken = function | (TOKEN (t, _), TOKEN (t', _)) -> t = t'
      end 
    open LrTable
    open Token
    let DEBUG1 = false__
    let DEBUG2 = false__
    exception ParseError 
    exception ParseImpossible of int 
    module Fifo : FIFO =
      struct
        type nonrec 'a queue = ('a list * 'a list)
        let empty = (nil, nil)
        exception Empty 
        let rec get =
          function
          | (a::x, y) -> (a, (x, y))
          | (nil, nil) -> raise Empty
          | (nil, y) -> get ((rev y), nil)
        let rec put (a, (x, y)) = (x, (a :: y))
      end 
    type nonrec ('a, 'b) elem = (state * ('a * 'b * 'b))
    type nonrec ('a, 'b) stack = ('a, 'b) elem list
    type nonrec ('a, 'b) lexv = ('a, 'b) token
    type nonrec ('a, 'b) lexpair =
      (('a, 'b) lexv * ('a, 'b) lexv Streamm.stream)
    type nonrec ('a, 'b) distanceParse =
      (('a, 'b) lexpair * ('a, 'b) stack * (('a, 'b) stack * ('a, 'b)
        lexpair) Fifo.queue * int) ->
        (('a, 'b) lexpair * ('a, 'b) stack * (('a, 'b) stack * ('a, 'b)
          lexpair) Fifo.queue * int * action option)
    type nonrec ('a, 'b) ecRecord =
      <
        is_keyword: term -> bool  ;preferred_change: (term list * term list)
                                                       list  ;error: 
                                                                (string * 'b
                                                                  * 'b) ->
                                                                  unit  ;
        errtermvalue: term -> 'a  ;terms: term list  ;showTerminal: term ->
                                                                    string  ;
        noShift: term -> bool   > 
    let print = function | s -> TextIO.output (TextIO.stdOut, s)
    let println = function | s -> (print s; print "\n")
    let showState = function | STATE s -> "STATE " ^ (Int.toString s)
    let rec printStack ((stack : ('a, 'b) stack), (n : int)) =
      match stack with
      | (state, _)::rest ->
          (print (((^) "\t" Int.toString n) ^ ": ");
           println (showState state);
           printStack (rest, (n + 1)))
      | nil -> ()
    let rec prAction arg__0 arg__1 =
      match (arg__0, arg__1) with
      | (showTerminal,
         (((state, _)::_ as stack), ((TOKEN (term, _), _) as next), action))
          ->
          (println "Parse: state stack:";
           printStack (stack, 0);
           print
             (((^) (((^) "       state=" showState state) ^ " next=")
                 showTerminal term)
                ^ " action=");
           (match action with
            | SHIFT state -> println ("SHIFT " ^ (showState state))
            | REDUCE i -> println ("REDUCE " ^ (Int.toString i))
            | ERROR -> println "ERROR"
            | ACCEPT -> println "ACCEPT"))
      | (_, (_, _, action)) -> ()
    (* ssParse: parser which maintains the queue of (state * lexvalues) in a
	steady-state.  It takes a table, showTerminal function, saction
	function, and fixError function.  It parses until an ACCEPT is
	encountered, or an exception is raised.  When an error is encountered,
	fixError is called with the arguments of parseStep (lexv,stack,and
	queue).  It returns the lexv, and a new stack and queue adjusted so
	that the lexv can be parsed *)
    let ssParse =
      function
      | (table, showTerminal, saction, fixError, arg) ->
          let prAction = prAction showTerminal in
          let action = LrTable.action table in
          let goto = LrTable.goto table in
          let rec parseStep =
            function
            | (((TOKEN (terminal, ((_, leftPos, _) as value)), lexer) as
                  lexPair),
               ((state, _)::_ as stack), queue) as args ->
                let nextAction = action (state, terminal) in
                let _ =
                  if DEBUG1
                  then prAction (stack, lexPair, nextAction)
                  else () in
                (match nextAction with
                 | SHIFT s ->
                     let newStack = (s, value) :: stack in
                     let newLexPair = Streamm.get lexer in
                     let (_, newQueue) =
                       Fifo.get (Fifo.put ((newStack, newLexPair), queue)) in
                     parseStep (newLexPair, ((s, value) :: stack), newQueue)
                 | REDUCE i ->
                     (match saction (i, leftPos, stack, arg) with
                      | (nonterm, value, ((state, _)::_ as stack)) ->
                          parseStep
                            (lexPair,
                              (((goto (state, nonterm)), value) :: stack),
                              queue)
                      | _ -> raise (ParseImpossible 197))
                 | ERROR -> parseStep (fixError args)
                 | ACCEPT ->
                     (match stack with
                      | (_, (topvalue, _, _))::_ ->
                          let (token, restLexer) = lexPair in
                          (topvalue, (Streamm.cons (token, restLexer)))
                      | _ -> raise (ParseImpossible 202)))
            | _ -> raise (ParseImpossible 204) in
          parseStep
    (*  distanceParse: parse until n tokens are shifted, or accept or
	error are encountered.  Takes a table, showTerminal function, and
	semantic action function.  Returns a parser which takes a lexPair
	(lex result * lexer), a state stack, a queue, and a distance
	(must be > 0) to parse.  The parser returns a new lex-value, a stack
	with the nth token shifted on top, a queue, a distance, and action
	option. *)
    let distanceParse =
      function
      | (table, showTerminal, saction, arg) ->
          let prAction = prAction showTerminal in
          let action = LrTable.action table in
          let goto = LrTable.goto table in
          let rec parseStep =
            function
            | (lexPair, stack, queue, 0) -> (lexPair, stack, queue, 0, NONE)
            | (((TOKEN (terminal, ((_, leftPos, _) as value)), lexer) as
                  lexPair),
               ((state, _)::_ as stack), queue, distance) ->
                let nextAction = action (state, terminal) in
                let _ =
                  if DEBUG1
                  then prAction (stack, lexPair, nextAction)
                  else () in
                (match nextAction with
                 | SHIFT s ->
                     let newStack = (s, value) :: stack in
                     let newLexPair = Streamm.get lexer in
                     parseStep
                       (newLexPair, ((s, value) :: stack),
                         (Fifo.put ((newStack, newLexPair), queue)),
                         (distance - 1))
                 | REDUCE i ->
                     (match saction (i, leftPos, stack, arg) with
                      | (nonterm, value, ((state, _)::_ as stack)) ->
                          parseStep
                            (lexPair,
                              (((goto (state, nonterm)), value) :: stack),
                              queue, distance)
                      | _ -> raise (ParseImpossible 240))
                 | ERROR ->
                     (lexPair, stack, queue, distance, (SOME nextAction))
                 | ACCEPT ->
                     (lexPair, stack, queue, distance, (SOME nextAction)))
            | _ -> raise (ParseImpossible 242) in
          (parseStep : ('a, 'b) distanceParse)
    (* mkFixError: function to create fixError function which adjusts parser state
   so that parse may continue in the presence of an error *)
    let rec mkFixError
      (({ is_keyword; terms; errtermvalue; preferred_change; noShift;
          showTerminal; error; terms; errtermvalue; preferred_change;
          noShift; showTerminal; error; errtermvalue; preferred_change;
          noShift; showTerminal; error; preferred_change; noShift;
          showTerminal; error; noShift; showTerminal; error; showTerminal;
          error; error }
         : ('a, 'b) ecRecord),
       (distanceParse : ('a, 'b) distanceParse), minAdvance, maxAdvance)
      (((TOKEN (term, ((_, leftPos, _) as value)), _) as lexv), stack, queue)
      =
      let _ =
        if DEBUG2
        then
          error
            (("syntax error found at " ^ (showTerminal term)), leftPos,
              leftPos)
        else () in
      let rec tokAt (t, p) = TOKEN (t, ((errtermvalue t), p, p)) in
      let minDelta = 3 in
      let stateList =
        let rec f q =
          try let (elem, newQueue) = Fifo.get q in elem :: (f newQueue)
          with | Fifo.Empty -> nil in
        f queue in
      let (_, numStateList) =
        List.foldr (function | (a, (num, r)) -> ((num + 1), ((a, num) :: r)))
          (0, []) stateList in
      let module _Types =
        struct
          type ('a, 'b) change =
            | CHANGE of
            <
              pos: int  ;distance: int  ;leftPos: 'b  ;rightPos: 'b  ;
              new__: ('a, 'b) lexv list  ;orig: ('a, 'b) lexv list   > 
            
        end in
        let showTerms =
          concat o map (function | TOKEN (t, _) -> (^) " " showTerminal t) in
        let printChange =
          function
          | c ->
              let CHANGE
                { distance; new__; orig; pos; new__; orig; pos; orig; 
                  pos; pos }
                = c in
              (print ("{distance= " ^ (Int.toString distance));
               print ",orig =";
               print (showTerms orig);
               print ",new =";
               print (showTerms new__);
               print (",pos= " ^ (Int.toString pos));
               print "}\n") in
        let printChangeList = app printChange in
        let rec parse (lexPair, stack, (queuePos : int)) =
          match distanceParse
                  (lexPair, stack, Fifo.empty, ((queuePos + maxAdvance) + 1))
          with
          | (_, _, _, distance, SOME (ACCEPT)) ->
              if ((maxAdvance - distance) - 1) >= 0
              then maxAdvance
              else (maxAdvance - distance) - 1
          | (_, _, _, distance, _) -> (maxAdvance - distance) - 1 in
        let rec catList l f =
          List.foldr (function | (a, r) -> (f a) @ r) [] l in
        let rec keywordsDelta new__ =
          if List.exists (function | TOKEN (t, _) -> is_keyword t) new__
          then minDelta
          else 0 in
        let rec tryChange
          { lex; stack; pos; leftPos; rightPos; orig; new__; stack; pos;
            leftPos; rightPos; orig; new__; pos; leftPos; rightPos; orig;
            new__; leftPos; rightPos; orig; new__; rightPos; orig; new__;
            orig; new__; new__ }
          =
          let lex' =
            List.foldr (function | (t', p) -> (t', (Streamm.cons p))) lex
              new__ in
          let distance =
            parse (lex', stack, ((-) ((+) pos length new__) length orig)) in
          if (+) (distance >= minAdvance) keywordsDelta new__
          then [CHANGE { pos; leftPos; rightPos; distance; orig; new__ }]
          else [] in
        let rec tryDelete n
          ((stack, ((TOKEN (term, (_, l, r)), _) as lexPair)), qPos) =
          let rec del =
            function
            | (0, accum, left, right, lexPair) ->
                tryChange
                  {
                    lex = lexPair;
                    stack;
                    pos = qPos;
                    leftPos = left;
                    rightPos = right;
                    orig = (rev accum);
                    new__ = []
                  }
            | (n, accum, left, right,
               ((TOKEN (term, (_, _, r)) as tok), lexer)) ->
                if noShift term
                then []
                else
                  del ((n - 1), (tok :: accum), left, r, (Streamm.get lexer)) in
          del (n, [], l, r, lexPair) in
        let rec tryInsert
          ((stack, ((TOKEN (_, (_, l, _)), _) as lexPair)), queuePos) =
          catList terms
            (function
             | t ->
                 tryChange
                   {
                     lex = lexPair;
                     stack;
                     pos = queuePos;
                     orig = [];
                     new__ = [tokAt (t, l)];
                     leftPos = l;
                     rightPos = l
                   }) in
        let rec trySubst
          ((stack, (((TOKEN (term, (_, l, r)) as orig), lexer) as lexPair)),
           queuePos)
          =
          if noShift term
          then []
          else
            catList terms
              (function
               | t ->
                   tryChange
                     {
                       lex = (Streamm.get lexer);
                       stack;
                       pos = queuePos;
                       leftPos = l;
                       rightPos = r;
                       orig = [orig];
                       new__ = [tokAt (t, r)]
                     }) in
        let rec do_delete =
          function
          | (nil, ((TOKEN (_, (_, l, _)), _) as lp)) -> SOME (nil, l, l, lp)
          | (t::[], ((TOKEN (t', (_, l, r)) as tok), lp')) ->
              if t = t' then SOME ([tok], l, r, (Streamm.get lp')) else NONE
          | (t::rest, ((TOKEN (t', (_, l, r)) as tok), lp')) ->
              if t = t'
              then
                (match do_delete (rest, (Streamm.get lp')) with
                 | SOME (deleted, l', r', lp'') ->
                     SOME ((tok :: deleted), l, r', lp'')
                 | NONE -> NONE)
              else NONE in
        let rec tryPreferred ((stack, lexPair), queuePos) =
          catList preferred_change
            (function
             | (delete, insert) ->
                 ((if List.exists noShift delete
                   then []
                   else
                     (match do_delete (delete, lexPair) with
                      | SOME (deleted, l, r, lp) ->
                          tryChange
                            {
                              lex = lp;
                              stack;
                              pos = queuePos;
                              leftPos = l;
                              rightPos = r;
                              orig = deleted;
                              new__ =
                                (map (function | t -> tokAt (t, r)) insert)
                            }
                      | NONE -> []))
                 (* should give warning at
						 parser-generation time *))) in
        let changes =
          (@) ((@) ((@) ((@) ((@) (catList numStateList tryPreferred) catList
                                numStateList tryInsert)
                           catList numStateList trySubst)
                      catList numStateList (tryDelete 1))
                 catList numStateList (tryDelete 2))
            catList numStateList (tryDelete 3) in
        let findMaxDist =
          function
          | l ->
              foldr
                (function
                 | (CHANGE { distance }, high) -> Int.max (distance, high)) 0
                l in
        let maxDist = findMaxDist changes in
        let changes =
          catList changes
            (function
             | CHANGE { distance } as c ->
                 if distance = maxDist then [c] else []) in
        ((match changes with
          | change::_ as l ->
              let rec print_msg (CHANGE
                { new__; orig; leftPos; rightPos; orig; leftPos; rightPos;
                  leftPos; rightPos; rightPos })
                =
                let s =
                  match (orig, new__) with
                  | (_::_, []) -> "deleting " ^ (showTerms orig)
                  | ([], _::_) -> "inserting " ^ (showTerms new__)
                  | _ ->
                      (("replacing " ^ (showTerms orig)) ^ " with ") ^
                        (showTerms new__) in
                error (("syntax error: " ^ s), leftPos, rightPos) in
              let _ =
                if ((length l) > 1) && DEBUG2
                then
                  (print "multiple fixes possible; could fix it by:\n";
                   app print_msg l;
                   print "chosen correction:\n")
                else ();
                print_msg change in
              let findNth =
                function
                | n ->
                    let rec f =
                      function
                      | (h::t, 0) -> (h, (rev t))
                      | (h::t, n) -> f (t, (n - 1))
                      | (nil, _) -> let exception FindNth  in raise FindNth in
                    f ((rev stateList), n) in
              let CHANGE { pos; orig; new__; orig; new__; new__ } = change in
              let (last, queueFront) = findNth pos in
              let (stack, lexPair) = last in
              let lp1 =
                foldl (function | (_, (_, r)) -> Streamm.get r) lexPair orig in
              let lp2 =
                foldr (function | (t, r) -> (t, (Streamm.cons r))) lp1 new__ in
              let restQueue =
                Fifo.put
                  ((stack, lp2), (foldl Fifo.put Fifo.empty queueFront)) in
              let (lexPair, stack, queue, _, _) =
                distanceParse (lp2, stack, restQueue, pos) in
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
          | nil ->
              (error
                 (("syntax error found at " ^ (showTerminal term)), leftPos,
                   leftPos);
               raise ParseError))
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
      function
      | { arg; table; lexer; saction; void; lookahead;
          ec = (({ showTerminal } : ('a, 'b) ecRecord) as ec); table;
          lexer; saction; void; lookahead;
          ec = (({ showTerminal } : ('a, 'b) ecRecord) as ec); lexer;
          saction; void; lookahead;
          ec = (({ showTerminal } : ('a, 'b) ecRecord) as ec); saction;
          void; lookahead;
          ec = (({ showTerminal } : ('a, 'b) ecRecord) as ec); void;
          lookahead; ec = (({ showTerminal } : ('a, 'b) ecRecord) as ec);
          lookahead; ec = (({ showTerminal } : ('a, 'b) ecRecord) as ec);
          ec = (({ showTerminal } : ('a, 'b) ecRecord) as ec) } ->
          let distance = 15 in
          let minAdvance = 1 in
          let maxAdvance = Int.max (lookahead, 0) in
          let lexPair = Streamm.get lexer in
          let (TOKEN (_, (_, leftPos, _)), _) = lexPair in
          let startStack = [((initialState table), (void, leftPos, leftPos))] in
          let startQueue = Fifo.put ((startStack, lexPair), Fifo.empty) in
          let distanceParse =
            distanceParse (table, showTerminal, saction, arg) in
          let fixError =
            mkFixError (ec, distanceParse, minAdvance, maxAdvance) in
          let ssParse = ssParse (table, showTerminal, saction, fixError, arg) in
          let rec loop =
            function
            | (lexPair, stack, queue, _, SOME (ACCEPT)) ->
                ssParse (lexPair, stack, queue)
            | (lexPair, stack, queue, 0, _) ->
                ssParse (lexPair, stack, queue)
            | (lexPair, stack, queue, distance, SOME (ERROR)) ->
                let (lexPair, stack, queue) =
                  fixError (lexPair, stack, queue) in
                loop (distanceParse (lexPair, stack, queue, distance))
            | _ -> let exception ParseInternal  in raise ParseInternal in
          ((loop (distanceParse (lexPair, startStack, startQueue, distance)))
            (* defer distance tokens *)(* must parse at least 1 token past error *)
            (* max distance for parse check *))
  end ;;
