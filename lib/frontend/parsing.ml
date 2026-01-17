
module type PARSING  =
  sig
    module Stream :
    ((STREAM)(* General basis for parsing modules *)
    (* Author: Frank Pfenning *))
    type nonrec lexResult =
      (((Lexer.__Token)(*
  structure Lexer : LEXER
    sharing Lexer.Stream = Stream
  *))
        * Paths.region)
    type nonrec 'a parser =
      lexResult Stream.front -> ('a * lexResult Stream.front)
    type 'a __RecParseResult =
      | Done of
      (('a)(* recursive parser (allows parsing functions that need to parse
     a signature expression to temporarily suspend themselves) *))
      
      | Continuation of 'a __RecParseResult parser 
    type nonrec 'a recparser = 'a __RecParseResult parser
    val recwith :
      ('a recparser * ('a -> 'b)) ->
        (('b)(* useful combinator for recursive parsers *))
          recparser
    exception Error of string 
    val error : (Paths.region * string) -> 'a
  end;;




module Parsing(Parsing:sig module Stream' : STREAM end) : PARSING =
  struct
    module Stream = Stream'
    type nonrec lexResult = (Lexer.__Token * Paths.region)
    type nonrec 'a parser =
      lexResult Stream.front -> ('a * lexResult Stream.front)
    type 'a __RecParseResult =
      | Done of 'a 
      | Continuation of 'a __RecParseResult parser 
    type nonrec 'a recparser = 'a __RecParseResult parser
    let rec recwith (recparser, func) f =
      match recparser f with
      | (Done x, f') -> ((Done (func x)), f')
      | (Continuation k, f') -> ((Continuation (recwith (k, func))), f')
    exception Error of string 
    let rec error (r, msg) = raise (Error (Paths.wrap (r, msg)))
  end 
module Parsing =
  (Make_Parsing)(struct
                   module Stream' =
                     ((Stream)(*! structure Lexer' : LEXER !*)(*! sharing Lexer'.Stream = Stream' !*)
                     (*! structure Lexer = Lexer' !*)
                     (* functor Parsing *))
                 end);;
