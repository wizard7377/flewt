module type PARSING  =
  sig
    module Stream : STREAM
    type nonrec lexResult = (Lexer.token_ * Paths.region)
    type nonrec 'a parser =
      lexResult Stream.front -> ('a * lexResult Stream.front)
    type 'a recParseResult_ =
      | Done of 'a 
      | Continuation of 'a recParseResult_ parser 
    type nonrec 'a recparser = 'a recParseResult_ parser
    val recwith : ('a recparser * ('a -> 'b)) -> 'b recparser
    exception Error of string 
    val error : (Paths.region * string) -> 'a
  end


module Parsing(Parsing:sig module Stream' : STREAM end) : PARSING =
  struct
    module Stream = Stream'
    type nonrec lexResult = (Lexer.token_ * Paths.region)
    type nonrec 'a parser =
      lexResult Stream.front -> ('a * lexResult Stream.front)
    type 'a recParseResult_ =
      | Done of 'a 
      | Continuation of 'a recParseResult_ parser 
    type nonrec 'a recparser = 'a recParseResult_ parser
    let rec recwith (recparser, func) f =
      begin match recparser f with
      | (Done x, f') -> ((Done (func x)), f')
      | (Continuation k, f') -> ((Continuation (recwith (k, func))), f') end
    exception Error of string 
    let rec error (r, msg) = raise (Error (Paths.wrap (r, msg))) end 
module Parsing = (Parsing)(struct module Stream' = Stream end)