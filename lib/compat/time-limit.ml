
module type TIME_LIMIT  =
  sig
    exception TimeOut 
    val timeLimit : Time.time option -> ('a -> 'b) -> 'a -> 'b
  end;;




module TimeLimit : TIME_LIMIT =
  struct
    exception TimeOut (* Ignores time limit *)(* Default implementation of timeLimit *)
    let timeLimit = function | t -> (function | f -> (function | x -> f x))
  end ;;
