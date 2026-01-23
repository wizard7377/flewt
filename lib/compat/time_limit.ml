module type TIME_LIMIT  =
  sig
    exception TimeOut 
    val timeLimit : Time.time option -> ('a -> 'b) -> 'a -> 'b
  end


module TimeLimit : TIME_LIMIT =
  struct
    exception TimeOut 
    let timeLimit =
      begin function
      | t -> (begin function | f -> (begin function | x -> f x end) end) end
end
