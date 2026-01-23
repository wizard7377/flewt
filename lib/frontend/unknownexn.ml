module type UNKNOWN_EXN  = sig val unknownExn : exn -> string end


module UnknownExn(UnknownExn:sig val exnHistory : exn -> string list end) :
  UNKNOWN_EXN =
  struct
    let rec unknownExn exn =
      let history = rev (exnHistory exn) in
      let rec wrap1 x = ("  raised at: " ^ x) ^ "\n" in
      let rec wrapn x = ("             " ^ x) ^ "\n" in
      concat
        ((("Unrecognized exception " :: (exnName exn)) :: "\n") ::
           (begin match history with
            | [] -> [""]
            | x::xs -> (::) (wrap1 x) map wrapn xs end)) end 