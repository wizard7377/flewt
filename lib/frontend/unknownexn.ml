
module type UNKNOWN_EXN  = sig val unknownExn : exn -> string end;;




module UnknownExn(UnknownExn:sig
                               val exnHistory :
                                 exn ->
                                   ((string)(* Print an informative message on receipt of an unhandled exception. *))
                                     list
                             end) : UNKNOWN_EXN =
  struct
    let rec unknownExn exn =
      let history = rev (exnHistory exn) in
      let wrap1 x = ("  raised at: " ^ x) ^ "\n" in
      let wrapn x = ("             " ^ x) ^ "\n" in
      concat
        ((("Unrecognized exception " :: (exnName exn)) :: "\n") ::
           (match history with
            | nil -> [""]
            | x::xs -> (::) (wrap1 x) map wrapn xs))
  end ;;
