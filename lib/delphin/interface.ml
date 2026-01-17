
module type INTERFACE  =
  sig
    type nonrec pos(* compare to Paths *)(* Author: Richard Fontana *)
    (* Interface for error reporting  syntax *)
    val line : pos ref
    val init_line : unit -> unit
    val next_line : unit -> unit
    val error : (string * pos * pos) -> unit
    type nonrec arg
    val nothing : arg
  end;;




module Interface() : INTERFACE =
  struct
    type nonrec pos = int
    let line = ref 0
    let rec init_line () = line := 1
    let rec next_line () = ((!) ((:=) line) line) + 1
    let rec error (errmsg, (line : pos), _) =
      TextIO.output
        (TextIO.stdOut,
          (((("Line " ^ (Int.toString line)) ^ ": ") ^ errmsg) ^ "\n"))
    type nonrec arg = unit
    let nothing = ()
  end ;;
