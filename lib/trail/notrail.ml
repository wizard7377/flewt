
(* Not Trailing Abstract Operations *)
(* Author: Roberto Virga *)
module NoTrail : Trail_core.TRAIL =
  struct
    type nonrec 'a trail = unit
    let rec trail () = ()
    let rec suspend ((), copy) = ()
    let rec resume ((), (), reset) = ()
    let rec reset () = ()
    let rec mark () = ()
    let rec unwind ((), undo) = ()
    let rec log ((), action) = ()
  end ;;
 