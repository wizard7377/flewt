
module NoTrail : TRAIL =
  struct
    type nonrec 'a trail =
      ((unit)(* Author: Roberto Virga *)(* Not Trailing Abstract Operations *))
    let rec trail () = ()
    let rec suspend ((), copy) = ()
    let rec resume ((), (), reset) = ()
    let rec reset () = ()
    let rec mark () = ()
    let rec unwind ((), undo) = ()
    let rec log ((), action) = ()
  end ;;
