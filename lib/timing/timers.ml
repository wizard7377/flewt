
module type TIMERS  =
  sig
    module Timing :
    ((TIMING)(* Timers collecting statistics about Twelf *)
    (* Author: Frank Pfenning *))
    val parsing :
      ((Timing.center)(* Programming interface *))
    val recon : ((Timing.center)(* lexing and parsing *))
    val abstract :
      ((Timing.center)(* term reconstruction *))
    val checking :
      ((Timing.center)(* abstraction after reconstruction *))
    val modes :
      ((Timing.center)(* redundant type-checking *))
    val subordinate : ((Timing.center)(* mode checking *))
    val printing :
      ((Timing.center)(* construction subordination relation *))
    val compiling : ((Timing.center)(* printing *))
    val solving : ((Timing.center)(* compilation *))
    val coverage : ((Timing.center)(* solving queries *))
    val worlds : ((Timing.center)(* coverage checking *))
    val ptrecon : ((Timing.center)(* world checking *))
    val filling :
      ((Timing.center)(* solving queries using ptskeleon *))
    val filltabled : ((Timing.center)(* filling in m2 *))
    val recursion : ((Timing.center)(* filling in m2 *))
    val splitting : ((Timing.center)(* recursion in m2 *))
    val inference : ((Timing.center)(* splitting in m2 *))
    val terminate : ((Timing.center)(* inference in m2 *))
    val delphin :
      ((Timing.center)(* checking termination *))
    val total :
      ((Timing.sum)(* Warning: time for printing of the answer substitution to a
     query is counted twice here.
  *)
        (* Operational Semantics of Delphin *))
    val time :
      Timing.center ->
        ('a -> 'b) ->
          'a ->
            (('b)(* time center f x = y
     if f x = y and time of computing f x is added to center.
     If f x raises an exception, it is re-raised.
  *)
            (* total time *))
    val reset : unit -> ((unit)(* External interface *))
    val check : unit -> ((unit)(* reset above centers *))
    val show : unit -> ((unit)(* check timer values *))
  end;;




module Timers(Timers:sig
                       module Timing' :
                       ((TIMING)(* Timers collecting statistics about Twelf *)
                       (* Author: Frank Pfenning *))
                     end) : TIMERS =
  struct
    module Timing = Timing'
    let parsing = Timing.newCenter "Parsing       "
    let recon = Timing.newCenter "Reconstruction"
    let abstract = Timing.newCenter "Abstraction   "
    let checking = Timing.newCenter "Checking      "
    let modes = Timing.newCenter "Modes         "
    let subordinate = Timing.newCenter "Subordination "
    let terminate = Timing.newCenter "Termination   "
    let printing = Timing.newCenter "Printing      "
    let compiling = Timing.newCenter "Compiling     "
    let solving = Timing.newCenter "Solving       "
    let coverage = Timing.newCenter "Coverage      "
    let worlds = Timing.newCenter "Worlds        "
    let ptrecon = Timing.newCenter "ProofRecon    "
    let filling = Timing.newCenter "Filling       "
    let filltabled = Timing.newCenter "Filling Tabled"
    let splitting = Timing.newCenter "Splitting     "
    let recursion = Timing.newCenter "Recursion     "
    let inference = Timing.newCenter "Inference     "
    let delphin = Timing.newCenter "Delphin       "
    let centers =
      [parsing;
      recon;
      abstract;
      checking;
      modes;
      subordinate;
      terminate;
      printing;
      compiling;
      solving;
      coverage;
      worlds;
      ptrecon;
      filling;
      filltabled;
      splitting;
      recursion;
      inference;
      delphin]
    let total = Timing.sumCenter ("Total         ", centers)
    let time = Timing.time
    let rec reset () = List.app Timing.reset centers
    let rec check () =
      List.app (print o Timing.toString) centers;
      print (Timing.sumToString total);
      print "Remember that the success continuation counts into Solving!\n"
    let rec show () = check (); reset ()
  end ;;




module Timers =
  (Make_Timers)(struct
                  module Timing' =
                    ((Timing)(* Timers *)(* Author: Frank Pfenning *))
                end);;
