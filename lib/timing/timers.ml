module type TIMERS  =
  sig
    module Timing : TIMING
    val parsing : Timing.center
    val recon : Timing.center
    val abstract : Timing.center
    val checking : Timing.center
    val modes : Timing.center
    val subordinate : Timing.center
    val printing : Timing.center
    val compiling : Timing.center
    val solving : Timing.center
    val coverage : Timing.center
    val worlds : Timing.center
    val ptrecon : Timing.center
    val filling : Timing.center
    val filltabled : Timing.center
    val recursion : Timing.center
    val splitting : Timing.center
    val inference : Timing.center
    val terminate : Timing.center
    val delphin : Timing.center
    val total : Timing.sum
    val time : Timing.center -> ('a -> 'b) -> 'a -> 'b
    val reset : unit -> unit
    val check : unit -> unit
    val show : unit -> unit
  end


module Timers(Timers:sig module Timing' : TIMING end) : TIMERS =
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
      begin List.app (print o Timing.toString) centers;
      print (Timing.sumToString total);
      print "Remember that the success continuation counts into Solving!\n" end
    let rec show () = begin check (); reset () end end



module Timers = (Timers)(struct module Timing' = Timing end)