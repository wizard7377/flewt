
module type SIGNAT  =
  sig
    type nonrec 'phantom sgn
    val empty : unit -> 'phantom sgn
    val insert : 'phantom sgn -> Syntax.const -> Syntax.dec -> 'phantom sgn
    val lookup : 'phantom sgn -> Syntax.const -> Syntax.dec
    val size : 'phantom sgn -> int
  end;;




module type SIGNAT  =
  sig
    type nonrec key
    type nonrec 'a sgn
    exception Signat of string 
    val empty : unit -> 'a sgn
    val insert : 'a sgn -> key -> 'a -> 'a sgn
    val lookup : 'a sgn -> key -> 'a
    val size : 'a sgn -> int
  end
module ListSignat : SIGNAT =
  struct
    module L = Lib
    type nonrec key = int
    type nonrec 'a sgn = (key * 'a) list
    exception Signat of string 
    let rec empty () = []
    let rec insert sgn ((k, a) as p) =
      if L.exists (fun k' -> fun _ -> k = k') sgn
      then raise (Signat "insert: signat contains key")
      else p :: sgn
    let rec lookup sgn x =
      match L.assoc x sgn with
      | Some y -> y
      | NONE -> raise (Signat "lookup: no such key")
    let rec size l = length l
  end 
module GrowarraySignat : SIGNAT =
  struct
    module L = Lib
    module G = GrowArray
    type nonrec key = int
    type nonrec 'a sgn = < arr: 'a G.growarray  ;size: int ref   > 
    exception Signat of string 
    let size = ref 0
    let rec empty () = { arr = (G.empty ()); size = (ref 0) }
    let rec insert sgn n v =
      if (G.length ((fun r -> r.arr) sgn)) > n
      then raise (Signat "insert: signat contains key")
      else
        (G.update ((fun r -> r.arr) sgn) n v;
         if (!) ((>) n) (((fun r -> r.size)) sgn)
         then ((fun r -> r.size) sgn) := n
         else ();
         sgn)
    let rec lookup sgn n = G.sub ((fun r -> r.arr) sgn) n
    let rec size sgn = !((fun r -> r.size) sgn)
  end  module Signat = GrowarraySignat;;
