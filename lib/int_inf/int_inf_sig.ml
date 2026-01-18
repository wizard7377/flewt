
(* int-inf-sig.sml
 *
 * COPYRIGHT (c) 1995 by AT&T Bell Laboratories.  See COPYRIGHT file for details.
 *
 * This package is derived from Andrzej Filinski's bignum package.  It is versy
 * close to the definition of the optional IntInf structure in the SML'97 basis.
 *)
open Base
module type INT_INF  =
  sig
    include Int.S
    val divmod : (int * int) -> (int * int)
    val quotrem : (int * int) -> (int * int)
    val pow : (int * Int.t) -> int
    val log2 : int -> Int.t
  end;;

