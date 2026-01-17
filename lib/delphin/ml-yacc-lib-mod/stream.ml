
module Streamm : STREAMM =
  struct
    type 'a str =
      | EVAL of
      ((('a)(* Stream: a structure implementing a lazy stream.  The signature STREAM
   is found in base.sig *)
      (* ML-Yacc Parser Generator (c) 1989 Andrew W. Appel, David R. Tarditi 
 *
 * $Log: not supported by cvs2svn $
 * Revision 1.1.2.1  2003/01/14 22:46:39  carsten_lf
 * delphin frontend added
 *
 * Revision 1.1  2001/11/12 23:23:09  carsten
 * mlyacc hack included
 *
 * Revision 1.1.1.1  1999/12/03 19:59:22  dbm
 * Import of 110.0.6 src
 *
 * Revision 1.2  1997/08/26 19:18:55  jhr
 *   Replaced used of "abstraction" with ":>".
 *
# Revision 1.1.1.1  1997/01/14  01:38:04  george
#   Version 109.24
#
 * Revision 1.1.1.1  1996/01/31  16:01:43  george
 * Version 109
 * 
 *))
      * 'a str ref) 
      | UNEVAL of (unit -> 'a) 
    type nonrec 'a stream = 'a str ref
    let rec get =
      function
      | ref (EVAL t) -> t
      | ref (UNEVAL f) as s ->
          let t = ((f ()), (ref (UNEVAL f))) in ((:=) s EVAL t; t)
    let rec streamify f = ref (UNEVAL f)
    let rec cons (a, s) = ref (EVAL (a, s))
  end ;;
