
(* Operational semantics *)
(* Author: Carsten Schuermann *)
module type Interpreter  =
  sig
    (*! structure FunSyn : FUNSYN !*)
    val run : FunSyn.__Pro -> FunSyn.__Pro
  end;;
