
module type Interpreter  =
  sig
    val run :
      FunSyn.__Pro ->
        ((FunSyn.__Pro)(*! structure FunSyn : FUNSYN !*)
        (* Author: Carsten Schuermann *)(* Operational semantics *))
  end;;
