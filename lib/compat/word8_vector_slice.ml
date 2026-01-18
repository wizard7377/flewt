
;;




module type MONO_VECTOR_SLICE  =
  sig
    type nonrec slice
    type nonrec vector
    val slice : (vector * int * int option) -> slice
    val vector : slice -> vector
    val full : vector -> slice
  end
module Word8VectorSlice : MONO_VECTOR_SLICE =
  struct
    type nonrec vector = Word8Vector.vector
    type nonrec slice = (Word8Vector.vector * int * int option)
    let rec slice s = s
    let vector = Word8Vector.extract
    let rec full v = (v, 0, None)
  end 
module type COMPAT_WORD8_VECTOR_SLICE  =
  sig val full : Word8Vector.vector -> Word8VectorSlice.slice end
(* Compatibility shim from Basis-02 Word8VectorSlice to Basis-97 Word8Vector *)
(* Author: Christopher Richards *)
module Word8VectorSlice97 : COMPAT_WORD8_VECTOR_SLICE =
  struct
    type nonrec vector = Word8Vector.vector
    type nonrec slice = Word8VectorSlice.slice
    let full = Word8VectorSlice.full
  end ;;
