module Word8ArraySlice : MONO_ARRAY_SLICE =
  struct
    type nonrec array = Word8Array.array
    type nonrec slice = (Word8Array.array * int * int option)
    type nonrec vector = Word8Array.vector
    let rec slice s = s
    let vector = Word8Array.extract
  end 