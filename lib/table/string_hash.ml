module type STRING_HASH  = sig val stringHash : string -> int end


module StringHash : STRING_HASH =
  struct
    let rec stringHash s =
      let rec num i = Char.code (String.get s i) mod 128 in
      let n = String.length s in if n = 0 then begin 0 end
        else begin
          (let a = n - 1 in
           let b = n / 2 in
           let c = b / 2 in
           let d = b + c in
           ((num a) + 128) *
             (((num b) + 128) * ( ((num c) + 128) * num d))) end(* sample 4 characters from string *)
end
