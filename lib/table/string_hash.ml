
module type STRING_HASH  = sig val stringHash : string -> int end;;




module StringHash : STRING_HASH =
  struct
    let rec stringHash s =
      let rec num i = Char.ord (String.sub (s, i)) mod__ 128 in
      let n = String.size s in
      if n = 0
      then 0
      else
        (let a = n - 1 in
         let b = n div 2 in
         let c = b div 2 in
         let d = b + c in
         ((num a) + 128) * (((num b) + 128) * (( * ) ((num c) + 128) num d)))
      (* sample 4 characters from string *)
  end ;;
