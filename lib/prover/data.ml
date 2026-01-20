
module type DATA  =
  sig val maxFill : int ref val maxSplit : int ref val maxRecurse : int ref
  end;;




module Data : DATA =
  struct let maxFill = ref 5
         let maxSplit = ref 5
         let maxRecurse = ref 2 end ;;
