
module type SYMBOL  =
  sig
    val str : string -> (string * int)
    val evar : string -> (string * int)
    val bvar : string -> (string * int)
    val const : string -> (string * int)
    val label : string -> (string * int)
    val skonst : string -> (string * int)
    val def : string -> (string * int)
    val fvar : string -> (string * int)
    val sym : string -> (string * int)
  end;;




module SymbolAscii() : SYMBOL =
  struct
    let rec idSize s = (s, (String.size s))
    let str = idSize
    let evar = idSize
    let bvar = idSize
    let const = idSize
    let skonst = idSize
    let label = idSize
    let def = idSize
    let rec fvar s = idSize ("`" ^ s)
    let sym = idSize
  end 
module SymbolTeXfp() : SYMBOL =
  struct
    let rec quoteChar =
      function
      | '\\' -> "\\\\"
      | '_' -> "\\_"
      | '$' -> "\\$"
      | '#' -> "\\#"
      | '\'' -> "$'$"
      | '<' -> "$<$"
      | '>' -> "$>$"
      | '^' -> "\\^{\\ }"
      | '0' -> "$_0$"
      | '1' -> "$_1$"
      | '2' -> "$_2$"
      | '3' -> "$_3$"
      | '4' -> "$_4$"
      | '5' -> "$_5$"
      | '6' -> "$_6$"
      | '7' -> "$_7$"
      | '8' -> "$_8$"
      | '9' -> "$_9$"
      | c -> String.str c(* not in math mode *)(* not in math mode *)
      (* not in math mode *)
    let rec quote s = String.translate quoteChar s
    let rec str s = ((((^) "\\Str{" quote s) ^ "}"), (String.size s))
    let rec evar s = ((((^) "\\EVar{" quote s) ^ "}"), (String.size s))
    let rec bvar s = ((((^) "\\BVar{" quote s) ^ "}"), (String.size s))
    let rec const s = ((((^) "\\Const{" quote s) ^ "}"), (String.size s))
    let rec label s = ((((^) "\\Label{" quote s) ^ "}"), (String.size s))
    let rec skonst s = ((((^) "\\Skonst{" quote s) ^ "}"), (String.size s))
    let rec def s = ((((^) "\\Def{" quote s) ^ "}"), (String.size s))
    let rec fvar s = ((((^) "\\FVar{" quote s) ^ "}"), (String.size s))
    let rec sym =
      function
      | "->" -> ("$\\rightarrow$", 1)
      | "<-" -> ("$\\leftarrow$", 1)
      | "{" -> ("$\\Pi$", 1)
      | "}" -> (".", 1)
      | "[" -> ("$\\lambda$", 1)
      | "]" -> (".", 1)
      | "type" -> ("{\\Type}", 4)
      | "kind" -> ("{\\Kind}", 4)
      | "_" -> ("\\_", 1)
      | "..." -> ("$\\ldots$", 3)
      | "%%" -> ("%%", 2)
      | "%skolem" -> ("%skolem", 7)
      | s -> (s, (String.size s))(* itself, for now *)
      (* itself, for now *)
  end 
module SymbolTeX() : SYMBOL =
  struct
    let rec quoteChar =
      function
      | '\\' -> "\\\\"
      | '_' -> "\\_"
      | '$' -> "\\$"
      | '#' -> "\\#"
      | '^' -> "\\^{\\ }"
      | '0' -> "$_0$"
      | '1' -> "$_1$"
      | '2' -> "$_2$"
      | '3' -> "$_3$"
      | '4' -> "$_4$"
      | '5' -> "$_5$"
      | '6' -> "$_6$"
      | '7' -> "$_7$"
      | '8' -> "$_8$"
      | '9' -> "$_9$"
      | c -> String.str c
    let rec quote s = String.translate quoteChar s
    let rec str s = ((((^) "\\Str{" quote s) ^ "}"), (String.size s))
    let rec evar s = ((((^) "\\EVar{" quote s) ^ "}"), (String.size s))
    let rec bvar s = ((((^) "\\BVar{" quote s) ^ "}"), (String.size s))
    let rec const s = ((((^) "\\Const{" quote s) ^ "}"), (String.size s))
    let rec label s = ((((^) "\\Label{" quote s) ^ "}"), (String.size s))
    let rec skonst s = ((((^) "\\Skonst{" quote s) ^ "}"), (String.size s))
    let rec def s = ((((^) "\\Def{" quote s) ^ "}"), (String.size s))
    let rec fvar s = ((((^) "\\FVar{" quote s) ^ "}"), (String.size s))
    let rec sym =
      function
      | "->" -> ("$\\rightarrow$", 1)
      | "<-" -> ("$\\leftarrow$", 1)
      | "{" -> ("$\\Pi$", 1)
      | "}" -> (".", 1)
      | "[" -> ("$\\lambda$", 1)
      | "]" -> (".", 1)
      | "type" -> ("{\\Type}", 4)
      | "kind" -> ("{\\Kind}", 4)
      | "_" -> ("\\_", 1)
      | "..." -> ("$\\ldots$", 3)
      | "%%" -> ("%%", 2)
      | "%skolem" -> ("%skolem", 7)
      | s -> (s, (String.size s))(* itself, for now *)
      (* itself, for now *)
  end ;;
