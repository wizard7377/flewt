(* Order type for comparisons *)
type order = LESS | EQUAL | GREATER

module type STRING_CVT

module StringCvt : StringCvt.STRING_CVT

module type TIME

module Time : Time.TIME
