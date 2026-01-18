(* Order type for comparisons - re-exported from Time module *)
type order = Time.order = LESS | EQUAL | GREATER

module type STRING_CVT = StringCvt.STRING_CVT
module StringCvt : StringCvt.STRING_CVT = StringCvt.StringCvt

module type TIME = Time.TIME
module Time : Time.TIME = Time.Time
