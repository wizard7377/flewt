
(* Front End Interface *)
(* Author: Frank Pfenning *)
(* Presently, we do not memoize the token stream returned *)
(* by the lexer.  Use Stream = MStream below if memoization becomes *)
(* necessary. *) (* Now in lexer.fun *)
(*
structure Lexer =
  Lexer (structure Stream' = Stream
	 structure Paths' = Paths);
*)
(* Now in parsing.fun *)
(*
structure Parsing =
  Parsing (structure Stream' = Stream
	   structure Lexer' = Lexer);
*)
module ReconTerm =
  (Make_ReconTerm)(struct
                     (*! structure IntSyn' = IntSyn !*)
                     module Names = Names
                     (*! structure Paths' = Paths !*)
                     module Approx = Approx
                     module Whnf = Whnf
                     module Unify = UnifyTrail
                     module Abstract = Abstract
                     module Print = Print
                     (*! structure CSManager = CSManager !*)
                     module StringTree = StringRedBlackTree
                     module Msg = Msg
                   end)
module ReconConDec =
  (Make_ReconConDec)(struct
                       module Global = Global
                       (*! structure IntSyn' = IntSyn !*)
                       module Names = Names
                       module Abstract = Abstract
                       (*! structure Paths' = Paths !*)
                       module ReconTerm' = ReconTerm
                       module Constraints = Constraints
                       module Strict = Strict
                       module TypeCheck = TypeCheck
                       module Timers = Timers
                       module Print = Print
                       module Msg = Msg
                     end)
module ReconQuery =
  (Make_ReconQuery)(struct
                      module Global = Global
                      (*! structure IntSyn' = IntSyn !*)
                      module Names = Names
                      module Abstract = Abstract
                      (*! structure Paths' = Paths !*)
                      module ReconTerm' = ReconTerm
                      module TypeCheck = TypeCheck
                      module Strict = Strict
                      module Timers = Timers
                      module Print = Print
                    end)
module ReconMode =
  (Make_ReconMode)(struct
                     module Global = Global
                     (*! structure ModeSyn' = ModeSyn !*)
                     module Whnf = Whnf
                     (*! structure Paths' = Paths !*)
                     module Names = Names
                     module ModePrint = ModePrint
                     module ModeDec = ModeDec
                     module ReconTerm' = ReconTerm
                   end)
module ReconThm =
  (Make_ReconThm)(struct
                    module Global = Global
                    module IntSyn = IntSyn
                    module Abstract = Abstract
                    module Constraints = Constraints
                    (*! structure ModeSyn = ModeSyn !*)
                    module Names = Names
                    (*! structure Paths' = Paths !*)
                    module ThmSyn' = ThmSyn
                    module ReconTerm' = ReconTerm
                    module Print = Print
                  end)
module ReconModule =
  (Make_ReconModule)(struct
                       module Global = Global
                       module IntSyn = IntSyn
                       module Names = Names
                       (*! structure Paths' = Paths !*)
                       module ReconTerm' = ReconTerm
                       module ModSyn' = ModSyn
                       module IntTree = IntRedBlackTree
                     end)
module ParseTerm =
  (Make_ParseTerm)(struct
                     (*! structure Parsing' = Parsing !*)
                     module ExtSyn' = ReconTerm
                     module Names = Names
                   end)
module ParseConDec =
  (Make_ParseConDec)(struct
                       (*! structure Parsing' = Parsing !*)
                       module ExtConDec' = ReconConDec
                       module ParseTerm = ParseTerm
                     end)
module ParseQuery =
  (Make_ParseQuery)(struct
                      (*! structure Parsing' = Parsing !*)
                      module ExtQuery' = ReconQuery
                      module ParseTerm = ParseTerm
                    end)
module ParseFixity =
  (Make_ParseFixity)(struct
                       (*! structure Parsing' = Parsing !*)
                       module Names' = Names
                     end)
module ParseMode =
  (Make_ParseMode)(struct
                     (*! structure Parsing' = Parsing !*)
                     module ExtModes' = ReconMode
                     (*! structure Paths = Paths !*)
                     module ParseTerm = ParseTerm
                   end)
module ParseThm =
  (Make_ParseThm)(struct
                    (*! structure Parsing' = Parsing !*)
                    module ThmExtSyn' = ReconThm
                    module ParseTerm = ParseTerm
                  end)
module ParseModule =
  (Make_ParseModule)(struct
                       (*! structure Parsing' = Parsing !*)
                       module ModExtSyn' = ReconModule
                       module ParseTerm = ParseTerm
                     end)
module Parser =
  (Make_Parser)(struct
                  (*! structure Parsing' = Parsing !*)
                  module Stream' = Stream
                  module ExtSyn' = ReconTerm
                  module Names' = Names
                  module ExtConDec' = ReconConDec
                  module ExtQuery' = ReconQuery
                  module ExtModes' = ReconMode
                  module ThmExtSyn' = ReconThm
                  module ModExtSyn' = ReconModule
                  module ParseConDec = ParseConDec
                  module ParseQuery = ParseQuery
                  module ParseFixity = ParseFixity
                  module ParseMode = ParseMode
                  module ParseThm = ParseThm
                  module ParseModule = ParseModule
                  module ParseTerm = ParseTerm
                end)
module Solve =
  (Make_Solve)(struct
                 module Global = Global
                 (*! structure IntSyn' = IntSyn !*)
                 module Names = Names
                 module Parser = Parser
                 module ReconQuery = ReconQuery
                 module Timers = Timers
                 (*! structure CompSyn = CompSyn !*)
                 module Compile = Compile
                 module CPrint = CPrint
                 (*! structure CSManager = CSManager !*)
                 module AbsMachine = SwMachine
                 module PtRecon = PtRecon
                 module AbsMachineSbt = AbsMachineSbt
                 module PtRecon = PtRecon
                 (*! structure TableParam = TableParam !*)
                 module Tabled = Tabled
                 (*	 structure TableIndex = TableIndex *)
                 (*	 structure MemoTable = MemoTable *)
                 module Print = Print
                 module Msg = Msg
               end)
module Fquery =
  (Make_Fquery)(struct
                  module Global = Global
                  module Names = Names
                  module ReconQuery = ReconQuery
                  module Timers = Timers
                  module Print = Print
                end)
module Twelf =
  (Make_Twelf)(struct
                 module Global = Global
                 module Timers = Timers
                 (*! structure IntSyn' = IntSyn !*)
                 module Whnf = Whnf
                 module Print = Print
                 module Names = Names
                 (*! structure Paths = Paths !*)
                 module Origins = Origins
                 module Lexer = Lexer
                 (*! structure Parsing = Parsing !*)
                 module Parser = Parser
                 module TypeCheck = TypeCheck
                 module Strict = Strict
                 module Constraints = Constraints
                 module Abstract = Abstract
                 module ReconTerm = ReconTerm
                 module ReconConDec = ReconConDec
                 module ReconQuery = ReconQuery
                 module ModeTable = ModeTable
                 module ModeCheck = ModeCheck
                 module ModeDec = ModeDec
                 module ReconMode = ReconMode
                 module ModePrint = ModePrint
                 module Unique = Unique
                 module UniqueTable = UniqueTable
                 module Cover = Cover
                 module Converter = Converter
                 module TomegaPrint = TomegaPrint
                 module TomegaCoverage = TomegaCoverage
                 module TomegaTypeCheck = TomegaTypeCheck
                 module Total = Total
                 module Reduces = Reduces
                 module Index = Index
                 module IndexSkolem = IndexSkolem
                 module Subordinate = Subordinate
                 (*! structure CompSyn' = CompSyn !*)
                 module Compile = Compile
                 module CPrint = CPrint
                 module AbsMachine = SwMachine
                 (*! structure TableParam = TableParam !*)
                 module Tabled = Tabled
                 module Solve = Solve
                 module Fquery = Fquery
                 module StyleCheck = StyleCheck
                 module ThmSyn = ThmSyn
                 module Thm = Thm
                 module ReconThm = ReconThm
                 module ThmPrint = ThmPrint
                 module TabledSyn = TabledSyn
                 module WorldSyn = WorldSyn
                 (*	 structure WorldPrint = WorldPrint *)
                 module Worldify = Worldify
                 module ModSyn = ModSyn
                 module ReconModule = ReconModule
                 module MetaGlobal = MetaGlobal
                 (*! structure FunSyn = FunSyn !*)
                 module Skolem = Skolem
                 module Prover = CombiProver
                 module ClausePrint = ClausePrint
                 module Trace = Trace
                 module PrintTeX = PrintTeX
                 module ClausePrintTeX = ClausePrintTeX
                 module CSManager = CSManager
                 module CSInstaller = CSInstaller
                 (* unused -- creates necessary CM dependency *)
                 module Compat = Compat
                 module UnknownExn = UnknownExn
                 module Msg = Msg
               end);;
