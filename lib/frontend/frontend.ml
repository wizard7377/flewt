module ReconTerm =
  (ReconTerm)(struct
                     module Names = Names
                     module Approx = Approx
                     module Whnf = Whnf
                     module Unify = UnifyTrail
                     module Abstract = Abstract
                     module Print = Print
                     module StringTree = StringRedBlackTree
                     module Msg = Msg
                   end)
module ReconConDec =
  (ReconConDec)(struct
                       module Global = Global
                       module Names = Names
                       module Abstract = Abstract
                       module ReconTerm' = ReconTerm
                       module Constraints = Constraints
                       module Strict = Strict
                       module TypeCheck = TypeCheck
                       module Timers = Timers
                       module Print = Print
                       module Msg = Msg
                     end)
module ReconQuery =
  (ReconQuery)(struct
                      module Global = Global
                      module Names = Names
                      module Abstract = Abstract
                      module ReconTerm' = ReconTerm
                      module TypeCheck = TypeCheck
                      module Strict = Strict
                      module Timers = Timers
                      module Print = Print
                    end)
module ReconMode =
  (ReconMode)(struct
                     module Global = Global
                     module Whnf = Whnf
                     module Names = Names
                     module ModePrint = ModePrint
                     module ModeDec = ModeDec
                     module ReconTerm' = ReconTerm
                   end)
module ReconThm =
  (ReconThm)(struct
                    module Global = Global
                    module IntSyn = IntSyn
                    module Abstract = Abstract
                    module Constraints = Constraints
                    module Names = Names
                    module ThmSyn' = ThmSyn
                    module ReconTerm' = ReconTerm
                    module Print = Print
                  end)
module ReconModule =
  (ReconModule)(struct
                       module Global = Global
                       module IntSyn = IntSyn
                       module Names = Names
                       module ReconTerm' = ReconTerm
                       module ModSyn' = ModSyn
                       module IntTree = IntRedBlackTree
                     end)
module ParseTerm =
  (ParseTerm)(struct module ExtSyn' = ReconTerm
                          module Names = Names end)
module ParseConDec =
  (ParseConDec)(struct
                       module ExtConDec' = ReconConDec
                       module ParseTerm = ParseTerm
                     end)
module ParseQuery =
  (ParseQuery)(struct
                      module ExtQuery' = ReconQuery
                      module ParseTerm = ParseTerm
                    end)
module ParseFixity = (ParseFixity)(struct module Names' = Names end)
module ParseMode =
  (ParseMode)(struct
                     module ExtModes' = ReconMode
                     module ParseTerm = ParseTerm
                   end)
module ParseThm =
  (ParseThm)(struct
                    module ThmExtSyn' = ReconThm
                    module ParseTerm = ParseTerm
                  end)
module ParseModule =
  (ParseModule)(struct
                       module ModExtSyn' = ReconModule
                       module ParseTerm = ParseTerm
                     end)
module Parser =
  (Parser)(struct
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
  (Solve)(struct
                 module Global = Global
                 module Names = Names
                 module Parser = Parser
                 module ReconQuery = ReconQuery
                 module Timers = Timers
                 module Compile = Compile
                 module CPrint = CPrint
                 module AbsMachine = SwMachine
                 module PtRecon = PtRecon
                 module AbsMachineSbt = AbsMachineSbt
                 module PtRecon = PtRecon
                 module Tabled = Tabled
                 module Print = Print
                 module Msg = Msg
               end)
module Fquery =
  (Fquery)(struct
                  module Global = Global
                  module Names = Names
                  module ReconQuery = ReconQuery
                  module Timers = Timers
                  module Print = Print
                end)
module Twelf =
  (Twelf)(struct
                 module Global = Global
                 module Timers = Timers
                 module Whnf = Whnf
                 module Print = Print
                 module Names = Names
                 module Origins = Origins
                 module Lexer = Lexer
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
                 module Compile = Compile
                 module CPrint = CPrint
                 module AbsMachine = SwMachine
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
                 module Worldify = Worldify
                 module ModSyn = ModSyn
                 module ReconModule = ReconModule
                 module MetaGlobal = MetaGlobal
                 module Skolem = Skolem
                 module Prover = CombiProver
                 module ClausePrint = ClausePrint
                 module Trace = Trace
                 module PrintTeX = PrintTeX
                 module ClausePrintTeX = ClausePrintTeX
                 module CSManager = CSManager
                 module CSInstaller = CSInstaller
                 module Compat = Compat
                 module UnknownExn = UnknownExn
                 module Msg = Msg
               end)