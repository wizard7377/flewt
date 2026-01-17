
module ReconTerm =
  (Make_ReconTerm)(struct
                     module Names =
                       ((Names)(* Front End Interface *)
                       (* Author: Frank Pfenning *)(* Presently, we do not memoize the token stream returned *)
                       (* by the lexer.  Use Stream = MStream below if memoization becomes *)
                       (* necessary. *)(* Now in lexer.fun *)
                       (*
structure Lexer =
  Lexer (structure Stream' = Stream
	 structure Paths' = Paths);
*)
                       (* Now in parsing.fun *)(*
structure Parsing =
  Parsing (structure Stream' = Stream
	   structure Lexer' = Lexer);
*)
                       (*! structure IntSyn' = IntSyn !*))
                     module Approx =
                       ((Approx)(*! structure Paths' = Paths !*))
                     module Whnf = Whnf
                     module Unify = UnifyTrail
                     module Abstract = Abstract
                     module Print = Print
                     module StringTree =
                       ((StringRedBlackTree)(*! structure CSManager = CSManager !*))
                     module Msg = Msg
                   end)
module ReconConDec =
  (Make_ReconConDec)(struct
                       module Global = Global
                       module Names =
                         ((Names)(*! structure IntSyn' = IntSyn !*))
                       module Abstract = Abstract
                       module ReconTerm' =
                         ((ReconTerm)(*! structure Paths' = Paths !*))
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
                      module Names =
                        ((Names)(*! structure IntSyn' = IntSyn !*))
                      module Abstract = Abstract
                      module ReconTerm' =
                        ((ReconTerm)(*! structure Paths' = Paths !*))
                      module TypeCheck = TypeCheck
                      module Strict = Strict
                      module Timers = Timers
                      module Print = Print
                    end)
module ReconMode =
  (Make_ReconMode)(struct
                     module Global = Global
                     module Whnf =
                       ((Whnf)(*! structure ModeSyn' = ModeSyn !*))
                     module Names =
                       ((Names)(*! structure Paths' = Paths !*))
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
                    module Names =
                      ((Names)(*! structure ModeSyn = ModeSyn !*))
                    module ThmSyn' =
                      ((ThmSyn)(*! structure Paths' = Paths !*))
                    module ReconTerm' = ReconTerm
                    module Print = Print
                  end)
module ReconModule =
  (Make_ReconModule)(struct
                       module Global = Global
                       module IntSyn = IntSyn
                       module Names = Names
                       module ReconTerm' =
                         ((ReconTerm)(*! structure Paths' = Paths !*))
                       module ModSyn' = ModSyn
                       module IntTree = IntRedBlackTree
                     end)
module ParseTerm =
  (Make_ParseTerm)(struct
                     module ExtSyn' =
                       ((ReconTerm)(*! structure Parsing' = Parsing !*))
                     module Names = Names
                   end)
module ParseConDec =
  (Make_ParseConDec)(struct
                       module ExtConDec' =
                         ((ReconConDec)(*! structure Parsing' = Parsing !*))
                       module ParseTerm = ParseTerm
                     end)
module ParseQuery =
  (Make_ParseQuery)(struct
                      module ExtQuery' =
                        ((ReconQuery)(*! structure Parsing' = Parsing !*))
                      module ParseTerm = ParseTerm
                    end)
module ParseFixity =
  (Make_ParseFixity)(struct
                       module Names' =
                         ((Names)(*! structure Parsing' = Parsing !*))
                     end)
module ParseMode =
  (Make_ParseMode)(struct
                     module ExtModes' =
                       ((ReconMode)(*! structure Parsing' = Parsing !*))
                     module ParseTerm =
                       ((ParseTerm)(*! structure Paths = Paths !*))
                   end)
module ParseThm =
  (Make_ParseThm)(struct
                    module ThmExtSyn' =
                      ((ReconThm)(*! structure Parsing' = Parsing !*))
                    module ParseTerm = ParseTerm
                  end)
module ParseModule =
  (Make_ParseModule)(struct
                       module ModExtSyn' =
                         ((ReconModule)(*! structure Paths = Paths !*)
                         (*! structure Parsing' = Parsing !*))
                       module ParseTerm = ParseTerm
                     end)
module Parser =
  (Make_Parser)(struct
                  module Stream' =
                    ((Stream)(*! structure Paths = Paths !*)
                    (*! structure Parsing' = Parsing !*))
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
                 module Names =
                   ((Names)(*! structure IntSyn' = IntSyn !*))
                 module Parser = Parser
                 module ReconQuery = ReconQuery
                 module Timers = Timers
                 module Compile =
                   ((Compile)(*! structure CompSyn = CompSyn !*))
                 module CPrint = CPrint
                 module AbsMachine =
                   ((SwMachine)(*! structure CSManager = CSManager !*))
                 module PtRecon = PtRecon
                 module AbsMachineSbt = AbsMachineSbt
                 module PtRecon = PtRecon
                 module Tabled =
                   ((Tabled)(*! structure TableParam = TableParam !*))
                 module Print =
                   ((Print)(*	 structure TableIndex = TableIndex *)
                   (*	 structure MemoTable = MemoTable *))
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
                 module Whnf =
                   ((Whnf)(*! structure IntSyn' = IntSyn !*))
                 module Print = Print
                 module Names = Names
                 module Origins =
                   ((Origins)(*! structure Paths = Paths !*))
                 module Lexer = Lexer
                 module Parser =
                   ((Parser)(*! structure Parsing = Parsing !*))
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
                 module Compile =
                   ((Compile)(*! structure CompSyn' = CompSyn !*))
                 module CPrint = CPrint
                 module AbsMachine = SwMachine
                 module Tabled =
                   ((Tabled)(*! structure TableParam = TableParam !*))
                 module Solve = Solve
                 module Fquery = Fquery
                 module StyleCheck = StyleCheck
                 module ThmSyn = ThmSyn
                 module Thm = Thm
                 module ReconThm = ReconThm
                 module ThmPrint = ThmPrint
                 module TabledSyn = TabledSyn
                 module WorldSyn = WorldSyn
                 module Worldify =
                   ((Worldify)(*	 structure WorldPrint = WorldPrint *))
                 module ModSyn = ModSyn
                 module ReconModule = ReconModule
                 module MetaGlobal = MetaGlobal
                 module Skolem =
                   ((Skolem)(*! structure FunSyn = FunSyn !*))
                 module Prover = CombiProver
                 module ClausePrint = ClausePrint
                 module Trace = Trace
                 module PrintTeX = PrintTeX
                 module ClausePrintTeX = ClausePrintTeX
                 module CSManager = CSManager
                 module CSInstaller = CSInstaller
                 module Compat =
                   ((Compat)(* unused -- creates necessary CM dependency *))
                 module UnknownExn = UnknownExn
                 module Msg = Msg
               end);;
