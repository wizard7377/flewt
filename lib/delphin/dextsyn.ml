
(* Delphin external syntax *)
module type DEXTSYN  =
  sig
    (* structure Lexer : LEXER *)
    type __Ast =
      | Ast of __Decs 
    and __Decs =
      | Empty 
      | FunDecl of (__FunDecl * __Decs) 
      | FormDecl of (__FormDecl * __Decs) 
      | ValDecl of (__ValDecl * __Decs) 
      | NewDecl of (__Dec * __Decs) 
      | TwelfDecl of (__Dec * __Decs) 
      | CreateDecl of (__CreateDecl * __Decs) 
    and __CreateDecl =
      | Create of (__Term * __CreateDecl) 
      | Decs of __Decs 
    and __FormDecl =
      | Form of (string * __Form) 
    and __FunDecl =
      | Fun of (__Head * __Prog) 
      | Bar of (__Head * __Prog) 
      | FunAnd of (__Head * __Prog) 
    and __ValDecl =
      | Val of (__Pat * __Prog * __Form option) 
    and __World =
      | WorldIdent of string 
      | Plus of (__World * __World) 
      | Concat of (__World * __World) 
      | Times of __World 
    and __Form =
      | True 
      | Forall of (__Dec * __Form) 
      | ForallOmitted of (__Dec * __Form) 
      | Exists of (__Dec * __Form) 
      | ExistsOmitted of (__Dec * __Form) 
      | And of (__Form * __Form) 
      | World of (__World * __Form) 
    and __Prog =
      | Unit 
      | Pair of (__Prog * __Prog) 
      | AppProg of (__Prog * __Prog) 
      | AppTerm of (__Prog * __Term) 
      | Inx of (__Term * __Prog) 
      | Lam of (__Dec * __Prog) 
      | Const of string 
      | Case of (__Pat list * __Prog) list 
      | Let of (__Decs * __Prog) 
      | Par of (__Prog * __Prog) 
      | New of (__Dec list * __Prog) 
      | Choose of (__Dec * __Prog) 
    and __Cases =
      | First of (__Pat * __Prog) 
      | Alt of (__Cases * __Pat * __Prog) 
    and __Head =
      | Head of string 
      | AppLF of (__Head * __Term) 
      | AppMeta of (__Head * __Pat) 
    and __Pat =
      | PatInx of (__Term * __Pat) 
      | PatPair of (__Pat * __Pat) 
      | PatVar of __MDec 
      | PatUnderscore 
      | PatUnit 
    and __MDec =
      | MDec of (string * __Form option) 
    and __Block =
      | Block of string list 
    and __Term =
      | Rtarrow of (__Term * __Term) 
      | Ltarrow of (__Term * __Term) 
      | Type 
      | Id of string 
      | Pi of (__Dec * __Term) 
      | Fn of (__Dec * __Term) 
      | App of (__Term * __Term) 
      | Dot of (__Term * string) 
      | Paren of __Term 
      | Omit 
      | Of of (__Term * __Term) 
    and __Dec =
      | Dec of (string * __Term) 
  end;;




(* Delphin external syntax *)
(* Author: Richard Fontana *)
module DextSyn(DextSyn:sig
                         (* structure Stream' : STREAM *)
                         module ExtSyn' : EXTSYN
                         module Parsing' : PARSING
                       end) : DEXTSYN =
  struct
    (*                    sharing Parsing'.Lexer.Paths = ExtSyn'.Paths  *)
    (*                  structure Lexer' : LEXER *)
    (*                    sharing Lexer' = Parsing'.Lexer *)
    (*  structure Stream = Stream' *)
    module ExtSyn = ExtSyn'
    module Parsing = Parsing'
    (*  structure Paths = ExtSyn.Paths
  structure Lexer = Lexer' *)
    module L = Lexer
    (*  structure S = Parsing'.Lexer.Stream *)
    module S = Stream
    type __Ast =
      | Ast of __Decs 
    and __Decs =
      | Empty 
      | FunDecl of (__FunDecl * __Decs) 
      | FormDecl of (__FormDecl * __Decs) 
      | ValDecl of (__ValDecl * __Decs) 
      | NewDecl of (__Dec * __Decs) 
      | TwelfDecl of (__Dec * __Decs) 
      | CreateDecl of (__CreateDecl * __Decs) 
    and __CreateDecl =
      | Create of (__Term * __CreateDecl) 
      | Decs of __Decs 
    and __FormDecl =
      | Form of (string * __Form) 
    and __FunDecl =
      | Fun of (__Head * __Prog) 
      | Bar of (__Head * __Prog) 
      | FunAnd of (__Head * __Prog) 
    and __ValDecl =
      | Val of (__Pat * __Prog * __Form option) 
    and __Cases =
      | First of (__Pat * __Prog) 
      | Alt of (__Cases * __Pat * __Prog) 
    and __World =
      | WorldIdent of string 
      | Plus of (__World * __World) 
      | Concat of (__World * __World) 
      | Times of __World 
    and __Form =
      | True 
      | Forall of (__Dec * __Form) 
      | ForallOmitted of (__Dec * __Form) 
      | Exists of (__Dec * __Form) 
      | ExistsOmitted of (__Dec * __Form) 
      | And of (__Form * __Form) 
      | World of (__World * __Form) 
    and __Prog =
      | Unit 
      | Pair of (__Prog * __Prog) 
      | AppProg of (__Prog * __Prog) 
      | AppTerm of (__Prog * __Term) 
      | Inx of (__Term * __Prog) 
      | Lam of (__Dec * __Prog) 
      | Par of (__Prog * __Prog) 
      | Const of string 
      | Case of (__Pat list * __Prog) list 
      | Let of (__Decs * __Prog) 
      | New of (__Dec list * __Prog) 
      | Choose of (__Dec * __Prog) 
    and __Head =
      | Head of string 
      | AppLF of (__Head * __Term) 
      | AppMeta of (__Head * __Pat) 
    and __Pat =
      | PatInx of (__Term * __Pat) 
      | PatPair of (__Pat * __Pat) 
      | PatVar of __MDec 
      | PatUnderscore 
      | PatUnit 
    and __MDec =
      | MDec of (string * __Form option) 
    and __Block =
      | Block of string list 
    and __Term =
      | Rtarrow of (__Term * __Term) 
      | Ltarrow of (__Term * __Term) 
      | Type 
      | Id of string 
      | Pi of (__Dec * __Term) 
      | Fn of (__Dec * __Term) 
      | App of (__Term * __Term) 
      | Dot of (__Term * string) 
      | Paren of __Term 
      | Omit 
      | Of of (__Term * __Term) 
    and __Dec =
      | Dec of (string * __Term) 
  end ;;
