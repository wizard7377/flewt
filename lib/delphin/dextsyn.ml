module type DEXTSYN  =
  sig
    type ast_ =
      | Ast of decs_ 
    and decs_ =
      | Empty 
      | FunDecl of (funDecl_ * decs_) 
      | FormDecl of (formDecl_ * decs_) 
      | ValDecl of (valDecl_ * decs_) 
      | NewDecl of (dec_ * decs_) 
      | TwelfDecl of (dec_ * decs_) 
      | CreateDecl of (createDecl_ * decs_) 
    and createDecl_ =
      | Create of (term_ * createDecl_) 
      | Decs of decs_ 
    and formDecl_ =
      | Form of (string * form_) 
    and funDecl_ =
      | Fun of (head_ * prog_) 
      | Bar of (head_ * prog_) 
      | FunAnd of (head_ * prog_) 
    and valDecl_ =
      | Val of (pat_ * prog_ * form_ option) 
    and world_ =
      | WorldIdent of string 
      | Plus of (world_ * world_) 
      | Concat of (world_ * world_) 
      | Times of world_ 
    and form_ =
      | True 
      | Forall of (dec_ * form_) 
      | ForallOmitted of (dec_ * form_) 
      | Exists of (dec_ * form_) 
      | ExistsOmitted of (dec_ * form_) 
      | And of (form_ * form_) 
      | World of (world_ * form_) 
    and prog_ =
      | Unit 
      | Pair of (prog_ * prog_) 
      | AppProg of (prog_ * prog_) 
      | AppTerm of (prog_ * term_) 
      | Inx of (term_ * prog_) 
      | Lam of (dec_ * prog_) 
      | Const of string 
      | Case of (pat_ list * prog_) list 
      | Let of (decs_ * prog_) 
      | Par of (prog_ * prog_) 
      | New of (dec_ list * prog_) 
      | Choose of (dec_ * prog_) 
    and cases_ =
      | First of (pat_ * prog_) 
      | Alt of (cases_ * pat_ * prog_) 
    and head_ =
      | Head of string 
      | AppLF of (head_ * term_) 
      | AppMeta of (head_ * pat_) 
    and pat_ =
      | PatInx of (term_ * pat_) 
      | PatPair of (pat_ * pat_) 
      | PatVar of mDec_ 
      | PatUnderscore 
      | PatUnit 
    and mDec_ =
      | MDec of (string * form_ option) 
    and block_ =
      | Block of string list 
    and term_ =
      | Rtarrow of (term_ * term_) 
      | Ltarrow of (term_ * term_) 
      | Type 
      | Id of string 
      | Pi of (dec_ * term_) 
      | Fn of (dec_ * term_) 
      | App of (term_ * term_) 
      | Dot of (term_ * string) 
      | Paren of term_ 
      | Omit 
      | Of of (term_ * term_) 
    and dec_ =
      | Dec of (string * term_) 
  end


module DextSyn(DextSyn:sig module ExtSyn' : EXTSYN module Parsing' : PARSING
                       end) : DEXTSYN =
  struct
    module ExtSyn = ExtSyn'
    module Parsing = Parsing'
    module L = Lexer
    module S = Stream
    type ast_ =
      | Ast of decs_ 
    and decs_ =
      | Empty 
      | FunDecl of (funDecl_ * decs_) 
      | FormDecl of (formDecl_ * decs_) 
      | ValDecl of (valDecl_ * decs_) 
      | NewDecl of (dec_ * decs_) 
      | TwelfDecl of (dec_ * decs_) 
      | CreateDecl of (createDecl_ * decs_) 
    and createDecl_ =
      | Create of (term_ * createDecl_) 
      | Decs of decs_ 
    and formDecl_ =
      | Form of (string * form_) 
    and funDecl_ =
      | Fun of (head_ * prog_) 
      | Bar of (head_ * prog_) 
      | FunAnd of (head_ * prog_) 
    and valDecl_ =
      | Val of (pat_ * prog_ * form_ option) 
    and cases_ =
      | First of (pat_ * prog_) 
      | Alt of (cases_ * pat_ * prog_) 
    and world_ =
      | WorldIdent of string 
      | Plus of (world_ * world_) 
      | Concat of (world_ * world_) 
      | Times of world_ 
    and form_ =
      | True 
      | Forall of (dec_ * form_) 
      | ForallOmitted of (dec_ * form_) 
      | Exists of (dec_ * form_) 
      | ExistsOmitted of (dec_ * form_) 
      | And of (form_ * form_) 
      | World of (world_ * form_) 
    and prog_ =
      | Unit 
      | Pair of (prog_ * prog_) 
      | AppProg of (prog_ * prog_) 
      | AppTerm of (prog_ * term_) 
      | Inx of (term_ * prog_) 
      | Lam of (dec_ * prog_) 
      | Par of (prog_ * prog_) 
      | Const of string 
      | Case of (pat_ list * prog_) list 
      | Let of (decs_ * prog_) 
      | New of (dec_ list * prog_) 
      | Choose of (dec_ * prog_) 
    and head_ =
      | Head of string 
      | AppLF of (head_ * term_) 
      | AppMeta of (head_ * pat_) 
    and pat_ =
      | PatInx of (term_ * pat_) 
      | PatPair of (pat_ * pat_) 
      | PatVar of mDec_ 
      | PatUnderscore 
      | PatUnit 
    and mDec_ =
      | MDec of (string * form_ option) 
    and block_ =
      | Block of string list 
    and term_ =
      | Rtarrow of (term_ * term_) 
      | Ltarrow of (term_ * term_) 
      | Type 
      | Id of string 
      | Pi of (dec_ * term_) 
      | Fn of (dec_ * term_) 
      | App of (term_ * term_) 
      | Dot of (term_ * string) 
      | Paren of term_ 
      | Omit 
      | Of of (term_ * term_) 
    and dec_ =
      | Dec of (string * term_) 
  end 