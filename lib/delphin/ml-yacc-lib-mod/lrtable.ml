module LrTable : LR_TABLE =
  struct
    open Array
    open List
    type ('a, 'b) pairlist =
      | EMPTY 
      | PAIR of ('a * 'b * ('a, 'b) pairlist) 
    type term =
      | t_ of int [@sml.renamed "t_"][@sml.renamed "t_"]
    type nonterm =
      | NT of int 
    type state =
      | STATE of int 
    type action =
      | SHIFT of state 
      | REDUCE of int 
      | ACCEPT 
      | ERROR 
    exception Goto of (state * nonterm) 
    type nonrec table =
      <
        states: int  ;rules: int  ;initialState: state  ;action: ((term,
                                                                   action)
                                                                   pairlist *
                                                                   action)
                                                                   array  ;
        goto: (nonterm, state) pairlist array   > 
    let numStates = begin function | ({ states } : table) -> states end
    let numRules = begin function | ({ rules } : table) -> rules end
  let describeActions =
    begin function
    | ({ action } : table) -> (begin function | STATE s -> action sub s end) end
let describeGoto =
  begin function
  | ({ goto } : table) -> (begin function | STATE s -> goto sub s end) end
let rec findTerm (t___ term, row, default) =
  let rec find =
    begin function
    | PAIR (t___ key, data, r) -> if key < term then begin find r end
        else begin if key = term then begin data end else begin default end end
  | EMPTY -> default end in
find row
let rec findNonterm (NT nt, row) =
  let rec find =
    begin function
    | PAIR (NT key, data, r) -> if key < nt then begin find r end
        else begin if key = nt then begin Some data end else begin None end end
  | EMPTY -> None end in
find row
let action =
  begin function
  | ({ action } : table) ->
      (begin function
       | (STATE state, term) ->
           let (row, default) = action sub state in
           findTerm (term, row, default) end) end
let goto =
  begin function
  | ({ goto } : table) ->
      (begin function
       | (STATE state, nonterm) as a ->
           (begin match findNonterm (nonterm, (goto sub state)) with
            | Some state -> state
            | None -> raise (Goto a) end) end) end
let initialState =
  begin function | ({ initialState } : table) -> initialState end
let mkLrTable =
  begin function
  | { actions; gotos; initialState; numStates; numRules; gotos; initialState;
      numStates; numRules; initialState; numStates; numRules; numStates;
      numRules; numRules } ->
      ({
         action = actions;
         goto = gotos;
         states = numStates;
         rules = numRules;
         initialState
       } : table) end end
