
module LrTable : LR_TABLE =
  struct
    open Array
    open List
    type ('a, 'b) pairlist =
      | EMPTY 
      | PAIR of ('a * 'b * ('a, 'b) pairlist) 
    type term =
      | T of int 
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
    let numStates { states } = states
    let numRules { rules } = rules
    let describeActions { action } (STATE s) = action sub s
    let describeGoto { goto } (STATE s) = goto sub s
    let rec findTerm (T term) row default =
      let rec find =
        function
        | PAIR (T key, data, r) ->
            if key < term
            then find r
            else if key = term then data else default
        | EMPTY -> default in
      find row
    let rec findNonterm (NT nt) row =
      let rec find =
        function
        | PAIR (NT key, data, r) ->
            if key < nt then find r else if key = nt then Some data else None
        | EMPTY -> None in
      find row
    let action { action } (STATE state) term =
      let (row, default) = action sub state in findTerm (term, row, default)
    let goto { goto } ((STATE state, nonterm) as a) =
      match findNonterm (nonterm, (goto sub state)) with
      | Some state -> state
      | None -> raise (Goto a)
    let initialState { initialState } = initialState
    let mkLrTable
      { actions; gotos; initialState; numStates; numRules; gotos;
        initialState; numStates; numRules; initialState; numStates; numRules;
        numStates; numRules; numRules }
      =
      ({
         action = actions;
         goto = gotos;
         states = numStates;
         rules = numRules;
         initialState
       } : table)
  end ;;
