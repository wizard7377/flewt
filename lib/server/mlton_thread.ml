module MLton =
  struct
    open MLton
    module Thread = struct open MLton.Thread
                           let rec prepare (f, x) = f end
  end