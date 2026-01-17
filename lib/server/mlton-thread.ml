
module MLton =
  struct
    open MLton
    module Thread =
      struct
        open MLton.Thread
        let rec prepare
          (((f)(* Construct a 20041109-workalike MLton.Thread for previous MLton versions *)),
           x)
          = f
      end
  end;;
