module UnknownExn =
  (UnknownExn)(struct let exnHistory = begin function | exn -> [] end
end)