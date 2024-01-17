(* ErrorFlag.ml *)
let error_occurred = ref false

let set_error () = error_occurred := true

let check_error () = !error_occurred