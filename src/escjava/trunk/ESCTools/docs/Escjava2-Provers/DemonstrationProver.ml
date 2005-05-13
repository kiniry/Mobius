let start_solver () = 0 ;;

let _ = Callback.register "start_solver" start_solver

let set_flags flags = 0 ;;

let _ = Callback.register "set_flags" set_flags

let declaration xr_sgt = 0 ;;

let _ = Callback.register "declaration" declaration

let add_axiom xr_axiom = 0 ;;

let _ = Callback.register "add_axiom" add_axiom

let add_assertion xr_asrt = 0 ;;

let _ = Callback.register "add_assertion" add_assertion

let backtrack n = 0 ;;

let _ = Callback.register "backtrack" backtrack

let query xr_q = 0 ;;

let _ = Callback.register "query" query

let stop_solver () = 0 ;;

let _ = Callback.register "stop_solver" stop_solver
