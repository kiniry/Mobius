#include <stdio.h>
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/callback.h>

int main(int argc, char** argv) {
  printf("Starting OCaml prover from C.\n");
  start_prover();
  printf("Stopping OCaml prover from C.\n");
  stop_prover();
}

value start_prover () {
  CAMLlocal1(f);
  f = *(caml_named_value("start_solver"));
  CAMLreturn callback(f);
}

value set_prover_resource_flags (value properties) {
  CAMLparam1(properties);
  CAMLlocal1(f);
  f = *(caml_named_value("set_flags"));
  CAMLreturn callback(f, v);
}

value signature (value signature) {
}

value declare_axiom (value axiom) {
}

value make_assumption (value formula) {
}

value retract_assumption (value count) {
}

value is_valid (value formula, value properties) {
}

value stop_prover () {
  CAMLlocal1(f);
  f = *(caml_named_value("stop_solver"));
}

