Add LoadPath "/home/jcharles/sources/EscJava-workspace/MobiusDirectVCGen/logic/Formalisation/Bicolano".
Add LoadPath "/home/jcharles/sources/EscJava-workspace/MobiusDirectVCGen/logic/Formalisation/Library".
Add LoadPath "/home/jcharles/sources/EscJava-workspace/MobiusDirectVCGen/logic/Formalisation/Library/Map".

Require Import Bool.
Require Import Sumbool.
Require Import "ImplemProgramWithList".
Require Import "ImplemDomain".

Module Dom := Make P.

Import Dom.

Variable heap: Heap.t.
Import Prog.
Variable p: Program.
Definition typeof (heap: Heap.t) (loc: Location) : ClassName :=
match (Heap.typeof heap loc) with
| Some c => c
| None => (javaLang, object)
end.
Variable this: value.
Variable undef: Location.

Definition loc (v: value): Location := 
match v with 
| Ref r => r
| _ => undef
end.
Lemma simple_loc : forall r, loc (Ref r) = r.
intros; simpl; auto.
Qed.

Definition eq_bool (v1: Int.t) (v2: Int.t): bool :=
  Zeq_bool (Int.toZ v1) (Int.toZ v2).
Definition le_bool (v1: Int.t) (v2: Int.t): bool :=
  Zle_bool (Int.toZ v1) (Int.toZ v2).
Definition lt_bool (v1: Int.t) (v2: Int.t): bool :=
  Zlt_bool (Int.toZ v1) (Int.toZ v2).



