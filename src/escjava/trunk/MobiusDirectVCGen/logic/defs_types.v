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
Variable iValue: Z -> value.
Variable fs_6_6_12: Heap.AdressingMode.
Variable typeof : Heap.t -> value -> ClassName.
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





