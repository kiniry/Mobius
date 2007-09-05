Add LoadPath "Formalisation/Bicolano".
Add LoadPath "Formalisation/Library".
Add LoadPath "Formalisation/Library/Map".
Add LoadPath "Formalisation/Logic".

Require Export Bool.
Require Export Sumbool.

Require Export BicoMap.
Export BicoMapProgram.
Import P.
Require Export ImplemSWp.
Import MDom.

Variable heap: Heap.t.
Definition p := program.

Definition get (heap: Heap.t) (loc: Heap.AdressingMode)  : value :=
match (Heap.get heap loc) with
| Some v => v
| None => Null
end.
Variable this: value.
Variable undef: Location.

Definition vInt (val: value) : Int.t :=
match val with 
| Num (I i) => i
| _ => Int.const 0
end.

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

Variable inv: value -> type -> Prop.
Variable isAlive: Heap.t -> value -> Prop.
