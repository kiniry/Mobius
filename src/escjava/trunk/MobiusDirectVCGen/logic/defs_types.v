Add LoadPath "Formalisation/Bicolano".
Add LoadPath "Formalisation/Library".
Add LoadPath "Formalisation/Library/Map".
Add LoadPath "Formalisation/Logic".
Add Rec LoadPath "classes".
Require Export Bool.
Require Export Sumbool.

Require Export Bico.
Export BicoProgram.
Import P.
Require Export ImplemSWp.
Import Mwp.

(* Variable heap: Heap.t. *)
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

Coercion Int.const: Z >->Int.t.
Coercion Int.toZ : Int.t >-> Z.
Definition classToType (cl: ClassName): type := ReferenceType (ClassType cl).
Coercion classToType: ClassName >-> type.

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

Definition isAlive (heap: Heap.t) (val: value) : Prop :=
  Heap.typeof heap val <> None.

Coercion Ref: Location >-> value.
(*  
 *  Here, we should put all information about invariants in it
 *  Let's assume for the moment that all invariants are always
 *  True 
 *)
Definition inv (heap:Heap.t) (val: value) (typ: type) : Prop := 
  True.

Definition assignPred (h: Heap.t) (h0: Heap.t) (t: value) (f: FieldSignature) : Prop :=
    Heap.get h (Heap.DynamicField (loc t) f) = Heap.get h0 (Heap.DynamicField (loc t) f)
    \/ not (isAlive h0 t).
    
Definition fieldPred : Heap.t -> value -> FieldSignature -> Prop :=
  fun heap v f =>
   forall (cn: ClassName),
    Heap.typeof heap v = Some (Heap.LocationObject cn) ->
     defined_field program cn f.
     