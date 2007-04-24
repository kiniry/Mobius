Add LoadPath "/home/jcharles/sources/EscJava-workspace/MobiusDirectVCGen/logic/Formalisation/Bicolano".
Add LoadPath "/home/jcharles/sources/EscJava-workspace/MobiusDirectVCGen/logic/Formalisation/Library".
Add LoadPath "/home/jcharles/sources/EscJava-workspace/MobiusDirectVCGen/logic/Formalisation/Library/Map".

Require Import Bool.
Require Import Sumbool.
Require Import "ImplemProgramWithList".
Require Import "ImplemDomain".

Module Dom := Make P.

Import Dom.
Definition f_pre: Prop := True.
Definition f_norm: Prop := True.
Definition f_excp: Prop := False.

Definition t_pre: Prop := True.
Definition t_norm : Prop := True.
Definition t_excp: Prop := False.
Variable heap: Heap.t.
Import Prog.
Variable p: Program.
Variable iValue: Z -> value.
Variable fs_6_6_12: Heap.AdressingMode.
Variable typeof : Heap.t -> value -> ClassName.


Definition T_java_lang_NullPointerException :=(javaLang, NullPointerException).
Variable loc: value -> Location.


Lemma l:
(f_pre -> (t_pre /\ (t_pre -> ((forall (r7:value), (t_norm -> (((Is_true (Zeq_bool 1 1)) -> (((not (r7 = Null)) -> f_norm) /\ ((r7 = Null) -> (forall (r3:value), (forall (heap0:Heap.t), (((Heap.new (Heap.update heap fs_6_6_12 (iValue 0)) p (Heap.LocationObject T_java_lang_NullPointerException)) = (Some ((loc r3) , heap0))) -> f_excp)))))) /\ ((not (Is_true (Zeq_bool 1 1))) -> (((not (r7 = Null)) -> f_norm) /\ ((r7 = Null) -> (forall (r3:value), (forall (heap0:Heap.t), (((Heap.new (Heap.update heap fs_6_6_12 (iValue 0)) p (Heap.LocationObject T_java_lang_NullPointerException)) = (Some ((loc r3) , heap0))) -> f_excp))))))))) /\ (forall (r6:value), (t_excp -> f_excp)))))).
Proof.
intros; repeat (split; intros).


