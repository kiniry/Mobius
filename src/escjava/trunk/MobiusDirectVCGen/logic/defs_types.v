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





