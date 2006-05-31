Add LoadPath "/home/jcharles/sources/runtime-workspace/QuickSort/JPOs/".
Require Import "jack_references".
Module LoopClasses <: JackClasses.

(* Class Definitions *)
Inductive Class : Set
   := c_int : Class
      | c_short : Class
      | c_char : Class
      | c_byte : Class
      | c_boolean : Class
      | c_java_lang_Object : Class
      | c_fr_Loop : Class
      | c_Object : Class.

Definition Classes := Class.
Definition IntClass := c_int.
Definition ShortClass := c_short.
Definition ByteClass := c_byte.
Definition CharClass := c_char.
Definition BooleanClass := c_boolean.
Definition StringClass := c_Object.
End LoopClasses.

