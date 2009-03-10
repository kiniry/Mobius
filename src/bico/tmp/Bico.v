Add LoadPath "Formalisation/Library".
Add LoadPath "Formalisation/Library/Map".
Add LoadPath "Formalisation/Bicolano".
Add LoadPath "Formalisation/Logic".
Load "Map_java_lang_Object.v".
Load "Map_java_lang_Throwable.v".
Load "Map_java_lang_Exception.v".
Load "Map_java_lang_NullPointerException.v".

Add LoadPath "classes/".
Require Export ImplemProgramWithMap.
Require Import ImplemSWp.
Import P.
Import MDom.

Require Export Bico_type.
Require Export Bico_signature.
Export BicoType.
Export BicoSignature.

Module BicoProgram.
    Load "Map_java_lang_Object.v".
    Load "Map_java_lang_Throwable.v".
    Load "Map_java_lang_Exception.v".
    Load "Map_java_lang_NullPointerException.v".

    Load "A.v".
  Definition AllClasses: PROG.MapClass.t :=     (mc_cons A.class(mc_cons java_lang_Object.class(mc_cons java_lang_Throwable.class(mc_cons java_lang_Exception.class(mc_cons java_lang_NullPointerException.class mc_empty))))).

  Definition AllInterfaces: PROG.MapInterface.t :=      mi_empty.
  Definition program: Program :=     PROG.Build_t
        AllClasses
        AllInterfaces
    .
    
  Definition subclass := 
        match P.subclass_test program with
        | Some f => f
        | None => fun x y => true
        end
    .
    
End BicoProgram.
