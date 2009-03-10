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

Module BicoType.
    Load "Map_java_lang_Object.v".
    Load "Map_java_lang_Throwable.v".
    Load "Map_java_lang_Exception.v".
    Load "Map_java_lang_NullPointerException.v".

    Load "A_type.v".
End BicoType.
