  Module java_lang_Object.

    Definition className : ClassName := (javaLang, object). 

    Definition _init_Signature : MethodSignature := METHODSIGNATURE.Build_t
      (className, 10%positive)
      nil
      None
    .

    Definition _init_Instructions : list (PC*Instruction) :=
      (0%N, Return)::
      nil
    .

    Definition _init_Body : BytecodeMethod := BYTECODEMETHOD.Build_t
      _init_Instructions
      nil
      1
      0
    .

    Definition _init_Method : Method := METHOD.Build_t
      _init_Signature
      (Some _init_Body)
      false
      false
      false
      Public
    .

    Definition class : Class := CLASS.Build_t
      className
      None (* (Some java_lang_Object.className) *)
      nil
      nil
      (_init_Method::nil)
      false
      true
      false
    .

  End java_lang_Object.
    