  Module java_lang_Throwable.

    Definition className : ClassName := (javaLang, throwable). 

    Definition _init_Signature : MethodSignature := METHODSIGNATURE.Build_t
      (className, 10%positive)
      nil
      None
    .

    Definition _init_Instructions : list (PC*Instruction) :=
      (0%N, Vload Aval 0%N)::
      (1%N, Invokespecial java_lang_Object._init_Signature)::
      (4%N, Vload Aval 0%N)::
      (5%N, Vload Aval 0%N)::
      (6%N, Putfield java_lang_Throwable.causeFieldSignature)::
      (9%N, Vload Aval 0%N)::
      (10%N, Invokevirtual java_lang_Throwable.fillInStackTraceSignature)::
      (13%N, Pop)::
      (14%N, Return)::
      nil
    .

    Definition _init_Body : BytecodeMethod := BYTECODEMETHOD.Build_t
      _init_Instructions
      nil
      1
      2
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
      (Some java_lang_Object.className)
      nil
      nil
      (_init_Method::nil)
      false
      true
      false
    .

  End java_lang_Throwable.
