Require Export List.
Require Export ZArith.
Require Export Program.
Require Export Relation_Operators.

Definition positive_dec: forall p1 p2:positive, {p1=p2}+{p1<>p2}.
Proof.
  decide equality.
Defined.

Definition N_dec: forall n1 n2:N, {n1=n2}+{n1<>n2}.
Proof.
  decide equality.
  apply positive_dec.
Defined.

Definition nat_of_N (n : N) : nat := match n with
  | N0 => 0
  | (Npos p) => nat_of_P p
end.

Section findList.
  Variable A B : Set.
  Variable getKey : A -> B.
  Variable B_eq_dec : forall x y : B, {x=y}+{~x=y}.
  Fixpoint find (b:B) (l:list A) {struct l} : option A :=
    match l with
      nil => None
    | a::q => if B_eq_dec (getKey a) b then Some a
              else find b q
    end.
  Lemma find_getKey : forall b l a,
    find b l = Some a -> b = getKey a.
  Proof.
    induction l; simpl.
    intros; discriminate.
    intro; destruct B_eq_dec; intros.
    inversion_clear H in e; auto.
    auto.
  Qed.

End findList.

Module Make <: PROGRAM.

  Definition Var := N. 
  Definition Var_eq_dec : forall x1 x2:Var, {x1=x2}+{~x1=x2} := N_dec.
  Definition Var_toN : Var -> nat := nat_of_N.

  Definition PC : Set := N.
  Definition PC_eq_dec := N_dec.

  Definition PackageName : Set := positive.
  Definition ShortClassName : Set := positive.
  Definition ShortMethodName : Set := positive.
  Definition ShortFieldName : Set := positive.
  Definition ClassName := PackageName * ShortClassName.
  Definition InterfaceName := PackageName * ShortClassName.
  Definition MethodName := ClassName * ShortMethodName.
  Definition FieldName := ClassName * ShortFieldName.

  (* IMPORTANT CONSTANT CONVENTIONS FOR PARSER !! *)
  Definition javaLang : PackageName := 1%positive.
  Definition object : ShortClassName := 1%positive.
  Definition NullPointerException : ShortClassName := 2%positive.
  Definition ArrayIndexOutOfBoundsException : ShortClassName := 3%positive.
  Definition ArrayStoreException : ShortClassName := 4%positive.
  Definition NegativeArraySizeException : ShortClassName := 5%positive.
  Definition ClassCastException : ShortClassName := 6%positive.
  Definition ArithmeticException : ShortClassName := 7%positive.

  Inductive Visibility : Set :=
    Package | Protected | Private | Public.

  Inductive type : Set :=
      | ReferenceType (rt : refType)
      | PrimitiveType (pt: primitiveType)
  with refType :Set := 
      | ArrayType (typ:type) 
      | ClassType  (ct:ClassName)
      | InterfaceType (it:InterfaceName)
  with  primitiveType : Set := 
      | BOOLEAN  | BYTE | SHORT | INT.

  Definition eq_dec (A:Set) := forall x y:A, {x=y}+{~x=y}.
  Scheme type_strong_rec := Induction for type Sort Set
    with refType_strong_rec := Induction for refType Sort Set.
  Lemma primitiveType_dec : eq_dec primitiveType.
  Proof. 
   unfold eq_dec; decide equality.
  Qed.
  Lemma type_dec : eq_dec type.
  Proof. 
   unfold eq_dec.
   intros x; pattern x.
   apply type_strong_rec with (P0:=fun r1:refType => forall r2, {r1=r2}+{~r1=r2}); intros.
   destruct y; try (right;discriminate).
   destruct (H rt0).
   left; subst; constructor.
   right; intro; elim n.
   injection H0; auto.
   destruct y; try (right;discriminate).
   destruct (primitiveType_dec pt pt0).
   left; subst; constructor.
   right; intro; elim n.
   injection H; auto.
   destruct r2; try (right;discriminate).
   destruct (H typ0).
   left; subst; constructor.
   right; intro; elim n.
   injection H0; auto.
   destruct r2; try (right;discriminate).
   decide equality ct ct0; try apply positive_dec; intros.
   destruct (H ct ct0).
   left; subst; constructor.
   right; intro; elim n.
   injection H0; auto.
   destruct r2; try (right;discriminate).
   decide equality it it0; try apply positive_dec; intros.
   destruct (H it it0).
   left; subst; constructor.
   right; intro; elim n.
   injection H0; auto.
  Qed.

  Inductive CompInt : Set := EqInt | NeInt | LtInt | LeInt | GtInt | GeInt.
  Inductive CompRef : Set := EqRef | NeRef.

  Inductive BinopInt : Set := AddInt | AndInt | DivInt | MulInt | OrInt | RemInt 
                            | ShlInt | ShrInt | SubInt | UshrInt | XorInt.

  Module Type OFFSET_TYPE.
    Parameter t : Set.
    Parameter jump : PC -> t -> PC.
  End OFFSET_TYPE.
  Module OFFSET <: OFFSET_TYPE.
    Definition t := N.
    Definition jump : PC -> t -> PC := Nplus.
  End OFFSET.

  Lemma prod_eq_dec : 
    forall (A B : Set)
           (tA : forall x y:A, {x=y}+{~x=y})
           (tB : forall x y:B, {x=y}+{~x=y})
           (x y : A*B), {x=y}+{~x=y}.
  Proof.
    intros A B tA tB (a1,b1) (a2,b2).
    destruct (tA a1 a2).
    destruct (tB b1 b2).
    left; congruence.
    right; intros H; elim n; inversion H; reflexivity.
    right; intros H; elim n; inversion H; reflexivity.    
  Qed.

  Lemma option_eq_dec : 
    forall (A : Set)
           (tA : forall x y:A, {x=y}+{~x=y})
           (x y : option A), {x=y}+{~x=y}.
  Proof.
    intros A tA x y; destruct x; destruct y.
    destruct (tA a a0).
    left; congruence.
    right; intros H; elim n; inversion H; reflexivity.
    right; intros H; discriminate.
    right; intros H; discriminate.
    left; reflexivity.
  Qed.

  Definition ClassName_eq_dec : eq_dec ClassName :=
      prod_eq_dec _ _ positive_dec positive_dec.
  Definition InterfaceName_eq_dec : eq_dec InterfaceName :=
      prod_eq_dec _ _ positive_dec positive_dec.
  Definition FieldName_eq_dec : eq_dec FieldName :=
      prod_eq_dec _ _ ClassName_eq_dec positive_dec.

  Module FIELDSIGNATURE.
    Record t :Set := {
      name : FieldName;
      type : type
    }.
    Lemma eq_dec : forall f1 f2:t, {f1=f2}+{~f1=f2}.
    Proof.
      intros.
      destruct f1 as [n1 t1]; destruct f2 as [n2 t2].
      destruct (FieldName_eq_dec n1 n2).
      destruct (type_dec t1 t2).
      left; congruence.
      right; intros H; elim n; inversion H; reflexivity.
      right; intros H; elim n; inversion H; reflexivity.    
    Qed.
  End FIELDSIGNATURE.
  Definition FieldSignature := FIELDSIGNATURE.t.
  Module Type FIELDSIGNATURE_TYPE.
    Parameter name : FieldSignature  -> FieldName.
    Parameter type : FieldSignature -> type.
    Parameter eq_dec : forall f1 f2:FieldSignature, {f1=f2}+{~f1=f2}.
  End FIELDSIGNATURE_TYPE.

  Definition MethodName_eq_dec : eq_dec MethodName :=
      FieldName_eq_dec.

  Module METHODSIGNATURE.
    Record t :Set := {
      name : MethodName;
      parameters : list type;
      result : option type
    }.
    Lemma eq_dec : forall mid1 mid2:t, {mid1=mid2}+{~mid1=mid2}.
    Proof.
      intros.
      destruct mid1 as [n1 p1 r1]; destruct mid2 as [n2 p2 r2].
      destruct (MethodName_eq_dec n1 n2).
      destruct (list_eq_dec type_dec p1 p2).
      destruct (option_eq_dec _ type_dec r1 r2).
      left; congruence.
      right; intros H; elim n; inversion H; reflexivity.
      right; intros H; elim n; inversion H; reflexivity.    
      right; intros H; elim n; inversion H; reflexivity.    
    Qed.
  End METHODSIGNATURE.

  Definition MethodSignature := METHODSIGNATURE.t.

  Module Type METHODSIGNATURE_TYPE.
    Parameter name : MethodSignature -> MethodName.
    Parameter parameters : MethodSignature -> list type.
    Parameter result : MethodSignature -> option type.
    Parameter eq_dec : forall mid1 mid2:MethodSignature, {mid1=mid2}+{~mid1=mid2}.
  End METHODSIGNATURE_TYPE.

  Inductive Instruction : Set :=
   | Aaload | Aastore | Aconst_null
   | Aload (x:Var) | Anewarray (t:refType) | Areturn 
   | Arraylength | Astore (x:Var) | Athrow
   | Baload | Bastore (* | Bipush z *)
   (* | Caload | Castore *) 
   | Checkcast (t:refType)
   | Const (t:primitiveType) (z:Z)
   (* | D2f | D2i | D2l | Dadd | Daload | Dastore | Dcmp_<op> 
      | Dconst_<d> | ddiv | dload | dload_<n> | dmul | dneg | drem | dreturn 
      | dstore | dstore_<n> | dsub  *)
   | Dup | Dup_x1 | Dup_x2 | Dup2 | Dup2_x1 | Dup2_x2
   (* | f2d | f2i | f2l | fadd | faload | fastore | fcmp_<op> | fconst_<f>
      | fdiv | fload | fload_<n> | fmul | fneg | frem | freturn 
      | fstore | fstore_<n> | fsub *)
   | Getfield (f:FieldSignature) | Getstatic  (f:FieldSignature) 
   | Goto (o:OFFSET.t)
   | I2b | (* I2c | i2d | i2f | i2l  *) I2s
   | Ibinop (op:BinopInt) | Iaload 
   | Iastore (* Iconst *) 
   | If_acmp (cmp:CompRef) (o:OFFSET.t)
   | If_icmp (cmp:CompInt) (o:OFFSET.t) 
   | If0 (cmp:CompInt) (o:OFFSET.t)
   | Ifnull (cmp:CompRef) (o:OFFSET.t) (* EqRef for Ifnull;
                                          NeRef for Ifnonnull *)
   | Iinc (x:Var) (z:Z) | Iload (x:Var) | Ineg 
   | Instanceof (t:refType) 
   | Invokeinterface (m:MethodSignature)
   | Invokespecial (m:MethodSignature)
   | Invokestatic (m:MethodSignature)
   | Invokevirtual (m:MethodSignature)
   | Ireturn | Istore (x:Var) (* | Jsr *)
   (* | l2d | l2f | l2i | ladd | laload | land | lastore | lcmp | lconst *)

   (* | Ldc (z:Z)  *)
   (* ldc2_w | ldiv | lload | lmul | lneg *) 

   | Lookupswitch (def:OFFSET.t) (l:list (Z*OFFSET.t)) 

   (* lor | lrem | lreturn | lshl | lshr | lstore | lsub  | lxor | lushr *)
   (* | monitorenter | monitorexit *)

   | Multianewarray (t:refType) (d:Z) | New (cl:ClassName) | Newarray (t:primitiveType)
   | Nop | Pop | Pop2 | Putfield (f:FieldSignature) | Putstatic (f:FieldSignature)
   (* | ret *)

   | Return | Saload | Sastore 
   (* | Sipush (z:Z)*)
   | Swap 
   | Tableswitch (def:OFFSET.t) (low high:Z) (l:list OFFSET.t) (* | wide *).


  Lemma Visibility_eq_dec : eq_dec Visibility.
  Proof.
    unfold eq_dec; decide equality.
  Qed.

  Lemma bool_eq_dec : eq_dec bool.
  Proof.
    unfold eq_dec; decide equality.
  Qed.

  Module FIELD.
    Inductive value : Set :=
    | Int (v:Z)
    | NULL 
    | UNDEF.

    Record t : Set := {
      signature : FieldSignature;
      isFinal : bool;
      isStatic : bool;
      visibility : Visibility;
      initValue : value
    }.

    Lemma value_eq_dec : forall x y:value, {x=y}+{~x=y}.
    Proof.
      intros.
      destruct x; destruct y; try (left;reflexivity) || (right;intros H;discriminate H).
      destruct (Z_eq_dec v v0).
      left; congruence.
      right; intros H; elim n; inversion H; reflexivity.
    Qed.

    Lemma eq_dec : forall x y:t, {x=y}+{~x=y}.
    Proof.
      intros.
      destruct x as [sgn1 f1 s1 v1 iv1];
      destruct y as [sgn2 f2 s2 v2 iv2].
      destruct (FIELDSIGNATURE.eq_dec sgn1 sgn2).
      destruct (bool_eq_dec f1 f2).
      destruct (bool_eq_dec s1 s2).
      destruct (Visibility_eq_dec v1 v2).
      destruct (value_eq_dec iv1 iv2).
      left; congruence.
      right; intros H; elim n; inversion H; reflexivity.
      right; intros H; elim n; inversion H; reflexivity.
      right; intros H; elim n; inversion H; reflexivity.
      right; intros H; elim n; inversion H; reflexivity.    
      right; intros H; elim n; inversion H; reflexivity.    
    Qed.
   
  End FIELD.

  Definition Field := FIELD.t.

  Module Type FIELD_TYPE.
    Parameter signature : Field -> FieldSignature.    
    Parameter isFinal : Field -> bool.
    Parameter isStatic : Field -> bool.
    Parameter visibility : Field -> Visibility.
    Inductive value : Set :=
    | Int (v:Z)
    | NULL 
    | UNDEF.
    Parameter initValue : Field ->  value.
  End FIELD_TYPE.

  Module EXCEPTIONHANDLER.
    Record t : Set := {
      catchType : option ClassName;
      begin : PC;
      end_e : PC;
      handler : PC
    }.
    (* TODO : check correctness of isPCinRange *)
    Definition isPCinRange : t -> PC -> bool :=
      fun ex i => 
        match Ncompare (begin ex) i with
          Gt => false
        | _ => 
             match Ncompare i (end_e ex) with
               Gt => false
             | _ => true
             end
        end.            
  End EXCEPTIONHANDLER.
  Definition ExceptionHandler := EXCEPTIONHANDLER.t.

  Module Type EXCEPTIONHANDLER_TYPE.
    Parameter catchType : ExceptionHandler -> option ClassName.
    Parameter isPCinRange : ExceptionHandler -> PC -> bool.
    Parameter handler : ExceptionHandler -> PC.
  End EXCEPTIONHANDLER_TYPE.
   
  Record BytecodeMethod_ : Set := {
    instr : list (PC*Instruction);
    exceptionHandlers : list ExceptionHandler;
    max_locals : nat;
    max_operand_stack_size : nat
  }.
  Definition BytecodeMethod := BytecodeMethod_.

  Module BYTECODEMETHOD.

    Definition exceptionHandlers : BytecodeMethod -> list ExceptionHandler :=
      exceptionHandlers.
    Definition max_locals : BytecodeMethod -> nat:=
      max_locals.
    Definition max_operand_stack_size : BytecodeMethod -> nat :=
      max_operand_stack_size.

    Definition  firstAddress (bm:BytecodeMethod) : PC :=
      match (instr bm) with
        nil => 0%N
      | (pp,_)::_ => pp
      end.
    Fixpoint instructionAt_rec (pp0:PC) (l:list (PC*Instruction)) {struct l} : option Instruction :=
       match l with
         nil => None
       | (pp,i)::q =>
         if N_dec pp0 pp then Some i
         else instructionAt_rec pp0 q
       end.
    Definition instructionAt (bm:BytecodeMethod) (pp:PC) : option Instruction :=
     instructionAt_rec pp (instr bm).

    Fixpoint nextAddress_rec (pp0:PC) (l:list (PC*Instruction)) {struct l} : option PC :=
       match l with
         nil => None
       | (pp1,_)::q =>
         if N_dec pp0 pp1 then 
            match q with
              nil => None
            | (pp2,_)::_ => Some pp2
            end
         else nextAddress_rec pp0 q
       end.

    Definition nextAddress (bm:BytecodeMethod) (pp:PC) : option PC :=
      nextAddress_rec pp (instr bm).

    Inductive reachable_pc (bm: BytecodeMethod) : PC -> Prop :=
    | reachable_pc_first: reachable_pc bm (firstAddress bm)
    | reachable_pc_handler: forall exn,
        In exn (exceptionHandlers bm) ->
        reachable_pc bm (EXCEPTIONHANDLER.handler exn)
    | reachable_pc_next: forall pc pc',
        reachable_pc bm pc ->
        nextAddress bm pc = Some pc' ->
        reachable_pc bm pc'.

    Definition DefinedInstruction (bm:BytecodeMethod) (pc:PC) : Prop :=
      exists i, instructionAt bm pc = Some i.
    Axiom all_instruction_in_reachable_pc : forall bm pc ins,
      instructionAt bm pc = Some ins -> reachable_pc bm pc.
    Axiom in_reachable_pc_some_instruction : forall bm pc,
      DefinedInstruction bm (firstAddress bm) ->
      (forall exn, In exn (exceptionHandlers bm) -> 
                   DefinedInstruction bm (EXCEPTIONHANDLER.handler exn)) ->
      reachable_pc bm pc ->
      DefinedInstruction bm pc.

   
  End BYTECODEMETHOD.

  Module Type BYTECODEMETHOD_TYPE.
    Parameter firstAddress : BytecodeMethod -> PC.
    Parameter nextAddress : BytecodeMethod -> PC -> option PC.
    Parameter instructionAt : BytecodeMethod -> PC -> option Instruction.
    Parameter exceptionHandlers : BytecodeMethod -> list ExceptionHandler.
    Parameter max_locals : BytecodeMethod -> nat.
    Parameter max_operand_stack_size : BytecodeMethod -> nat.

    Inductive reachable_pc (bm: BytecodeMethod) : PC -> Prop :=
    | reachable_pc_first: reachable_pc bm (firstAddress bm)
    | reachable_pc_handler: forall exn,
        In exn (exceptionHandlers bm) ->
        reachable_pc bm (EXCEPTIONHANDLER.handler exn)
    | reachable_pc_next: forall pc pc',
        reachable_pc bm pc ->
        nextAddress bm pc = Some pc' ->
        reachable_pc bm pc'.
    Definition DefinedInstruction (bm:BytecodeMethod) (pc:PC) : Prop :=
      exists i, instructionAt bm pc = Some i.

    Parameter all_instruction_in_reachable_pc : forall bm pc ins,
      instructionAt bm pc = Some ins -> reachable_pc bm pc.
    Parameter in_reachable_pc_some_instruction : forall bm pc,
      DefinedInstruction bm (firstAddress bm) ->
      (forall exn, In exn (exceptionHandlers bm) -> 
                   DefinedInstruction bm (EXCEPTIONHANDLER.handler exn)) ->
      reachable_pc bm pc ->
      DefinedInstruction bm pc.
   
  End BYTECODEMETHOD_TYPE.

  Module METHOD.
    Record t : Set := {
      signature : MethodSignature;
      body : option BytecodeMethod;
      isFinal : bool;
      isStatic : bool;
      visibility : Visibility      
    }.
  End METHOD.

  Definition Method := METHOD.t.

  Module Type METHOD_TYPE.
    Parameter signature : Method -> MethodSignature.
    Parameter body : Method -> option BytecodeMethod.
    Parameter isFinal : Method -> bool.
    Parameter isStatic : Method -> bool.
    Parameter visibility : Method -> Visibility.
  End METHOD_TYPE.

  Module CLASS.
    Record t : Set := {
      name : ClassName;
      superClass : option ClassName;
      superInterfaces : list InterfaceName;
      fields : list Field;
      methods : list Method;
      isFinal : bool;
      isPublic : bool;
      isAbstract : bool
    }.

    Definition field : t -> ShortFieldName -> option Field :=
      fun cl s => 
      find Field ShortFieldName 
           (fun f => snd (FIELDSIGNATURE.name (FIELD.signature f)))
            positive_dec
           s (fields cl).
    Lemma field_shortname_prop : forall cl s f,
      field cl s = Some f -> s = snd (FIELDSIGNATURE.name (FIELD.signature f)).
    Proof.
      unfold field; intros cl s f.
      apply (find_getKey Field ShortFieldName 
           (fun f => snd (FIELDSIGNATURE.name (FIELD.signature f)))).
    Qed.

    Definition method : t -> MethodSignature -> option Method :=
      fun cl mid =>
       find Method MethodSignature METHOD.signature
            METHODSIGNATURE.eq_dec
            mid (methods cl) .
    Lemma method_signature_prop : forall cl mid m,
      method cl mid = Some m -> mid = METHOD.signature m.
    Proof.
      unfold method; intros p cl mid.
      apply find_getKey.
    Qed.
    Definition defined_Method (cl:t) (m:Method) :=
      method cl (METHOD.signature m) = Some m.
  End CLASS.

  Definition Class := CLASS.t.

  Module Type CLASS_TYPE.
    Parameter name : Class -> ClassName.
    Parameter superClass : Class -> option ClassName.
    Parameter superInterfaces : Class -> list InterfaceName.
    Parameter field : Class -> ShortFieldName -> option Field.
    Parameter method : Class -> MethodSignature -> option Method.
    Parameter method_signature_prop : forall cl mid m,
      method cl mid = Some m -> mid = METHOD.signature m.
    Parameter isFinal : Class -> bool.
    Parameter isPublic : Class -> bool.
    Parameter isAbstract : Class -> bool.
    Definition defined_Method (cl:Class) (m:Method) :=
      method cl (METHOD.signature m) = Some m.
  End CLASS_TYPE.

  Module INTERFACE.
    Record t : Set := {
      name : InterfaceName;
      superInterfaces : list InterfaceName;
      fields : list Field;
      methods : list Method;
      isFinal : bool;
      isPublic : bool;
      isAbstract : bool
    }.

    Definition field : t -> ShortFieldName -> option Field :=
      fun cl s => 
      find Field ShortFieldName 
           (fun f => snd (FIELDSIGNATURE.name (FIELD.signature f)))
            positive_dec
           s (fields cl).
    Lemma field_shortname_prop : forall cl s f,
      field cl s = Some f -> s = snd (FIELDSIGNATURE.name (FIELD.signature f)).
    Proof.
      unfold field; intros cl s f.
      apply (find_getKey Field ShortFieldName 
           (fun f => snd (FIELDSIGNATURE.name (FIELD.signature f)))).
    Qed.

    Definition method : t -> MethodSignature -> option Method :=
      fun cl mid =>
       find Method MethodSignature METHOD.signature
            METHODSIGNATURE.eq_dec
            mid (methods cl) .
    Lemma method_signature_prop : forall cl mid m,
      method cl mid = Some m -> mid = METHOD.signature m.
    Proof.
      unfold method; intros p cl mid.
      apply find_getKey.
    Qed.
  End INTERFACE.
 
  Definition Interface := INTERFACE.t.

  Module Type INTERFACE_TYPE.
    Parameter name : Interface -> InterfaceName. 
    Parameter superInterfaces : Interface ->  list InterfaceName.
    Parameter field : Interface -> ShortFieldName -> option Field.
    Parameter method : Interface -> MethodSignature -> option Method.
    Parameter isFinal : Interface -> bool.
    Parameter isPublic : Interface -> bool.
    Parameter isAbstract : Interface -> bool.
  End INTERFACE_TYPE.

  Module PROG.
    Record t : Set := {
      classes : list Class;
      interfaces : list Interface
    }.
    Definition class : t -> ClassName -> option Class :=
      fun p cn =>
       find Class ClassName CLASS.name
          ClassName_eq_dec
          cn (classes p).
    Definition defined_Class (p:t) (cl:Class) :=
      class p (CLASS.name cl) = Some cl.
    Lemma name_class_invariant1 : forall p cn cl,
      class p cn = Some cl -> cn = CLASS.name cl.
    Proof.
      unfold class; intros p cn cl.
      apply (find_getKey Class ClassName CLASS.name).
    Qed.
    Lemma In_classes_defined_Class : forall p cl,
      distinct CLASS.name (classes p) ->
      In cl (classes p) -> defined_Class p cl.
    Proof.
      unfold defined_Class, class; intros p. 
      generalize (classes p).
      induction l; simpl; intros.
      elim H0.
      destruct H0; subst.
      destruct (ClassName_eq_dec (CLASS.name cl) (CLASS.name cl)).
      reflexivity.
      elim n; reflexivity.
      destruct (ClassName_eq_dec (CLASS.name a) (CLASS.name cl)).
      rewrite (H a cl); auto with datatypes.
      apply IHl; auto.
      repeat intro; apply H; auto with datatypes.
    Qed.
    Lemma defined_Class_In_classes : forall p cl,
      defined_Class p cl -> In cl (classes p).
    Proof.
      unfold defined_Class, class; intros p. 
      generalize (classes p).
      induction l; simpl; intro.
      intros; discriminate.
      destruct (ClassName_eq_dec (CLASS.name a) (CLASS.name cl)); intros.
      inversion H; auto.
      right; auto.
    Qed.

    Definition interface : t -> InterfaceName -> option Interface :=
      fun p iname =>
       find Interface InterfaceName INTERFACE.name
          InterfaceName_eq_dec
          iname (interfaces p).
    Definition defined_Interface (p:t) (i:Interface) :=
      interface p (INTERFACE.name i) = Some i.
    Lemma name_interface_invariant1 : forall p iname i,
      interface p iname = Some i -> iname = INTERFACE.name i.
    Proof.
      unfold interface; intros p iname i.
      apply (find_getKey Interface InterfaceName INTERFACE.name).
    Qed.
  End PROG.

  Definition Program := PROG.t.

  Module Type PROG_TYPE.
    Parameter class : Program -> ClassName -> option Class.
    Definition defined_Class (p:Program) (cl:Class) :=
      class p (CLASS.name cl) = Some cl.
    Parameter name_class_invariant1 : forall p cn cl,
      class p cn = Some cl -> cn = CLASS.name cl.
    Parameter interface : Program -> InterfaceName -> option Interface.
    Definition defined_Interface (p:Program) (i:Interface) :=
      interface p (INTERFACE.name i) = Some i.
    Parameter name_interface_invariant1 : forall p cn cl,
      interface p cn = Some cl -> cn = INTERFACE.name cl.
  End PROG_TYPE.

  Inductive isStatic (p:Program) (fs: FieldSignature) : Prop :=
    isStatic_field : forall (cn:ClassName) (sfn:ShortFieldName) (cl:Class) (f:Field),
     (cn,sfn) = FIELDSIGNATURE.name fs ->
     PROG.class p cn = Some cl ->
     CLASS.field cl sfn = Some f ->
     FIELD.isStatic f = true ->
     isStatic p fs.

  Definition javaLangObject : ClassName := (javaLang,object).

  Inductive direct_subclass (p:Program) (c:Class) (s:Class) : Prop :=
    | direct_subclass1 : 
        PROG.defined_Class p c -> 
        PROG.defined_Class p s ->
        CLASS.superClass c = Some (CLASS.name s) -> 
        direct_subclass p c s.

  (** [subclass] is the reflexive transitive closure of the [direct_subclass] relation 
    (defined over the classes of the program) *)
  Definition subclass (p:Program) : Class -> Class -> Prop :=
    clos_refl_trans Class (direct_subclass p).

  Inductive subclass_name (p:Program) : ClassName -> ClassName -> Prop :=
    | subclass_name1 : forall c1 c2, 
       subclass p c1 c2 -> 
       subclass_name p (CLASS.name c1) (CLASS.name c2).

  Inductive direct_subclass_name (p:Program) : ClassName -> ClassName -> Prop :=
    | direct_subclass_name1 : forall c s,
       direct_subclass p c s ->
       direct_subclass_name p (CLASS.name c) (CLASS.name s).

  (** Similar definitions for interfaces *)
  Inductive direct_subinterface (p:Program) (c:Interface) (s:Interface) : Prop :=
    | direct_subinterface1 : 
      PROG.defined_Interface p c -> 
      PROG.defined_Interface p s ->
      In (INTERFACE.name s) (INTERFACE.superInterfaces c) -> 
      direct_subinterface p c s.

  (** [subinterface] is the reflexive transitive closure of the [direct_subinterface] 
      relation (defined over the interfaces of the program) *)
  Definition subinterface (p:Program) : Interface -> Interface -> Prop :=
    clos_refl_trans Interface (direct_subinterface p).

  Inductive subinterface_name (p:Program) : InterfaceName -> InterfaceName -> Prop :=
    | subinterface_name1 : forall c1 c2, 
       subinterface p c1 c2 -> 
       subinterface_name p (INTERFACE.name c1) (INTERFACE.name c2).

  Inductive direct_subinterface_name (p:Program) : InterfaceName -> InterfaceName -> Prop :=
    | direct_subinterface_name1 : forall c s,
       direct_subinterface p c s ->
       direct_subinterface_name p (INTERFACE.name c) (INTERFACE.name s).

  Inductive class_declares_field (p:Program) (cn:ClassName) (fd:FieldSignature) : Field -> Prop :=
    | class_decl_field : forall sfd cl f, 
      FIELDSIGNATURE.name fd = (cn,sfd) -> 
      PROG.class p cn = Some cl -> 
      CLASS.field cl sfd = Some f -> class_declares_field p cn fd f.

  Inductive interface_declares_field (p:Program) (cn:InterfaceName) (fd:FieldSignature) : Field -> Prop :=
    | interface_decl_field : forall sfd cl f, 
      FIELDSIGNATURE.name fd = (cn,sfd) -> 
      PROG.interface p cn = Some cl -> 
      INTERFACE.field cl sfd = Some f -> interface_declares_field p cn fd f.

  (** [defined_field p c fd] holds if the class [c] declares or inherits a field 
      of signature [fd] *)
  Inductive is_defined_field (p:Program) : ClassName -> FieldSignature -> Field -> Prop :=
    | def_class_field : forall cn fd cn' f,
        subclass_name p cn cn' -> 
        class_declares_field p cn' fd f -> 
        is_defined_field p cn fd f
    | def_interface_field : forall cn fd cl i1 i' f, 
        PROG.class p cn = Some cl -> 
        In i1 (CLASS.superInterfaces cl) ->
        subinterface_name p i1 i' -> 
        interface_declares_field p i' fd f -> 
        is_defined_field p cn fd f.

  Definition defined_field (p:Program) (cn:ClassName) (fs:FieldSignature) : Prop :=
    exists f, is_defined_field p cn fs f.

  Definition findMethod (p:Program) (msig: MethodSignature) : option Method :=
    let (cn,meth) := METHODSIGNATURE.name msig in
      match PROG.class p cn with
	| None => None
	| Some cl => CLASS.method cl msig 
      end.

  Definition findField (p:Program) (fd: FieldSignature) : option Field :=
    let (cn,sfd) := FIELDSIGNATURE.name fd in
      match PROG.class p cn with
	| None => None
	| Some cl => CLASS.field cl sfd
      end.
    

  Definition methodPackage (mname: MethodName) : PackageName :=  fst (fst mname).

  (* Relations [check_visibility,check_signature,overrides] are needed
  to define the method [lookup] algorithm **)

  Inductive check_visibility : Visibility -> PackageName -> PackageName ->  Prop :=
    | check_public :  forall p1 p2, check_visibility Public p1 p2
    | check_protected :forall p1 p2, check_visibility Protected p1 p2
    | check_package :forall p, check_visibility Package p p.


  (** [check_signature] verifies that the two methods share the same signature and that the defining classes belong to the [subclass] relation. *)
  (* CAVEAT: the methods may not be defined in the program *)
  Inductive check_signature (p:Program) : MethodName*Method -> MethodName*Method -> Prop :=
    | check_signature_c : forall  mn1 meth1 mn2 meth2,
      subclass_name p (fst mn1) (fst mn2) ->
      snd mn1 = snd mn2 -> 
      METHODSIGNATURE.parameters (METHOD.signature meth1) =
        METHODSIGNATURE.parameters (METHOD.signature meth2) -> 
      METHODSIGNATURE.result (METHOD.signature meth1) =
        METHODSIGNATURE.result (METHOD.signature meth2) -> 
      check_signature p (mn1,meth1) (mn2,meth2).
      
  (* FIXME: lookup should deal with interfaces - fb *)

  (**  Definition of the #<a href=http://java.sun.com/docs/books/jls/third_edition/html/classes.html##8.4.8>  overrides relation </a># *)
  Inductive overrides (p:Program) : MethodName*Method -> MethodName*Method -> Prop :=
    | overrides_here : forall  mn1 meth1 mn2 meth2,
      check_signature p (mn1,meth1) (mn2,meth2) -> 
      check_visibility (METHOD.visibility meth2) (methodPackage mn1) (methodPackage mn2) ->
      overrides p (mn1,meth1) (mn2,meth2)
    | overrides_trans : forall  mn1 meth1 mn' meth' mn2 meth2,
	  (* In the spec, there is a side-condition which says that minter is different from msig1 and msig2 !?! *)
      check_signature p (mn1,meth1) (mn2,meth2) -> 
      overrides p (mn1,meth1) (mn',meth') -> overrides p (mn',meth') (mn2,meth2) -> 
      overrides p (mn1,meth1) (mn2,meth2).
	  
  Inductive lookup_here (p:Program) : ClassName ->  MethodSignature -> Method -> Prop :=
    | lookup_here_c : forall cn cl msig m meth, 
      findMethod p msig = Some m -> 
      PROG.class p cn = Some cl -> 
      CLASS.method cl msig = Some meth -> 
      (* By construction, CLASS.method returns a method with the same short name *)
      overrides p ((cn,snd (METHODSIGNATURE.name msig)),meth) (METHODSIGNATURE.name msig,m) -> 
      lookup_here p cn msig meth.


  Inductive lookup (p:Program) : ClassName -> MethodSignature -> (ClassName*Method) -> Prop :=
    | lookup_no_up : forall cn  msig  meth, lookup_here p cn msig meth -> lookup p cn msig (cn,meth)
    | lookup_up : forall cn  msig, (forall meth, ~ lookup_here p cn msig meth) -> 
      forall super res , direct_subclass_name p cn super -> lookup p super msig res -> lookup p cn msig res.

  (** Get the next pc *)
  Definition next (m:Method) (pc:PC) : option PC :=
    match METHOD.body m with
      None => None
    | Some body => BYTECODEMETHOD.nextAddress body pc
    end.

  (** Get the instruction at the given pc *)
  Definition instructionAt (m:Method) (pc:PC) : option Instruction :=
    match METHOD.body m with
      None => None
    | Some body => BYTECODEMETHOD.instructionAt body pc
    end.

  Inductive implements (p:Program) : ClassName -> InterfaceName -> Prop :=
    | implements_def : forall i cl i', 
           PROG.defined_Interface p i -> 
           PROG.defined_Class p cl ->
           In (INTERFACE.name i) (CLASS.superInterfaces cl) ->
           subinterface_name p (INTERFACE.name i) i' ->
           implements p (CLASS.name cl) i'.

  (** [compat_refType source target] holds if a reference value of type [source] can be 
    assigned to a reference variable of type [target]. See 
    #<a href=http://java.sun.com/docs/books/vmspec/2nd-edition/html/Concepts.doc.html##19674>assignment conversion rules</a># *)

  Inductive compat_refType (p:Program) : refType -> refType -> Prop :=
   | compat_refType_class_class : forall clS clT,
       subclass_name p clS clT ->
       compat_refType p (ClassType clS) (ClassType clT)
   | compat_refType_class_interface : forall clS clT,
       implements p clS clT ->
       compat_refType p (ClassType clS) (ClassType clT)
   | compat_refType_interface_class : forall clS,
       PROG.defined_Interface p clS ->
       compat_refType p (ClassType (INTERFACE.name clS)) (ClassType javaLangObject)
   | compat_refType_interface_interface : forall clS clT,
       PROG.defined_Interface p clS ->
       subinterface p clS clT ->
       compat_refType p (ClassType (INTERFACE.name clS)) (ClassType (INTERFACE.name clT))
   | compat_refType_array_class : forall tpS,       
       compat_refType p (ArrayType tpS) (ClassType javaLangObject)
   (* FIXME: array_interface : T must be either Cloneable or java.io.Serializable? - dp *)
   | compat_refType_array_array_primitive_type : forall t,       
       compat_refType p (ArrayType (PrimitiveType t)) (ArrayType (PrimitiveType t))
   | compat_refType_array_array_reference_type : forall tpS tpT,       
       compat_refType p tpS tpT ->
       compat_refType p (ArrayType (ReferenceType tpS)) (ArrayType (ReferenceType tpT)).

  Axiom subclass_name_dec : forall p cn1 cn2,
    {subclass_name p cn1 cn2}+{~subclass_name p cn1 cn2}.
  
  Axiom defined_field_dec : forall p cn f,
    {defined_field p cn f}+{~defined_field p cn f}.

End Make.

Module P <: PROGRAM := Make.

(* 
 Local Variables: 
 coq-prog-name: "coqtop -I ../maps -I ../reference_semantics -emacs"
 End:
*)
