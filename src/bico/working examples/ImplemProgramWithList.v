Add LoadPath "../Library".
Require Export List.
Require Export ZArith.
Require Export Program.
Require Export Relation_Operators.
Require Export EqBoolAux.
Require Export PosAux.

Section findList.
  Variable A B : Set.
  Variable getKey : A -> B.
  Variable Beq : B -> B -> bool.
  Variable Beq_spec : forall x y, if Beq x y then x = y else x <> y.

  Fixpoint find (b:B) (l:list A) {struct l} : option A :=
    match l with
      nil => None
    | a::q => if Beq (getKey a) b then Some a
              else find b q
    end.
  Lemma find_getKey : forall b l a,
    find b l = Some a -> b = getKey a.
  Proof.
    induction l; simpl.
    intros; discriminate.
    intro; generalize (Beq_spec (getKey a) b);destruct (Beq (getKey a) b); intros.
    injection H0;intros;subst;trivial.    auto.
  Qed.

End findList.

Module Make <: PROGRAM.

  Definition eq_dec (A:Set) := forall x y:A, x=y \/~x=y.

  Definition Var := N. 
  Lemma Var_eq_dec : eq_dec Var.
  Proof. exact (Aeq_dec _ Neq Neq_spec). Qed.
  Definition Var_toN : Var -> nat := nat_of_N.
  Definition N_toVar : nat -> Var := N_of_nat.
  Lemma Var_toN_bij1 : forall v, N_toVar (Var_toN v) = v.
  Proof. exact nat_of_N_bij2. Qed.
  Lemma Var_toN_bij2 : forall n, Var_toN (N_toVar n) = n.
  Proof. exact nat_of_N_bij1. Qed.

  Definition PC : Set := N.
  Definition PC_eq := Neq.
  Definition PC_eq_spec := Neq_spec.
  Lemma PC_eq_dec : eq_dec PC.
  Proof. exact Var_eq_dec. Qed.

  Definition PackageName : Set := positive.
  Definition ShortClassName : Set := positive.
  Definition ShortMethodName : Set := positive.
  Definition ShortFieldName : Set := positive.
  Open Local Scope type_scope.
  Definition ClassName := PackageName * ShortClassName.
  Definition InterfaceName := PackageName * ShortClassName.
  Definition MethodName := ClassName * ShortMethodName.
  Definition FieldName := ClassName * ShortFieldName.

 Definition eqClassName : ClassName -> ClassName -> bool := prod_eq _ Peq _ Peq.
  Lemma eqClassName_spec : forall x y, if eqClassName x y then x = y else x <> y.
  Proof. exact (prod_eq_spec _ Peq Peq_spec _ Peq Peq_spec). Qed.
  Lemma ClassName_eq_dec : eq_dec ClassName.
  Proof. exact (Aeq_dec _ eqClassName eqClassName_spec). Qed.

  Definition eqInterfaceName : InterfaceName ->InterfaceName -> bool := 
      prod_eq _ Peq _ Peq.
  Lemma eqInterfaceName_spec : forall x y, if eqInterfaceName x y then x = y else x <> y.
  Proof. exact (prod_eq_spec _ Peq Peq_spec _ Peq Peq_spec). Qed.
  Lemma InterfaceName_eq_dec : eq_dec InterfaceName.
  Proof. exact (Aeq_dec _ eqClassName eqClassName_spec). Qed.

  Definition eqMethodName : MethodName -> MethodName -> bool := 
    prod_eq _ eqClassName _ Peq.
  Lemma eqMethodName_spec : forall x y, if eqMethodName x y then x = y else x <> y.
  Proof. exact (prod_eq_spec _ eqClassName eqClassName_spec _ Peq Peq_spec). Qed.
  Lemma MethodName_eq_dec : eq_dec MethodName.
  Proof. exact (Aeq_dec _ eqMethodName eqMethodName_spec). Qed.

  Definition eqFieldName : FieldName -> FieldName -> bool :=
     prod_eq _ eqClassName _ Peq.
  Lemma eqFieldName_spec : forall x y, if eqFieldName x y then x = y else x <> y.
  Proof. exact (prod_eq_spec _ eqClassName eqClassName_spec _ Peq Peq_spec). Qed.
  Lemma FieldName_eq_dec : eq_dec FieldName.
  Proof. exact (Aeq_dec _ eqFieldName eqFieldName_spec). Qed.

  Open Scope positive_scope.
  (* IMPORTANT CONSTANT CONVENTIONS FOR PARSER !! *)
  Definition javaLang : PackageName := 1.
  Definition EmptyPackageName : PackageName := 2.
  Definition object : ShortClassName := 1.
  Definition NullPointerException : ShortClassName := 2.
  Definition ArrayIndexOutOfBoundsException : ShortClassName := 3.
  Definition ArrayStoreException : ShortClassName := 4.
  Definition NegativeArraySizeException : ShortClassName := 5.
  Definition ClassCastException : ShortClassName := 6.
  Definition ArithmeticException : ShortClassName := 7.
  Definition throwable : ShortClassName := 8.

  Inductive Visibility : Set :=
    Package | Protected | Private | Public.

 Definition eqVisibility x y := 
    match x, y with 
    | Package, Package => true
    | Protected, Protected => true
    | Private, Private => true
    | Public, Public => true
    | _, _ => false
    end.
  Lemma eqVisibility_spec : forall x y, if eqVisibility x y then x = y else x <> y.
  Proof. destruct x;destruct y;simpl;trivial;intro; discriminate. Qed.
  Lemma Visibility_eq_dec : eq_dec Visibility.
  Proof. exact (Aeq_dec _ eqVisibility eqVisibility_spec). Qed.

  Inductive type : Set :=
      | ReferenceType (rt : refType)
      | PrimitiveType (pt: primitiveType)
  with refType :Set := 
      | ArrayType (typ:type) 
      | ClassType  (ct:ClassName)
      | InterfaceType (it:InterfaceName)
  with  primitiveType : Set := 
      | BOOLEAN  | BYTE | SHORT | INT.

  Scheme type_strong_rec := Induction for type Sort Set
    with refType_strong_rec := Induction for refType Sort Set.
 
  Scheme type_strong_ind := Induction for type Sort Prop
    with refType_strong_ind := Induction for refType Sort Prop.
  Definition eq_primitiveType x y :=
    match x, y with
    | BOOLEAN, BOOLEAN => true
    | BYTE, BYTE => true
    | SHORT, SHORT => true
    | INT, INT => true 
    | _, _ => false
    end.
  Lemma eq_primitiveType_spec : forall x y, if eq_primitiveType x y then x = y else x <> y.
  Proof.
   destruct x;destruct y;simpl;trivial; intro;discriminate.
  Qed.
  Lemma primitiveType_dec : eq_dec primitiveType.
  Proof.  exact (Aeq_dec _ eq_primitiveType eq_primitiveType_spec). Qed.

  Fixpoint eq_type (t1 t2:type) {struct t1} : bool := 
    match t1, t2 with 
    | ReferenceType rt1, ReferenceType rt2 => eq_reftype rt1 rt2
    | PrimitiveType pt1, PrimitiveType pt2 => eq_primitiveType pt1 pt2
    | _, _ => false
    end
  with eq_reftype (rt1 rt2: refType) {struct rt1} : bool := 
    match rt1, rt2 with
    | ArrayType t1, ArrayType t2 => eq_type t1 t2
    | ClassType cn1, ClassType cn2 => eqClassName cn1 cn2
    | InterfaceType in1, InterfaceType in2 => eqInterfaceName in1 in2
    |_, _ => false
    end.

  Lemma eq_type_spec : forall t1 t2, if eq_type t1 t2 then t1 = t2 else t1 <> t2.
  Proof.
   induction t1 using type_strong_ind with 
        (P0:=
          fun rt1 => forall rt2, if eq_reftype rt1 rt2 then rt1 = rt2 else rt1 <> rt2);intros.
   destruct t2;simpl;try (intro;discriminate;fail).
   assert (UU:=IHt1 rt0);destruct (eq_reftype rt rt0);subst;trivial.
   intro H;injection H;auto.
   destruct t2;simpl;try (intro;discriminate;fail).
   assert (UU := eq_primitiveType_spec pt pt0);destruct (eq_primitiveType pt pt0);subst;trivial.
   intro H;injection H;auto.
   destruct rt2;simpl;try (intro H;discriminate H).
   assert (UU:=IHt1 typ);destruct (eq_type t1 typ);subst;trivial.
   intro H;injection H;auto.
   destruct rt2;simpl;intros;try (intro;discriminate;fail).
   assert (UU := eqClassName_spec ct ct0);destruct (eqClassName ct ct0);subst;trivial.
   intro H;injection H;auto.
   destruct rt2;simpl;intros;try (intro;discriminate;fail).
   assert (UU := eqInterfaceName_spec it it0);destruct (eqInterfaceName it it0);subst;trivial.
   intro H;injection H;auto.
  Qed.
  Lemma type_dec : eq_dec type.
  Proof. exact (Aeq_dec _ eq_type eq_type_spec). Qed.

  Inductive CompInt : Set := EqInt | NeInt | LtInt | LeInt | GtInt | GeInt.
  Inductive CompRef : Set := EqRef | NeRef.

  Inductive BinopInt : Set := AddInt | AndInt | DivInt | MulInt | OrInt | RemInt 
                            | ShlInt | ShrInt | SubInt | UshrInt | XorInt.

  Module Type OFFSET_TYPE.
    Parameter t : Set.
    Parameter jump : PC -> t -> PC.
  End OFFSET_TYPE.
  Module OFFSET <: OFFSET_TYPE.
    Definition t := Z.
    Definition jump (pc:PC) (ofs:t) : PC := Zabs_N (Zplus (Z_of_N pc) ofs).
  End OFFSET.

  Module FIELDSIGNATURE.
    Record t :Set := {
      name : FieldName;
      type : type
    }.
    Definition eq_t (x y : t) := 
         let (n1,t1) := x in
         let (n2,t2) := y in
         if eqFieldName n1 n2 then eq_type t1 t2 else false.
    Lemma eq_t_spec : forall x y, if eq_t x y then x = y else x <> y.
    Proof. 
      intros (n1,t1) (n2,t2);simpl;generalize (eqFieldName_spec n1 n2);
       destruct (eqFieldName n1 n2);intros.
      generalize (eq_type_spec t1 t2);destruct (eq_type t1 t2);intros;subst;trivial.
      intro H;injection H;auto.
      intro H1;injection H1;auto.
    Qed.
    Lemma eq_dec : eq_dec t.
    Proof. exact (Aeq_dec _ eq_t eq_t_spec). Qed.
  End FIELDSIGNATURE.

  Definition FieldSignature := FIELDSIGNATURE.t.

  Module Type FIELDSIGNATURE_TYPE.
    Parameter name : FieldSignature  -> FieldName.
    Parameter type : FieldSignature -> type.
    Parameter eq_dec : forall f1 f2:FieldSignature,  f1=f2 \/~f1=f2.
  End FIELDSIGNATURE_TYPE.


  Module METHODSIGNATURE.
    Record t :Set := {
      name : MethodName;
      parameters : list type;
      result : option type
    }.
     Definition eq_t (x y : t) :=
      let (n1,p1,r1) := x in
      let (n2,p2,r2) := y in
      if eqMethodName n1 n2 then 
       if list_eq _ eq_type p1 p2 then opt_eq _ eq_type r1 r2 
       else false
      else false.
    Lemma eq_t_spec : forall x y, if eq_t x y then x = y else x <> y.
    Proof.
      intros (n1,p1,r1) (n2,p2,r2);simpl;generalize (eqMethodName_spec n1 n2);
       destruct (eqMethodName n1 n2);intros.
      generalize (list_eq_spec _ eq_type eq_type_spec p1 p2);
       destruct (list_eq _ eq_type p1 p2);intros.
      generalize (opt_eq_spec _ eq_type eq_type_spec r1 r2);
       destruct (opt_eq _ eq_type r1 r2);intros. subst;trivial.
      intro UU;injection UU;auto.
      intro UU;injection UU;auto.
      intro H1;injection H1;auto.
    Qed.
    Lemma eq_dec : eq_dec t.
    Proof. exact (Aeq_dec _ eq_t eq_t_spec). Qed.
  End METHODSIGNATURE.

  Definition MethodSignature := METHODSIGNATURE.t.

  Module Type METHODSIGNATURE_TYPE.
    Parameter name : MethodSignature -> MethodName.
    Parameter parameters : MethodSignature -> list type.
    Parameter result : MethodSignature -> option type.
    Parameter eq_dec : forall mid1 mid2:MethodSignature,  mid1=mid2 \/~mid1=mid2.
  End METHODSIGNATURE_TYPE.

  Inductive ArrayKind : Set :=
    | Aarray
    | Iarray
    | Barray
    | Sarray.
    
  Inductive ValKind : Set :=
    | Aval
    | Ival.

  Inductive Instruction : Set :=
   | Aconst_null
   | Arraylength 
   | Athrow
   | Checkcast (t:refType)
   | Const (t:primitiveType) (z:Z)
   | Dup
   | Dup_x1
   | Dup_x2
   | Dup2
   | Dup2_x1
   | Dup2_x2
   | Getfield (f:FieldSignature)
   | Getstatic  (f:FieldSignature) 
   | Goto (o:OFFSET.t)
   | I2b
   | I2s
   | Ibinop (op:BinopInt)
   | If_acmp (cmp:CompRef) (o:OFFSET.t)
   | If_icmp (cmp:CompInt) (o:OFFSET.t) 
   | If0 (cmp:CompInt) (o:OFFSET.t)
   | Ifnull (cmp:CompRef) (o:OFFSET.t)
   | Iinc (x:Var) (z:Z)
   | Ineg 
   | Instanceof (t:refType) 
   | Invokeinterface (m:MethodSignature)
   | Invokespecial (m:MethodSignature)
   | Invokestatic (m:MethodSignature)
   | Invokevirtual (m:MethodSignature)
   | Lookupswitch (def:OFFSET.t) (l:list (Z*OFFSET.t)) 
   | New (c:ClassName)
   | Newarray (t:type)
   | Nop
   | Pop
   | Pop2
   | Putfield (f:FieldSignature)
   | Putstatic (f:FieldSignature)
   | Return
   | Swap 
   | Tableswitch (def:OFFSET.t) (low high:Z) (l:list OFFSET.t)
   | Vaload (k:ArrayKind) 
   | Vastore (k:ArrayKind)
   | Vload (k:ValKind) (x:Var)
   | Vreturn (k:ValKind)
   | Vstore (k:ValKind) (x:Var).

  Module FIELD.
    Inductive value : Set :=
    | Int (v:Z)
    | NULL 
    | UNDEF.
  Definition eq_value x y := 
     match x, y with
     | Int z1, Int z2 => Zeq z1 z2
     | NULL, NULL => true
     | UNDEF, UNDEF => true
     | _, _ => false
     end.
    Lemma eq_value_spec : forall x y, if eq_value x y then x = y else x <> y.
    Proof.
      destruct x;destruct y;intros;simpl;trivial;try (intro;discriminate;fail).
      generalize (Zeq_spec v v0);destruct (Zeq v v0);intros. subst;trivial.
      intro H1;injection H1;auto.
    Qed.

    Record t : Set := {
      signature : FieldSignature;
      isFinal : bool;
      isStatic : bool;
      visibility : Visibility;
      initValue : value
    }.
    Definition eq_t (x y:t) := 
       let (s1,f1,st1,v1,val1) := x in
       let (s2,f2,st2,v2,val2) := y in
       if FIELDSIGNATURE.eq_t s1 s2 then
        if bool_eq f1 f2 then 
         if bool_eq st1 st2 then
          if eqVisibility v1 v2 then eq_value val1 val2
          else false
        else false
      else false
     else false.
    Lemma eq_t_spec : forall x y, if eq_t x y then x = y else x <> y.
    Proof with try (intro UU;injection UU;auto;fail).     
     intros (s1,f1,st1,v1,val1)(s2,f2,st2,v2,val2);simpl.
     generalize (FIELDSIGNATURE.eq_t_spec s1 s2);destruct (FIELDSIGNATURE.eq_t s1 s2);intros...
     generalize (bool_eq_spec f1 f2);destruct (bool_eq f1 f2);intros...
     generalize (bool_eq_spec st1 st2);destruct (bool_eq st1 st2);intros...
     generalize (eqVisibility_spec v1 v2);destruct (eqVisibility v1 v2);intros...
     generalize (eq_value_spec val1 val2);destruct (eq_value val1 val2);intros...
     subst;trivial. 
    Qed.
    Lemma eq_dec : eq_dec t.
    Proof. exact (Aeq_dec _ eq_t eq_t_spec). Qed.
   
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
   Definition eq_t (x y:t) :=
     let (c1,b1,e1,h1) := x in
     let (c2,b2,e2,h2) := y in
     if opt_eq _ eqClassName c1 c2 then
      if Neq b1 b2 then 
       if Neq e1 e2 then Neq h1 h2 
       else false
      else false
     else false.
    Lemma eq_t_spec : forall x y, if eq_t x y then x = y else x <> y.    
    Proof with  try (intro UU;injection UU;auto;fail).     
      intros (c1,b1,e1,h1)(c2,b2,e2,h2);simpl.
      generalize (opt_eq_spec _ eqClassName eqClassName_spec c1 c2);
        destruct (opt_eq ClassName eqClassName c1 c2);intros ...
      generalize (Neq_spec b1 b2);destruct (Neq b1 b2);intros...
      generalize (Neq_spec e1 e2);destruct (Neq e1 e2);intros ...
      generalize (Neq_spec h1 h2);destruct (Neq h1 h2);intros ...
      subst;trivial.
     Qed.
    End EXCEPTIONHANDLER.
  Definition ExceptionHandler := EXCEPTIONHANDLER.t.

  Module Type EXCEPTIONHANDLER_TYPE.
    Parameter catchType : ExceptionHandler -> option ClassName.
    Parameter isPCinRange : ExceptionHandler -> PC -> bool.
    Parameter handler : ExceptionHandler -> PC.
  End EXCEPTIONHANDLER_TYPE.
   
  Module BYTECODEMETHOD.

    Record t : Set := {
      instr : list (PC*Instruction);
      exceptionHandlers : list ExceptionHandler;
      max_locals : nat;
      max_operand_stack_size : nat
    }.

    Definition  firstAddress (bm:t) : PC :=
      match (instr bm) with
        nil => 0%N
      | (pp,_)::_ => pp
      end.
    Fixpoint instructionAt_rec (pp0:PC) (l:list (PC*Instruction)) {struct l} : option Instruction :=
       match l with
         nil => None
       | (pp,i)::q =>
         if Neq pp0 pp then Some i
         else instructionAt_rec pp0 q
       end.
    Definition instructionAt (bm:t) (pp:PC) : option Instruction :=
     instructionAt_rec pp (instr bm).

    Fixpoint nextAddress_rec (pp0:PC) (l:list (PC*Instruction)) {struct l} : option PC :=
       match l with
         nil => None
       | (pp1,_)::q =>
         if Neq pp0 pp1 then 
            match q with
              nil => None
            | (pp2,_)::_ => Some pp2
            end
         else nextAddress_rec pp0 q
       end.

    Definition nextAddress (bm:t) (pp:PC) : option PC :=
      nextAddress_rec pp (instr bm).

    Definition DefinedInstruction (bm:t) (pc:PC) : Prop :=
      exists i, instructionAt bm pc = Some i.
   
  End BYTECODEMETHOD.
  Definition BytecodeMethod := BYTECODEMETHOD.t.


  Module Type BYTECODEMETHOD_TYPE.
    Parameter firstAddress : BytecodeMethod -> PC.
    Parameter nextAddress : BytecodeMethod -> PC -> option PC.
    Parameter instructionAt : BytecodeMethod -> PC -> option Instruction.
    Parameter exceptionHandlers : BytecodeMethod -> list ExceptionHandler.
    Parameter max_locals : BytecodeMethod -> nat.
    Parameter max_operand_stack_size : BytecodeMethod -> nat.

    Definition DefinedInstruction (bm:BytecodeMethod) (pc:PC) : Prop :=
      exists i, instructionAt bm pc = Some i.

  End BYTECODEMETHOD_TYPE.

  Module METHOD.
    Record t : Set := {
      signature : MethodSignature;
      body : option BytecodeMethod;
      isFinal : bool;
      isStatic : bool;
      isNative : bool;
      visibility : Visibility      
    }.
    Definition valid_var (m:t) (x:Var) : Prop :=
      forall bm, body m = Some bm ->
         (Var_toN x) <= (BYTECODEMETHOD.max_locals bm).
    Definition valid_stack_size (m:t) (length:nat) : Prop :=
      forall bm, body m = Some bm ->
         length <= (BYTECODEMETHOD.max_operand_stack_size bm).
  End METHOD.

  Definition Method := METHOD.t.
(***
  Parameter Meth_eq : Method -> Method -> bool.
***)
  Definition Meth_eq (m1 m2:Method) : bool :=
        METHODSIGNATURE.eq_t (METHOD.signature m1) (METHOD.signature m2).
  Parameter Meth_eq_spec :
          forall p q:Method, if Meth_eq p q then p=q else p<>q.

  Module Type METHOD_TYPE.
    Parameter signature : Method -> MethodSignature.
    Parameter body : Method -> option BytecodeMethod.
    Parameter isFinal : Method -> bool.
    Parameter isStatic : Method -> bool.
    Parameter isNative : Method -> bool.
    Parameter visibility : Method -> Visibility.
    Definition valid_var (m:Method) (x:Var) : Prop :=
      forall bm, body m = Some bm ->
         (Var_toN x) <= (BYTECODEMETHOD.max_locals bm).

    Definition valid_stack_size (m:Method) (length:nat) : Prop :=
      forall bm, body m = Some bm ->
         length <= (BYTECODEMETHOD.max_operand_stack_size bm).
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
            Peq
           s (fields cl).
    Lemma field_shortname_prop : forall cl s f,
      field cl s = Some f -> s = snd (FIELDSIGNATURE.name (FIELD.signature f)).
    Proof.
      unfold field; intros cl s f.
      apply (find_getKey Field ShortFieldName 
           (fun f => snd (FIELDSIGNATURE.name (FIELD.signature f)))).
      exact Peq_spec.
    Qed.

    Definition method : t -> MethodSignature -> option Method :=
      fun cl mid =>
       find Method MethodSignature METHOD.signature
            METHODSIGNATURE.eq_t
            mid (methods cl) .
    Lemma method_signature_prop : forall cl mid m,
      method cl mid = Some m -> mid = METHOD.signature m.
    Proof.
      unfold method; intros p cl mid.
      apply find_getKey.
      exact METHODSIGNATURE.eq_t_spec.
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
            Peq
           s (fields cl).
    Lemma field_shortname_prop : forall cl s f,
      field cl s = Some f -> s = snd (FIELDSIGNATURE.name (FIELD.signature f)).
    Proof.
      unfold field; intros cl s f.
      apply (find_getKey Field ShortFieldName 
           (fun f => snd (FIELDSIGNATURE.name (FIELD.signature f)))).
      exact Peq_spec.
    Qed.

    Definition method : t -> MethodSignature -> option Method :=
      fun cl mid =>
       find Method MethodSignature METHOD.signature
            METHODSIGNATURE.eq_t
            mid (methods cl) .
    Lemma method_signature_prop : forall cl mid m,
      method cl mid = Some m -> mid = METHOD.signature m.
    Proof.
      unfold method; intros p cl mid.
      apply find_getKey.
      exact METHODSIGNATURE.eq_t_spec.
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
          eqClassName
          cn (classes p).
    Definition defined_Class (p:t) (cl:Class) :=
      class p (CLASS.name cl) = Some cl.
    Lemma name_class_invariant1 : forall p cn cl,
      class p cn = Some cl -> cn = CLASS.name cl.
    Proof.
      unfold class; intros p cn cl.
      apply (find_getKey Class ClassName CLASS.name).
      exact eqClassName_spec.
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
      generalize (eqClassName_spec (CLASS.name cl) (CLASS.name cl));
        destruct (eqClassName (CLASS.name cl) (CLASS.name cl));intros.
      reflexivity.
      elim H0; reflexivity.
      generalize (eqClassName_spec (CLASS.name a) (CLASS.name cl));
       destruct (eqClassName (CLASS.name a) (CLASS.name cl));intros.
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
      generalize (eqClassName_spec (CLASS.name a) (CLASS.name cl));
        destruct (eqClassName (CLASS.name a) (CLASS.name cl)); intros.
      inversion H0; auto.
      right; auto.
    Qed.

    Definition interface : t -> InterfaceName -> option Interface :=
      fun p iname =>
       find Interface InterfaceName INTERFACE.name
          eqInterfaceName
          iname (interfaces p).
    Definition defined_Interface (p:t) (i:Interface) :=
      interface p (INTERFACE.name i) = Some i.
    Lemma name_interface_invariant1 : forall p iname i,
      interface p iname = Some i -> iname = INTERFACE.name i.
    Proof.
      unfold interface; intros p iname i.
      apply (find_getKey Interface InterfaceName INTERFACE.name).
      exact eqInterfaceName_spec.
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
  Definition javaLangThrowable : ClassName := (javaLang,throwable).

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

 
End Make.

Module P <: PROGRAM := Make.

(* 
 Local Variables: 
 coq-prog-name: "coqtop -emacs"
 End:
*)
