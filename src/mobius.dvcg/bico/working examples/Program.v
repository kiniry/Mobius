(* <Insert License Here>

    $Id: Program.v 81 2006-03-30 22:27:58Z davidpichardie $ *)

(** Formalization of Java programs.
 Based on the report secsafe-tl-005:
 @see http://www.doc.ic.ac.uk/~siveroni/secsafe/docs/secsafe-tl-005.pdf
 Simplifications have been made with the objective that a straightforward
 classfile parser would implement this API.

 @author Frederic Besson and David Pichardie *)


Require Import List.
Require Import ZArith.
Require Import Relation_Operators.

(*Require Export MapSignatures.*)
Open Local Scope type_scope.

(* Where Lists are used, sometimes Sets would be more adequate.
  However, this would complicate the specification.
*)

Definition distinct (A B:Set) (f:A->B) (l:list A) : Prop :=
  forall x y, In x l -> In y l -> f x = f y -> x = y.
Implicit Arguments distinct.

(** Main module for representing a Java program *)

Module Type PROGRAM.

  (** Main types to be manipulated by the API *)
  Parameter Program :Set.
  Parameter Class : Set.
  Parameter Interface : Set.
  Parameter Var : Set.
  Parameter Field : Set.
  Parameter Method : Set.
  Parameter BytecodeMethod : Set.
  Parameter ExceptionHandler : Set.
  Parameter MethodSignature : Set.
  Parameter FieldSignature :Set.
  Parameter PC : Set.

 (** Variables are indexed by integers *)
  Parameter Var_toN : Var -> nat.
  Parameter N_toVar : nat -> Var.
  Parameter Var_toN_bij1 : forall v, N_toVar (Var_toN v) = v.
  Parameter Var_toN_bij2 : forall n, Var_toN (N_toVar n) = n.


  (** Handling of qualified names *)
  Parameter PackageName : Set.
  Parameter ShortClassName : Set.
  Parameter ShortMethodName : Set.
  Parameter ShortFieldName : Set.

  (**For example the qualified name [java.lang.String] of the class [String],
      is decomposed into [java.lang] for the package name and [String] for the
       short name.  *)
  Definition ClassName := PackageName * ShortClassName.
  Definition InterfaceName := PackageName * ShortClassName.
  Definition MethodName := ClassName * ShortMethodName.
  Definition FieldName := ClassName * ShortFieldName.

  (** Some constants *)
  Parameter javaLang : PackageName.
  Parameter object : ShortClassName.
  Parameter throwable : ShortClassName.

  (** Native Exceptions *)
  Parameter NullPointerException ArrayIndexOutOfBoundsException ArrayStoreException
            NegativeArraySizeException ClassCastException ArithmeticException : ShortClassName.

  (** visibility modifiers *)
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
      (* + Int64, Float,Double *)
      (* + ReturnAddressType subroutines *)

 
  Inductive CompInt : Set := EqInt | NeInt | LtInt | LeInt | GtInt | GeInt.
  Inductive CompRef : Set := EqRef | NeRef.

  Inductive BinopInt : Set := AddInt | AndInt | DivInt | MulInt | OrInt | RemInt 
                            | ShlInt | ShrInt | SubInt | UshrInt | XorInt.

  (* Type information used for Vaload and Saload *)
  Inductive ArrayKind : Set :=
    | Aarray
    | Iarray
    | Barray
    | Sarray.
    
  (* Type information used for Vload, Vstore and Vreturn *)
  Inductive ValKind : Set :=
    | Aval
    | Ival.


  Module Type OFFSET_TYPE.
    (* The type of address offsets *)
    Parameter t : Set.
     (** Jumps are defined in terms of offsets with respect to the current address. **)
    Parameter jump : PC -> t -> PC.
  End OFFSET_TYPE.
  Declare Module OFFSET : OFFSET_TYPE.

  (** Operations on the signatures of fields *)
  Module Type FIELDSIGNATURE_TYPE.
    Parameter name : FieldSignature  -> FieldName.
    Parameter type : FieldSignature -> type.
    Parameter eq_dec : forall f1 f2:FieldSignature, f1=f2 \/ ~f1=f2.
  End FIELDSIGNATURE_TYPE.
  Declare Module FIELDSIGNATURE : FIELDSIGNATURE_TYPE.

  (** Content of a method signature *)
  Module Type METHODSIGNATURE_TYPE.
    (* The method name *)
    Parameter name : MethodSignature -> MethodName.
    (** Java types for parameters values *)
    Parameter parameters : MethodSignature -> list type.
    (** Java type for return value, the constructor [None] of type option being used for the [Void] type *)
    Parameter result : MethodSignature -> option type.

    Parameter eq_dec : 
      forall mid1 mid2:MethodSignature, mid1=mid2 \/ ~mid1=mid2.
  End METHODSIGNATURE_TYPE.
  Declare Module METHODSIGNATURE : METHODSIGNATURE_TYPE.

    (** Parser translation :

  aaload             --> Vaload Aarray
  aastore            --> Vastore Aarray
  aconst_null        --> Aconst_null
  aload x            --> Vload Aval x
  aload_<n>          --> Vload Aval n
  anewarray t        --> Newarray (ReferenceType t)
  areturn            --> Vreturn Aarray
  arraylength        --> Arraylength
  astore x           --> Vstore Aval x
  astore_<n>         --> Vstore Aval n
  athrow             --> Athrow
  baload             --> Vaload Barray
  bastore            --> Vastore Barray
  bipush c           --> Const BYTE c
  caload             --> char not supported
  castore            --> char not supported
  checkcast t        --> Checkcast t
  d2f                --> double not supported
  d2i                --> double not supported
  d2l                --> double not supported
  dadd               --> double not supported
  daload             --> double not supported
  dastore            --> double not supported
  dcmp<op>           --> double not supported
  dconst_<d>         --> double not supported
  ddiv               --> double not supported
  dload              --> double not supported
  dload_<n>          --> double not supported
  dmul               --> double not supported
  dneg               --> double not supported
  drem               --> double not supported
  dreturn            --> double not supported
  dstore             --> double not supported
  dstore_<n>         --> double not supported
  dsub               --> double not supported
  dup                --> Dup
  dup_x1             --> Dup_x1
  dup_x2             --> Dup_x2
  dup2               --> Dup2
  dup2_x1            --> Dup2_x1
  dup2_x2            --> Dup2_x2
  f2d                --> float not supported
  f2i                --> float not supported
  f2l                --> float not supported
  fadd               --> float not supported
  faload             --> float not supported
  fastore            --> float not supported
  fcmp<op>           --> float not supported
  fconst_<f>         --> float not supported
  fdiv               --> float not supported
  fload              --> float not supported
  fload_<n>          --> float not supported
  fmul               --> float not supported
  fneg               --> float not supported
  frem               --> float not supported
  freturn            --> float not supported
  fstore             --> float not supported
  fstore_<n>         --> float not supported
  fsub               --> float not supported
  getfield f         --> Getfield f
  getstatic f        --> Getstatic f
  goto o             --> Goto o    
  goto_w o           --> Goto o
  i2b                --> I2b
  i2c                --> char not supported
  i2d                --> double not supported
  i2f                --> float not supported
  i2l                --> long not supported
  i2s                --> I2s
  iadd               --> Ibinop AddInt
  iaload             --> Vaload Iarray
  iand               --> Ibinop AndInt
  iastore            --> Vastore Iarray
  iconst_<i>         --> Const i
  idiv               --> Ibinop DivInt
  if_acmp<cond> o    --> If_acmp cond o
  if_icmp<cond> o    --> If_icmp cond o
  if<cond> o         --> If0 cond o
  ifnonnull o        --> Ifnull NeRef o
  ifnull o           --> Ifnull EqRef o
  iinc x c           --> Iinc x c
  iload x      	     --> Vload Ival x
  iload_<n>    	     --> Vload Ival n
  imul         	     --> Ibinop MulInt
  ineg         	     --> Ineg
  instanceof t       --> Instanceof t
  invokeinterface m  --> Invokeinterface m
  invokespecial m    --> Invokespecial m
  invokestatic m     --> Invokestatic m
  invokevirtual m    --> Invokevirtual m
  ior                --> Ibinop OrInt
  irem               --> Ibinop RemInt
  ireturn            --> Vreturn Ival
  ishl               --> Ibinop ShlInt
  ishr               --> Ibinop ShrInt
  istore x     	     --> Vstore Ival x
  istore_<n>   	     --> Vstore Ival n
  isub               --> Ibinop SubInt
  iushr              --> Ibinop UshrInt
  ixor               --> Ibinop XorInt
  jsr                --> subroutines not supported
  jsr_w              --> subroutines not supported
  l2d                --> long not supported
  l2f                --> long not supported
  l2i                --> long not supported
  ladd               --> long not supported
  laload             --> long not supported
  land               --> long not supported
  lastore            --> long not supported
  lcmp               --> long not supported
  lconst_<l>         --> long not supported
  ldc c              --> Const c (but strings not supported)
  ldc_w c            --> Const c (but strings not supported)
  ldc2_w c           --> long and double not supported
  ldiv               --> long not supported
  lload              --> long not supported
  lload_<n>          --> long not supported
  lmul               --> long not supported
  lneg               --> long not supported
  lookupswitch d l   --> Lookupswitch d l
  lor                --> long not supported
  lrem               --> long not supported
  lreturn            --> long not supported
  lshl               --> long not supported
  lshr               --> long not supported
  lstore             --> long not supported
  lstore_<n>         --> long not supported
  lsub               --> long not supported
  lushr              --> long not supported
  lxor               --> long not supported
  monitorenter       --> multithreading not supported
  monitorexit        --> multithreading not supported
  multianewarray     --> not supported
  new c              --> New c
  newarray t         --> Newarray (PrimitiveType t)
  nop                --> Nop
  pop                --> Pop
  pop2               --> Pop2
  putfield f         --> Putfield f
  putstatic f        --> Putstatic f
  ret                --> subroutines not supported
  return             --> Return
  saload             --> Vaload Sarray
  sastore            --> Vastore Sarray
  sipush c           --> Const c
  swap               --> Swap
  tableswitch d lo l --> Tableswitch d lo l
   *)

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
(*   | Multianewarray (t:refType) (d:Z) | New (cl:ClassName) *)
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

  (** Operations on exception handlers *)
  Module Type EXCEPTIONHANDLER_TYPE.
  (** class of the caught exception *)
    (** The constructor [None] of type option being used to implement [finally]. It
    matches any exception *)
    Parameter catchType : ExceptionHandler -> option ClassName.
    (** is the given PC in range of the handler *)
    Parameter isPCinRange : ExceptionHandler -> PC -> bool.
    (** location of the handler code *) 
    Parameter handler : ExceptionHandler -> PC.
  End EXCEPTIONHANDLER_TYPE.
  Declare Module EXCEPTIONHANDLER : EXCEPTIONHANDLER_TYPE.

  (** Operations on bytecode methods *)
  Module Type BYTECODEMETHOD_TYPE.
    Parameter firstAddress : BytecodeMethod -> PC.
    Parameter nextAddress : BytecodeMethod -> PC -> option PC.
    Parameter instructionAt : BytecodeMethod -> PC -> option Instruction.
    (* The list of exception is supposed to be ordered from the innermost to
       the outermost handler, otherwise the behavior might be unexpected 
       @see JVMS 3.10 *)
    Parameter exceptionHandlers : BytecodeMethod -> list ExceptionHandler.

    (** max number of local variables *)
    Parameter max_locals : BytecodeMethod -> nat.
    (** max number of elements on the operand stack *)
    Parameter max_operand_stack_size : BytecodeMethod -> nat.

    Definition DefinedInstruction (bm:BytecodeMethod) (pc:PC) : Prop :=
      exists i, instructionAt bm pc = Some i.
   
  End BYTECODEMETHOD_TYPE.
  Declare Module BYTECODEMETHOD : BYTECODEMETHOD_TYPE.
 
  (** Content of a method *)
  Module Type METHOD_TYPE.

    Parameter signature : Method -> MethodSignature.
    (** A method that is not abstract has a method body *)
    Parameter body : Method -> option BytecodeMethod.

    (* modifiers *)
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
  Declare Module METHOD : METHOD_TYPE.

  (** Operations on fields *)
  Module Type FIELD_TYPE.
    Parameter signature : Field -> FieldSignature.    
    Parameter isFinal : Field -> bool.
    Parameter isStatic : Field -> bool.

    Parameter visibility : Field -> Visibility.

    Inductive value : Set :=
      | Int (v:Z) (* Numeric value *)
(*      | Lst (l:list Z)   Array of nums *)
      | NULL (* reference *)
      | UNDEF (* default value *).

    (** Initial (default) value. Must be compatible with the type of the field. *)
    Parameter initValue : Field ->  value.

  End FIELD_TYPE.
  Declare Module FIELD : FIELD_TYPE.

  (** Content of a Java class *)
  Module Type CLASS_TYPE.

    Parameter name : Class -> ClassName.
    (** direct superclass *)
    (** All the classes have a superClass except [java.lang.Object]. (see [Wf.v]) *)
    Parameter superClass : Class -> option ClassName.
    (** list of implemented interfaces *)
    Parameter superInterfaces : Class -> list InterfaceName.

    Parameter field : Class -> ShortFieldName -> option Field.

    Parameter method : Class -> MethodSignature -> option Method.
    Parameter method_signature_prop : forall cl mid m,
      method cl mid = Some m -> mid = METHOD.signature m.
    Definition defined_Method (cl:Class) (m:Method) :=
      method cl (METHOD.signature m) = Some m.
    
    (* modifiers *)
    Parameter isFinal : Class -> bool.
    Parameter isPublic : Class -> bool.
    Parameter isAbstract : Class -> bool.

  End CLASS_TYPE.
  Declare Module CLASS : CLASS_TYPE.

  (** Content of a Java interface *)
  Module Type INTERFACE_TYPE.

    Parameter name : Interface -> InterfaceName. 

    Parameter superInterfaces : Interface -> list InterfaceName.

    Parameter field : Interface -> ShortFieldName -> option Field.

    Parameter method : Interface -> MethodSignature -> option Method.

   (* modifiers *)
    Parameter isFinal : Interface -> bool.
    Parameter isPublic : Interface -> bool.
    Parameter isAbstract : Interface -> bool.
  End INTERFACE_TYPE.
  Declare Module INTERFACE : INTERFACE_TYPE.

  (** Content of a Java Program *)
  Module Type PROG_TYPE.
    (** accessor to a class from its qualified name *)
    Parameter class : Program -> ClassName -> option Class.
    Definition defined_Class (p:Program) (cl:Class) :=
      class p (CLASS.name cl) = Some cl.

    Parameter name_class_invariant1 : forall p cn cl,
      class p cn = Some cl -> cn = CLASS.name cl.

    (** accessor to an interface from its qualified name *)
    Parameter interface : Program -> InterfaceName -> option Interface.
    Definition defined_Interface (p:Program) (i:Interface) :=
      interface p (INTERFACE.name i) = Some i.

    Parameter name_interface_invariant1 : forall p cn cl,
      interface p cn = Some cl -> cn = INTERFACE.name cl.

  End PROG_TYPE.
  Declare Module PROG : PROG_TYPE.

(**  
      Definitions on programs 
 
  *)

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


  (** Extra tools for implementation *)
  Parameter PC_eq : PC -> PC -> bool.
  Parameter PC_eq_spec : forall p q:PC, if PC_eq p q then p=q else p<>q.
  Parameter PC_eq_dec : forall pc1 pc2:PC, pc1=pc2 \/ ~pc1=pc2.

  Parameter Meth_eq : Method -> Method -> bool.
  Parameter Meth_eq_spec :
          forall p q:Method, if Meth_eq p q then p=q else p<>q.
  
  Parameter Var_eq_dec : forall x1 x2:Var, x1=x2 \/ ~x1=x2. 
  Parameter ClassName_eq_dec : forall c1 c2:ClassName, c1=c2 \/ ~c1=c2.

End PROGRAM.
    
(** printing -> # &rarr #*)
(** printing <= # <font size=3>&le</font> #*)
(** printing < # <font size=3>&lt</font> #*)
(** printing > # <font size=3>&gt</font> #*)
(** printing >: # <font size=3>&ge</font> #*)
(** printing <-> # &harr #*)
(** printing /\ # &and #*)
(** printing \/ # &or #*)
(** printing <> # <font size=3>&ne</font> #*)
(** printing forall # &forall #*)
(** printing exists # &exist #*)
 
  
(* 
 Local Variables: 
 coq-prog-name: "coqtop -emacs"
 End:
*)
