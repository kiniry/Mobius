Require Import ImplemProgramWithList.

Import P.

Module TheProgram.

  Module Object.
    Definition className : ClassName := javaLangObject.
   
    Definition _init_Signature : MethodSignature := METHODSIGNATURE.Build_t
	(className, 1%positive)	(** method name **)
	nil						(** parameters : list type **)
	None					(** result : option type **)
    .

    Definition _init_Method : Method := METHOD.Build_t
	_init_Signature
	None
	false 					(** isFinal **)
	true						(** isStatic **)
	Public					(** Visibility **)
    .

    Definition class : Class := CLASS.Build_t
	className
	None     					(** superClass : option ClassName **)
	nil						(** superInterfaces : list InterfaceName **)
	nil						(** fields : list Field **)
	(_init_Method::nil)			(** methods : list Method **)
	false					(** isFinal : bool **)
	true						(** isPublic : bool **)
	false					(** isAbstract : bool **)
    .

  End Object.	

  Definition EmptyPackageName := 2%positive.

  Module Addition. 				(** one module for each class **)

    Definition className : ClassName := (EmptyPackageName, 11%positive). (** package id, class id **)

    (* signatures *)

    Definition zFieldSignature : FieldSignature := FIELDSIGNATURE.Build_t
	(className, 12%positive)	(** field name **)
	(PrimitiveType INT)
    .
		
    Definition AdditionSignature : MethodSignature := METHODSIGNATURE.Build_t
	(className, 13%positive) 	(** method name **)
	nil						(** list of parameter types **)
	(Some (ReferenceType (ClassType className)))	(** optional result type **)
    .

    Definition addSignature : MethodSignature := METHODSIGNATURE.Build_t
	(className,14%positive) 	(** method name **)
	(PrimitiveType INT :: nil)		(** list of parameter types **)
	(Some (PrimitiveType INT))	(** optional result type **)
    .	

    (* fields *)

    Definition zField : Field := FIELD.Build_t
	zFieldSignature
	false 					(** isFinal : bool **)
	true						(** isStatic : bool **)
	Private					(** visibility : Visibility **)
	UNDEF					(** initValue : value **)
    .

    (* methods *)

    (* method: public Addition() *)

    Definition AdditionInstructions : list (PC*Instruction) :=
	(0%N, Aload 0%N) ::
	(1%N, Invokespecial Object._init_Signature) ::
	(4%N, Return) ::
	nil
    .

    Definition AdditionBody : BytecodeMethod := Build_BytecodeMethod_
	AdditionInstructions
	nil 						(** list of ExceptionHandlers **)
	1						(** max_locals **)
	1						(** max_operand_stack_size **)
    .

    Definition AdditionMethod : Method := METHOD.Build_t
	AdditionSignature
	(Some AdditionBody)
	false 					(** isFinal **)
	true						(** isStatic **)
	Public					(** Visibility **)
    .


    (* method: public static int add(int) *)

    Definition addInstructions : list (PC*Instruction) :=
	(0%N, Iload 0%N) ::
	(1%N, Getstatic zFieldSignature) ::
	(4%N, Ibinop AddInt) ::
	(5%N, Istore 1%N) ::
	(6%N, Iload 1%N) ::
	(7%N, Ireturn) ::
        nil
    .

    Definition addBody : BytecodeMethod := Build_BytecodeMethod_ 
	addInstructions
	nil 						(** list of ExceptionHandlers **)
	2						(** max_locals **)
	2						(** max_operand_stack_size **)
    .

    Definition addMethod : Method := METHOD.Build_t
	addSignature
	(Some addBody)
	false 					(** isFinal **)
	true						(** isStatic **)
	Public					(** Visibility **)
    .

    Definition class : Class := CLASS.Build_t
	className
	(Some javaLangObject) 		(** superclass **)        
	nil 						(** list of implemented interfaces **)
   	(zField::nil)				(** list of fields **)
	(AdditionMethod::addMethod::nil)	(** list of methods **)
	false					(** isFinal **)
	true						(** isPublic **)
	false					(** isAbstract **) 
    .

  End Addition.


  Definition AllClasses : list Class := Addition.class :: Object.class :: nil.
	(** in general: Class1 :: ... :: Classn :: nil **)

  Definition AllInterfaces : list Interface := nil.
	(** in general: Interface1 :: ... :: Interfacen :: nil **)

  Definition program : Program := PROG.Build_t
	AllClasses
	AllInterfaces
  .

End TheProgram.
