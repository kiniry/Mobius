Require Import ImplemProgramWithList.

Import P.

Module TheProgram.

  Module java_lang_Object.
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
	false						(** isNative **)
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

  End java_lang_Object.	

  Module Addition. 				(** one module for each class **)

    Definition className : ClassName := (EmptyPackageName, 11%positive). (** package id, class id **)

    (* signatures *)

    Definition zFieldSignature : FieldSignature := FIELDSIGNATURE.Build_t
	(className, 12%positive)	(** field name **)
	(PrimitiveType INT)
    .
		
    Definition _init_Signature : MethodSignature := METHODSIGNATURE.Build_t
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
	FIELD.UNDEF				(** initValue : value **)
    .

    (* methods *)

    (* method: public Addition() *)

    Definition _init_Instructions : list (PC*Instruction) :=
        (0%N, Vload Aval 0%N)::
        (1%N, Invokespecial java_lang_Object._init_Signature)::
        (4%N, Return)::
        nil
    .

    Definition _init_Body : BytecodeMethod := BYTECODEMETHOD.Build_t
	_init_Instructions
	nil 						(** list of ExceptionHandlers **)
	1						(** max_locals **)
	1						(** max_operand_stack_size **)
    .

    Definition _init_Method : Method := METHOD.Build_t
	_init_Signature
	(Some _init_Body)
	false 					(** isFinal **)
	true						(** isStatic **)
	false 					(** isNative **)
	Public					(** Visibility **)
    .


    (* method: public static int add(int) *)

    Definition addInstructions : list (PC*Instruction) :=
        (0%N, Vload Ival 0%N)::
        (1%N, Getstatic Addition.zFieldSignature)::
        (4%N, Ibinop AddInt)::
        (5%N, Vstore Ival 1%N)::
        (6%N, Vload Ival 1%N)::
        (7%N, Vreturn Ival)::
        nil
    .

    Definition addBody : BytecodeMethod := BYTECODEMETHOD.Build_t 
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
	false 					(** isNative **)
	Public					(** Visibility **)
    .

    Definition class : Class := CLASS.Build_t
	className
	(Some javaLangObject) 		(** superclass **)        
	nil 						(** list of implemented interfaces **)
   	(zField::nil)				(** list of fields **)
	(_init_Method::addMethod::nil)	(** list of methods **)
	false						(** isFinal **)
	true						(** isPublic **)
	false						(** isAbstract **) 
    .

  End Addition.


  Definition AllClasses : list Class := Addition.class :: java_lang_Object.class :: nil.
	(** in general: Class1 :: ... :: Classn :: nil **)

  Definition AllInterfaces : list Interface := nil.
	(** in general: Interface1 :: ... :: Interfacen :: nil **)

  Definition program : Program := PROG.Build_t
	AllClasses
	AllInterfaces
  .

End TheProgram.
