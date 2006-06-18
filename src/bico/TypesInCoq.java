
public interface TypesInCoq {
	//instruction types in BCEL the same as in umbra
	public static String[] instructions = new String[] {"aconst_null", "dadd", "ddiv", "dmul", "dneg", "drem", "dsub", 
		"fadd", "fdiv", "fmul", "fneg", "frem", "fsub", "iadd", "iand", "idiv", "imul", "ineg",
		"ior", "irem", "isub", "iushr", "ixor", "ladd", "land", "ldiv", "lmul", "lneg", "lor",
		"lrem", "lshl", "lshr", "lsub", "lushr", "lxor", "aaload", "aastore", "baload", "bastore",
		"caload", "castore", "daload", "dastore", "faload", "fastore", "iaload", "iastore",
		"laload", "lastore", "saload", "sastore", "arraylength", "athrow", "bipush", "goto", "goto_w",
		"if_acmpeq", "if_acmpne", "if_icmpeq", "if_icmpge", "if_icmpgt", "if_icmple", "if_icmplt", "if_icmpne",
		"ifeq", "ifge", "ifgt", "ifle", "iflt", "ifne", "ifnonnull", "ifnull", "jsr", "jsr_w", 
		"lookupswitch", "tableswitch", "breakpoint", "d2f", "d2i", "d2l", "f2d", "f2i", "f2l",
		"i2b", "i2c", "i2d", "i2f", "i2l", "i2s", "l2d", "l2f", "l2i", "anewarray", "checkcast",
		"getfield", "getstatic", "putfield", "putstatic", "invokeinterface", "invokespecial",
		"invokestatic", "invokevirtual", "instanceof", "ldc", "ldc_w", "ldc2_w", "multilinewarray",
		"new", "dcmpg", "dcmpl", "dconst", "fcmpg", "fcmpl", "fconst", "iconst", "iconst_0", "iconst_1", "iconst_2", "iconst_3", "iconst_4", "iconst_5", "iconst_m1", "impdep1", "impdep2",
		"lcmp", "lconst", "iinc", "aload", "aload_0", "aload_1", "aload_2", "aload_3",
		"astore", "astore_0", "astore_1", "astore_2", "astore_3", "dload", "dload_0", "dload_1", "dload_2", "dload_3",
		"dstore", "dstore_0", "dstore_1", "dstore_2", "dstore_3", "fload", "fload_0", "fload_1", "fload_2", "fload_3",
		"fstore", "fstore_0", "fstore_1", "fstore_2", "fstore_3", "iload", "iload_0", "iload_1", "iload_2", "iload_3",
		"istore", "istore_0", "istore_1", "istore_2", "istore_3", "lload", "lload_0", "lload_1", "lload_2", "lload_3",
		"lstore", "lstore_0", "lstore_1", "lstore_2", "lstore_3", "monitorenter", "monitorexit", "newarray", "nop", "ret", "areturn",
		"dreturn", "freturn", "ireturn", "lreturn", "return", "sipush", "dup", "dup_x1", "dup_x2",
		"dup2", "dup2_x1", "dup2_x2", "pop", "pop2", "swap"};

		//instructions with no parameter
	public static String[] single = new String[] {"aconst_null", "dadd", "ddiv", "dmul", "dneg" , 
		"drem", "dsub", "fadd", "fdiv", "fmul", "fneg", "frem", "fsub", "iadd", "iand", 
		"imul", "idiv", "ineg", "ior", "isub", "irem", "iushr", "ixor", "lsub", 
		"ladd", "land", "ldiv", "lmul", "lneg", "lor", "lrem", "lshl", "lshr", "lushr", "lxor", 
		"aaload", "aastore", "baload", "bastore", "caload", "castore", "daload", "dastore", "faload", "fastore", 
		"iaload", "iastore", "laload", "lastore", "saload", "sastore", 
		"arraylength", "athrow",  "iconst_m1", 
		"lcmp", 		
		"monitorenter", "monitorexit", "areturn", "dreturn", "freturn", "ireturn", "lreturn", "return", 
		"dup", "dup_x1", "dup_x2","dup2", "dup2_x1", "dup2_x2", "pop", "pop2", "swap"};

	//instructions with parameter inside
	public static String[] notsosingle = new String[] {
		"iconst_0", "iconst_1", "iconst_2", "iconst_3", "iconst_4", "iconst_5",
		"aload_0", "aload_1", "aload_2", "aload_3",
		"astore_0", "astore_1", "astore_2", "astore_3",
		"dload_0", "dload_1", "dload_2", "dload_3",
		"dstore_0", "dstore_1", "dstore_2", "dstore_3", 
		"fload_0", "fload_1", "fload_2", "fload_3",
		"fstore_0", "fstore_1", "fstore_2", "fstore_3",
		"iload_0", "iload_1", "iload_2", "iload_3",
		"istore_0", "istore_1", "istore_2", "istore_3", 
		"lload_0", "lload_1", "lload_2", "lload_3", 
		"lstore_0", "lstore_1", "lstore_2", "lstore_3"
		
	};
	
	//stack push
	public static String[] push = new String[] {"bipush", "sipush"};
	//jump
	public static String[] jump = new String[] {"goto", "goto_w", 
		"if_acmpeq", "if_acmpne", "if_icmpeq", "if_icmpge", "if_icmpgt", "if_icmple", "if_icmplt", "if_icmpne",
		"ifeq", "ifge", "ifgt", "ifle", "iflt", "ifne", "ifnonnull", "ifnull", "jsr", "jsr_w", 
		"lookupswitch", "tableswitch"};
	//two parameters  
	public static String[] incc = new String[] {"iinc"};
	//stack  
	public static String[] stack = new String[] {"aload", "astore", "dload", "dstore", 
		"fload", "fstore", "iload", "istore", "lload", "lstore"};
	//array
	public static String[] array = new String[] {"newarray"};
	//new
	public static String[] anew = new String[] {"anewarray", "checkcast", "instanceof", 
		"new"};
	//field
	public static String[] field = new String[] {"getfield", "getstatic", 
		"putfield", "putstatic"};
	//invokeinstr
	public static String[] invoke = new String[] {"invokeinterface", "invokespecial", 
		"invokestatic", "invokevirtual"};
	// "true" || "false" || "null" || "tr" || number + (number)
	public static String[] ldc = new String[] {"ldc", "ldc_w", "ldc2_w"};
	//cannot classify
	public static String[] unknown = new String[] { "breakpoint", "d2f", "d2i", "d2l", "f2d", "f2i", "f2l", 
		"i2b", "i2c", "i2d", "i2f", "i2l", "i2s", "l2d", "l2f", "l2i", "multilinewarray", 
		"dcmpg", "dcmpl", "dconst", "fcmpg", "fcmpl", "fconst", "iconst", "impdep1", "impdep2", 
		"lconst", "nop", "ret"};
	
	//object->number all will be type int
	public static String[] typeint = new String[] {
		"AtomicInteger", "AtomicLong","BigDecimal","BigInteger",
		"Double","Float","Integer","Long"
	};
	public static String[] typebyte = new String[] {
		"Byte"
	};
	public static String[] typeshort = new String[] {
		"Short"
	};
	public static String[] typebool = new String[] {
		"boolean"
	};	
	//FIXME deal with lconst_0
	
	
}
