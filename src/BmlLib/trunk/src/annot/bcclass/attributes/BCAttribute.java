package annot.bcclass.attributes;

import annot.bcclass.BMLConfig;

public interface BCAttribute {
	// method specification
	public static final String MethodSpecification = "MethodSpecification";
	public static final String ASSERT = "Assert";
	public static final String SET = "Set";
	public static final String BLOCKSPECIFICATION = "BlockSpecification"; 
	public static final String LOOPSPECIFICATION = "LoopSpecification";
	
	// class specification
	public static final String HISTORY_CONSTRAINTS = "HistoryConstraints";
	public static final String CLASSINVARIANT = "ClassInvariant";
	public static final String SECOND_CONSTANT_POOL = "SecondConstantPool";
}
