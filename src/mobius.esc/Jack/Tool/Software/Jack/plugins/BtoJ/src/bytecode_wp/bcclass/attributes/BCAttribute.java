/*
 * Created on 6 mai 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bytecode_wp.bcclass.attributes;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
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
